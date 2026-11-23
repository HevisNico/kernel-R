"""M2 of CALIBRATION_PROPOSAL.md: the instrument for the layered calibration. Development only.

New file. The pushed modules (deck, session, run, spec) are imported and not modified (owner rule: a pushed file is
never changed). What this adds:

1. **Per-port leak control.** The deck of deck.build with one imposed-leak node per port (`gl<cell><port>`, zero by
   default) instead of the shared `gl`: a scan can raise one stored voltage alone (method of
   network-circuit/net.py `leak_per_port` and campaign 6's scan6.py).
2. **The stored voltage of every port in every slot.** u_p = mean(vmem_p) - mean(sum_p) over the 35 us before the
   slot's gate setting (T - gate_lead), as scan6 measures u near the end of the previous slot. Recorded in each slot
   record as `u` = {cell: [u_1, u_2]} in volts. The slot after the last test is measured too (`u_end`).
3. **Scans per (cell, group), parallel over cells, from the training bracket.** After the tests, in the same session
   (the same mismatch sample). Each cell's groups are scanned one after another (an either cell's two lines share its
   main capacitor); different cells are scanned in the same slots. A scan is campaign 6's bisection along the
   training path u_p(s) = u_p(0) - s D_p (scan6.scan), with three changes:
   - no ascent from s = 0: the bracket starts from the cell's own training reads (the last silent read and the
     first firing read, at their measured s);
   - a read injects ideal pulses at the gate's amplitude (0.49 on both, 1.0 on copy and either); for a both cell the
     second port's pulse keeps the median offset of its training reads (the rail offset);
   - one slot carries a read and, in its tail, the leak or the dose toward the next state.
   It stops when (hi - lo) times the larger D_p is at most 20 uV (scan6's BRACKET_V), or after `max_slots`.
   No repeats, no one-sided set and no both-lines check here (not in M2's scope).

The scores (mapping, decoder check, question 1) are computed from the record by scores.py.
"""
from fractions import Fraction as F
import json
import math
from pathlib import Path
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import deck as deckmod  # noqa: E402
import run as runmod  # noqa: E402
import session as sess  # noqa: E402
import spec as specmod  # noqa: E402

CAL = json.loads((HERE / "calibration.json").read_text())


# ------------------------------------------------------------------------------------------------ the deck

def deck_text(s, cfg):
    """deck.build with one leak node per port."""
    text = deckmod.build(s, cfg)
    cells, _ = deckmod.names(s)
    text = deckmod.swap(text, ".subckt rcell vdd vr0 vfire vreopen vcm vhi vlo vpre gl ",
                        ".subckt rcell vdd vr0 vfire vreopen vcm vhi vlo vpre gl1 gl2 ")
    for p in deckmod.PORTS:
        old = f"x{p} vq vr0 pb vmem{p} vdd vcm vhi vlo vpre vinit{p} ks{p} kr{p} kp{p} ts{p} amp{p} gl rport"
        text = deckmod.swap(text, old, old.replace(" gl rport", f" gl{p} rport"))
    for c in cells:
        old = f"x{c} vdd vr0 vfire vreopen vcm vhi vlo vpre gl "
        new = f"x{c} vdd vr0 vfire vreopen vcm vhi vlo vpre gl{c}1 gl{c}2 "
        text = deckmod.swap(text, old, new)
        text = deckmod.swap(text, "vgl gl 0 dc 0\n", "".join(f"vgl{c}{p} gl{c}{p} 0 pulse(0 0 1 1n 1n 1u 2)\n" for p in deckmod.PORTS)
                            + "vgl gl 0 dc 0\n")
    return text


# ------------------------------------------------------------------------------------------------ one scan, pure

class ScanCell:
    """The scan state machine of one cell (no simulator): its groups one after another. Each step returns an action
    from the current u; `result` gives a read's FIRE bit. Units: volts and stages."""

    def __init__(self, name, groups, u0, D, tol_V, bracket_V, step_V, max_slots):
        self.name, self.groups, self.u0, self.D = name, list(groups), u0, D
        self.tol, self.bracket, self.step, self.max_slots = tol_V, bracket_V, step_V, max_slots
        self.done, self.results, self.cur = [], [], None
        self._next_group()

    def _next_group(self):
        """The bracket is made of this scan's own reads only (rule D3): L = the largest silent state read, U = the
        smallest firing state read. The training reads only choose the first targets: the stop state first (where the
        cell already is), then the last silent training state."""
        self.cur = None
        while self.groups:
            g = self.groups.pop(0)
            if g.get("lo") is None or g.get("hi") is None:
                self.results.append(dict(group=g["group"], ok=False, why="no training bracket (" + g.get("why", "") + ")"))
                continue
            self.cur = dict(g, reads=[], slots=0, L=None, U=None, tried_lo=False, s=F(g["hi"]))
            return

    def _next_target(self):
        c = self.cur
        L, U = c["L"], c["U"]
        if U is None:                                   # no FIRE yet: up by half a stage (an ascent above the stop)
            return min(max(L, F(c["hi"])) + F(1, 2), F(8)) if L is not None else F(c["hi"])
        if L is None:                                   # no silence yet: the last silent training state, then down
            if not c["tried_lo"] and F(c["lo"]) < U:
                c["tried_lo"] = True
                return F(c["lo"])
            return max(U - F(1, 2), F(0))
        return (L + U) / 2

    def target(self, s):
        return {p: self.u0[p] - float(s) * self.D[p] for p in self.cur["ports"]}

    def action(self, u, count=True):
        """('read', ports) when at the current state within tolerance, ('dose', ports) to lower, ('leak', {port: V})
        to raise, or None when every group is done. count=False: a look at the next action (for a read slot's tail)."""
        if self.cur is None:
            return None
        if count:
            self.cur["slots"] += 1
        if self.cur["slots"] > self.max_slots:
            self.results.append(dict(group=self.cur["group"], ok=False, why=f"more than {self.max_slots} slots",
                                     reads=self.cur["reads"], slots=self.cur["slots"] - 1))
            self._next_group()
            return self.action(u)
        goal = self.target(self.cur["s"])
        gap = {p: goal[p] - u[p] for p in goal}
        low = tuple(p for p in gap if gap[p] < -self.tol)
        if low:
            return ("dose", low)
        # undershoot by 4 % of the leak (the leak gain is refined on the run), at least half the tolerance; scan6 kept
        # 30 uV, which with a 10 uV tolerance costs one more slot per state
        high = {p: (g if g <= 0.05e-3 else min(g - max(self.tol / 2, 0.04 * g), self.step)) for p, g in gap.items() if g > self.tol}
        if high:
            return ("leak", high)
        return ("read", tuple(self.cur["ports"]))

    def measured_s(self, u):
        """The state actually read: the mean over the moving ports of (u0 - u) / D, exactly (from the float u)."""
        ps = self.cur["ports"]
        return sum(F(self.u0[p] - u[p]) / F(self.D[p]) for p in ps) / len(ps)

    def result(self, fired, u):
        """The bracket is kept at the measured states of the reads, not at their targets (a change from scan6, which
        keeps the targets within 2 uV): the tolerance then bounds only how close a read lands to its target."""
        c = self.cur
        s_read = self.measured_s(u)
        c["reads"].append(dict(target=str(c["s"]), s=str(s_read), fired=bool(fired), u={str(p): u[p] for p in c["ports"]}))
        if fired:
            c["U"] = s_read if c["U"] is None else min(c["U"], s_read)
        else:
            c["L"] = s_read if c["L"] is None else max(c["L"], s_read)
        L, U = c["L"], c["U"]
        width = max(self.D[p] for p in c["ports"])
        why = None
        if L is not None and U is not None and L >= U:
            why = f"contradictory: silent at {float(L):.4f}, FIRE at {float(U):.4f}"
        elif U is None and L is not None and L >= 8:
            why = "no FIRE below s = 8"
        elif L is None and U is not None and U <= 0:
            why = "fires at the preset (s = 0)"
        if why:
            self.results.append(dict(group=c["group"], ok=False, why=why, reads=c["reads"], slots=c["slots"]))
            self._next_group()
            return
        if L is not None and U is not None and (U - L) * F(width) <= F(self.bracket):
            self.results.append(dict(group=c["group"], ok=True, s_star=str((L + U) / 2), half_bracket=str((U - L) / 2),
                                     bracket=[str(L), str(U)], reads=c["reads"], slots=c["slots"], consistent=True,
                                     native=True))
            self._next_group()
        else:
            c["s"] = self._next_target()


# ------------------------------------------------------------------------------------------------ the network

class CalNetwork(runmod.Network):
    """run.Network on the per-port-leak deck, recording u of every port at every slot's setting."""

    def __init__(self, s, cfg, out, seed):              # run.Network.__init__ with the deck of deck_text
        self.s, self.cfg = s, cfg
        st = cfg["stimulus"]
        self.tu_ns = round(st["tu_s"] * 1e9)
        self.grid, self.goff = round(st["noise_step_s"] * 1e9), round(st["snap_offset_s"] * 1e9)
        self.lead_ns = round(st["lead_s"] * 1e9)
        self.tim = specmod.timing(s, cfg)
        self.delta = self.ns(self.tim["delta"])
        self.cells, self.invs = deckmod.names(s)
        self.text = deck_text(s, cfg)
        cal = cfg["calendar"]
        self.slot_ns = self.ns(cal["slot_tu"])
        n_part = sum(len(self.partitions(l, g)) for l in range(len(s["layers"])) for g in range(2))
        n_scan = 2 * CAL["scan"]["max_slots"] * sum(specmod.GROUPS[n["gate"]] for nodes in s["layers"] for n in nodes)
        horizon = (cal["first_slot_tu"] + cal["slot_tu"] * (n_part * cal["max_rounds"] + 2 ** s["m"] + 2 + n_scan)) * st["tu_s"]
        self.ses = sess.Session(out, self.text, cfg, seed=seed, stop_s=horizon)
        self.ses.saved = [f"x{c}.p" for c in self.cells + self.invs] + \
            [f"x{c}.vmem{p}" for c in self.cells for p in deckmod.PORTS] + \
            [f"x{c}.x{p}.sum" for c in self.cells for p in deckmod.PORTS]
        self.gate_state = {}
        self.slots = []
        self.next_T = self.snap(self.ns(CAL["first_slot_tu"]))     # later than config's: u(0) after the preset settles
        self.last_u = None
        self.n_meas = 0

    def ns(self, v):
        return self._ns(v)

    def mean(self, node, lo, hi):
        self.n_meas += 1
        name = f"u{self.n_meas}"
        self.ses.cmd(f"meas tran {name} avg v({node}) from={lo:.12g} to={hi:.12g}")
        out = self.ses.cmd(f"print {name}")
        return float(out.strip().split("=")[-1])

    def measure_u(self):
        """u of every port over the 35 us before now."""
        hi = self.ses.now
        lo = hi - CAL["u_window_s"]
        return {c: [self.mean(f"x{c}.vmem{p}", lo, hi) - self.mean(f"x{c}.x{p}.sum", lo, hi) for p in deckmod.PORTS]
                for c in self.cells}

    def set_gates(self, ungated):
        """Called by run.Network.slot right after the run reached T - gate_lead: u is measured first."""
        self.last_u = self.measure_u()
        super().set_gates(ungated)

    def slot(self, kind, lines, top, allowed, ungated, info):
        rec = super().slot(kind, lines, top, allowed, ungated, info)
        rec["u"] = self.last_u
        # a second rise is measured again from 1 us after the first: run.Network's rise=2 can catch the same edge
        # crossing 0.9 V twice (records.py, same-edge rule)
        gap = CAL.get("same_edge_ns", 1000)
        for r in rec["reads"]:
            if r.get("second") is not None and r["second"] - r["latch"] < gap:
                again = self.ses.rise(f"xc{r['layer']}_{r['index']}.p", (r["latch"] + gap) * 1e-9)
                r["second"] = None if again is None else round(again * 1e9)
        for j, v in enumerate(rec["inv"]):
            if v.get("second") is not None and v["second"] - v["latch"] < gap:
                again = self.ses.rise(f"xn{j}.p", (v["latch"] + gap) * 1e-9)
                v["second"] = None if again is None else round(again * 1e9)
        return rec

    # ---------------------------------------------------------------------------------------- scan slots

    def gate_ports(self, writing):
        """writing: set of (cell, port) whose dose source is on; every other port read-only."""
        idis = self.cfg["circuit"]["idis"]
        for c in self.cells:
            for p in deckmod.PORTS:
                v = idis if (c, p) in writing else 0.0
                if self.gate_state.get((c, p)) != v:
                    self.ses.alter_dc(f"i.x{c}.x{p}.idis", v)
                    self.gate_state[(c, p)] = v
            self.gate_state.pop(c, None)                   # run.Network's per-cell state no longer applies

    def scan_slot(self, decide, tail=None):
        """One slot of the scan phase. At the slot's setting u is measured, the leak gain refined, and
        decide(u) gives the actions: {cell: ('read', ports, offsets) | ('dose', ports) | ('leak', {port: volts})}.
        Reads are at T + delta (+ offset); a dose is a clock-only pulse at T + dose_tu with the port's dose source on; a
        leak is a conductance on [T + leak_on_tu, T + leak_off_tu], from the leak gain. Returns (actions, fired, u)."""
        cal, sc = self.cfg["calendar"], CAL["scan"]
        T = self.next_T
        self.next_T = self.snap(T + self.slot_ns)
        self.ses.run((T - self.ns(cal["gate_lead_tu"])) * 1e-9)
        u = self.measure_u()
        self.update_leak_gain(u)
        actions = decide(u)
        if not actions:
            return actions, {}, u
        writing = {(c, p) for c, a in actions.items() if a[0] == "dose" for p in a[1]}
        self.gate_ports(writing)
        watch, fired = {}, {}
        for c, a in actions.items():
            gate = self.gate_of(c)
            if a[0] == "read":
                first = T + self.delta
                last = first
                for p in a[1]:
                    date = self.snap(first + self.ns(a[2].get(p, 0)))
                    last = max(last, date)
                    self.pulse(c, p, date, self.cfg["stimulus"]["amp"][gate])
                watch[f"x{c}.p"] = (c, first, last)
                fired[c] = False
            elif a[0] == "dose":
                for p in a[1]:
                    self.pulse(c, p, self.snap(T + self.ns(sc["dose_tu"])), 0.0)
            elif a[0] == "leak":
                for p, volts in a[1].items():
                    g = self.leak_gain.get((c, p), sc["leak_S_per_mV"]) * volts * 1e3
                    on, off = T + self.ns(sc["leak_on_tu"]), T + self.ns(sc["leak_off_tu"])
                    self.ses.alter_pulse(f"vgl{c}{p}", [0, g, on * 1e-9, "1n", "1n", (off - on) * 1e-9, 2])
                    self.leak_used[(c, p)] = (g, u[c][p - 1])
        end = (T + self.ns(sc["watch_tu"])) * 1e-9
        live = dict(watch)
        while live:
            t = self.ses.run(end, list(live))
            if t >= end - 1e-12:
                break
            for node in list(live):
                if self.ses.last(f"v({node})") > 0.9:
                    c, first, last = live.pop(node)
                    lt = self.ses.rise(node, (first - 1000) * 1e-9)
                    fired[c] = lt is not None and lt * 1e9 <= last + self.ns(self.tim["dmax_design"])
        tails = {}
        if tail is not None:                               # the leak toward the next state, in the read slot's tail
            sc = CAL["scan"]
            for c, a in actions.items():
                if a[0] != "read":
                    continue
                nxt = tail(c, fired.get(c, False), u)
                if nxt is None:
                    continue
                tails[c] = {str(p): v for p, v in nxt.items()}
                for p, volts in nxt.items():
                    g = self.leak_gain.get((c, p), sc["leak_S_per_mV"]) * volts * 1e3
                    on, off = T + self.ns(sc["leak_on_tu"]), T + self.ns(sc["leak_off_tu"])
                    assert self.ses.now * 1e9 < on - 200, "the tail leak must be set before it starts"
                    self.ses.alter_pulse(f"vgl{c}{p}", [0, g, on * 1e-9, "1n", "1n", (off - on) * 1e-9, 2])
                    self.leak_used[(c, p)] = (g, u[c][p - 1])
        self.slots.append(dict(kind="scan", T=T, u=u, actions={c: [a[0], list(a[1]) if a[0] != "leak" else
                                                                  {str(p): v for p, v in a[1].items()}] for c, a in actions.items()},
                               fired=fired, tail=tails))
        return actions, fired, u

    def gate_of(self, c):
        k, i = c[1:].split("_")
        return self.s["layers"][int(k) - 1][int(i)]["gate"]

    def update_leak_gain(self, u):
        """The leak's scale, refined on the run (scan6): conductance per mV actually moved."""
        for (c, p), (g, before) in list(self.leak_used.items()):
            moved_mV = (u[c][p - 1] - before) * 1e3
            if moved_mV > 0.005:
                self.leak_gain[(c, p)] = g / moved_mV
            self.leak_used.pop((c, p))


# ------------------------------------------------------------------------------------------------ the training path

def training_path(s, rec):
    """From a record with `u` per slot: u0 per port (the first slot), D_p (mean move of the port over the silent
    lessons that wrote it), and per (cell, group) the measured s of each lesson read with its FIRE bit."""
    slots = rec["slots"]
    u0 = {c: v for c, v in slots[0]["u"].items()}

    def u_after(idx):
        return slots[idx + 1]["u"] if idx + 1 < len(slots) else rec["u_end"]
    moves = {}
    for x in rec["lessons"]:
        c = f"c{x['layer']}_{x['cell']}"
        r = next(r for r in slots[x["slot"]]["reads"] if r["layer"] == x["layer"] and r["index"] == x["cell"])
        n = s["layers"][x["layer"] - 1][x["cell"]]
        ports = [a + 1 for a in range(2) if specmod.GROUP_MASK[n["gate"]][x["group"]][a]]
        if r["emission"] is None:
            for p in ports:
                moves.setdefault((c, p), []).append(slots[x["slot"]]["u"][c][p - 1] - u_after(x["slot"])[c][p - 1])
    D = {k: sum(v) / len(v) for k, v in moves.items()}
    groups = {}
    for x in rec["lessons"]:
        c = f"c{x['layer']}_{x['cell']}"
        n = s["layers"][x["layer"] - 1][x["cell"]]
        ports = [a + 1 for a in range(2) if specmod.GROUP_MASK[n["gate"]][x["group"]][a]]
        r = next(r for r in slots[x["slot"]]["reads"] if r["layer"] == x["layer"] and r["index"] == x["cell"])
        u = slots[x["slot"]]["u"][c]
        w = [(u0[c][p - 1] - u[p - 1]) / D[(c, p)] for p in ports if (c, p) in D]
        g = groups.setdefault((c, x["group"]), dict(ports=ports, reads=[], offsets=[]))
        g["reads"].append(dict(round=x["round"], s=sum(w) / len(w) if w else None, fired=r["emission"] is not None))
        arr = [a for a in r["arrivals"] if a is not None]
        if len(arr) == 2:
            g["offsets"].append({p: r["arrivals"][p - 1] - min(arr) for p in ports})
    return u0, D, groups


def bracket(g):
    """The training bracket: the measured s of the last silent read before the first FIRE, and of that FIRE."""
    reads = sorted(g["reads"], key=lambda r: r["round"])
    first = next((i for i, r in enumerate(reads) if r["fired"]), None)
    if first is None:
        return None, None, "never fired"
    if first == 0:
        return None, None, "fired at round 0"
    lo, hi = reads[first - 1]["s"], reads[first]["s"]
    if lo is None or hi is None or not lo < hi:
        return None, None, "bracket not ordered"
    return F(lo), F(hi), ""


def median(xs):
    xs = sorted(xs)
    return xs[len(xs) // 2] if xs else 0


def scan_all(net, rec, log=print, solo=False):
    """The scan phase, after the tests, in the same session."""
    s, sc = net.s, CAL["scan"]
    net.ses.run((net.next_T - net.ns(net.cfg["calendar"]["gate_lead_tu"])) * 1e-9)
    u_now = net.measure_u()
    rec["u_end"] = u_now
    u0, D, groups = training_path(s, rec)
    tu_ns = net.tu_ns
    cells, groups_of = {}, {}
    for c in net.cells:
        gs = []
        for (cc, g), info in sorted(groups.items()):
            if cc != c:
                continue
            lo, hi, why = bracket(info)
            offs = {}
            if info["offsets"]:
                offs = {p: F(median([o[p] for o in info["offsets"]]), tu_ns) for p in info["ports"]}
            gs.append(dict(group=g, ports=info["ports"], lo=lo, hi=hi, why=why, offsets=offs))
        groups_of[c] = [dict(x) for x in gs]
        if any((c, p) not in D for g in gs for p in g["ports"]):
            cells[c] = None
            log(f"scan {c}: no dose measured")
            continue
        cells[c] = ScanCell(c, gs, {p: u0[c][p - 1] for p in (1, 2)}, {p: D.get((c, p), 0.0) for p in (1, 2)},
                            sc["tol_V"], sc["bracket_V"], sc["step_V"], sc["max_slots"])
    net.leak_gain, net.leak_used = {}, {}
    del u_now
    t0 = time.time()
    n = run_scans(net, cells)
    out = {c: (None if sc_ is None else sc_.results) for c, sc_ in cells.items()}
    for c, res in out.items():
        for r in res or []:
            log(f"scan {c} group {r['group']}: " + (f"s* {float(F(r['s_star'])):.5f} +- {float(F(r['half_bracket'])):.5f} in {r['slots']} slots"
                                                     if r["ok"] else f"failed: {r['why']}"))
    result = dict(slots=n, wall_s=time.time() - t0, u0={c: v for c, v in u0.items()},
                  D={f"{c}/{p}": v for (c, p), v in D.items()}, cells=out)
    if solo:                                            # D4: each cell again, alone, from where the parallel scan left it
        t1, n_solo, solo_out = time.time(), 0, {}
        for c in net.cells:
            if cells.get(c) is None:
                continue
            gs = []
            for r in out[c]:
                if not r.get("ok"):
                    continue
                g = next(x for x in groups_of[c] if x["group"] == r["group"])
                gs.append(dict(g, lo=F(r["bracket"][0]), hi=F(r["bracket"][1])))
            one = {c: ScanCell(c, gs, cells[c].u0, cells[c].D, sc["tol_V"], sc["bracket_V"], sc["step_V"], sc["max_slots"])}
            n_solo += run_scans(net, one)
            solo_out[c] = one[c].results
            for r in one[c].results:
                log(f"solo scan {c} group {r['group']}: " + (f"s* {float(F(r['s_star'])):.5f} +- {float(F(r['half_bracket'])):.5f} in {r['slots']} slots"
                                                              if r["ok"] else f"failed: {r['why']}"))
        result["solo"] = dict(slots=n_solo, wall_s=time.time() - t1, cells=solo_out)
    return result


def run_scans(net, cells):
    """The scan slots of the given ScanCells, in parallel, until every group is done. Returns the slot count."""
    n = 0

    def decide(ub):
        u = {c: {p: ub[c][p - 1] for p in (1, 2)} for c in net.cells}
        actions = {}
        for c, sc_ in cells.items():
            if sc_ is None:
                continue
            a = sc_.action(u[c])
            if a is None:
                continue
            actions[c] = ("read", a[1], {p: sc_.cur["offsets"].get(p, 0) for p in a[1]}) if a[0] == "read" else a
        return actions

    def tail(c, fired, ub):
        """The read's result, then the next action if it is a leak (the read moves no stored voltage)."""
        u = {p: ub[c][p - 1] for p in (1, 2)}
        cells[c].result(fired, u)
        if cells[c].cur is None:
            return None
        a = cells[c].action(u, count=False)
        if a is not None and a[0] == "leak":
            cells[c].cur["slots"] += 1
            return a[1]
        return None
    while True:
        actions, fired, ub = net.scan_slot(decide, tail)
        if not actions:
            return n
        n += 1


# ------------------------------------------------------------------------------------------------ one instance

def cal_run(s, cfg, out, seed, log=print, solo=False):
    """run.train_and_test's calendar on CalNetwork, then the scans. Writes record.json (with u, u_end, scans)."""
    out = Path(out)
    t_start = time.time()
    net = CalNetwork(s, cfg, out, seed)
    net.ses.cmd("echo ready")
    t_setup, c_setup = time.time() - t_start, runmod.cpu_of(net.ses.p.pid)
    calc = cfg["calendar"]
    t0 = time.time()
    lessons, words, tests, scans = [], {}, [], None
    status = "done"
    c_train = c_test = None
    t_train = t_test = 0.0
    try:
        for l in range(len(s["layers"])):
            k = l + 1
            for g in range(2):
                for stim, members in net.partitions(l, g):
                    x = specmod.line_pattern(s, stim)
                    state = {i: dict(r=0, run=0, word="") for i in members}
                    while state:
                        cells = set(state)
                        r_ = net.slot("lesson", x, k, {k: cells}, {f"c{k}_{i}" for i in cells},
                                      dict(layer=k, group=g, cells=sorted(cells), stimulus=sorted(stim)))
                        idx = len(net.slots) - 1
                        for i in sorted(cells):
                            r = next(r for r in r_["reads"] if r["layer"] == k and r["index"] == i)
                            f = r["emission"] is not None
                            st = state[i]
                            lessons.append(dict(layer=k, cell=i, group=g, round=st["r"], slot=idx))
                            st["word"] += "F" if f else "s"
                            st["run"] = st["run"] + 1 if f else 0
                            st["r"] += 1
                            if st["run"] >= calc["hold"] or st["r"] >= calc["max_rounds"]:
                                words[(k, i, g)] = st["word"]
                                log(f"lesson layer {k} cell {i} group {g}: {st['word']}")
                                del state[i]
        t_train, c_train = time.time() - t0, runmod.cpu_of(net.ses.p.pid)
        for x in specmod.patterns(s["m"]):
            r_ = net.slot("test", specmod.rails(s, x), len(s["layers"]), {}, set(), dict(pattern=[int(b) for b in x]))
            tests.append(len(net.slots) - 1)
            top = r_["reads"][-1]
            log(f"test {''.join(str(int(b)) for b in x)}: out {'FIRE' if top['emission'] is not None else 'silent'}")
        t_test, c_test = time.time() - t0 - t_train, runmod.cpu_of(net.ses.p.pid)
        partial = dict(slots=net.slots, lessons=lessons)
        scans = scan_all(net, partial, log, solo=solo)
        u_end = partial["u_end"]
    except Exception as e:
        status = f"failed: {e}"
        log(status)
        u_end = None
    finally:
        simulated = net.ses.now
        c_end = runmod.cpu_of(net.ses.p.pid)
        net.ses.close()
    n_test_slots = len(tests)
    n_lesson_slots = len({x["slot"] for x in lessons})
    record = dict(tag=s["tag"], seed=seed, status=status, cells=net.cells, inverters=net.invs,
                  cost=dict(wall_setup_s=t_setup, wall_train_s=t_train, wall_test_s=t_test,
                            wall_scan_s=None if scans is None else scans["wall_s"],
                            cpu_setup_s=c_setup, cpu_end_s=c_end, simulated_s=simulated,
                            lesson_slots=n_lesson_slots, test_slots=n_test_slots,
                            scan_slots=None if scans is None else scans["slots"]),
                  words={f"{k}/{i}/{g}": w for (k, i, g), w in words.items()},
                  lessons=lessons, tests=tests, slots=net.slots, u_end=u_end, scans=scans)
    (out / "record.json").write_text(json.dumps(record, indent=1, default=str) + "\n")
    return record
