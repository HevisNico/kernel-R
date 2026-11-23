"""One instance: build the deck, train layer by layer, test every input pattern, write record.json.

Calendar. Slots are `slot_tu` apart, each with base date T on the noise grid. At T - gate_lead the write gates are
set (dose source idis of every port: 8.2 nA for the cells of the lesson, 0 elsewhere). The lines (layer 0) emit at
s0 = T (no front end) or, with the front end, the inverters start at T (input current on [T, T + tau] when the input
is present) and the direct rails emit at s0 = T + emit_early. Every emission of a line or a cell is routed: each port
that the spec wires to it receives a pulse at arrival = emission + delta.

Emission date. The router launches the pulses of a FIRE at the first date of the noise grid at or after
latch + delta (latch: the rise of the protection latch through 0.9 V). The emission date recorded for the Lean trace
is that launch date minus delta: it is between the latch date and the latch date + 0.4 us. Both are recorded.

Lessons (TrainingTrace order: layer, cell, group, round). For layer l and group g, the cells of l whose group g has the
same stimulus share one slot per round (config share_lessons). The lower layers replay read-only and are routed to the
lesson's cells only. A cell's rounds go on until it has fired `hold` times in a row (or max_rounds); the cell then
leaves the lesson. Its maxWrites in the Lean cell is its number of rounds minus one (the least over its groups).
Tests: every input pattern in code order, all cells read-only, routed through every layer.

  run.py SPEC OUT SEED          (or through lnet.py run)
"""
from fractions import Fraction as F
import json
import os
from pathlib import Path
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import deck as deckmod  # noqa: E402
import session as sess  # noqa: E402
import spec as specmod  # noqa: E402


def cpu_of(pid):
    try:
        f = Path(f"/proc/{pid}/stat").read_text().rsplit(")", 1)[1].split()
        return (int(f[11]) + int(f[12])) / os.sysconf("SC_CLK_TCK")
    except Exception:
        return None


class Network:
    def __init__(self, s, cfg, out, seed):
        self.s, self.cfg = s, cfg
        st = cfg["stimulus"]
        self.tu_ns = round(st["tu_s"] * 1e9)
        self.ns = lambda v: self._ns(v)
        self.grid, self.goff = round(st["noise_step_s"] * 1e9), round(st["snap_offset_s"] * 1e9)
        self.lead_ns = round(st["lead_s"] * 1e9)
        self.tim = specmod.timing(s, cfg)
        self.delta = self.ns(self.tim["delta"])
        self.cells, self.invs = deckmod.names(s)
        self.text = deckmod.build(s, cfg)
        cal = cfg["calendar"]
        self.slot_ns = self.ns(cal["slot_tu"])
        n_part = sum(sum(1 for _ in self.partitions(l, g)) for l in range(len(s["layers"])) for g in range(2))
        horizon = (cal["first_slot_tu"] + cal["slot_tu"] * (n_part * cal["max_rounds"] + 2 ** s["m"] + 2)) * st["tu_s"]
        self.ses = sess.Session(out, self.text, cfg, seed=seed, stop_s=horizon)
        self.ses.saved = [f"x{c}.p" for c in self.cells + self.invs]
        self.gate_state = {}
        self.slots = []
        self.next_T = self.snap(self.ns(cal["first_slot_tu"]))

    def _ns(self, v):
        x = F(str(v)) * self.tu_ns
        assert x.denominator == 1, f"{v} tu is not a whole number of ns"
        return int(x)

    def snap(self, t):
        k = -(-(t - self.goff) // self.grid)
        return max(k, 0) * self.grid + self.goff

    def partitions(self, l, g):
        nodes = self.s["layers"][l]
        groups = {}
        for i, n in enumerate(nodes):
            if g < specmod.GROUPS[n["gate"]]:
                key = n["stimulus"][g] if self.cfg["calendar"]["share_lessons"] else (i,)
                groups.setdefault(key, []).append(i)
        return list(groups.items())

    # ------------------------------------------------------------------ stimulus

    def set_gates(self, ungated):
        idis = self.cfg["circuit"]["idis"]
        for c in self.cells:
            v = idis if c in ungated else 0.0
            if self.gate_state.get(c) != v:
                for p in deckmod.PORTS:
                    self.ses.alter_dc(f"i.x{c}.x{p}.idis", v)
                self.gate_state[c] = v

    def pulse(self, c, port, date_ns, amp):
        st = self.cfg["stimulus"]
        d, tu, cyc, lead = date_ns * 1e-9, st["tu_s"], st["cycle_tu"] * st["tu_s"], st["lead_s"]
        assert date_ns - self.lead_ns >= self.ses.now * 1e9 + 200, (c, port, date_ns, self.ses.now)
        self.ses.alter_pulse(f"vks{c}{port}", [0, 1, d, "1n", "1n", tu - 1e-9, 2])
        self.ses.alter_pulse(f"vkr{c}{port}", [1, 0, d - lead, "1n", "1n", cyc + lead, 2])
        self.ses.alter_pulse(f"vkp{c}{port}", [0, 1, d, "1n", "1n", cyc, 2])
        self.ses.alter_dc(f"vts{c}{port}", d)
        self.ses.alter_dc(f"vamp{c}{port}", amp)

    def inverter(self, x, T_ns, present):
        d, tu = self.cfg["inverter"], self.cfg["stimulus"]["tu_s"]
        T = T_ns * 1e-9
        self.ses.alter_pulse(f"vkh{x}", [0, 1.8, T + d["h"] * tu, "1n", "1n", d["hl"] * tu - 1e-9, 2])
        self.ses.alter_pulse(f"vki{x}", [1.8, 0, T, "1n", "1n", d["tau"] * tu - 1e-9, 2])
        self.ses.alter_pulse(f"vkj{x}", [0, 1, T if present else 1.0, "1n", "1n", d["tau"] * tu - 1e-9, 2])
        self.ses.alter_pulse(f"vkr{x}", [0, 1.8, T + d["D"] * tu, "1n", "1n", d["reset_len"] * tu - 1e-9, 2])
        self.ses.alter_pulse(f"vkb{x}", [1.8, 0, T + d["D"] * tu, "1n", "1n", d["reset_len"] * tu - 1e-9, 2])

    # ------------------------------------------------------------------ one slot

    def slot(self, kind, lines, top, allowed, ungated, info):
        """lines: the line pattern (with a front end: the rails of the input pattern). top: the highest layer routed
        (1-based). allowed: {layer: set of cell indices} routed at that layer (None: all). ungated: cell names that may
        write. Returns the slot record."""
        s, tim, cal = self.s, self.tim, self.cfg["calendar"]
        T = self.next_T
        self.next_T = self.snap(T + self.slot_ns)
        self.ses.run((T - self.ns(cal["gate_lead_tu"])) * 1e-9)
        self.set_gates(ungated)
        rec = dict(kind=kind, T=T, info=info, lines=[None] * s["lines"], inv=[], reads={})
        starts = {k: T + self.ns(tim["offset"][k]) for k in tim["offset"]}
        for k in range(1, top + 1):
            for i in range(len(s["layers"][k - 1])):
                if allowed.get(k) is None or i in allowed[k]:
                    rec["reads"][(k, i)] = dict(start=starts[k], arrivals=[None, None], latch=None, emission=None, second=None)
        watch = {}                                         # node -> (what, since)

        def emit(layer, i, date):
            """Route an emission of layer `layer` (0: line i) at `date` to the next layer."""
            if layer == 0:
                rec["lines"][i] = date
            if layer >= top:
                return
            for j, n in enumerate(s["layers"][layer]):
                if (layer + 1, j) not in rec["reads"]:
                    continue
                for a in range(2):
                    if n["source"][a] == i:
                        arr = date + self.delta
                        r = rec["reads"][(layer + 1, j)]
                        assert r["arrivals"][a] is None
                        r["arrivals"][a] = arr
                        c = f"c{layer + 1}_{j}"
                        self.pulse(c, a + 1, arr, self.cfg["stimulus"]["amp"][n["gate"]])
                        watch.setdefault(f"x{c}.p", (("cell", layer + 1, j), arr))

        if s["front"]:
            m = s["m"]
            for j in range(m):
                present = bool(lines[j])
                self.inverter(f"n{j}", T, present)
                rec["inv"].append(dict(start=T, arrival=T if present else None, latch=None, emission=None, second=None))
                watch[f"xn{j}.p"] = (("inv", j), T)
            for j in range(m):
                if lines[j]:
                    emit(0, j, starts[0])
        else:
            for j in range(s["lines"]):
                if lines[j]:
                    emit(0, j, starts[0])
        end = (T + self.ns(cal["watch_tu"])) * 1e-9
        fired = set()
        while True:
            live = [n for n in watch if n not in fired]
            if not live:
                break
            t = self.ses.run(end, live)
            if t >= end - 1e-12:
                break
            for node in live:
                if self.ses.last(f"v({node})") <= 0.9:
                    continue
                what, since = watch[node]
                latch = self.ses.rise(node, (since - 1000) * 1e-9)
                assert latch is not None, node
                fired.add(node)
                lt = round(latch * 1e9)
                launch = self.snap(lt + self.delta) - self.delta
                if what[0] == "inv":
                    rec["inv"][what[1]].update(latch=lt, emission=launch)
                    emit(0, s["m"] + what[1], launch)
                else:
                    r = rec["reads"][(what[1], what[2])]
                    r.update(latch=lt, emission=launch)
                    emit(what[1], what[2], launch)
        for node, (what, since) in watch.items():          # a second rise within the slot, if any
            if node in fired:
                two = self.ses.rise(node, (since - 1000) * 1e-9, 2)
                if two is not None:
                    tgt = rec["inv"][what[1]] if what[0] == "inv" else rec["reads"][(what[1], what[2])]
                    tgt["second"] = round(two * 1e9)
        rec["reads"] = [dict(layer=k, index=i, **r) for (k, i), r in sorted(rec["reads"].items())]
        self.slots.append(rec)
        return rec


def train_and_test(s, cfg, out, seed, log=print):
    out = Path(out)
    t_start = time.time()
    net = Network(s, cfg, out, seed)
    net.ses.cmd("echo ready")
    t_setup, c_setup = time.time() - t_start, cpu_of(net.ses.p.pid)
    cal = cfg["calendar"]
    t0, c0 = time.time(), 0.0
    lessons = []                                            # (layer, cell, group, round, slot index)
    words = {}
    try:
        for l in range(len(s["layers"])):
            k = l + 1
            for g in range(2):
                for stim, members in net.partitions(l, g):
                    x = specmod.line_pattern(s, stim)
                    state = {i: dict(r=0, run=0, word="") for i in members}
                    while state:
                        cells = set(state)
                        rec = net.slot("lesson", x, k, {k: cells}, {f"c{k}_{i}" for i in cells},
                                       dict(layer=k, group=g, cells=sorted(cells), stimulus=sorted(stim)))
                        idx = len(net.slots) - 1
                        for i in sorted(cells):
                            r = next(r for r in rec["reads"] if r["layer"] == k and r["index"] == i)
                            f = r["emission"] is not None
                            st = state[i]
                            lessons.append(dict(layer=k, cell=i, group=g, round=st["r"], slot=idx))
                            st["word"] += "F" if f else "s"
                            st["run"] = st["run"] + 1 if f else 0
                            st["r"] += 1
                            if st["run"] >= cal["hold"] or st["r"] >= cal["max_rounds"]:
                                words[(k, i, g)] = st["word"]
                                log(f"lesson layer {k} cell {i} group {g}: {st['word']}")
                                del state[i]
        t_train, c_train = time.time() - t0, cpu_of(net.ses.p.pid)
        tests = []
        for x in specmod.patterns(s["m"]):
            rec = net.slot("test", specmod.rails(s, x), len(s["layers"]), {}, set(),
                           dict(pattern=[int(b) for b in x]))
            tests.append(len(net.slots) - 1)
            top = rec["reads"][-1]
            log(f"test {''.join(str(int(b)) for b in x)}: out {'FIRE' if top['emission'] is not None else 'silent'}"
                f" (expected {'FIRE' if s['expect'][specmod.code(x)] else 'silent'})")
        t_all, c_all = time.time() - t0, cpu_of(net.ses.p.pid)
        status = "done"
    except Exception as e:                                   # reported, never hidden
        t_train = t_all = time.time() - t0
        c_train = c_all = cpu_of(net.ses.p.pid)
        tests, status = [], f"failed: {e}"
        log(status)
    finally:
        simulated = net.ses.now
        net.ses.close()
    nodes = sess.count_nodes(out, cfg)
    record = dict(tag=s["tag"], seed=seed, status=status, cells=net.cells, inverters=net.invs,
                  deck=dict(**deckmod.size(net.text), nodes=nodes, r_cells=len(net.cells), inverters=len(net.invs)),
                  cost=dict(wall_setup_s=t_setup, wall_train_s=t_train, wall_test_s=t_all - t_train,
                            cpu_setup_s=c_setup, cpu_train_s=None if c_train is None else c_train - c_setup,
                            cpu_test_s=None if c_all is None or c_train is None else c_all - c_train,
                            simulated_s=simulated, slots=len(net.slots), lesson_slots=len(net.slots) - len(tests),
                            test_slots=len(tests)),
                  words={f"{k}/{i}/{g}": w for (k, i, g), w in words.items()},
                  lessons=lessons, tests=tests, slots=net.slots)
    (out / "record.json").write_text(json.dumps(record, indent=1) + "\n")
    return record


if __name__ == "__main__":
    cfg = json.loads((HERE / "config.json").read_text())
    s = specmod.load(sys.argv[1])
    r = train_and_test(s, cfg, sys.argv[2], int(sys.argv[3]))
    print(json.dumps(dict(status=r["status"], cost=r["cost"], deck=r["deck"]), indent=1))
