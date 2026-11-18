"""Campaign 6's development batch: the robust scan along the training path, and the one-sided set (BATCH_SPEC.md,
section 2 and section 5, option B or C). New code; it imports campaign 5's frozen modules and network-circuit's, and
edits none.

One simulator session on campaign 5's three-cell deck (`net.deck(cells=c4.CELLS, ...)`), with `leak_per_port` so that
each stored voltage can be raised alone (an imposed leak `vgl<cell><port>`, zero when not in use, as campaign 3's
robust scan). Only the scanned cell receives pulses. Each event takes one slot of 22 units (campaign 5's SLOT):

- a read: every port of the cell gated read-only (`idis` = 0, 3 units ahead), the read's pulses at campaign 5's
  amplitudes (0.49 on a and b, 1 on c, the second line 0.3 unit late for c's both-lines read). FIRE: the protection
  latch rises through 0.9 V within 1.1 units of the read's start;
- a dose: the ports to lower take a clock-only pulse (amplitude 0) with their `idis` restored, as the calibration's
  joint dose;
- idle, with imposed leaks on the ports to raise (from 200 us to 370 us of the slot, in steps of at most 1.2 mV, the
  leak's scale refined on the run, as campaign 3's `period`).

The stored voltage of a port is `u = mean(vmem) - mean(sum)` over [t + 400 us, t + 435 us] of its slot, as campaign 5's
reads measure a move. The training path is `u_p(s) = u_p(0) - s D_p` (D_p in volts, from the guard-on calibration
deck); the cell is brought to it within 2 uV per port (`move`).

  scan6.py OUT SEED|none CELL KIND DELTA D1_V D2_V NGSPICE PDK       KIND: pair (a, b), line1, line2, both (c)
  scan6.py OUT SEED|none CELL onesided S1 S2 D1_V D2_V NGSPICE PDK    a or b: port 1 alone read at s = S1, port 2 at S2

The run's record (`record.json`): what was asked, every read (its s, the ports' u, FIRE and its date), and the
bracket, the threshold, the half bracket and the trip level of a scan (or the two verdicts of a one-sided set), the
SHA-256 of the evidence and the run's wall time. No word of the batch's report is computed here.
"""
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import sys
import time

HERE = Path(__file__).resolve().parent
C5 = HERE.parent.parent / "learned-dnf-circuit-campaign-5"
sys.path.insert(0, str(C5))
import c4                                               # noqa: E402  (campaign 5, frozen)
import reads4                                           # noqa: E402  (campaign 5, frozen: q_peak)
import predicted as P                                   # noqa: E402  (campaign 5, frozen: zint)
from session4 import net, measure                       # noqa: E402  (network-circuit, frozen)

import batch6                                           # noqa: E402

SLOT_S = c4.SLOT * net.TU
GATE_LEAD_S = c4.GATE_LEAD * net.TU
FIRE_WINDOW_S = net.TU + 2e-6                           # 1.1 units: campaign 5's window for a, b and c in the calibration
LEAK_PER_MV = 4.42e-10                                  # campaign 3's first guess; refined on the run
TOL_V = 2e-6                                            # each port within 2 uV of its target
BRACKET_V = 20e-6                                       # the bracket, on the port of larger D
S_MAX = 8
ORIGIN = 100e-6
READS = dict(pair=((1, 0.0), (2, 0.0)), line1=((1, 0.0),), line2=((2, 0.0),), both=((1, 0.0), (2, c4.SKEW_PAIR)),
             port1=((1, 0.0),), port2=((2, 0.0),))
MOVING = dict(pair=(1, 2), line1=(1,), line2=(2,), both=(1, 2), onesided=(1, 2))


def amp(cell):
    return c4.AMP_OR if cell == "c" else c4.AMP_AND


def kinds_of(cell):
    return ("line1", "line2", "both") if cell == "c" else ("pair",)


class Driver:
    """One session, the state of the scanned cell, and every read made."""

    def __init__(self, out, seed, cell, moving, D, ngspice, pdk, stop_s=0.4):
        section = "tt" if seed is None else c4.SECTION
        text = net.deck(cells=c4.CELLS, section=section, leak_per_port=True)
        self.s = net.Session(out, text, c4.CELLS, ngspice, pdk, seed=seed, stop_s=stop_s)
        self.c, self.moving, self.D = cell, tuple(moving), {p: float(D[p]) for p in (1, 2)}
        self.t = ORIGIN
        self.scale = {p: LEAK_PER_MV for p in net.PORTS}
        self.reads, self.events = [], []
        self.u = None
        self.slot("idle")
        self.u0 = dict(self.u)

    def gates(self, writing):
        for p in net.PORTS:
            self.s.set(f"i.x{self.c}.x{p}.idis", c4.IDIS if p in writing else 0.0)

    def measure_u(self, lo, hi):
        c = self.c
        return {p: self.s.mean(f"v(x{c}.vmem{p})", lo, hi) - self.s.mean(f"v(x{c}.x{p}.sum)", lo, hi) for p in net.PORTS}

    def slot(self, kind, ports=(), s_target=None, leaks=None, label=None):
        """One slot of 22 units from self.t: kind read (ports: ((port, offset_units), ...)), dose (ports: the ports to
        lower) or idle; then imposed leaks {port: volts}. Returns the read's FIRE (or None) and the new u."""
        date = net.snap(self.t)
        self.t = date + SLOT_S
        s, c = self.s, self.c
        fired = fire_date = None
        if kind in ("read", "dose"):
            s.run(date - GATE_LEAD_S)
            self.gates(ports if kind == "dose" else ())
            s.run(date - net.LEAD - 1e-6)
            was = s.protected(c)
            if was:
                raise RuntimeError(f"cell {c} already protected before the slot at {date}")
            if kind == "read":
                for p, off in ports:
                    s.pulse(c, p, net.snap(date + off * net.TU), amp=amp(c))
                t = s.run(date + 25e-6, watch=(c,))
                fired = False
                if t < date + 25e-6 - 1e-12 and s.protected(c):
                    fire_date = s.fire_date(c, date - 1e-6)
                    fired = fire_date - date <= FIRE_WINDOW_S
                    s.run(date + 25e-6)
            else:
                for p in ports:
                    s.pulse(c, p, date, amp=0.0)
        s.run(date + 200e-6)
        if leaks:
            before = self.measure_u(date + 160e-6, date + 195e-6)
            for p, dv in leaks.items():
                s.set(f"vgl{c}{p}", dv * 1e3 * self.scale[p])
            s.run(date + 370e-6)
            for p in leaks:
                s.set(f"vgl{c}{p}", 0.0)
        s.run(date + SLOT_S - 3e-6)
        self.u = self.measure_u(date + 400e-6, date + 435e-6)
        if leaks:
            for p, dv in leaks.items():
                if self.u[p] - before[p] > 0.2 * dv:
                    self.scale[p] *= dv / (self.u[p] - before[p])
        if kind == "read":
            self.reads.append(dict(s=s_target, date_s=date, ports=[list(x) for x in ports], fire=bool(fired),
                                   fire_date_s=fire_date, u_V={str(p): self.u[p] for p in net.PORTS}, label=label))
        self.events.append(dict(kind=kind, date_s=date, ports=[list(x) if isinstance(x, tuple) else x for x in ports],
                                leaks={str(p): v for p, v in (leaks or {}).items()}))
        return fired

    def target(self, s_value):
        return {p: self.u0[p] - (float(s_value) * self.D[p] if p in self.moving else 0.0) for p in net.PORTS}

    def move(self, s_value):
        """Doses and imposed leaks until every port is within 2 uV of the path at s (campaign 3's `move`)."""
        goal = self.target(s_value)
        for _ in range(60):
            gap = {p: goal[p] - self.u[p] for p in net.PORTS}
            low = tuple(p for p in net.PORTS if gap[p] < -TOL_V)
            if low:
                self.slot("dose", low)
                continue
            high = {p: (g if g <= 0.05e-3 else min(g - 0.03e-3, 1.2e-3)) for p, g in gap.items() if g > TOL_V}
            if not high:
                return
            self.slot("idle", leaks=high)
        raise RuntimeError(f"the path state s = {s_value} was not reached within 60 slots")

    def read_at(self, s_value, ports, label=None):
        self.move(s_value)
        return self.slot("read", ports, s_target=str(F(s_value)), label=label)

    def close(self):
        self.s.run(self.t)
        return measure.Trace(self.s.close())


def verdicts(reads):
    """The majority verdict of each state read (by its s), and whether the states are ordered (every state that fired
    above every state that stayed silent). Returns (states {s: fired}, consistent)."""
    by = {}
    for r in reads:
        by.setdefault(F(r["s"]), []).append(r["fire"])
    states = {s: sum(v) * 2 > len(v) for s, v in by.items()}
    fired = [s for s, v in states.items() if v]
    silent = [s for s, v in states.items() if not v]
    return states, (not fired or not silent or min(fired) > max(silent))


def contradictory(reads):
    fired = [F(r["s"]) for r in reads if r["fire"]]
    silent = [F(r["s"]) for r in reads if not r["fire"]]
    return bool(fired and silent and min(fired) <= max(silent))


def scan(drv, kind, delta):
    """The coarse ascent from s = 0 in steps of delta, the bisection to 20 uV on the port of larger D, then at most one
    round of repeats on the two disputed states (the fired state of smallest s, then the silent state of largest s),
    each read twice more. Returns the scan's outcome (no trip level yet: it needs the waveform)."""
    ports = READS[kind]
    width = max(drv.D[p] for p in drv.moving)
    lo = hi = None
    k = 0
    while k * delta <= S_MAX:
        s_value = k * delta
        if drv.read_at(s_value, ports, "ascent"):
            hi = s_value
            break
        lo = s_value
        k += 1
    if hi is None:
        return dict(crossing=False, why="no crossing below 8")
    if lo is None:
        return dict(crossing=True, consistent=False, why="fires at the preset (s = 0)")
    for _ in range(40):
        if (hi - lo) * width <= BRACKET_V:
            break
        mid = (lo + hi) / 2
        if drv.read_at(mid, ports, "bisection"):
            hi = mid
        else:
            lo = mid
    disputed = contradictory(drv.reads)
    if disputed:
        fired = min(F(r["s"]) for r in drv.reads if r["fire"])
        silent = max(F(r["s"]) for r in drv.reads if not r["fire"])
        for state in (fired, silent):
            for _ in range(2):
                drv.read_at(state, ports, "repeat")
    states, ok = verdicts(drv.reads)
    out = dict(crossing=True, contradictory=disputed, consistent=ok, states={str(s): v for s, v in sorted(states.items())})
    if ok:
        s_lo = max((s for s, v in states.items() if not v), default=None)
        s_hi = min(s for s, v in states.items() if v)
        out.update(bracket=[str(s_lo), str(s_hi)], s_star=str((s_lo + s_hi) / 2), half_bracket=str((s_hi - s_lo) / 2))
    return out


def trip_level(tr, drv, out):
    """L: the Z (campaign 5's zint) of the weakest fired state's first FIRE, its q_peak before the FIRE crossing."""
    s_hi = F(out["bracket"][1])
    r = next(x for x in drv.reads if x["fire"] and F(x["s"]) == s_hi)
    return int(P.zint(reads4.q_peak(tr, drv.c, r["date_s"], r["fire_date_s"])))


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main(argv=None):
    a = sys.argv[1:] if argv is None else argv
    batch6.require_debug()
    began = time.time()
    out, seed_text, cell, kind = Path(a[0]), a[1], a[2], a[3]
    seed = batch6.guard_seed(seed_text)
    print(c4.require_pinned())
    assert cell in c4.CELLS, cell
    ev = out / "evidence"
    if kind == "onesided":
        assert cell in ("a", "b"), "a one-sided set is for the ports alone of layer 1"
        s1, s2, d1, d2, ngspice, pdk = a[4:10]
        D = {"1": d1, "2": d2}
        drv = Driver(ev, seed, cell, MOVING["onesided"], {1: d1, 2: d2}, Path(ngspice), Path(pdk))
        order = sorted(((F(s1), 1), (F(s2), 2)))
        res = dict(kind="onesided", bounds={"1": str(F(s1)), "2": str(F(s2))}, silent={})
        for s_value, p in order:
            res["silent"][str(p)] = not drv.read_at(s_value, READS[f"port{p}"], f"one-sided port {p}")
        res["all_silent"] = all(res["silent"].values())
    else:
        assert kind in kinds_of(cell), (cell, kind)
        delta, d1, d2, ngspice, pdk = F(a[4]), a[5], a[6], a[7], a[8]
        D = {"1": d1, "2": d2}
        assert delta in batch6.DELTAS, f"the ascent step is 1/4 (B) or 1/2 (C), not {delta}"
        drv = Driver(ev, seed, cell, MOVING[kind], {1: d1, 2: d2}, Path(ngspice), Path(pdk))
        res = dict(kind=kind, delta=str(delta), **scan(drv, kind, delta))
    tr = drv.close()
    if res.get("consistent"):
        res["L"] = trip_level(tr, drv, res)
    (ev / "pdk").unlink()
    rec = dict(batch6.run_header(seed, cell, kind), D_V=D,
               u0_V={str(p): v for p, v in drv.u0.items()}, reads=drv.reads, slots=len(drv.events), result=res,
               files={x: sha(ev / x) for x in ("input.spice", "session.log", "trace.raw")}, wall_s=time.time() - began)
    (ev / "events.json").write_text(json.dumps(drv.events) + "\n")
    rec["files"]["events.json"] = sha(ev / "events.json")
    (out / "record.json").write_text(json.dumps(rec, indent=1) + "\n")
    print(json.dumps(dict(cell=cell, kind=kind, reads=len(drv.reads), wall_s=round(rec["wall_s"]), result={k: v for k, v in res.items() if k != "states"})))
    return rec


if __name__ == "__main__":
    main()
