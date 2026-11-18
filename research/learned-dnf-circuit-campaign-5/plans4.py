"""Campaign 4: the plans of the calibration decks and of the network runs, as session4.play plays them. The calendar of
a network run is phase 0's `dnf.calendar` unchanged; this file adds the gates, the amplitudes and the edges that
PREDICTION.md gives it. No simulation is run here.
"""
import c4
from c4 import dnf

PORT_NAMES = [f"{c}{p}" for c in c4.CELLS for p in (1, 2)]


def gates(may_write):
    """idis of every port: restored where the port may write in the slot, zero elsewhere."""
    return {n: (c4.IDIS if n[0] in may_write else 0.0) for n in PORT_NAMES}


CAL_READS = (("empty", {}), ("port 1", {1: 0}), ("port 2", {2: 0}), ("both", {1: 0, 2: 0}), ("both, second 0.3 late", {1: 0, 2: c4.SKEW_PAIR}))


def calibration():
    """Per stage k = 0..7: five gated reads 22 units apart (the empty read, port 1, port 2, both at one date, and on c
    both with the second line 0.3 unit late; a and b take no pulse in that fifth slot), then one clock-only dose
    (amplitude 0) on both ports of each cell, writes enabled. Cells a, b at 0.49, c at 1."""
    t, plan, reads = 0.0, dict(cells=list(c4.CELLS), gates=[], sources=[], edges=[]), []
    for k in range(c4.STAGES):
        for name, offsets in CAL_READS:
            plan["gates"].append((t - c4.GATE_LEAD, gates(())))
            for c in c4.CELLS:
                if name.startswith("both, second") and c != "c":
                    continue
                amp = c4.AMP_OR if c == "c" else c4.AMP_AND
                for p, off in offsets.items():
                    plan["sources"].append((t + off, c, p, amp))
            reads.append(dict(stage=k, read=name, date=t, gated=True))
            t += c4.SLOT
        plan["gates"].append((t - c4.GATE_LEAD, gates(c4.CELLS)))
        for c in c4.CELLS:
            for p in (1, 2):
                plan["sources"].append((t, c, p, 0.0))
        reads.append(dict(stage=k, read="joint dose", date=t, gated=False))
        t += c4.SLOT
    plan["horizon"] = t + dnf.SETTLE
    return plan, reads


def network(needs, control=None):
    """The plan of a network run on the calendar of the needs (a, b, c1, c2) and its slots. control: None (a noisy
    run), "skew" (the run without noise, with the two skew slots after the tests) or "untrained"."""
    slots = dnf.calendar(*needs, control)
    plan = dict(cells=list(c4.CELLS), gates=[], sources=[], edges=[])
    for s in slots:
        plan["gates"].append((s["date"] - c4.GATE_LEAD, gates(s["writes"])))
        for n, off in s["inputs"].items():
            c, p = dnf.INPUTS[n]
            plan["sources"].append((s["date"] + off, c, p, c4.AMP_AND))
        if s["routed"]:
            for src, (c, p) in dnf.LINES.items():
                offs = [o for n, o in s["inputs"].items() if dnf.INPUTS[n][0] == src]
                if offs:
                    lo = s["date"] + min(offs)
                    plan["edges"].append(dict(name=f"{src}->{c}{p}@{s['date']}", source=src, cell=c, port=p, delay=c4.WIRE,
                                              gate=(lo, lo + c4.WINDOW), amp=c4.AMP_OR))
    plan["horizon"] = slots[-1]["date"] + dnf.SLOT + dnf.SETTLE
    return plan, slots
