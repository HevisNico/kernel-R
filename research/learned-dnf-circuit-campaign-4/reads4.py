"""Campaign 4: what the waveform of a run shows for each read, by the definitions of PREDICTION.md. No simulation.

A read of a cell is a slot in which the cell receives at least one pulse. Its start is the date of its first pulse.
- FIRE: the protection latch rises through 0.9 V in the decision window: for a and b, and for c in the calibration,
  within one unit and 2 us after the start (1.1 units); for c in a routed slot, after its last arrival and before
  its deadline, 2.2 units after its first arrival.
- write: the write signal of a port (`v(x<c>.x<p>.si)`) rises through 0.9 V during the cycle of the read;
  write': a write that stays above 0.9 V for at least 1 us.
- score: the peak of the main charge q = (1.25 - v(vq)) / 0.5 + 0.1 over the read (0.1 at rest, 1 at the FIRE level),
  over [start, start + 3 units]; and, for a read that fires, the peak before the FIRE crossing.
- the stored voltage of each port before the read and after its cycle (`measure.Trace.u`), and its move.
"""
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "network-circuit"))
import net                                              # noqa: E402

import c4                                               # noqa: E402
from c4 import dnf                                      # noqa: E402

TU, CYCLE = net.TU, net.CYCLE


def q_peak(tr, c, lo, hi):
    import numpy as np
    i0, i1 = np.searchsorted(tr.t, [lo, hi])
    v = tr.v[f"v(x{c}.vq)"][max(i0, 0):max(i1, i0 + 1)]
    return float(((1.25 - v) / 0.5 + 0.1).max())


def writes(tr, c, p, start):
    """(writes, writes'), and every rise of the write signal with its width, over the cycle of the read."""
    name = f"v(x{c}.x{p}.si)"
    rises = tr.crossings(name, start, start + CYCLE)
    falls = tr.crossings(name, start, start + CYCLE + 2 * TU, rising=False)
    out = []
    for r in rises:
        f = next((x for x in falls if x > r), start + CYCLE + 2 * TU)
        out.append(dict(rise_s=r, width_s=f - r))
    return len(out), sum(1 for x in out if x["width_s"] >= c4.WRITE_PRIME_S), out


def read(tr, c, start, fire_lo, fire_hi, gated):
    fires = tr.crossings(f"v(x{c}.p)", fire_lo, fire_hi)
    late = tr.crossings(f"v(x{c}.p)", fire_hi, start + CYCLE)
    r = dict(cell=c, start_s=start, gated=gated, fire=bool(fires), fire_date_s=fires[0] if fires else None,
             latency=(fires[0] - start) / TU if fires else None, late_fires=len(late),
             q_peak=q_peak(tr, c, start, start + 3 * TU),
             q_peak_before_fire=q_peak(tr, c, start, fires[0]) if fires else None, ports={})
    for p in net.PORTS:
        w, wp, detail = writes(tr, c, p, start)
        before = tr.u(c, p, start - 30e-6, start - 2e-6)
        after = tr.u(c, p, start + CYCLE - 30e-6, start + CYCLE - 2e-6)
        r["ports"][str(p)] = dict(writes=w, writes_prime=wp, rises=detail, u_before_mV=before * 1e3, move_mV=(before - after) * 1e3)
    return r


def calibration_reads(tr, result, reads):
    """The calibration deck: per stage, read and cell, the record of `read` (c's skewed pair: only c)."""
    by = {}
    for o in result["occurrences"]:
        if o["delivered"]:
            by.setdefault((round(o["calendar_date"]), o["cell"]), []).append(o["date_s"])
    out = []
    for x in reads:
        for c in c4.CELLS:
            if x["read"].startswith("both, second") and c != "c":
                continue
            starts = by.get((round(x["date"]), c), [])
            start = min(starts) if starts else net.snap(c4_at(x["date"]))
            rec = read(tr, c, start, start, start + c4.WINDOW * TU, x["gated"])
            out.append(dict(rec, stage=x["stage"], read=x["read"]))
    return out


def c4_at(units):
    return 100e-6 + units * TU


def letter(r, p, prime=False):
    """s: no FIRE and exactly one write on that port; F: one FIRE, no write; otherwise its own letter: w (a FIRE
    with a write), o (no FIRE, no write), m (more than one write)."""
    n = r["ports"][str(p)]["writes_prime" if prime else "writes"]
    if r["fire"]:
        return "F" if n == 0 else "w"
    return "s" if n == 1 else ("o" if n == 0 else "m")


def network_reads(tr, result, slots):
    """Per slot of a network run: the read of each cell that receives a pulse, with the arrivals on c."""
    delivered = [o for o in result["occurrences"] if o["delivered"]]
    out = []
    for i, s in enumerate(slots):
        lo, hi = c4_at(s["date"]) - 1e-9, c4_at(s["date"] + dnf.SLOT) - 1e-9
        here = [o for o in delivered if lo <= o["date_s"] < hi]
        rec = dict(slot=i, stage=s["stage"], date=s["date"], pattern=s.get("pattern"), line=s.get("line"), reads={})
        for c in ("a", "b"):
            mine = [o for o in here if o["cell"] == c]
            if mine:
                start = min(o["date_s"] for o in mine)
                rec["reads"][c] = read(tr, c, start, start, start + c4.WINDOW * TU, gated=c not in s["writes"])
        arr = [o for o in here if o["cell"] == "c"]
        if arr:
            first, last = min(o["date_s"] for o in arr), max(o["date_s"] for o in arr)
            r = read(tr, "c", first, last, first + c4.DEADLINE_C * TU, gated="c" not in s["writes"])
            r["arrivals"] = [dict(port=o["port"], date_s=o["date_s"], origin=o["origin"], fire_date_s=o.get("fire_date_s")) for o in arr]
            r["skew_units"] = (last - first) / TU
            rec["reads"]["c"] = r
        out.append(rec)
    return out


def words(rows, prime=False):
    """Words of the ports of a and b over layer 1, and of the lines of c over layer 2 (a line that does not arrive
    in its teaching slot gives '-'); outputs of a, b, c on each test pattern; the skew slots."""
    w = {"a1": "", "a2": "", "b1": "", "b2": "", "c1": "", "c2": ""}
    tests, skew = {}, {}
    for x in rows:
        if x["stage"] == "layer 1":
            for c in ("a", "b"):
                for p in (1, 2):
                    w[f"{c}{p}"] += letter(x["reads"][c], p, prime) if c in x["reads"] else "-"
        elif x["stage"] == "layer 2":
            p = dnf.LINES[x["line"]][1]
            r = x["reads"].get("c")
            w[f"c{p}"] += letter(r, p, prime) if r and any(a["port"] == p for a in r["arrivals"]) else "-"
        elif x["stage"] == "test":
            tests[x["pattern"]] = {c: bool(x["reads"].get(c, {}).get("fire")) for c in c4.CELLS}
        elif x["stage"] == "skew control":
            skew[x["pattern"]] = {c: bool(x["reads"].get(c, {}).get("fire")) for c in ("a", "b")}
    return dict(words=w, tests=tests, skew=skew)
