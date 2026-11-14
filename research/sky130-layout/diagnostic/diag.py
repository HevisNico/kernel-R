"""Diagnostic of the stage-P report: exploratory, not a campaign. Nominal cell, no noise, 27 C.

  python3 -I diag.py refusals     point 1, from the committed results of stage P: no simulation
  python3 -I diag.py levels       one simulation of three periods of the stage-P netlist (primary list),
                                  every node saved: which nodes sit at another level, or move, where
                                  the stored voltage and the rest charge are read
  python3 -I diag.py ablate       five nominal trains of 22 periods, each with some capacitances taken out
  python3 -I diag.py report       the tables of DIAGNOSTIC.md, from the three above

Nothing here was preregistered and nothing here decides a prediction. The simulations use the
runner of the certification campaign (cert_run.py, unchanged) through the harness of stage P.
Outputs go to build/, not committed; SHA256SUMS holds their hashes.
"""
import csv
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
P1 = HERE.parent / "phase1"
sys.path.insert(0, str(P1))
import netlist
import p_plan
import p_run

BUILD = HERE / "build"
CIRCUIT = p_run.CIRCUIT
PERIOD, OFFSET, TU = 440e-6, 4.1e-6, 20e-6
CF, CQ = 30e-12, 5e-12
CELLS = [f"t{s}" for s in p_plan.LARGE + p_plan.SMALL]


def read_csv(path):
    with open(path, newline="") as fh:
        return list(csv.DictReader(fh))


def caps_list(path=P1 / "p_caps_primary.csv"):
    return [(r["node1"], r["node2"], float(r["farad"])) for r in read_csv(path)]


def on(node, caps):
    """Capacitances with one end on `node`: other end -> farad."""
    out = {}
    for a, b, v in caps:
        if node in (a, b) and a != b:
            other = b if a == node else a
            out[other] = out.get(other, 0.0) + v
    return out


# ---- point 1

def refusals():
    """The rest-charge condition of rule A1 and of status 3: 0.1 <= c_pre <= 0.1001 on every read
    from 0 to the need m of the port, in its noisy test run."""
    pred = {(r["cell"], int(r["port"])): r for r in read_csv(P1 / "build" / "p_analysis" / "stage" / "certification" / "predictions.csv")}
    lines, table = [], []
    for cell in CELLS:
        rows = read_csv(P1 / "results_p" / f"{cell}_train.csv")
        for port in (1, 2):
            m = int(pred[(cell, port)]["m"])
            reads = [r for r in rows if int(r["port"]) == port][:m + 1]
            c = [float(r["c_pre"]) for r in reads]
            high = [x - 0.1001 for x in c if x > 0.1001]
            low = [0.1 - x for x in c if x < 0.1]
            after1 = [int(r["pulse"]) for r, x in zip(reads, c) if x > 0.1001]
            table.append(dict(cell=cell, port=port, m=m, reads=len(c), above=len(high), worst_above=max(high, default=0.0),
                              below=len(low), worst_below=max(low, default=0.0), pulses_above=after1, c_max=max(c)))
    (BUILD / "refusals.json").write_text(json.dumps(table, indent=1) + "\n")
    for t in table:
        print(f"REFUSAL {t['cell']} port {t['port']}: need {t['m']}, {t['reads']} reads; above 0.1001 on {t['above']} "
              f"(pulses {t['pulses_above']}), by {t['worst_above']:.6f} at most; below 0.1 on {t['below']}, by {t['worst_below']:.2e} at most")
    return table


# ---- the harness, for the two kinds of simulation

def root_for(tag, runs):
    root = BUILD / tag
    shutil.rmtree(root, ignore_errors=True)
    return p_run.mirror(root, runs)


def levels():
    """Three periods: rest, a pulse on port 1, a pulse on port 2. Every node of the capacitance list is saved."""
    import numpy as np
    sys.path.insert(0, str(CIRCUIT / "certification"))
    import cert_run
    caps = caps_list()
    nodes = sorted({n for a, b, _ in caps for n in (a, b)} - {"0"})
    root = root_for("levels", [])
    deck = cert_run.deck(dict(name="diag_read", mode="read", section="tt", seed=None, noise=False), "raw.txt")
    text, _ = netlist.build(deck, (CIRCUIT / "blocks.spice").read_text(), areas=netlist.read_areas(P1 / "p_areas.csv"),
                            caps=netlist.read_caps(P1 / "p_caps_primary.csv"))
    vectors = " ".join(f"v({n})" for n in nodes)
    out = []
    for line in text.splitlines():
        if line.startswith(".save "):
            line = ".save " + vectors
        elif line.startswith("wrdata "):
            line = "wrdata raw.txt " + vectors
        out.append(line)
    (root / "levels.spice").write_text("\n".join(out) + "\n")
    subprocess.run([p_run.NGSPICE, "-b", "levels.spice"], cwd=root, check=True, capture_output=True,
                   env=dict(os.environ, SPICE_SCRIPTS=str(CIRCUIT / "bridge_check" / "runtime")))
    d = np.loadtxt(root / "raw.txt")
    t = d[:, 0]

    def mean(col, lo, hi):
        sel = (t >= lo) & (t <= hi)
        return float(np.trapezoid(d[sel, col], t[sel]) / (t[sel][-1] - t[sel][0]))

    def at(col, x):
        return float(np.interp(x, t, d[:, col]))
    res = {}
    for k, n in enumerate(nodes, 1):
        read = [mean(k, (p + 1) * PERIOD - 42e-6, (p + 1) * PERIOD - 2e-6) for p in range(3)]     # where the stored voltage is read
        # across the end of period 1, in which port 1 was pulsed: from 0.3 us before its end to the instant
        # where the rest charge of the next pulse is read
        edge = at(k, 2 * PERIOD + OFFSET) - at(k, 2 * PERIOD - 0.3e-6)
        res[n] = dict(read=read, edge=edge)
    (BUILD / "levels.json").write_text(json.dumps(res, indent=1) + "\n")
    print(f"LEVELS {len(nodes)} nodes saved over {t[-1] * 1e6:.0f} us, {len(t)} points")
    return res


VARIANTS = {
    "base": "the primary list, as in stage P",
    "no_vq_ad": "without the capacitance between vq and x1.ad",
    "no_sum_logic": "without the capacitances between x1.sum or x2.sum and the nodes of their own port, the stored voltage and the supplies apart",
    "no_both": "without both",
    "areas_only": "no capacitance at all: the source and drain areas of the layout alone",
}


def variant(name, caps):
    keep = []
    for a, b, v in caps:
        pair = {a, b}
        drop = False
        if name in ("no_vq_ad", "no_both") and pair == {"vq", "x1.ad"}:
            drop = True
        if name in ("no_sum_logic", "no_both"):
            for q in ("x1", "x2"):
                if f"{q}.sum" in pair:
                    other = (pair - {f"{q}.sum"}).pop()
                    if other.startswith(q + ".") and not other.startswith(q + ".xop."):
                        drop = True
        if name == "areas_only":
            drop = True
        if not drop:
            keep.append((a, b, v))
    return keep


def ablate():
    from concurrent.futures import ThreadPoolExecutor
    caps = caps_list()
    runs = [dict(name=f"v_{n}", tool="cert", stage="preflight", mode="train", section="tt", seed=None, noise=False) for n in VARIANTS]
    root = root_for("ablate", runs)
    results = BUILD / "ablate_results"
    shutil.rmtree(results, ignore_errors=True)
    jobs = []
    for run, name in zip(runs, VARIANTS):
        path = BUILD / f"caps_{name}.csv"
        with open(path, "w", newline="") as fh:
            w = csv.writer(fh, lineterminator="\n")
            w.writerow(["node1", "node2", "farad"])
            for a, b, v in variant(name, caps):
                w.writerow([a, b, f"{v:.6g}"])
        jobs.append((run, path))
    with ThreadPoolExecutor(4) as ex:
        for line in ex.map(lambda j: p_run.run_in(root, j[0], j[0]["name"], "stage", j[1], results), jobs):
            print(line, flush=True)


def summary(name):
    rows = read_csv(BUILD / "ablate_results" / f"v_{name}.csv")
    c = [float(r["c_pre"]) for r in rows]
    s1 = [float(r["step1_mV"]) for r in rows]
    s2 = [float(r["step2_mV"]) for r in rows]
    fired = [int(r["fired"]) for r in rows]
    port = [int(r["port"]) for r in rows]
    silent1 = [s for s, f, p in zip(s1, fired, port) if p == 1 and not f]
    silent2 = [s for s, f, p in zip(s2, fired, port) if p == 2 and not f]
    return dict(c_pre_max=max(c), c_pre_after_port1=c[1], c_pre_after_port2=c[11], count1=len(silent1), count2=len(silent2),
                first_step1=silent1[0], later_step1=silent1[1], first_step2=silent2[0], later_step2=silent2[1],
                port1_becomes_idle=s1[10], port1_pulsed_again=s1[20],
                largest_firing_step=max(abs(s) for s, f, p in zip(s1, fired, port) if f and p in (1, 0)))


def report():
    caps = caps_list()
    L = json.loads((BUILD / "levels.json").read_text())
    out = []
    # the stored voltage of port 1: pulsed period (1) against idle period (2)
    for q, pulsed, idle in (("x1", 1, 2), ("x2", 2, 1)):
        rows = []
        for other, c in on(f"{q}.sum", caps).items():
            if other in ("0", "vdd") or other not in L:
                continue
            dv = L[other]["read"][pulsed] - L[other]["read"][idle]
            rows.append((-c * dv / CF, other, c, dv))
        rows.sort(key=lambda r: -abs(r[0]))
        total = sum(r[0] for r in rows)
        out.append(f"SUM {q}: predicted move of the stored voltage, pulsed period against idle period: {total * 1e6:+.2f} uV "
                   f"from {len(rows)} capacitances")
        for dvm, other, c, dv in rows[:10]:
            out.append(f"SUM {q}   {other}: {c * 1e15:.3f} fF, level {dv:+.3f} V -> {dvm * 1e6:+.2f} uV")
    rows = []
    ctot = CQ + sum(on("vq", caps).values())
    for other, c in on("vq", caps).items():
        if other in L:
            rows.append((c * L[other]["edge"] / ctot, other, c, L[other]["edge"]))
    rows.sort(key=lambda r: -abs(r[0]))
    out.append(f"VQ: predicted move of vq across the end of a period of port 1: {sum(r[0] for r in rows) * 1e3:+.3f} mV "
               f"(vq itself moves by {L['vq']['edge'] * 1e3:+.3f} mV in the simulation); total capacitance on vq {ctot * 1e12:.3f} pF")
    for dvq, other, c, dv in rows[:8]:
        out.append(f"VQ   {other}: {c * 1e15:.3f} fF, edge {dv:+.3f} V -> {dvq * 1e3:+.3f} mV, {dvq / 0.5:+.6f} in rest charge")
    for name, text in VARIANTS.items():
        s = summary(name)
        out.append(f"ABLATE {name} ({text}): rest charge after a period of port 1 {s['c_pre_after_port1']:.6f}, of port 2 "
                   f"{s['c_pre_after_port2']:.6f}; silent pulses {s['count1']} and {s['count2']}; first silent step {s['first_step1']:.3f} "
                   f"then {s['later_step1']:.3f} mV; step of port 1 when it becomes idle {s['port1_becomes_idle']:+.3f} mV, when it is "
                   f"pulsed again {s['port1_pulsed_again']:+.3f} mV; largest step of a firing pulse {s['largest_firing_step']:.3f} mV")
    (BUILD / "diag.txt").write_text("\n".join(out) + "\n")
    print("\n".join(out))


if __name__ == "__main__":
    BUILD.mkdir(exist_ok=True)
    cmd = sys.argv[1] if len(sys.argv) > 1 else ""
    if cmd not in ("refusals", "levels", "ablate", "report"):
        sys.exit(__doc__)
    globals()[cmd]()
