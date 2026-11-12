"""One run of the certification campaign, by the rules of PREDICTION.md.

  cert_run.py STAGE NAME

The run is looked up in manifest.json. The deck is the netlist of the original campaign, read
unchanged, with the additions listed in PREDICTION.md. Writes, under results/STAGE/:
  NAME.csv   one row per pulse: the columns of the original campaign, then the measures of this one
  NAME.json  metadata, with the hashes of the deck and of the compact trace
  NAME.failed  instead of the two others, when the run or a check fails
and the compact trace traces/STAGE/NAME.npz, which goes to the private repository.
"""
import hashlib
import json
import math
import os
from pathlib import Path
import subprocess
import sys
import time

import numpy as np

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT))
import analyze                      # read_run: the checks of a result

TU, PERIOD, OFFSET = 20e-6, 440e-6, 4.1e-6
TC = 0.75                           # date of the early gain, in units after the start of the pulse
SIGNALS = ["v(vq)", "v(p)", "v(cmpm)", "v(vrefmn)", "v(nzm)", "v(vmem1)", "v(vmem2)"]
for _q in (1, 2):
    SIGNALS += [f"v(x{_q}.{node})" for node in ("vs", "sum", "a", "b", "si")]
COL = dict(t=0, vq=1, p=2, cmpm=3, vrefmn=4, nzm=5, vmem1=6, vmem2=7, vs1=8, sum1=9, a1=10, b1=11, si1=12,
           vs2=13, sum2=14, a2=15, b2=16, si2=17)
EXTRA = ["c_pre", "q_peak", "q_tc", "q_fire", "noise_sup_V", "latch_rises", "comparator_transitions",
         "vbar1", "vbar2", "steer_rises1", "steer_rises2",
         "vs_entry", "vs_exit", "vmem_entry", "vmem_exit", "sum_entry", "sum_exit",
         "vs_entry2", "vs_exit2", "vmem_entry2", "vmem_exit2", "sum_entry2", "sum_exit2"]
MODES = {  # periods simulated, pulses per port, ports of the rows
    "train": dict(periods=22, kp=10, ports=[1] * 10 + [2] * 10 + [0]),
    "read": dict(periods=3, kp=1, ports=[1, 2]),
    "read_zero": dict(periods=3, kp=1, ports=[1, 2]),
    "ramp": dict(periods=2, kp=10, ports=[]),
    "leak": dict(periods=41, kp=10, ports=[1] * 40),
}


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def deck(run, raw):
    mode = MODES[run["mode"]]
    text = (ROOT / "cell.spice").read_text()
    if run["noise"]:
        params = json.loads((ROOT / "noise.json").read_text())["params"]
        for node, white, flicker in (("nzc", params["vncw"], params["vncf"]), ("nzo", params["vnow"], params["vnof"]),
                                    ("nzi", params["inmw"], 0), ("nzm", params["vnmw"], params["vnmf"])):
            old = f"vnz{node[2]} {node} 0 dc 0"
            assert text.count(old) == 1
            text = text.replace(old, f"{old} trnoise({white:.6g} {params['tnz']:.6g} {1 if flicker else 0} {flicker:.6g})")
    if run["mode"] in ("ramp", "leak"):               # the pulse schedule of the two ports
        x1 = next(l for l in text.splitlines() if l.startswith("x1 "))
        x2 = next(l for l in text.splitlines() if l.startswith("x2 "))
        first = " ta=1 tb=1 tj=1" if run["mode"] == "ramp" else f" ta={PERIOD:.9g} tb={41 * PERIOD:.9g} tj=1"
        text = text.replace(x1, x1.split(" ta=")[0] + first).replace(x2, x2.split(" ta=")[0] + " ta=1 tb=1 tj=1")
    lines = [f"* Certification campaign: {run['name']}", f'.lib "pdk/models/sky130.lib.spice" {run["section"]}'] + text.splitlines()[1:-1]
    lines += [f".param kp={mode['kp']}" + (" rlk=1e11" if run["mode"] == "leak" else ""), ".option temp=27"]
    if run["mode"] == "ramp":                         # draws the main capacitor from rest to 0.75 V in 800 us
        lines.append("iramp vq 0 pwl(0 0 20u 0 820u 62.5n)")
    if run["mode"] == "read_zero":                    # an added source of no current: must change nothing
        lines.append("izero vq 0 dc 0")
    lines += [".save " + " ".join(SIGNALS), ".control"]
    if run["seed"] is not None:
        lines += [f"setseed {run['seed']}", "reset"]
    lines += [f"tran 1u {mode['periods'] * PERIOD:.12g} 0 200n", "set wr_singlescale", "set numdgt=16",
              f"wrdata {raw} " + " ".join(SIGNALS), "quit", ".endc", ".end"]
    return "\n".join(lines) + "\n"


# ---- measures on the solver points
def crossings(d, col, lo, hi):
    """Every 0.9 V crossing of a column in [lo, hi): (time, +1 rising or -1 falling), linearly interpolated."""
    i0, i1 = np.searchsorted(d[:, 0], [lo, hi])
    i0, i1 = max(i0 - 1, 0), min(i1 + 1, len(d))
    a, b, t = d[i0:i1 - 1, col], d[i0 + 1:i1, col], d[i0:i1, 0]
    out = []
    for sign, idx in ((1, np.flatnonzero((a < 0.9) & (b >= 0.9))), (-1, np.flatnonzero((a >= 0.9) & (b < 0.9)))):
        for i in idx:
            x = t[i] + (t[i + 1] - t[i]) * (0.9 - a[i]) / (b[i] - a[i])
            if lo <= x < hi:
                out.append((float(x), sign))
    return sorted(out)


def at(d, col, t):
    j = int(np.searchsorted(d[:, 0], t, side="right"))
    a, b = d[j - 1], d[j]
    return float(a[col] + (b[col] - a[col]) * (t - a[0]) / (b[0] - a[0]))


def mean(d, col, lo, hi):
    """Time-weighted mean over [lo, hi], with the two ends interpolated."""
    i0, i1 = np.searchsorted(d[:, 0], [lo, hi], side="right")
    t = np.concatenate(([lo], d[i0:i1, 0], [hi]))
    v = np.concatenate(([at(d, col, lo)], d[i0:i1, col], [at(d, col, hi)]))
    return float(np.sum(np.diff(t) * (v[:-1] + v[1:]) / 2) / (hi - lo))


def extreme(d, col, lo, hi, fn):
    i0, i1 = np.searchsorted(d[:, 0], [lo, hi], side="right")
    return float(fn(np.concatenate(([at(d, col, lo)], d[i0:i1, col], [at(d, col, hi)]))))


def q_of(v):
    return 0.1 + (1.25 - v) / 0.5


def rows_of(d, ports):
    """One row per pulse. The first 17 values are those of the original campaign, measured on the solver points."""
    out, prev = [], None
    for k in range(0, len(ports) + 1):
        lo, hi, edge = k * PERIOD, (k + 1) * PERIOD, k * PERIOD + OFFSET
        b = hi - 2e-6
        v = (mean(d, COL["vmem1"], b - 40e-6, b), mean(d, COL["vmem2"], b - 40e-6, b))
        watch = lo + (2.6e-6 if k == 0 else 0.05e-6)
        latch = crossings(d, COL["p"], watch, b)
        rises = [t for t, s in latch if s > 0]
        if k == 0:
            prev, rest_fire = v, bool(rises)
            continue
        port = ports[k - 1]
        falls = [t for t, s in latch if s < 0 and t >= edge + 25e-6]
        u = lambda x: (x - edge) / TU
        win = {}
        for q in (1, 2):
            e = [t for t, s in crossings(d, COL[f"a{q}"], edge - 0.5e-6, b) if s > 0]
            x = [t for t, s in crossings(d, COL[f"b{q}"], edge - 0.5e-6, b) if s > 0]
            st = [t for t, s in crossings(d, COL[f"si{q}"], edge - 0.5e-6, b) if s > 0]
            win[q] = (e[0] if e else None, x[0] if x else None, len(st))
        row = [k - 1, port, int(bool(rises)), u(rises[0]) if rises else -1, u(falls[0]) if falls else -1,
               u(win[1][0]) if win[1][0] else -1, u(win[1][1]) if win[1][1] else -1, int(win[1][2] > 0),
               u(win[2][0]) if win[2][0] else -1, u(win[2][1]) if win[2][1] else -1, int(win[2][2] > 0),
               v[0], v[1], extreme(d, COL["vq"], edge - 0.5e-6, b, np.min), int(len(rises) > 1),
               1e3 * (prev[0] - v[0]), 1e3 * (prev[1] - v[1])]
        end = min(edge + TU, rises[0]) if rises else edge + TU
        extra = dict(c_pre=q_of(at(d, COL["vq"], edge - 1e-12)), q_peak=q_of(extreme(d, COL["vq"], edge, b, np.min)),
                     q_tc=q_of(at(d, COL["vq"], edge + TC * TU)), q_fire=q_of(at(d, COL["vq"], rises[0])) if rises else -1,
                     noise_sup_V=extreme(d, COL["nzm"], edge, edge + TU, lambda x: np.max(np.abs(x))),
                     latch_rises=len(rises), comparator_transitions=len(crossings(d, COL["cmpm"], watch, b)),
                     vbar1=mean(d, COL["vmem1"], edge, end), vbar2=mean(d, COL["vmem2"], edge, end),
                     steer_rises1=win[1][2], steer_rises2=win[2][2])
        for q, tag in ((1, ""), (2, "2")):
            active = port in (q, 0) and win[q][0] is not None and win[q][1] is not None and win[q][1] > win[q][0]
            for label, t in (("entry", win[q][0]), ("exit", win[q][1])):
                for sig in ("vs", "vmem", "sum"):
                    extra[f"{sig}_{label}{tag}"] = at(d, COL[f"{sig}{q}"], t) if active else -1
        if port == 2:                                   # the window of the pulsed port is in the unnumbered columns
            for label in ("entry", "exit"):
                for sig in ("vs", "vmem", "sum"):
                    extra[f"{sig}_{label}"], extra[f"{sig}_{label}2"] = extra[f"{sig}_{label}2"], -1
        out.append(row + [extra[k_] for k_ in EXTRA])
        prev = v
    return out, rest_fire


def compact(d, ports):
    """The points kept: around each pulse and around each write window."""
    keep = np.zeros(len(d), dtype=bool)
    for k in range(0, len(ports) + 1):
        edge, b = k * PERIOD + OFFSET, (k + 1) * PERIOD - 2e-6
        spans = [(edge - 1e-6, edge + 1.1 * TU)]
        for q in (1, 2):
            e = [t for t, s in crossings(d, COL[f"a{q}"], edge - 0.5e-6, b) if s > 0]
            x = [t for t, s in crossings(d, COL[f"b{q}"], edge - 0.5e-6, b) if s > 0]
            if e:
                spans.append((e[0] - 0.5e-6, (x[0] if x else e[0]) + 3e-6))
        for lo, hi in spans:
            i0, i1 = np.searchsorted(d[:, 0], [lo, hi])
            keep[max(i0 - 1, 0):min(i1 + 1, len(d))] = True
    return d[keep]


def main():
    stage, name = sys.argv[1], sys.argv[2]
    manifest = json.loads((HERE / "manifest.json").read_text())
    run = next(r for r in manifest["stages"][stage] if r["name"] == name)
    mode = MODES[run["mode"]]
    out, tr, work = HERE / "results" / stage, HERE / "traces" / stage, HERE / "work"
    for folder in (out, tr, work):
        folder.mkdir(parents=True, exist_ok=True)
    if (out / f"{name}.json").exists() or (out / f"{name}.failed").exists():
        print(name, "already there")
        return 0
    for relative, expected in manifest["source_sha256"].items():
        assert digest(ROOT / relative) == expected, relative
    ngspice = Path(manifest["ngspice_path"])
    assert digest(ngspice) == manifest["ngspice_sha256"], "executable changed"
    assert subprocess.check_output(["git", "-C", str(ROOT / "pdk"), "rev-parse", "HEAD"], text=True).strip() == manifest["pdk_commit"], "PDK changed"
    assert (ROOT / ".spiceinit").read_bytes() == (ROOT / "spiceinit.txt").read_bytes(), "compatibility settings changed"
    raw, circuit = work / f"{stage}_{name}.txt", work / f"{stage}_{name}.spice"
    circuit.write_text(deck(run, raw))
    meta = dict(run=run, stage=stage, started_unix=time.time(), deck_sha256=digest(circuit), ngspice_sha256=digest(ngspice), signals=SIGNALS)

    def fail(reason, log=""):
        (out / f"{name}.failed").write_text(reason + "\n" + log[-3000:])
        print(name, "FAILED", reason)
        return 1

    try:
        p = subprocess.run([str(ngspice), "-b", str(circuit)], cwd=ROOT, capture_output=True, text=True, timeout=1500,
                           env=dict(os.environ, SPICE_SCRIPTS=str(ROOT / "bridge_check" / "runtime")))
    except subprocess.TimeoutExpired:
        return fail("stopped at the time limit")
    log = p.stdout + p.stderr
    if p.returncode != 0 or not raw.exists() or "aborted" in log or "too small" in log:
        return fail(f"simulator status {p.returncode}", log)
    d = np.loadtxt(raw)
    raw.unlink()
    if d.ndim != 2 or d.shape[1] != len(SIGNALS) + 1 or not np.isfinite(d).all():
        return fail("trace of the wrong shape or with a value that is not finite")
    if np.any(np.diff(d[:, 0]) < 0) or d[-1, 0] < mode["periods"] * PERIOD - 1e-10:
        return fail("trace not ordered or cut short")
    meta.update(finished_unix=time.time(), points=int(len(d)))
    if run["mode"] == "ramp":
        rise = [t for t, s in crossings(d, COL["p"], 20e-6, 2 * PERIOD) if s > 0]
        comp = [t for t, s in crossings(d, COL["cmpm"], 20e-6, 2 * PERIOD) if s > 0]
        if not rise:
            return fail("the latch does not rise during the ramp")
        meta.update(latch_rise_s=rise[0], vq_at_latch_rise=at(d, COL["vq"], rise[0]), static_level=q_of(at(d, COL["vq"], rise[0])),
                    vq_at_comparator_rise=at(d, COL["vq"], comp[0]) if comp else None, latch_rises=len(rise),
                    slope_V_per_s=(at(d, COL["vq"], rise[0]) - at(d, COL["vq"], rise[0] - 10e-6)) / 10e-6)
        kept = d[(d[:, 0] >= rise[0] - 20e-6) & (d[:, 0] <= rise[0] + 5e-6)]
    else:
        rows, rest_fire = rows_of(d, mode["ports"])
        meta["rest_fire"] = rest_fire
        path = out / f"{name}.csv"
        with path.open("w") as fh:
            fh.write(",".join(analyze.COLS + EXTRA) + "\n")
            for r in rows:
                fh.write(",".join(["%d" % x for x in r[:3]] + ["%.6f" % r[3], "%.5f" % r[4], "%.5f" % r[5], "%.5f" % r[6], "%d" % r[7],
                                   "%.5f" % r[8], "%.5f" % r[9], "%d" % r[10], "%.9f" % r[11], "%.9f" % r[12], "%.9f" % r[13], "%d" % r[14],
                                   "%.6f" % r[15], "%.6f" % r[16]] + ["%.12g" % x for x in r[17:]]) + "\n")
        checked, why = analyze.read_run(str(path), mode["ports"])          # rows of the plan, order of the ports, finite values, flags
        if checked is None or not all(math.isfinite(x) for r in rows for x in r):
            path.rename(out / f"{name}.rejected.csv")
            return fail("result rejected: " + (why or "a value is not finite"))
        meta["csv_sha256"] = digest(path)
        kept = compact(d, mode["ports"])
    np.savez_compressed(tr / f"{name}.npz", data=kept, signals=np.array(["time"] + SIGNALS))
    meta.update(trace_points_kept=int(len(kept)), trace_sha256=digest(tr / f"{name}.npz"), status="done")
    (out / f"{name}.json").write_text(json.dumps(meta, indent=2) + "\n")
    print(name, "done", len(d), "points,", len(kept), "kept")
    return 0


if __name__ == "__main__":
    sys.exit(main())
