"""One run of the repetition campaign, by the rules of PREDICTION.md.

  rep_run.py STAGE NAME

The run is looked up in manifest.json. The deck is made by the function deck of
../certification/cert_run.py, which is not modified, and three lines of it are then replaced: the
largest step and the stop time of the transient analysis, and, when the options say so, the output
format and the linear solver. The rows of a run are made by rows_of of cert_run.py and written in its
format. The charges of the mirrors are measured by the two functions of ../certification-unconditional/.
Writes, under results/STAGE/ (results/repeat/repNN/ for a repetition):
  NAME.csv         one row per pulse, the columns of the certification campaign
  NAME.charge.csv  one row per pulse: the weighted charge of each mirror, whole pulse and up to 0.75 unit
  NAME.json        metadata and hashes
  NAME.failed      when the run or a check fails
and the reduced trace traces/STAGE/.../NAME.npz, which goes to the private repository.
"""
import hashlib
import json
import math
import os
from pathlib import Path
import socket
import subprocess
import sys
import time

import numpy as np

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT / "certification-unconditional"))
import uncond_run as UR            # weighted_charge; imports cert_run as C
import uncond_early as UE          # early_charge

C = UR.C
MANIFEST = json.loads((HERE / "manifest.json").read_text())
SIGNALS = C.SIGNALS[:17] + MANIFEST["added_signals"]          # 17 signals of the certification campaign, 2 drain currents, 2 noise currents
KEEP = ["v(vq)", "v(p)", "v(nzm)", "v(x1.si)", "v(x2.si)"] + MANIFEST["added_signals"]   # signals of the reduced trace
TIME_LIMIT = 9000


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def folders(stage, run):
    sub = Path(stage) / f"rep{run['rep']:02d}" if stage == "repeat" else Path(stage)
    return HERE / "results" / sub, HERE / "traces" / sub


def options(stage, run):
    """Largest step, linear solver and output format of a run."""
    if stage == "accel":
        return dict(tmax=run["tmax"], klu=run["klu"], binary=run["binary"])
    campaign = json.loads((HERE / "campaign.json").read_text())      # written by rep_analyze.py from the measurements
    if stage == "step":
        return dict(tmax=run["tmax"], klu=campaign["klu"], binary=campaign["binary"])
    assert (HERE / "AMENDMENT_1.md").exists(), "no noisy run before amendment 1"
    return dict(tmax=campaign["tmax"], klu=campaign["klu"], binary=campaign["binary"])


def ports_of(run):
    """The port of each simulated pulse, in order."""
    plan = [1] * 40 if run["mode"] == "leak" else [1] * 10 + [2] * 10 + [0]
    return plan[:run["periods"] - 1]


def deck(run, opt, raw):
    saved = C.SIGNALS
    C.SIGNALS = SIGNALS
    try:
        text = C.deck(dict(name=run["name"], mode=run["mode"], section=run["section"], seed=run["seed"], noise=run["noise"]), raw)
    finally:
        C.SIGNALS = saved
    full = C.MODES[run["mode"]]["periods"]
    old = f"tran 1u {full * C.PERIOD:.12g} 0 200n"
    assert text.count(old) == 1
    text = text.replace(old, f"tran 1u {run['periods'] * C.PERIOD:.12g} 0 {opt['tmax']}")
    if opt["binary"]:
        old = f"set wr_singlescale\nset numdgt=16\nwrdata {raw} " + " ".join(SIGNALS)
        assert text.count(old) == 1
        text = text.replace(old, f"set filetype=binary\nwrite {raw} " + " ".join(SIGNALS))
    if opt["klu"]:
        assert text.count(".option temp=27\n") == 1
        text = text.replace(".option temp=27\n", ".option temp=27\n.option klu\n")
    return text


def read_binary(path, columns):
    """The points of a binary raw file of ngspice: real values, one row per time point, time first."""
    blob = Path(path).read_bytes()
    head, _, body = blob.partition(b"Binary:\n")
    lines = head.decode("ascii", "replace").splitlines()
    nvar = int(next(l for l in lines if l.startswith("No. Variables:")).split(":")[1])
    npts = int(next(l for l in lines if l.startswith("No. Points:")).split(":")[1])
    assert any(l.startswith("Flags:") and "real" in l for l in lines) and nvar == columns, "unexpected raw file"
    assert len(body) == 8 * nvar * npts, "raw file of the wrong size"
    return np.frombuffer(body, dtype="<f8").reshape(npts, nvar).copy()


def shim():
    """The preloaded library that fixes the process id seen by the simulator: built from fakepid.c."""
    so = HERE / "work" / "fakepid.so"
    if not so.exists():
        tmp = so.with_suffix(f".{os.getpid()}.tmp")
        subprocess.run(["gcc", "-shared", "-fPIC", "-O2", "-o", str(tmp), str(HERE / "fakepid.c")], check=True)
        os.replace(tmp, so)
    return so


def reduced(d, run, stage):
    """Points kept: the pulse of each read that enters a measure, with the signals of KEEP."""
    ports = ports_of(run)
    if stage == "repeat":
        periods = sorted({k for port, m in run["ports"] for k in (range(1, m + 2) if port == 1 else range(11, 12 + m))})
    else:
        periods = list(range(1, len(ports) + 1))
    keep = np.zeros(len(d), dtype=bool)
    for k in periods:
        edge = k * C.PERIOD + C.OFFSET
        i0, i1 = np.searchsorted(d[:, 0], [edge - 1e-6, edge + 1.1 * C.TU])
        keep[max(i0 - 1, 0):min(i1 + 1, len(d))] = True
    cols = [0] + [1 + SIGNALS.index(s) for s in KEEP]
    return d[keep][:, cols], periods


def main():
    stage, name = sys.argv[1], sys.argv[2]
    run = next(r for r in MANIFEST["stages"][stage] if r["name"] == name)
    out, tr = folders(stage, run)
    work = HERE / "work"
    for folder in (out, tr, work):
        folder.mkdir(parents=True, exist_ok=True)
    if (out / f"{name}.json").exists() or (out / f"{name}.failed").exists():
        print(name, "already there")
        return 0
    machine = os.environ.get("REP_MACHINE", "A")
    if stage == "repeat":
        assert machine == run["machine"], f"this run belongs to machine {run['machine']}"
    for relative, expected in MANIFEST["source_sha256"].items():
        assert digest(ROOT / relative) == expected, relative
    for relative, expected in MANIFEST["code_sha256"].items():
        assert digest(ROOT / relative) == expected, relative
    ngspice = Path(MANIFEST["ngspice_path"])
    assert digest(ngspice) == MANIFEST["ngspice_sha256"], "executable changed"
    assert subprocess.check_output(["git", "-C", str(ROOT / "pdk"), "rev-parse", "HEAD"], text=True).strip() == MANIFEST["pdk_commit"], "PDK changed"
    assert (ROOT / ".spiceinit").read_bytes() == (ROOT / "spiceinit.txt").read_bytes(), "compatibility settings changed"
    opt = options(stage, run)
    raw, circuit = work / f"{stage}_{name}.raw", work / f"{stage}_{name}.spice"
    circuit.write_text(deck(run, opt, raw))
    env = dict(os.environ, SPICE_SCRIPTS=str(ROOT / "bridge_check" / "runtime"))
    if run["noise_id"] is not None:
        env.update(LD_PRELOAD=str(shim()), FAKEPID=str(run["noise_id"]))
    meta = dict(run=run, stage=stage, machine=machine, host=socket.gethostname(), options=opt, started_unix=time.time(),
                deck_sha256=digest(circuit), ngspice_sha256=digest(ngspice), signals=SIGNALS, trace_signals=["time"] + KEEP)

    def fail(reason, log=""):
        (out / f"{name}.failed").write_text(reason + "\n" + log[-3000:])
        print(name, "FAILED", reason)
        return 1

    try:
        p = subprocess.run([str(ngspice), "-b", str(circuit)], cwd=ROOT, capture_output=True, text=True, timeout=TIME_LIMIT, env=env)
    except subprocess.TimeoutExpired:
        return fail("stopped at the time limit")
    meta["simulator_seconds"] = time.time() - meta["started_unix"]
    log = p.stdout + p.stderr
    if p.returncode != 0 or not raw.exists() or "aborted" in log or "too small" in log:
        return fail(f"simulator status {p.returncode}", log)
    try:
        d = read_binary(raw, len(SIGNALS) + 1) if opt["binary"] else np.loadtxt(raw)
    except (AssertionError, ValueError, StopIteration) as e:
        return fail(f"output not readable: {e}")
    raw.unlink()
    meta["read_seconds"] = time.time() - meta["started_unix"] - meta["simulator_seconds"]
    if d.ndim != 2 or d.shape[1] != len(SIGNALS) + 1 or not np.isfinite(d).all():
        return fail("trace of the wrong shape or with a value that is not finite")
    if np.any(np.diff(d[:, 0]) < 0) or d[-1, 0] < run["periods"] * C.PERIOD - 1e-10:
        return fail("trace not ordered or cut short")
    ports = ports_of(run)
    rows, rest_fire = C.rows_of(d, ports)
    path = out / f"{name}.csv"
    with path.open("w") as fh:                                   # the format of cert_run.py
        fh.write(",".join(C.analyze.COLS + C.EXTRA) + "\n")
        for r in rows:
            fh.write(",".join(["%d" % x for x in r[:3]] + ["%.6f" % r[3], "%.5f" % r[4], "%.5f" % r[5], "%.5f" % r[6], "%d" % r[7],
                               "%.5f" % r[8], "%.5f" % r[9], "%d" % r[10], "%.9f" % r[11], "%.9f" % r[12], "%.9f" % r[13], "%d" % r[14],
                               "%.6f" % r[15], "%.6f" % r[16]] + ["%.12g" % x for x in r[17:]]) + "\n")
    checked, why = C.analyze.read_run(str(path), ports)
    if checked is None or not all(math.isfinite(x) for r in rows for x in r):
        path.rename(out / f"{name}.rejected.csv")
        return fail("result rejected: " + (why or "a value is not finite"))
    # the current of each mirror: the drain current of its output transistor plus the current of its noise source
    col = {s: 1 + i for i, s in enumerate(SIGNALS)}
    a = MANIFEST["added_signals"]
    im = np.column_stack([d[:, 0], d[:, col[a[0]]] + d[:, col[a[2]]], d[:, col[a[1]]] + d[:, col[a[3]]]])
    charge = []
    for k in range(1, len(ports) + 1):
        edge = k * C.PERIOD + C.OFFSET
        charge.append((k - 1, ports[k - 1], UR.weighted_charge(im, 1, edge), UR.weighted_charge(im, 2, edge),
                       UE.early_charge(im, 1, edge), UE.early_charge(im, 2, edge)))
    if not all(math.isfinite(w) and w > 0 for r in charge for w in r[2:]):
        return fail("charge measure: a value is not finite or not positive")
    with (out / f"{name}.charge.csv").open("w") as fh:
        fh.write("pulse,port,w1,w2,e1,e2\n")
        for r in charge:
            fh.write("%d,%d,%.12g,%.12g,%.12g,%.12g\n" % r)
    kept, periods = reduced(d, run, stage)
    np.savez_compressed(tr / f"{name}.npz", data=kept, signals=np.array(["time"] + KEEP), periods=np.array(periods))
    edge = C.PERIOD + C.OFFSET
    i0, i1 = np.searchsorted(d[:, 0], [edge, edge + C.TU])
    noise = np.ascontiguousarray(d[i0:i1][:, [col["v(nzm)"], col[a[2]], col[a[3]]]])
    meta.update(finished_unix=time.time(), points=int(len(d)), rest_fire=rest_fire, csv_sha256=digest(path),
                charge_sha256=digest(out / f"{name}.charge.csv"), trace_points_kept=int(len(kept)), trace_periods=periods,
                trace_sha256=digest(tr / f"{name}.npz"), noise_sha256=hashlib.sha256(noise.tobytes()).hexdigest(), status="done")
    (out / f"{name}.json").write_text(json.dumps(meta, indent=1) + "\n")
    print(name, "done", len(d), "points,", len(kept), "kept,", round(meta["simulator_seconds"]), "s")
    return 0


if __name__ == "__main__":
    sys.exit(main())
