"""One run of stage P, made by a runner of research/circuit that is not edited.

  python3 -I p_run.py check        the harness on the schematic: eight runs, compared with committed results;
                                   writes ref_p/check.txt and the schematic reference ref_p/nom_read.csv
  python3 -I p_run.py compare      the comparison again, on the runs already made
  python3 -I p_run.py check_extra  three more schematic runs: the noise identifier and the supply current

The runners of the certification campaigns look their runs up in a manifest beside them, write
their results beside them, and call the simulator by the path the manifest gives. So each run is
made in a mirror: a folder under build/ that holds copies of the files of research/circuit the
runners read, byte for byte, and a manifest written here, which names the runs of stage P and
gives p_shim/ngspice as the simulator. The shim rewrites the deck with netlist.py (areas and
capacitances) and starts the real simulator.

After a run, its result files are copied to results_p/ under the name of the run:
  NAME.csv, NAME.json            rows and metadata of the runner (for a ramp, NAME.csv holds its static level)
  NAME.charge.csv, NAME.early.csv  for the runs of uncond_run.py: the charges of each mirror
  NAME.supply.json               for the nominal cell run: the mean current of the supply in each period
  NAME.failed                    instead, when the run fails
The compact traces stay in the mirror: they are not committed.
"""
import hashlib
import json
import os
import shutil
import subprocess
import sys
import threading
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import p_plan

CIRCUIT = HERE.parent.parent / "circuit"
RESULTS = HERE / "results_p"
BUILD = HERE / "build" / "p"
SHIM = HERE / "p_shim" / "ngspice"
NGSPICE = os.environ.get("P1_NGSPICE", "/usr/bin/ngspice")
MODELS = Path(os.environ.get("MODELS", CIRCUIT / "pdk"))
CAPS = dict(primary=HERE / "p_caps_primary.csv", secondary=HERE / "p_caps.csv")
SOURCES = ["cell.spice", "blocks.spice", "noise.json", "spiceinit.txt", "bridge_check/runtime/spinit"]
COPIES = SOURCES + ["analyze.py", "campaign.py", "run.py", "certification/cert_run.py", "certification/cert_analyze.py",
                    "certification-unconditional/uncond_run.py", "certification-unconditional/uncond_early.py",
                    "certification-unconditional/uncond_analyze.py", "certification-unconditional/uncond_amend1.py"]
ADDED_SIGNALS = ["@m.x1.xmout.msky130_fd_pr__nfet_01v8[id]", "@m.x2.xmout.msky130_fd_pr__nfet_01v8[id]"]
LIMIT_S = 60 * 60
LOCK = threading.Lock()
PERIOD = 440e-6


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def pdk_commit():
    return subprocess.run(["git", "-C", str(MODELS), "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()


def mirror(root, runs):
    """The folder a runner works in. runs: the cert and uncond runs it must find in its manifest,
    as dicts with name, tool, stage, mode, section, seed, noise. Returns root."""
    root = Path(root)
    for rel in COPIES:
        dst = root / rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy(CIRCUIT / rel, dst)
    shutil.copy(CIRCUIT / "spiceinit.txt", root / ".spiceinit")
    if not (root / "pdk").exists():
        os.symlink(MODELS, root / "pdk")
    so = root / "fakepid.so"
    if not so.exists():
        subprocess.run(["gcc", "-shared", "-fPIC", "-O2", "-o", str(so), str(CIRCUIT / "repetition" / "fakepid.c")], check=True)
    base = dict(ngspice_path=str(SHIM), ngspice_version="p_shim/ngspice in front of " + NGSPICE, ngspice_sha256=digest(SHIM),
                pdk_commit=pdk_commit(), temperature_C=27, max_step_s=2e-07,
                source_sha256={rel: digest(CIRCUIT / rel) for rel in SOURCES})

    def stages(tool, names):
        out = {s: [] for s in names}
        for r in runs:
            if r["tool"] == tool:
                out[r["stage"]].append(dict(name=r["name"], mode=r["mode"], section=r["section"], seed=r["seed"], noise=r["noise"]))
        return out
    (root / "certification" / "manifest.json").write_text(json.dumps(dict(
        base, kind="stage P of research/sky130-layout, runs of cert_run.py",
        stages=stages("cert", ["preflight", "calibration", "characterization", "test"])), indent=1) + "\n")
    (root / "certification-unconditional" / "manifest.json").write_text(json.dumps(dict(
        base, kind="stage P of research/sky130-layout, runs of uncond_run.py",
        cert_run_sha256=digest(CIRCUIT / "certification" / "cert_run.py"), added_signals=ADDED_SIGNALS,
        stages=stages("uncond", ["preflight", "scan", "gain"])), indent=1) + "\n")
    return root


def supply_summary(path, periods):
    import numpy as np
    d = np.loadtxt(path)
    t, i = d[:, 0], -d[:, 1]                         # the source delivers -i(vdd)
    mean = []
    for k in range(periods):
        a, b = k * PERIOD, (k + 1) * PERIOD
        sel = (t >= a) & (t <= b)
        tt = np.concatenate(([a], t[sel], [b]))
        ii = np.interp(tt, t, i)
        mean.append(float(np.sum(np.diff(tt) * (ii[:-1] + ii[1:]) / 2) / PERIOD))
    return dict(what="mean current delivered by the 1.8 V source in each period of 440 us; period 0 is at rest",
                period_s=PERIOD, mean_A=mean, points=int(len(t)))


def run_in(root, run, name, mode, caps, results):
    """Make `run` in the mirror `root` under the name it has there, and copy its results as `name`."""
    results.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, P1_HOME=str(HERE), P1_NGSPICE=NGSPICE, P1_MODE=mode, P1_AREAS=str(HERE / "p_areas.csv"),
               P1_CAPS=str(caps), P1_FAKEPID=str(root / "fakepid.so"))
    env.pop("P1_NOISE_ID", None)
    env.pop("P1_SUPPLY", None)
    if run.get("noise_id") is not None:
        env["P1_NOISE_ID"] = str(run["noise_id"])
    inner, started = run["name"], time.time()

    def failed(reason):
        (results / f"{name}.failed").write_text(reason.rstrip() + "\n")
        return f"{name} FAILED {reason.splitlines()[0][:120]}"

    if run["tool"] == "circuit":
        d = root / "circuit_runs" / inner
        shutil.rmtree(d, ignore_errors=True)
        (d / "work").mkdir(parents=True)
        (d / "results").mkdir()
        for f in ("cell.spice", "blocks.spice", "run.py", "noise.json"):
            shutil.copy(CIRCUIT / f, d / f)
        shutil.copy(CIRCUIT / "spiceinit.txt", d / ".spiceinit")
        os.symlink(MODELS, d / "pdk")
        env["PATH"] = f"{SHIM.parent}:{env['PATH']}"
        supply = d / "supply.txt" if inner == "nom_cell" else None
        if supply:
            env["P1_SUPPLY"] = str(supply)
        try:
            p = subprocess.run([sys.executable, "-I", "run.py", run["kind"], inner, "tt"] + run["args"], cwd=d, env=env,
                               capture_output=True, text=True, timeout=LIMIT_S)
            status = p.returncode
        except subprocess.TimeoutExpired:
            subprocess.run(["pkill", "-f", f"{d}/work/"])
            status = "time limit"
        out, deck = d / "results" / f"{inner}.csv", d / "work" / f"{inner}.spice.p1"
        if status != 0 or not out.exists() or not deck.exists():
            f = d / "results" / f"{inner}.failed"
            return failed(f.read_text() if f.exists() else f"status {status}")
        meta = dict(name=name, tool="circuit", kind=run["kind"], args=run["args"], started_unix=started, finished_unix=time.time(),
                    deck_sha256=digest(deck), csv_sha256=digest(out), mode=mode, caps=caps.name)
        if supply and supply.exists():
            periods = sum(1 for _ in open(out)) - 1 + 1          # one row per pulse, and the period at rest
            (results / f"{name}.supply.json").write_text(json.dumps(supply_summary(supply, periods), indent=1) + "\n")
            supply.unlink()
        if (d / "results" / f"{inner}.restfire").exists():
            shutil.copy(d / "results" / f"{inner}.restfire", results / f"{name}.restfire")
        (results / f"{name}.json").write_text(json.dumps(meta, indent=1) + "\n")
        shutil.copy(out, results / f"{name}.csv")
        return f"{name} done, {meta['finished_unix'] - started:.0f} s"

    folder = root / ("certification" if run["tool"] == "cert" else "certification-unconditional")
    script = "cert_run.py" if run["tool"] == "cert" else "uncond_run.py"
    try:
        p = subprocess.run([sys.executable, "-B", script, run["stage"], inner], cwd=folder, env=env, capture_output=True,
                           text=True, timeout=LIMIT_S)
        log = p.stdout[-2000:] + p.stderr[-2000:]
    except subprocess.TimeoutExpired:
        return failed("time limit")
    out = folder / "results" / run["stage"]
    if (out / f"{inner}.failed").exists():
        return failed((out / f"{inner}.failed").read_text())
    if p.returncode != 0 or not (out / f"{inner}.json").exists():
        return failed(f"status {p.returncode}\n{log}")
    meta = json.loads((out / f"{inner}.json").read_text())
    extra = []
    if run["tool"] == "uncond":
        listed = json.loads((folder / "manifest.json").read_text())["stages"][run["stage"]]
        k = next(i for i, r in enumerate(listed) if r["name"] == inner)
        e = subprocess.run([sys.executable, "-B", "uncond_early.py", run["stage"], str(k), str(k + 1)], cwd=folder, env=env,
                           capture_output=True, text=True)
        extra = [f"{inner}.charge.csv", f"{inner}.early.csv"]
        if not all((out / x).exists() for x in extra):
            return failed("charge or early charge missing\n" + e.stdout[-1000:] + e.stderr[-1000:])
    for x in extra:
        shutil.copy(out / x, results / x.replace(inner, name, 1))
    shutil.copy(out / f"{inner}.json", results / f"{name}.json")
    if run["mode"] == "ramp":
        (results / f"{name}.csv").write_text("static_level\n%.12g\n" % meta["static_level"])
    else:
        shutil.copy(out / f"{inner}.csv", results / f"{name}.csv")
    return f"{name} done, {meta['finished_unix'] - meta['started_unix']:.0f} s"


def one(name):
    """A run of the queues of stage P, by its name."""
    plan = {r["name"]: r for q in p_plan.queues().values() for r in q}
    run = plan[name]
    if (RESULTS / f"{name}.csv").exists() or (RESULTS / f"{name}.failed").exists():
        return f"{name} already there"
    root = BUILD / run["analysis"]
    inner = dict(run, name=name[2:] if run["analysis"] == "secondary" else name)
    with LOCK:
        if not (root / "certification" / "manifest.json").exists():
            same = [dict(r, name=r["name"][2:] if r["analysis"] == "secondary" else r["name"])
                    for r in plan.values() if r["analysis"] == run["analysis"]]
            mirror(root, same)
    try:
        return run_in(root, inner, name, "stage", CAPS[run["analysis"]], RESULTS)
    except Exception as e:                                    # a run that cannot be made is a failed run
        (RESULTS / f"{name}.failed").write_text(f"{type(e).__name__}: {e}\n")
        return f"{name} FAILED {type(e).__name__}"


# ---- the harness on the schematic

CHECKS = [("nom_ramp", "certification/results/preflight"), ("nom_read", None), ("t6065_ramp", "certification/results/characterization"),
          ("t6065_read", "certification/results/characterization"), ("nom_leak", "certification/results/preflight"),
          ("u6065_leak", "certification-unconditional/results/scan"), ("u6065_train", "certification-unconditional/results/gain"),
          ("c5001_train", "certification/results/calibration")]


def check(simulate=True):
    """Eight runs of the harness with the deck of the schematic, against the committed results.
    With simulate=False the runs already in build/ are compared again."""
    from concurrent.futures import ThreadPoolExecutor
    plan = {r["name"]: r for q in p_plan.queues().values() for r in q}
    root, results, ref = BUILD / "check", BUILD / "check_results", HERE / "ref_p"
    if simulate:
        shutil.rmtree(root, ignore_errors=True)
        shutil.rmtree(results, ignore_errors=True)
        mirror(root, [plan[n] for n, _ in CHECKS])
        with ThreadPoolExecutor(4) as ex:
            for line in ex.map(lambda n: run_in(root, plan[n], n, "schematic", CAPS["primary"], results), [n for n, _ in CHECKS]):
                print(line, flush=True)
    ref.mkdir(exist_ok=True)
    lines, ok = [], True
    for name, where in CHECKS:
        if where is None:
            lines.append(f"{name}: no committed result; csv sha256 {digest(results / (name + '.csv'))} is the schematic reference of stage P")
            continue
        folder = CIRCUIT / where
        if plan[name]["mode"] == "ramp":
            a = json.loads((results / f"{name}.json").read_text())["static_level"]
            b = json.loads((folder / f"{name}.json").read_text())["static_level"]
            same = a == b
            lines.append(f"{name}: static level {a!r} against {b!r}: {'identical' if same else 'DIFFERENT'}")
        else:
            files = [f"{name}.csv"] + ([f"{name}.charge.csv", f"{name}.early.csv"] if plan[name]["tool"] == "uncond" else [])
            same = all((results / f).exists() and (results / f).read_bytes() == (folder / f).read_bytes() for f in files)
            lines.append(f"{name}: {', '.join(files)} {'identical byte for byte to' if same else 'DIFFERENT from'} research/circuit/{where}")
        ok = ok and same
    lines.append("HARNESS " + ("PASSES" if ok else "FAILS"))
    (ref / "check.txt").write_text("\n".join(lines) + "\n")
    for f in ("nom_read.csv", "nom_read.json"):              # the schematic reference of the nominal read
        shutil.copy(results / f, ref / f)
    print("\n".join(lines))
    return ok


def check_extra(simulate=True):
    """Two more checks on the schematic: a noisy run made twice with the same noise identifier gives
    the same rows, and saving the supply current changes nothing. The nominal cell run uses the
    option rel=1 of run.py, as in stage J: times are then printed from the start of each pulse, with
    more digits than in the committed nom.csv, so the six time columns are compared within 0.0003."""
    import csv
    from concurrent.futures import ThreadPoolExecutor
    plan = {r["name"]: r for q in p_plan.queues().values() for r in q}
    jobs = []
    for tag in ("extra_a", "extra_b"):
        root = BUILD / tag
        if simulate:
            shutil.rmtree(root, ignore_errors=True)
            shutil.rmtree(BUILD / (tag + "_results"), ignore_errors=True)
            mirror(root, [plan["t6065_train"]])
        jobs.append((root, plan["t6065_train"], "t6065_train", BUILD / (tag + "_results")))
    jobs.append((BUILD / "extra_a", plan["nom_cell"], "nom_cell", BUILD / "extra_a_results"))
    if simulate:
        with ThreadPoolExecutor(4) as ex:
            for line in ex.map(lambda j: run_in(j[0], j[1], j[2], "schematic", CAPS["primary"], j[3]), jobs):
                print(line, flush=True)
    a, b = BUILD / "extra_a_results", BUILD / "extra_b_results"
    same_noise = (a / "t6065_train.csv").read_bytes() == (b / "t6065_train.csv").read_bytes()
    committed = (a / "t6065_train.csv").read_bytes() == (CIRCUIT / "certification" / "results" / "test" / "t6065_train.csv").read_bytes()
    with open(a / "nom_cell.csv", newline="") as fa, open(CIRCUIT / "results" / "nom.csv", newline="") as fb:
        ra, rb = list(csv.DictReader(fa)), list(csv.DictReader(fb))
    times = ["fire_latency", "reopen", "entry1", "exit1", "entry2", "exit2"]
    exact = len(ra) == len(rb) and all(x[k] == y[k] for x, y in zip(ra, rb) for k in x if k not in times)
    drift = round(max(abs(float(x[k]) - float(y[k])) for x, y in zip(ra, rb) for k in times), 6)
    same_cell = exact and drift <= 0.0003
    lines = [f"t6065_train with noise, noise identifier {plan['t6065_train']['noise_id']}, made twice: "
             + ("identical byte for byte" if same_noise else "DIFFERENT"),
             "the same run against the committed run of the campaign, whose noise was not fixed: "
             + ("identical" if committed else "different, as two draws of the noise must be"),
             "nom_cell with the supply current saved and rel=1, against research/circuit/results/nom.csv: flags, stored "
             f"voltages, lowest voltage and steps {'identical' if exact else 'DIFFERENT'}; times within {drift:.4f} unit",
             "EXTRA " + ("PASSES" if same_noise and same_cell and not committed else "FAILS")]
    shutil.copy(a / "nom_cell.supply.json", HERE / "ref_p" / "nom_cell.supply.json")      # the supply current of the schematic
    (HERE / "ref_p" / "check_extra.txt").write_text("\n".join(lines) + "\n")
    print("\n".join(lines))
    return same_noise and same_cell


if __name__ == "__main__":
    if sys.argv[1:] in (["check_extra"], ["compare_extra"]):
        sys.exit(0 if check_extra(simulate=sys.argv[1] == "check_extra") else 1)
    if sys.argv[1:] in (["check"], ["compare"]):
        sys.exit(0 if check(simulate=sys.argv[1] == "check") else 1)
    sys.exit(__doc__)
