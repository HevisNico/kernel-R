"""Stage J of ../PREDICTION.md: junction areas on the full cell, no layout.

  python3 -I j_stage.py plan          the six runs
  python3 -I j_stage.py manifest      write j_manifest.json: the hash of every input (before any run)
  python3 -I j_stage.py launch --go   run them, four at a time; refuses to start without --go
  python3 -I j_stage.py report        write J_REPORT.md from results_j/

Each run is `../../circuit/run.py`, unchanged, in a folder of its own. For the runs with areas the
simulator is reached through shim/ngspice, which rewrites the deck with netlist.py and areas.csv.
The control run J6 uses the deck of run.py as it is.

The launch checks the manifest first: an input whose hash has changed stops it.
MODELS points at the clone made by ../../circuit/fetch_pdk.sh.
"""
import hashlib
import json
import os
import shutil
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

HERE = Path(__file__).resolve().parent
CIRCUIT = HERE.parent.parent / "circuit"
RESULTS = HERE / "results_j"
NGSPICE = os.environ.get("P1_NGSPICE", "/usr/bin/ngspice")
MODELS = Path(os.environ.get("MODELS", CIRCUIT / "pdk"))
LIMIT_S = 60 * 60

# name, kind, arguments of run.py after the section, areas, reference
RUNS = [
    ("j1", "cell", ["rel=1"], True, "nom"),
    ("j2", "cell", ["temp=125", "rel=1"], True, "pvt_tt_125"),
    ("j3", "refresh", ["60", "rel=1"], True, "refresh_none"),
    ("j4", "refresh", ["100", "rlk=1e11", "rel=1"], True, "refresh_lk11"),
    ("j5", "refresh", ["60", "temp=125", "rel=1"], True, None),
    ("j6", "refresh", ["60", "temp=125", "rel=1"], False, None),
]
INPUTS = [CIRCUIT / "cell.spice", CIRCUIT / "blocks.spice", CIRCUIT / "run.py", CIRCUIT / "noise.json",
          CIRCUIT / "spiceinit.txt", HERE / "netlist.py", HERE / "shim" / "ngspice", HERE / "areas.csv",
          HERE / "j_stage.py"]


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def pdk_commit():
    return subprocess.run(["git", "-C", str(MODELS), "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()


def manifest():
    return dict(stage="J", prediction_sha256=digest(HERE.parent / "PREDICTION.md"),
                ngspice_path=NGSPICE, ngspice_sha256=digest(NGSPICE), pdk_commit=pdk_commit(),
                inputs={str(p.relative_to(HERE.parent.parent)): digest(p) for p in INPUTS},
                runs=[dict(name=n, kind=k, section="tt", args=a, areas=ar, reference=ref) for n, k, a, ar, ref in RUNS])


def check_manifest():
    stored = json.loads((HERE / "j_manifest.json").read_text())
    now = manifest()
    bad = [k for k in stored if stored[k] != now[k]]
    if bad:
        sys.exit("the manifest does not match the inputs: " + ", ".join(bad))
    return stored


def one(run):
    name, kind, args, areas, _ = run
    if (RESULTS / f"{name}.csv").exists() or (RESULTS / f"{name}.failed").exists():
        return f"{name} already there"
    d = HERE / "build" / "j" / name
    shutil.rmtree(d, ignore_errors=True)
    (d / "work").mkdir(parents=True)
    (d / "results").mkdir()
    for f in ("cell.spice", "blocks.spice", "run.py", "noise.json"):
        shutil.copy(CIRCUIT / f, d / f)
    shutil.copy(CIRCUIT / "spiceinit.txt", d / ".spiceinit")
    os.symlink(MODELS, d / "pdk")
    env = dict(os.environ)
    if areas:
        env.update(PATH=f"{HERE / 'shim'}:{env['PATH']}", P1_HOME=str(HERE), P1_NGSPICE=NGSPICE,
                   P1_MODE="areas", P1_AREAS=str(HERE / "areas.csv"))
        env.pop("P1_CAPS", None)
    started = time.time()
    try:
        p = subprocess.run([sys.executable, "-I", "run.py", kind, name, "tt"] + args, cwd=d, env=env,
                           capture_output=True, text=True, timeout=LIMIT_S)
        status = p.returncode
    except subprocess.TimeoutExpired:
        subprocess.run(["pkill", "-f", f"work/{name}.spice"])
        status = "time limit"
    meta = dict(name=name, started_unix=started, finished_unix=time.time(), status=status, areas=areas)
    deck = d / "work" / (f"{name}.spice.p1" if areas else f"{name}.spice")
    if deck.exists():
        meta["deck_sha256"] = digest(deck)
    if areas and status == 0 and not deck.exists():
        status = meta["status"] = "the deck was not rewritten"
    produced = d / "results" / f"{name}.csv"
    if status == 0 and produced.exists():
        shutil.copy(produced, RESULTS / f"{name}.csv")
        meta["csv_sha256"] = digest(produced)
        if (d / "results" / f"{name}.restfire").exists():
            shutil.copy(d / "results" / f"{name}.restfire", RESULTS / f"{name}.restfire")
    else:
        failed = d / "results" / f"{name}.failed"
        (RESULTS / f"{name}.failed").write_text(failed.read_text() if failed.exists() else f"status {status}\n")
    (RESULTS / f"{name}.json").write_text(json.dumps(meta, indent=1) + "\n")
    return f"{name} status {status}, {meta['finished_unix'] - started:.0f} s"


def launch():
    if "--go" not in sys.argv:
        sys.exit("stage J starts only on the owner's word: launch --go")
    check_manifest()
    RESULTS.mkdir(exist_ok=True)
    with ThreadPoolExecutor(4) as ex:
        for line in ex.map(one, RUNS):
            print(line, flush=True)


# ---- report

HOLDS, FAILS, NA = "holds", "fails", "not evaluable"


def load():
    sys.path.insert(0, str(CIRCUIT))
    import analyze                       # read_run and the two predicates of the guard, unchanged
    runs, why = {}, {}
    for name, *_ in RUNS:
        if (RESULTS / f"{name}.failed").exists():
            runs[name], why[name] = None, "run failed"
            continue
        runs[name], why[name] = analyze.read_run(RESULTS / f"{name}.csv")
    return analyze, runs, why


def series(rows, q):
    """Pulses of port q alone in a cell run: fired flags, latencies, steps of the pulsed port."""
    return [x for x in rows if x["port"] == q]


def first_fire(xs):
    return next((i for i, x in enumerate(xs) if x["fired"]), None)


def silent_after_stop(rows):
    k = first_fire(rows)
    return None if k is None else [x["pulse"] for x in rows[k + 1:] if not x["fired"]]


def every(rows, lo, hi):
    """After the stop, silent pulses at least twice, every lo to hi periods."""
    s = silent_after_stop(rows)
    if s is None:
        return FAILS, "no FIRE"
    gaps = [b - a for a, b in zip(s, s[1:])]
    text = f"silent after the stop at pulses {s}; intervals {gaps}"
    return (HOLDS if len(s) >= 2 and all(lo <= g <= hi for g in gaps) else FAILS), text


def verdicts(runs, why, analyze):
    V = []

    def add(key, run, text, fn):
        if runs[run] is None:
            V.append((key, text, NA, f"{run}: {why[run]}"))
        else:
            status, measured = fn(runs[run])
            V.append((key, text, status, measured))

    def ja(rows):
        s = [series(rows, q) for q in (1, 2)]
        k = [first_fire(x) for x in s]
        ok = all(ki == 4 and all(x["fired"] for x in si[4:]) for ki, si in zip(k, s)) and rows[-1]["fired"]
        return (HOLDS if ok else FAILS), f"first FIRE after {k[0]} and {k[1]} silent pulses; joint pulse {'fires' if rows[-1]['fired'] else 'silent'}"

    def silent_steps(rows):
        return [x["step"][q] for q in (1, 2) for x in series(rows, q) if not x["fired"]]

    def jb(rows):
        st = silent_steps(rows)
        return (HOLDS if st and all(1.346 <= v <= 1.356 for v in st) else FAILS), f"{len(st)} silent steps from {min(st):.3f} to {max(st):.3f} mV" if st else "no silent pulse"

    def other_steps(rows):
        st = []
        for x in rows:
            for q in (1, 2):
                pulsed = x["port"] in (q, 0)
                if (pulsed and x["fired"]) or not pulsed:
                    st.append(x["step"][q])
        return st

    def jc(rows):
        st = other_steps(rows)
        return (HOLDS if all(abs(v) <= 0.002 for v in st) else FAILS), f"{len(st)} steps of firing pulses and of ports at rest, largest {max(abs(v) for v in st):.3f} mV"

    def jd(rows):
        single = [x["lat"] for x in rows[:-1] if x["fired"]]
        joint = rows[-1]["lat"]
        ok = single and joint is not None and all(0.905 <= v <= 0.925 for v in single) and 0.265 <= joint <= 0.272
        return (HOLDS if ok else FAILS), (f"single port {min(single):.4f} to {max(single):.4f}; " if single else "no single FIRE; ") + (f"joint {joint:.4f}" if joint is not None else "joint silent")

    def none_after(rows):
        s = silent_after_stop(rows)
        if s is None:
            return FAILS, "no FIRE"
        return (HOLDS if not s else FAILS), f"{len(s)} silent pulses after the stop" + (f", at {s}" if s else "")

    def jg(rows):
        st = [x["step"][2] for x in rows if x["port"] == 1]
        m = sum(st) / len(st)
        return (HOLDS if -0.28 <= m <= -0.12 else FAILS), f"mean step of port 2 at rest {m:+.4f} mV per period over {len(st)} periods"

    def count(q, allowed):
        def fn(rows):
            s = series(rows, q)
            k = first_fire(s)
            n = len(s) if k is None else k
            return (HOLDS if n in allowed else FAILS), f"{n} silent pulses" + (", no FIRE in its series" if k is None else "")
        return fn

    def jj(rows):
        return (HOLDS if rows[-1]["fired"] else FAILS), (f"fires at {rows[-1]['lat']:.4f}" if rows[-1]["fired"] else "silent")

    add("JA", "j1", "J1: 4 silent pulses on each port, then a FIRE on the 6 that follow; the joint pulse fires", ja)
    add("JB", "j1", "J1: every silent step between 1.346 and 1.356 mV", jb)
    add("JC", "j1", "J1: steps of firing pulses and of ports at rest at most 0.002 mV", jc)
    add("JD", "j1", "J1: latency of a single port 0.905 to 0.925, of the joint pulse 0.265 to 0.272", jd)
    add("JE", "j3", "J3: no silent pulse after the stop", none_after)
    add("JF", "j4", "J4: after the stop, a silent pulse every 22 to 24 periods", lambda r: every(r, 22, 24))
    add("JG", "j2", "J2: a port at rest drifts toward a lower gain by 0.12 to 0.28 mV per period", jg)
    add("JH", "j2", "J2: port 1 silent for 8 or 9 pulses", count(1, (8, 9)))
    add("JI", "j2", "J2: port 2 silent for 9 or 10 pulses", count(2, (9, 10)))
    add("JJ", "j2", "J2: the joint pulse fires", jj)
    add("JK", "j5", "J5: after the stop, a silent pulse every 5 to 11 periods", lambda r: every(r, 5, 11))
    add("JL", "j6", "J6: no silent pulse after the stop", none_after)
    events = []
    for name, *_ in RUNS:
        if runs[name] is None:
            events.append(f"{name}: {why[name]}")
            continue
        if (RESULTS / f"{name}.restfire").exists():
            events.append(f"{name}: protection in the period at rest")
        for x in runs[name]:
            e = analyze.not_a_fire(x) or analyze.against(x)
            if e:
                events.append(f"{name} pulse {x['pulse']}: {e}")
    V.append(("JM", "The guard reports nothing on the six runs",
              NA if any(runs[n] is None for n, *_ in RUNS) else (FAILS if events else HOLDS),
              "; ".join(events) if events else "nothing"))
    return V


def report():
    analyze, runs, why = load()
    V = verdicts(runs, why, analyze)
    out = ["# Stage J: report", "",
           "Written by `j_stage.py report` under [`../PREDICTION.md`](../PREDICTION.md). Simulations of the "
           "nominal cell, typical corner, no noise, with the source and drain areas of `areas.csv`. No layout.", "",
           f"{sum(v[2] == HOLDS for v in V)} hold, {sum(v[2] == FAILS for v in V)} fail, "
           f"{sum(v[2] == NA for v in V)} not evaluable, of {len(V)}.", "",
           "| | Prediction | Measured | Verdict |", "|---|---|---|---|"]
    out += [f"| {k} | {t} | {m} | {s} |" for k, t, s, m in V]
    out += ["", "## Runs", "", "| Run | Result | Pulses | Wall time |", "|---|---|---|---|"]
    for name, *_ in RUNS:
        meta = json.loads((RESULTS / f"{name}.json").read_text()) if (RESULTS / f"{name}.json").exists() else {}
        wall = f"{meta['finished_unix'] - meta['started_unix']:.0f} s" if meta else "—"
        out.append(f"| `{name}` | {'result' if runs[name] is not None else why[name]} | "
                   f"{len(runs[name]) if runs[name] is not None else '—'} | {wall} |")
    out += ["", "## Rows", ""]
    for name, kind, *_ in RUNS:
        if runs[name] is None:
            continue
        out += [f"### `{name}`", "", "| Pulse | Port | FIRE | Latency | Step 1 (mV) | Step 2 (mV) |", "|---|---|---|---|---|---|"]
        for x in runs[name]:
            out.append(f"| {x['pulse']} | {x['port']} | {'yes' if x['fired'] else 'no'} | "
                       f"{x['lat']:.4f} | {x['step'][1]:+.3f} | {x['step'][2]:+.3f} |" if x["fired"] else
                       f"| {x['pulse']} | {x['port']} | no | — | {x['step'][1]:+.3f} | {x['step'][2]:+.3f} |")
        out.append("")
    (HERE / "J_REPORT.md").write_text("\n".join(out) + "\n")
    for k, t, s, m in V:
        print(k, s, "|", m)


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "plan"
    if cmd == "plan":
        for n, k, a, ar, ref in RUNS:
            print(n, k, "tt", " ".join(a), "areas" if ar else "no area", "reference:", ref)
    elif cmd == "manifest":
        (HERE / "j_manifest.json").write_text(json.dumps(manifest(), indent=1) + "\n")
        print("j_manifest.json written")
    elif cmd == "launch":
        launch()
    elif cmd == "report":
        report()
    else:
        sys.exit(__doc__)
