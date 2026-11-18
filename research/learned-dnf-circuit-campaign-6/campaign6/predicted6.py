"""Campaign 6's prediction record (PREDICTION.md 3, 4 and 8): PREDICTED.json, computed on machine a from the collected
evidence of M1 to M3, pushed before any network run. New code.

  predicted6.py OUT_DIR STAGE_DIR...       the campaign's five instances (STAGE_DIR: the collected folders of M1 to M3, both machines)

1. The runs of the measure stages are laid out as the batch's code reads them (BATCH_DIR/<machine>/<seed>-<run>, and
   BATCH_DIR/RUNS.json with each run's status: "complete" when it counts, else the kit's status). Every run of an
   instance is gathered under its instance's assigned machine, wherever it ran (amendment 1).
2. `predict_batch` is predict6.predict_batch copied verbatim but for two lines: it takes the seeds and their machines
   as arguments instead of reading batch6.SEEDS and batch6.MACHINE_OF, which name only the batch's 7701 to 7710
   (test_campaign6.PredictCopy shows the difference). It runs under predict6_guard's wrapper (amendment 1, stated from
   the start in PREDICTION.md 2): an instance on which campaign 5's predicted.instance raises is not eligible.
3. Each instance gets its own Lean file and its own check.sh call (predict6.gate_each, unchanged).
4. The network runs (PREDICTION.md 4) of every eligible instance (measured, eligible and gate_K0), in seed order:
   the run without noise with the skew slots, the noisy runs of rounds 1 to 3 (noise seeds 10 S + n), and the
   untrained run on the first eligible instance. None if no instance is eligible.
PREDICTED.json holds the instances as predict6_guard gives them, the network runs, decision 5's constants and
the protocol's commit. analyze6.py reproduces it byte for byte from the same evidence before any claim.
"""
import json
from pathlib import Path
import sys
from unittest import mock

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import c6                                               # noqa: E402
import c4                                               # noqa: E402
import inputs6                                          # noqa: E402
import plan                                             # noqa: E402
import predict6                                         # noqa: E402
import predict6_guard                                   # noqa: E402
from predict6 import CROSSINGS, P, collected, gate_each, predict_instance, questions, table     # noqa: E402,F401


def predict_batch(batch_dir, out_dir, seeds, machine_of, check=True):
    """Every instance of the batch from its collected runs (BATCH_DIR/<machine>/<run id>/ and BATCH_DIR/RUNS.json),
    then the gate, one Lean file per instance, each checked by its own call of campaign 5's check.sh. Writes
    PREDICTIONS.json, Gate6_<seed>.lean and check_<seed>.log."""
    import subprocess
    import gate4
    import batch6
    bd, od = Path(batch_dir), Path(out_dir)
    od.mkdir(parents=True, exist_ok=True)
    runs = json.loads((bd / "RUNS.json").read_text())
    status = {r["id"]: r["status"] for r in runs}
    xs = []
    for seed in seeds:
        m = machine_of[seed]
        mine = {i: s for i, s in status.items() if i.startswith(f"{seed}-")}
        on, off = bd / m / f"{seed}-cal-on", bd / m / f"{seed}-cal-off"
        if mine.get(f"{seed}-cal-on") != "complete" or mine.get(f"{seed}-cal-off") != "complete":
            xs.append(dict(seed=seed, machine=m, measured=False, eligible=False, why_not_measured=[f"run {i} did not complete: {s}" for i, s in sorted(mine.items()) if s != "complete"]))
            continue
        scans, ones = {}, {}
        for c, kind in CROSSINGS:
            i = f"{seed}-scan-{c}-{kind}"
            if mine.get(i) == "complete":
                rec = collected(bd / m / i)
                scans[(c, kind)] = dict(rec["result"], u0_V=rec["u0_V"])
        for c in ("a", "b"):
            i = f"{seed}-onesided-{c}"
            if mine.get(i) == "complete":
                rec = collected(bd / m / i)
                ones[c] = dict(rec["result"], u0_V=rec["u0_V"])
        bf = None
        if mine.get(f"{seed}-bothfire-c") == "complete":
            rec = collected(bd / m / f"{seed}-bothfire-c")
            bf = dict(rec["result"], u0_V=rec["u0_V"])
        x = predict_instance(seed, m, mine, on, off, scans, ones, bf)
        t, dose, _ = table(on, off)
        x.update(questions(scans, dose, P.needs(t)))
        xs.append(x)
    gate_each(xs, od, check)
    (od / "PREDICTIONS.json").write_text(json.dumps(dict(instances=xs), indent=1, default=str) + "\n")
    return xs


def layout(bd, stage_dirs, seeds, machine_of):
    """BATCH_DIR from the collected stage folders: a link per run, named as the batch's code reads it, and RUNS.json."""
    bd = Path(bd)
    recs = inputs6.records(*stage_dirs)
    runs = []
    for seed in seeds:
        m = machine_of[seed]
        (bd / m).mkdir(parents=True, exist_ok=True)
        tails = [f"cal-{g}" for g in ("on", "off")] + [f"scan-{c}-{k}" for c, k in CROSSINGS] + ["bothfire-c", "onesided-a", "onesided-b"]
        for tail in tails:
            rec = recs.get(f"{seed}-{tail}")                    # run ids by seed (amendment 1: a run may have run on the other machine)
            status = "complete" if inputs6.complete(rec) else (rec.get("status") if rec else "not started")
            if rec is not None:
                (bd / m / f"{seed}-{tail}").symlink_to(Path(rec["folder"]).resolve())
            runs.append(dict(id=f"{seed}-{tail}", machine=m, status=status))
    (bd / "RUNS.json").write_text(json.dumps(runs, indent=1) + "\n")
    return runs


def network_runs(instances):
    """PREDICTION.md 4: the network runs of the eligible instances (measured, eligible, gate_K0), in seed order."""
    elig = [x for x in sorted(instances, key=lambda x: x["seed"]) if x.get("measured") and x.get("eligible") and x.get("gate_K0")]
    runs = []
    for i, x in enumerate(elig):
        n = list(plan.calendar_needs([x["needs"][k] for k in ("a", "b", "c1", "c2")]))
        runs.append(dict(id=f"{x['seed']}-quiet", seed=x["seed"], needs=n, scenario="quiet", control="skew", noise="none", round=0))
        if i == 0:
            runs.append(dict(id=f"{x['seed']}-untrained", seed=x["seed"], needs=n, scenario="untrained", control="untrained", noise="none", round=0))
    for k in (1, 2, 3):
        for x in elig:
            n = list(plan.calendar_needs([x["needs"][j] for j in ("a", "b", "c1", "c2")]))
            runs.append(dict(id=f"{x['seed']}-n{k}", seed=x["seed"], needs=n, scenario=f"n{k}", control=None, noise="injected", round=k,
                             noise_seed=c6.noise_seed(x["seed"], k)))
    return runs


def predictions(stage_dirs, out_dir, check=True, seeds=c6.SEEDS, machine_of=c6.MACHINE_OF, batch_dir=None):
    """PREDICTED.json (as a dict) from the collected stage folders; the Lean files and check logs go to out_dir.
    batch_dir: a folder already laid out as the batch's code reads it (the rehearsal's RN, on the batch's merged
    evidence, a d9e431b and b 88a34de, for seeds 7701 and 7706), used instead of laying out stage_dirs."""
    import tempfile
    with tempfile.TemporaryDirectory() as bd:
        if batch_dir is None:
            layout(bd, stage_dirs, seeds, machine_of)
        with mock.patch.object(P, "instance", predict6_guard.guarded_instance):
            xs = predict_batch(batch_dir or bd, out_dir, seeds, machine_of, check)
    xs = json.loads(json.dumps(xs, default=str))
    return dict(what="the predictions of campaign 6 (PREDICTION.md), written by predicted6.py; no network run exists when this file is written",
                protocol=c6.PROTOCOL_COMMIT, constants={k: c4.DECISION5[k] for k in c4.DECISION5}, instances=xs, network_runs=network_runs(xs))


def text(p):
    return json.dumps(p, indent=1, default=str) + "\n"


def main(argv=None):
    a = sys.argv[1:] if argv is None else argv
    c6.require_debug()
    print(c4.require_pinned())
    out = Path(a[0])
    p = predictions(a[1:], out)
    (out / "PREDICTED.json").write_text(text(p))
    print(json.dumps(dict(eligible=[r["seed"] for r in p["network_runs"] if r["scenario"] == "quiet"], network_runs=len(p["network_runs"]))))


if __name__ == "__main__":
    main()
