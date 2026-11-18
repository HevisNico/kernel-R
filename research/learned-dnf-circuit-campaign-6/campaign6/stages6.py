"""Campaign 6's stages (PREDICTION.md 4, 6 and 7): the runs of each stage, their machines, expected costs and limits,
and the launch kit's manifest of each. New code.

  stages6.py manifest STAGE OUT.json SOURCE_COMMIT [INPUTS.json | PREDICTED.json]

Stages, in a fixed sequence (PREDICTION.md 6): M1 (the calibration decks), M2 (the scans and the both-lines checks),
M3 (the one-sided sets), Q (the runs without noise of the eligible instances and the untrained run), N1, N2, N3 (the
noisy runs of rounds 1 to 3), or one merged N stage when exactly one instance is eligible. The rehearsal (7): RM1, RM2,
RM3 on the nominal cell, one instance per machine; RN, the network runs of 7701 (machine a) and 7706 (machine b).

Machines. A measure run keeps its instance's machine (PREDICTION.md 1 and 6: 7801 to 7803 on a, 7804 and 7805 on b).
A network run follows the two-shard rule (PREDICTION.md 4): within its stage, the runs in a fixed order (the runs
without noise in seed order, then the untrained run; in an N stage, in seed order) alternate a, b, a, ... from a.
Every manifest is checked here as the kit checks it: both shards nonempty, the round-robin order, and the budget. A
measure stage whose runs would all be on one machine is refused (MeasureStageOneShard), since the preregistered rule
keeps measure runs on their instance's machine: it needs an amendment before its launch, never a silent move.
"""
from fractions import Fraction as F
import hashlib
import json
import math
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import c6                                               # noqa: E402
import c4                                               # noqa: E402
import plan                                             # noqa: E402  (campaign 5, frozen: dcost, the cost formula of a calendar)
from c4 import dnf                                      # noqa: E402

ROOT = HERE.parent.parent.parent
CLOSURE = "research/sky130-supervisor-closure"
CAMPAIGN6 = f"{c6.BASE}/campaign6"
WORKFLOWS = ["Learned DNF circuit campaign 6"]
SCAN_OUTPUTS = ["evidence/input.spice", "evidence/session.log", "evidence/trace.raw", "evidence/events.json", "record.json", "noise.sha256"]
DECK_OUTPUTS = ["evidence/input.spice", "evidence/session.log", "evidence/trace.raw", "evidence/result.json", "record.json", "noise.sha256"]
BATCH_FILES = [f"{c6.BASE}/batch/{n}" for n in ("batch6.py", "scan6.py", "predict6.py", "predict6_guard.py", "report6.py", "report6_guard.py")]
OWN_FILES = [f"{CAMPAIGN6}/{n}" for n in ("c6.py", "meas6.py", "net6.py", "inputs6.py", "stages6.py", "predicted6.py", "analyze6.py",
                                          "test_campaign6.py")]
REHEARSAL_PREDICTIONS = f"{c6.BASE}/rehearsal/PREDICTIONS_BATCH.json"      # the batch's PREDICTIONS.json, 0bd3b60
REHEARSAL_PREDICTIONS_SHA256 = "e2e9e572cc80ca20f953f5ed800c306e47d3413ee7efdeceed323ea12ef3cc89"


class MeasureStageOneShard(AssertionError):
    pass


def frozen():
    """Every file a stage's runs, the predictions and the analysis read: campaign 6's own, the batch's, and campaign 5's
    frozen list but its workflow (which is not on this branch), and campaign 6's workflow."""
    c5 = [f for f in plan.FROZEN if not f.startswith(".github/")]
    return sorted(set(OWN_FILES + BATCH_FILES + c5 + [".github/workflows/learned-dnf-circuit-campaign-6.yml"]))


# ------------------------------------------------------------------------------------------------ costs and limits

def network_expected(needs, scenario):
    """PREDICTION.md 4: 718 s at need 4 with the skew slots, 1 400 s for a noisy run at need 4, 132 s untrained; another
    calendar scaled by campaign 5's dcost ratio against the need-4 calendar of the same control."""
    if scenario == "untrained":
        return c6.UNTRAINED_S
    n = tuple(plan.calendar_needs(needs))
    if scenario == "quiet":
        return c6.QUIET_SKEW_NEED4_S * F(plan.dcost(dnf.calendar(*n, "skew"))).limit_denominator(10**12) / F(plan.dcost(dnf.calendar(4, 4, 4, 4, "skew"))).limit_denominator(10**12)
    return c6.NOISY_NEED4_S * F(plan.dcost(dnf.calendar(*n))).limit_denominator(10**12) / F(plan.dcost(dnf.calendar(4, 4, 4, 4))).limit_denominator(10**12)


def with_cost(run, expected):
    e = F(expected)
    lim = c6.limit(e)
    return dict(run, expected_s=float(e), estimate_s=min(c4.ceil10(e), lim), timeout_s=lim)


def machine_expected(runs):
    e = [r["expected_s"] for r in runs]
    return sum(e) / c4.JOBS + 0.75 * max(e) if e else 0.0


def machine_cap(runs):
    caps = [r["timeout_s"] + c4.CLEANUP_S for r in runs]
    return sum(caps) / c4.JOBS + max(caps) if caps else 0.0


def expected_compute(stages):
    return sum(machine_expected([r for r in runs if r["machine"] == m]) for runs in stages for m in ("a", "b"))


def stage_cap(runs):
    return sum(machine_cap([r for r in runs if r["machine"] == m]) for m in ("a", "b"))


# ----------------------------------------------------------------------------------------------------- the runs

def measure_runs(stage, inputs=None):
    """M1: both decks of every instance. M2: the four scans and the both-lines check of every instance the inputs allow.
    M3: the two one-sided sets of every instance the inputs allow. RM1 to RM3: the same on the nominal cell."""
    base = stage[1:] if stage.startswith("R") else stage
    runs = []
    for inst in (["a-none", "b-none"] if stage.startswith("RM") else [f"{c6.MACHINE_OF[s]}-{s}" for s in c6.SEEDS]):
        m = inst.split("-")[0]
        if base != "M1" and "why_not" in inputs["instances"][inst]:
            continue
        if base == "M1":
            for g in ("on", "off"):
                runs.append(with_cost(dict(id=f"{inst}-cal-{g}", machine=m, instance=inst, kind="cal", guard=g), c6.MEASURE_S[f"cal-{g}"]))
        elif base == "M2":
            for c, kind in (("a", "pair"), ("b", "pair"), ("c", "line1"), ("c", "line2")):
                cost = c6.MEASURE_S["pair" if kind == "pair" else "line"]
                runs.append(with_cost(dict(id=f"{inst}-scan-{c}-{kind}", machine=m, instance=inst, kind="scan", cell=c, scan=kind), cost))
            runs.append(with_cost(dict(id=f"{inst}-bothfire-c", machine=m, instance=inst, kind="scan", cell="c", scan="bothfire"), c6.MEASURE_S["bothfire"]))
        else:
            for c in ("a", "b"):
                runs.append(with_cost(dict(id=f"{inst}-onesided-{c}", machine=m, instance=inst, kind="scan", cell=c, scan="onesided"), c6.MEASURE_S["onesided"]))
    if runs and {r["machine"] for r in runs} != {"a", "b"}:
        raise MeasureStageOneShard(f"refused: every run of {stage} is on machine {runs[0]['machine']}; the kit needs both shards, and "
                                   "the preregistered rule keeps measure runs on their instance's machine (an amendment is needed)")
    return runs


def two_shard(runs):
    """PREDICTION.md 4: the runs, in their fixed order, alternate a, b, a, ... from a."""
    return [dict(r, machine="ab"[i % 2]) for i, r in enumerate(runs)]


def network_stages(network_runs):
    """Q, then N1, N2, N3, from the prediction record's network runs (eligible instances only, in seed order), with
    the merged N stage when exactly one instance is eligible. Returns [(name, runs)]."""
    seeds = sorted({r["seed"] for r in network_runs})
    quiet = [r for r in network_runs if r["scenario"] == "quiet"]
    ctl = [r for r in network_runs if r["scenario"] == "untrained"]
    out = []
    if not seeds:
        return out
    cost = lambda r: with_cost(dict(r), network_expected(r["needs"], r["scenario"]))
    out.append(("Q", two_shard([cost(r) for r in sorted(quiet, key=lambda r: r["seed"]) + ctl])))
    noisy = {k: sorted((r for r in network_runs if r["scenario"] == f"n{k}"), key=lambda r: r["seed"]) for k in (1, 2, 3)}
    if len(seeds) == 1:
        out.append(("N", two_shard([cost(r) for k in (1, 2, 3) for r in noisy[k]])))
    else:
        out += [(f"N{k}", two_shard([cost(r) for r in noisy[k]])) for k in (1, 2, 3)]
    return out


def rehearsal_network_runs(predictions):
    """RN (PREDICTION.md 7): on 7701 (a) and 7706 (b), the run without noise with skew and one noisy run of round 1;
    the untrained run on 7701. The needs are those of the batch's pushed predictions."""
    by = {x["seed"]: x for x in predictions["instances"]}
    runs = []
    for seed, m in c6.REHEARSAL_SEEDS.items():
        x = by[seed]
        assert x.get("eligible") and x.get("gate_K0"), f"{seed} is not an eligible development instance"
        n = [x["needs"][k] for k in ("a", "b", "c1", "c2")]
        runs.append(with_cost(dict(id=f"{seed}-quiet", machine=m, seed=seed, needs=n, scenario="quiet", control="skew", noise="none", round=0),
                              network_expected(n, "quiet")))
        runs.append(with_cost(dict(id=f"{seed}-n1", machine=m, seed=seed, needs=n, scenario="n1", control=None, noise="injected", round=1),
                              network_expected(n, "n1")))
        if seed == 7701:
            runs.append(with_cost(dict(id=f"{seed}-untrained", machine=m, seed=seed, needs=n, scenario="untrained", control="untrained",
                                       noise="none", round=0), c6.UNTRAINED_S))
    return runs


# ------------------------------------------------------------------------------------------------- the manifest

def argv(stage, r, inputs_path=None):
    if r.get("kind") == "cal":
        return ["{python}", "{repo}/" + f"{CAMPAIGN6}/meas6.py", "cal", stage, "{out}", r["instance"].split("-", 1)[1], r["guard"], "{ngspice}", "{pdk}"]
    if r.get("kind") == "scan":
        return ["{python}", "{repo}/" + f"{CAMPAIGN6}/meas6.py", "scan", stage, "{out}", r["instance"], r["cell"], r["scan"],
                "{repo}/" + inputs_path, "{ngspice}", "{pdk}"]
    return ["{python}", "{repo}/" + f"{CAMPAIGN6}/net6.py", stage, "{out}", r["id"], str(r["seed"]), ",".join(map(str, plan.calendar_needs(r["needs"]))),
            r["control"] or "none", r["noise"], str(r["round"]), "{ngspice}", "{pdk}"]


def entry(stage, r, inputs_path=None):
    runner = f"{CAMPAIGN6}/meas6.py" if r.get("kind") in ("cal", "scan") else f"{CAMPAIGN6}/net6.py"
    return dict(id=r["id"], machine=r["machine"], scenario="stage", deck="research/circuit/cell.spice", runner=runner,
                argv=argv(stage, r, inputs_path), estimate_s=r["estimate_s"], timeout_s=r["timeout_s"],
                required_outputs=SCAN_OUTPUTS if r.get("kind") == "scan" else DECK_OUTPUTS,
                diagnostic_logs=["evidence/session.log"], noise_fingerprint="noise.sha256")


def manifest(stage, runs, source_commit, inputs_path=None, root=ROOT):
    def blob(commit, path):
        return subprocess.run(["git", "-C", str(root), "show", f"{commit}:{path}"], check=True, capture_output=True).stdout
    assert stage in c6.STAGES
    rehearsal = stage.startswith("R")
    extra = [inputs_path] if inputs_path else []
    if stage == "RN":
        extra.append(REHEARSAL_PREDICTIONS)
    m = dict(kind="registered", campaign_id=("learned-dnf-circuit-6-rehearsal-" if rehearsal else "learned-dnf-circuit-6-") + stage.lower(),
             attempt=1, executor=c4.EXECUTOR, protocol_commit=c6.PROTOCOL_COMMIT, protocol_path=c6.PROTOCOL,
             protocol_sha256=hashlib.sha256(blob(c6.PROTOCOL_COMMIT, c6.PROTOCOL)).hexdigest(), source_commit=source_commit,
             launcher_path=f"{CLOSURE}/launchkit/launch.py", marker_path=f"{c6.BASE}/RUN_ATTEMPT_{stage}.json",
             spinit_path=f"{CLOSURE}/runtime/spinit", inventory_a_path=f"{c6.BASE}/INVENTORY_a.json", inventory_b_path=f"{c6.BASE}/INVENTORY_b.json",
             source_sha256={n: hashlib.sha256(blob(source_commit, n)).hexdigest() for n in frozen() + extra},
             expected_workflows=WORKFLOWS, jobs=c4.JOBS, scenario_order=["stage"], budget_s=math.ceil(stage_cap(runs)),
             runs=[entry(stage, r, inputs_path) for r in runs])
    assert m["protocol_sha256"] == c6.PROTOCOL_SHA256, "the protocol is not PREDICTION.md as pushed at df1a3cb"
    kit_checks(m)
    return m


def kit_checks(m):
    """The kit's own checks that need no repository: both shards, the round-robin order, the budget."""
    sys.path.insert(0, str(ROOT / CLOSURE / "launchkit"))
    import launch
    assert {r["machine"] for r in m["runs"]} == {"a", "b"}, "Both machine shards must be nonempty"
    launch.round_robin(m["runs"], m["scenario_order"])
    launch.check_budget(m["runs"], m["budget_s"], m["jobs"])


def stage_runs(stage, path=None):
    """The runs of one stage from its frozen input: INPUTS_M2/M3 for M2/M3 (RM2/RM3), PREDICTED.json for Q and N, the
    batch's predictions for RN."""
    if stage in ("M1", "RM1"):
        return measure_runs(stage)
    if stage in ("M2", "M3", "RM2", "RM3"):
        return measure_runs(stage, json.loads(Path(path).read_text()))
    if stage == "RN":
        data = Path(path).read_bytes()
        assert hashlib.sha256(data).hexdigest() == REHEARSAL_PREDICTIONS_SHA256, "not the batch's pushed PREDICTIONS.json (0bd3b60)"
        return rehearsal_network_runs(json.loads(data))
    named = dict(network_stages(json.loads(Path(path).read_text())["network_runs"]))
    assert stage in named, f"refused: {stage} is not a stage of this prediction record ({sorted(named)})"
    return named[stage]


def main(argv_=None):
    a = sys.argv[1:] if argv_ is None else argv_
    c6.require_debug()
    if a[0] != "manifest":
        raise SystemExit(__doc__)
    stage, out, source = a[1], Path(a[2]), a[3]
    path = a[4] if len(a) > 4 else None
    rel = None if path is None else str(Path(path).resolve().relative_to(ROOT))
    runs = stage_runs(stage, path)
    m = manifest(stage, runs, source, rel if stage in ("M2", "M3", "RM2", "RM3") else None)
    out.write_text(json.dumps(m, indent=1) + "\n")
    print(json.dumps(dict(stage=stage, runs=len(runs), budget_s=m["budget_s"], expected_s=round(expected_compute([runs]), 2))))


if __name__ == "__main__":
    main()
