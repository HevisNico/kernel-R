"""Campaign 6's stages (PREDICTION.md 4, 6 and 7): the runs of each stage, their machines, expected costs and limits,
and the launch kit's manifest of each. New code.

  stages6.py stage-file STAGE OUT.md ATTEMPT                         the stage file: the kit's protocol of the stage
  stages6.py runs STAGE OUT.json ATTEMPT [INPUTS.json | PREDICTED.json | PREDICTED_RN.json]   the stage's run list
  stages6.py manifest STAGE OUT.json SOURCE_COMMIT ATTEMPT [INPUTS.json | PREDICTED.json | PREDICTED_RN.json]

Attempts (the audit of 2026-11-19, finding 2): every file of an attempt is under stages/<ATTEMPT>/, and the attempt's id
is written in each stage file, so each attempt's stage files, and so its claim refs, are its own; an aborted attempt
never blocks a later one.

The kit's protocol of each stage is its own stage file, stages/STAGE_<S>.md, as in campaign 5 (CAMPAIGN_RC.json named
STAGE_RC.md): the kit's claim ref is keyed by the protocol's SHA-256 and the machine alone (launch.claim_ref), so each
stage has its own claim. The stage file names PREDICTION.md (and amendment 1 for M2, M3, RM2, RM3) as its governing
documents, which every runner checks (c6.stage_check, safeguard i). The manifest's protocol_commit is the one commit
that adds the stage file; its source_commit is a later, different commit that adds the stage's run list
(stages/RUNS_<S>.json, which the manifest must equal) and, for M2, M3, RM2, RM3, its inputs file (stages/INPUTS_<S>.json),
or, for Q and the N stages, PREDICTED.json and the gate's files. (The first rehearsal named PREDICTION.md as every
stage's kit protocol, so RM1's claims refused every later stage: the defect this layout fixes.)

Stages, in a fixed sequence (PREDICTION.md 6): M1 (the calibration decks), M2 (the scans and the both-lines checks),
M3 (the one-sided sets), Q (the runs without noise of the eligible instances and the untrained run), N1, N2, N3 (the
noisy runs of rounds 1 to 3), or one merged N stage when exactly one instance is eligible. The rehearsal (7): RM1, RM2,
RM3 on the nominal cell, one instance per machine; RN, the network runs of 7701 (machine a) and 7706 (machine b).

Machines. An M1 run keeps its instance's machine (PREDICTION.md 1 and 6: 7801 to 7803 on a, 7804 and 7805 on b; in
the rehearsal, none-a on a and none-b on b). M2 and M3 (RM2, RM3) follow the two-shard alternation (PREDICTION.md
amendment 1, a0d4ad3): their runs whose inputs are complete, listed by instance in seed order (none-a before none-b),
then by run kind (M2: pair a, pair b, line 1, line 2, both-lines; M3: one-sided a, then b), alternate a, b, a, ...
from a. A network run follows the same alternation (PREDICTION.md 4): the runs without noise in seed order, then the
untrained run; in an N stage, in seed order. Every manifest is checked here as the kit checks it: both shards nonempty,
the round-robin order, and the budget. A measure stage with a single run cannot occur (M2 has 5 runs per instance, M3
has 2); MeasureStageOneShard is kept for it, as an impossible case.
"""
from fractions import Fraction as F
import hashlib
import json
import math
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import c6                                               # noqa: E402
import c4                                               # noqa: E402
import plan                                             # noqa: E402  (campaign 5, frozen: dcost, the cost formula of a calendar)
from c4 import dnf                                      # noqa: E402

ROOT = HERE.parent.parent.parent
STAGES_ROOT = f"{c6.BASE}/stages"                       # stages/<attempt>/: each stage's stage file, run list, inputs, manifest, attempt marker


def attempt_dir(attempt):
    import re
    assert isinstance(attempt, str) and re.fullmatch(c6.ATTEMPT_RE, attempt), f"refused: {attempt!r} is not a valid attempt id"
    return f"{STAGES_ROOT}/{attempt}"
CLOSURE = "research/sky130-supervisor-closure"
CAMPAIGN6 = f"{c6.BASE}/campaign6"
WORKFLOWS = ["Learned DNF circuit campaign 6"]
SCAN_OUTPUTS = ["evidence/input.spice", "evidence/session.log", "evidence/trace.raw", "evidence/events.json", "record.json", "noise.sha256"]
DECK_OUTPUTS = ["evidence/input.spice", "evidence/session.log", "evidence/trace.raw", "evidence/result.json", "record.json", "noise.sha256"]
BATCH_FILES = [f"{c6.BASE}/batch/{n}" for n in ("batch6.py", "scan6.py", "predict6.py", "predict6_guard.py", "report6.py", "report6_guard.py")]
OWN_FILES = [f"{CAMPAIGN6}/{n}" for n in ("c6.py", "meas6.py", "net6.py", "inputs6.py", "stages6.py", "predicted6.py", "analyze6.py",
                                          "test_campaign6.py")]
REHEARSAL_PREDICTIONS = f"{c6.BASE}/rehearsal/PREDICTIONS_BATCH.json"      # the batch's PREDICTIONS.json, 0bd3b60
# campaign 5's smoke run of M8's eligible path (m8_case.py, CI): its files besides the waveform, from f805c20; the waveform
# itself is fetched by CI from evidence/learned-dnf-circuit-campaign-5-smoke. Bound so that M8's inputs are pinned.
C5_SMOKE = [f"research/learned-dnf-circuit-campaign-5/smoke/{n}" for n in (
    "README.md", "nominal-quiet/record.json", "nominal-quiet/noise.sha256", "nominal-quiet/evidence/.spiceinit",
    "nominal-quiet/evidence/input.spice", "nominal-quiet/evidence/result.json", "nominal-quiet/evidence/session.log")]
REHEARSAL_PREDICTIONS_SHA256 = "e2e9e572cc80ca20f953f5ed800c306e47d3413ee7efdeceed323ea12ef3cc89"


class MeasureStageOneShard(AssertionError):
    pass


def frozen():
    """Every file a stage's runs, the predictions and the analysis read: campaign 6's own, the batch's, and campaign 5's
    frozen list but its workflow (which is not on this branch), campaign 5's smoke files that M8's eligible path reads,
    amendment 1, the rehearsal's batch predictions, and campaign 6's workflow."""
    c5 = [f for f in plan.FROZEN if not f.startswith(".github/")]
    return sorted(set(OWN_FILES + BATCH_FILES + c5 + C5_SMOKE + [c6.AMENDMENT, REHEARSAL_PREDICTIONS, ".github/workflows/learned-dnf-circuit-campaign-6.yml"]))


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
    for inst in (list(c6.NOMINAL_INSTANCES) if stage.startswith("RM") else [str(s) for s in c6.SEEDS]):
        m = c6.instance_machine(inst)
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
    if base != "M1":
        runs = two_shard(runs)                                  # PREDICTION.md amendment 1
    if runs and {r["machine"] for r in runs} != {"a", "b"}:
        raise MeasureStageOneShard(f"refused: every run of {stage} is on machine {runs[0]['machine']} (an impossible case)")
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


def rehearsal_network_runs(record, batch):
    """RN (PREDICTION.md 7): on 7701 (a) and 7706 (b), the run without noise with skew and one noisy run of round 1;
    the untrained run on 7701. record: RN's prediction record (predicted6 --rehearsal, PREDICTED_RN.json), whose needs
    must equal the batch's pushed predictions' (batch, PREDICTIONS_BATCH.json) and whose network runs must be exactly
    these (the audit of 2026-11-19, C1)."""
    by = {x["seed"]: x for x in record["instances"]}
    old = {x["seed"]: x for x in batch["instances"]}
    runs = []
    for seed, m in c6.REHEARSAL_SEEDS.items():
        x = by[seed]
        assert x.get("measured") and x.get("eligible") and x.get("gate_K0"), f"{seed} is not an eligible development instance in RN's record"
        assert x.get("needs") == old[seed].get("needs"), f"refused: {seed}'s needs in RN's record differ from the batch's pushed predictions"
        n = [x["needs"][k] for k in ("a", "b", "c1", "c2")]
        runs.append(with_cost(dict(id=f"{seed}-quiet", machine=m, seed=seed, needs=n, scenario="quiet", control="skew", noise="none", round=0),
                              network_expected(n, "quiet")))
        runs.append(with_cost(dict(id=f"{seed}-n1", machine=m, seed=seed, needs=n, scenario="n1", control=None, noise="injected", round=1),
                              network_expected(n, "n1")))
        if seed == 7701:
            runs.append(with_cost(dict(id=f"{seed}-untrained", machine=m, seed=seed, needs=n, scenario="untrained", control="untrained",
                                       noise="none", round=0), c6.UNTRAINED_S))
    assert sorted(r["id"] for r in runs) == sorted(r["id"] for r in record["network_runs"]), "refused: RN's record lists other network runs"
    return runs


# ------------------------------------------------------------------------------------------------- the manifest

def stage_path(stage, attempt):
    assert stage in c6.STAGES
    return f"{attempt_dir(attempt)}/STAGE_{stage}.md"


def runs_path(stage, attempt):
    assert stage in c6.STAGES
    return f"{attempt_dir(attempt)}/RUNS_{stage}.json"


def data_path(stage, attempt):
    """The stage's declared data file, bound by its manifest: the inputs (M2, M3, RM2, RM3), the prediction record (Q,
    N1-N3, N) or RN's record (RN); None for M1 and RM1."""
    if stage in ("M2", "M3", "RM2", "RM3"):
        return f"{attempt_dir(attempt)}/INPUTS_{stage}.json"
    if stage == "RN":
        return f"{attempt_dir(attempt)}/PREDICTED_RN.json"
    if stage in ("Q", "N1", "N2", "N3", "N"):
        return f"{attempt_dir(attempt)}/PREDICTED.json"
    return None


def runs_text(stage, runs):
    """The stage's run list, committed at its source commit (the manifest must equal it)."""
    return json.dumps(dict(stage=stage, runs=runs), indent=1, sort_keys=True) + "\n"


def stage_file_text(stage, attempt):
    """The stage file (safeguard i): its governing protocol is PREDICTION.md as pushed, with its commit and SHA-256,
    and the attempt's id."""
    attempt_dir(attempt)
    block = dict(stage=stage, attempt=attempt, governing_protocol=dict(path=c6.PROTOCOL, commit=c6.PROTOCOL_COMMIT, sha256=c6.PROTOCOL_SHA256))
    if stage in c6.AMENDED_STAGES:                              # amendment 1 governs these stages' machines
        block["governing_amendment"] = dict(path=c6.AMENDMENT, commit=c6.AMENDMENT_COMMIT, sha256=c6.AMENDMENT_SHA256)
    return "\n".join([f"# Campaign 6: the protocol of stage {stage}, attempt {attempt}", "",
                      "Written by `stages6.py stage-file` and pushed alone before the stage's source commit. It is the launch",
                      "kit's protocol file of this stage (the manifest's `protocol_path`), so each stage has its own claim.",
                      "Its governing protocol is",
                      f"`{c6.PROTOCOL}` at commit `{c6.PROTOCOL_COMMIT}`, SHA-256 `{c6.PROTOCOL_SHA256}`; every runner of",
                      "the stage refuses its run if that file has another SHA-256 in the repository (c6.stage_check).", "",
                      plan.STAGE_BEGIN, json.dumps(block, indent=1, sort_keys=True), "```", ""])


def argv(stage, r, attempt, inputs_path=None):
    sf = "{repo}/" + stage_path(stage, attempt)
    if r.get("kind") == "cal":
        return ["{python}", "{repo}/" + f"{CAMPAIGN6}/meas6.py", "cal", sf, "{out}", r["instance"], r["guard"], "{ngspice}", "{pdk}"]
    if r.get("kind") == "scan":
        return ["{python}", "{repo}/" + f"{CAMPAIGN6}/meas6.py", "scan", sf, "{out}", r["instance"], r["cell"], r["scan"],
                "{repo}/" + inputs_path, "{ngspice}", "{pdk}"]
    return ["{python}", "{repo}/" + f"{CAMPAIGN6}/net6.py", sf, "{out}", r["id"], str(r["seed"]), ",".join(map(str, plan.calendar_needs(r["needs"]))),
            r["control"] or "none", r["noise"], str(r["round"]), "{ngspice}", "{pdk}"]


def entry(stage, r, attempt, inputs_path=None):
    runner = f"{CAMPAIGN6}/meas6.py" if r.get("kind") in ("cal", "scan") else f"{CAMPAIGN6}/net6.py"
    return dict(id=r["id"], machine=r["machine"], scenario="stage", deck="research/circuit/cell.spice", runner=runner,
                argv=argv(stage, r, attempt, inputs_path), estimate_s=r["estimate_s"], timeout_s=r["timeout_s"],
                required_outputs=SCAN_OUTPUTS if r.get("kind") == "scan" else DECK_OUTPUTS,
                diagnostic_logs=["evidence/session.log"], noise_fingerprint="noise.sha256")


def protocol_commit(stage, source_commit, attempt, root=ROOT):
    """The one commit, in source_commit's history, that adds the stage file; it must precede source_commit."""
    out = subprocess.run(["git", "-C", str(root), "log", "--diff-filter=A", "--format=%H", source_commit, "--", stage_path(stage, attempt)],
                         check=True, capture_output=True, text=True).stdout.split()
    assert len(out) == 1, f"refused: {stage_path(stage, attempt)} is added by {len(out)} commits in {source_commit}'s history, not one"
    assert out[0] != source_commit, "refused: the stage file must be pushed alone before the source commit (the kit: protocol must precede implementation)"
    return out[0]


def manifest(stage, runs, source_commit, attempt, root=ROOT):
    def blob(commit, path):
        return subprocess.run(["git", "-C", str(root), "show", f"{commit}:{path}"], check=True, capture_output=True).stdout
    assert stage in c6.STAGES
    rehearsal = stage.startswith("R")
    pc = protocol_commit(stage, source_commit, attempt, root)
    protocol = blob(pc, stage_path(stage, attempt))
    assert blob(source_commit, stage_path(stage, attempt)) == protocol, "refused: the stage file differs at the source commit"
    assert blob(source_commit, runs_path(stage, attempt)) == runs_text(stage, runs).encode(), "refused: the run list at the source commit is not this stage's runs"
    # PREDICTION.md is bound by its SHA-256 through the stage file (safeguard i). Its commit's ancestry is checked by
    # tools/marker_check.py in a full clone (protocol_commit descends from the marker), not here: CI's checkout is shallow.
    with tempfile.TemporaryDirectory() as tmp:                 # safeguard i on the protocol's own bytes
        f = Path(tmp) / "STAGE.md"
        f.write_bytes(protocol)
        st = c6.stage_check(f)
        assert (st["stage"], st["attempt"]) == (stage, attempt), "refused: the stage file names another stage or attempt"
    inputs_path = data_path(stage, attempt) if stage in ("M2", "M3", "RM2", "RM3") else None
    data = data_path(stage, attempt)
    extra = [stage_path(stage, attempt), runs_path(stage, attempt)] + ([data] if data else [])     # the data file bound (finding 11)
    m = dict(kind="registered", campaign_id=("learned-dnf-circuit-6-rehearsal-" if rehearsal else "learned-dnf-circuit-6-") + stage.lower(),
             attempt=1, executor=c4.EXECUTOR, protocol_commit=pc, protocol_path=stage_path(stage, attempt),
             protocol_sha256=hashlib.sha256(protocol).hexdigest(), source_commit=source_commit,
             launcher_path=f"{CLOSURE}/launchkit/launch.py", marker_path=f"{attempt_dir(attempt)}/RUN_ATTEMPT_{stage}.json",
             spinit_path=f"{CLOSURE}/runtime/spinit", inventory_a_path=f"{c6.BASE}/INVENTORY_a.json", inventory_b_path=f"{c6.BASE}/INVENTORY_b.json",
             source_sha256={n: hashlib.sha256(blob(source_commit, n)).hexdigest() for n in frozen() + extra},
             expected_workflows=WORKFLOWS, jobs=c4.JOBS, scenario_order=["stage"], budget_s=math.ceil(stage_cap(runs)),
             runs=[entry(stage, r, attempt, inputs_path) for r in runs])
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
    """The runs of one stage from its frozen input: INPUTS_M2/M3 for M2/M3 (RM2/RM3), PREDICTED.json for Q and N, RN's
    record PREDICTED_RN.json for RN (checked against the batch's pushed predictions)."""
    if stage in ("M1", "RM1"):
        return measure_runs(stage)
    if stage in ("M2", "M3", "RM2", "RM3"):
        return measure_runs(stage, json.loads(Path(path).read_text()))
    if stage == "RN":
        batch = (ROOT / REHEARSAL_PREDICTIONS).read_bytes()
        assert hashlib.sha256(batch).hexdigest() == REHEARSAL_PREDICTIONS_SHA256, "not the batch's pushed PREDICTIONS.json (0bd3b60)"
        return rehearsal_network_runs(json.loads(Path(path).read_text()), json.loads(batch))
    named = dict(network_stages(json.loads(Path(path).read_text())["network_runs"]))
    assert stage in named, f"refused: {stage} is not a stage of this prediction record ({sorted(named)})"
    return named[stage]


def main(argv_=None):
    a = sys.argv[1:] if argv_ is None else argv_
    c6.require_debug()
    if a[0] == "stage-file":
        Path(a[2]).write_text(stage_file_text(a[1], a[3]))
        return
    if a[0] == "runs":
        stage, out, attempt = a[1], Path(a[2]), a[3]
        path = a[4] if len(a) > 4 else None
        assert (path is None) == (data_path(stage, attempt) is None), f"refused: {stage} takes {data_path(stage, attempt)}"
        assert path is None or Path(path).resolve() == (ROOT / data_path(stage, attempt)).resolve(), f"refused: {stage}'s data is {data_path(stage, attempt)}"
        out.write_text(runs_text(stage, stage_runs(stage, path)))
        return
    if a[0] != "manifest":
        raise SystemExit(__doc__)
    stage, out, source, attempt = a[1], Path(a[2]), a[3], a[4]
    path = a[5] if len(a) > 5 else None
    assert (path is None) == (data_path(stage, attempt) is None), f"refused: {stage} takes {data_path(stage, attempt)}"
    runs = stage_runs(stage, path)
    m = manifest(stage, runs, source, attempt)
    out.write_text(json.dumps(m, indent=1) + "\n")
    print(json.dumps(dict(stage=stage, runs=len(runs), budget_s=m["budget_s"], expected_s=round(expected_compute([runs]), 2))))


if __name__ == "__main__":
    main()
