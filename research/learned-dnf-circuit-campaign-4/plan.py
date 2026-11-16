"""Campaign 4: the runs of each stage, their costs, the sizing rule, BEFORE_M.md and the manifests of the kit.

  plan.py size [COSTS.json]                                  the expected compute and stage caps for I = 1..15
  plan.py before-m DECISIONS.json BEFORE_M.md                 BEFORE_M.md from the noise study's outcome
  plan.py stage-file STAGE                                    STAGE_<STAGE>.md, the stage's protocol (amendment 5, section 1)
  plan.py runs STAGE                                          STAGE_<STAGE>_RUNS.json, the stage's runs (M, M1, M2, E1, ..., Q,
                                                              N1, N2, N3; E from MEASURED.json, Q and N from PREDICTED.json)
  plan.py manifest STAGE STAGE_COMMIT SOURCE_COMMIT FROZEN_COMMIT OUT.json   the stage's manifest of the kit, from its
                                                              run list, after safeguard (ii) on SOURCE_COMMIT
  plan.py measured MEASURES_DIR... MEASURED.json              the measured instances after stage M (for the E manifests)

Stages, in the fixed order of PREDICTION.md: M (M1, M2 if needed: the calibration decks), E1, E2, ... (the
extraction per cell, state and output, device model only), Q (the runs without noise with the skew control, and the
untrained control run), N1, N2, N3 (the noisy runs of round 1, 2, 3). M and E have PREDICTION.md as their protocol;
Q and N1 to N3 have PREDICTED.json. Nothing here is chosen at launch time: the runs follow from BEFORE_M.md,
from the measured instances (MEASURED.json, written by `predicted.py` from stage M), and from PREDICTED.json.

The cost model (COST_MODEL_DECISION.md, 2ffe04d): wall times measured on the nominal cell, three-cell decks, four
at a time, scaled to a run's calendar by the ratio of `dnf.cost` for that calendar to `dnf.cost` for the measured
calendar. Expected compute: per stage and machine, the sum of the expected costs over four runs at a time plus
three quarters of the largest; summed over every stage and both machines.
"""
import hashlib
import json
import math
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import c4                                               # noqa: E402
from c4 import dnf                                      # noqa: E402

ROOT = HERE.parent.parent
BASE = c4.BASE
CLOSURE = "research/sky130-supervisor-closure"
MISSING_NEED = 7                                        # a cell or line with no firing stage up to 7: the calendar of need 7
EXTRACTION_OUTPUTS = [(state, port) for state in ("hold", "window", "fire", "pulse") for port in ((None,) if state == "fire" else (1, 2))]
# The costs known when PREDICTION.md was pushed (BEFORE_M.md replaces the noisy run's and the extraction's).
COSTS = dict(quiet_need4_s=814.0, noisy_need4_s=dict(device=1033.0, injected=1316.0), calibration_deck_s=925.0, untrained_s=369.2,
             extraction_s=dict(hold=100.0, window=260.0, fire=290.0, pulse=95.0), isolation_per_instance_s=40.0)
OUTPUTS = dict(cal=["evidence/input.spice", "evidence/session.log", "evidence/trace.raw", "evidence/result.json", "record.json", "noise.sha256"],
               network=["evidence/input.spice", "evidence/session.log", "evidence/trace.raw", "evidence/result.json", "record.json", "noise.sha256"],
               extract=["part.json", "record.json", "noise.sha256"])
FROZEN = [f"{BASE}/{n}" for n in ("PREDICTION.md", "AMENDMENT_1.md", "AMENDMENT_2.md", "AMENDMENT_3.md", "AMENDMENT_4.md", "AMENDMENT_5.md", "c4.py", "noisemodel.py", "session4.py", "plans4.py", "reads4.py", "run4.py", "predicted.py",
                                   "gate4.py", "cases.py", "mirror_mutations.py", "plan.py", "analyze.py", "rehearsal.py", "test_campaign.py",
                                   "check.sh", "noise/devnoise.py", "noise/model.py", "noise/pilot.py", "noise/noisegen.py", "noise/compare.py",
                                   "noise/README.md")] + [
    "research/learned-dnf-circuit/dnf.py", "research/network-circuit/net.py", "research/network-circuit/router.py",
    "research/network-circuit/measure.py", "research/circuit/cell.spice", "research/circuit/blocks.spice", "research/circuit/noise.json",
    "research/circuit/spiceinit.txt", "research/circuit/repetition/fakepid.c", f"{CLOSURE}/launchkit/launch.py", f"{CLOSURE}/runtime/spinit",
    f"{CLOSURE}/sim.py", f"{CLOSURE}/junction/netlist.py", f"{CLOSURE}/junction/areas.csv"]
WORKFLOWS = ["Learned DNF circuit campaign 4"]


def ms(slots):
    return (slots[-1]["date"] + dnf.SLOT + dnf.SETTLE) * 0.02


def dcost(slots):
    return dnf.cost(ms(slots), dnf.run_pulses(slots))


REF = dcost(dnf.calendar(4, 4, 4, 4))


def calendar_needs(needs):
    return tuple(MISSING_NEED if x is None else x for x in needs)


def costs(before=None):
    c = json.loads(json.dumps(COSTS))
    if before:
        c.update(before["costs"])
    return c


def expected(run, cost, model):
    k = run["kind"]
    if k == "cal":
        return cost["calibration_deck_s"]
    if k == "extract":
        if run["state"] == "all":       # the rehearsal's single-run extraction: every output of every cell, and the isolation check
            return sum(cost["extraction_s"][st] for _, st, _ in [(c, st, p) for c in c4.CELLS for st, p in EXTRACTION_OUTPUTS]) + cost["isolation_per_instance_s"]
        return cost["extraction_s"][run["state"]] + (cost["isolation_per_instance_s"] / 3 if run["isolation"] else 0.0)
    slots = dnf.calendar(*calendar_needs(run["needs"]), run["control"])
    if run["control"] == "untrained":
        return cost["untrained_s"]
    base = cost["noisy_need4_s"][model] if run["noise"] != "none" else cost["quiet_need4_s"]
    return base * dcost(slots) / REF


def ceil10(x):
    return 10 * math.ceil(x / 10 - 1e-9)


def run_kind(run):
    """The kind of a run for its time limit: cal, extract, quiet, untrained, noisy_device, noisy_injected."""
    if run["kind"] == "extract":
        return "extract_reuse" if run.get("reuse_trip") else "extract_noreuse"
    if run["kind"] != "network":
        return run["kind"]
    if run["control"] == "untrained":
        return "untrained"
    return "quiet" if run["noise"] == "none" else "noisy_" + run["noise"]


def with_limits(run, cost, model, rehearsal=None):
    """expected_s: the cost model's expected cost (it sizes I and the expected compute). With the rehearsal's limits
    basis (REHEARSAL.json: per run kind, the largest ratio of a rehearsal run's measured wall time to its expected
    cost), the estimate is that ratio times the expected cost, and the time limit 1.3 times it, never above 1.3
    times the cost model (PREDICTION.md, Time limits). Without it (sizing before the rehearsal), 1.3 times the cost
    model."""
    e = expected(run, cost, model)
    ratio = (rehearsal or {}).get(run_kind(run))
    est = e if ratio is None else ratio * e
    limit = min(ceil10(c4.MARGIN * est), c4.MARGIN * e)        # rounded up to 10 s, then capped (amendment 4, a)
    return dict(run, estimate_s=min(ceil10(est), limit), timeout_s=limit, expected_s=e)


def machine_cap(runs):
    caps = [r["timeout_s"] + c4.CLEANUP_S for r in runs]
    return sum(caps) / c4.JOBS + max(caps) if caps else 0.0


def stage_cap(runs):
    return sum(machine_cap([r for r in runs if r["machine"] == m]) for m in ("a", "b"))


def machine_expected(runs):
    e = [r["expected_s"] for r in runs]
    return sum(e) / c4.JOBS + 0.75 * max(e) if e else 0.0


# --------------------------------------------------------------------------------------------------- the runs

def cal_runs(seed, machine):
    return [dict(id=f"{machine}-{seed}-cal-{g}", machine=machine, seed=seed, kind="cal", guard=g) for g in ("on", "off")]


def extract_runs(seed, machine, reuse_trip):
    out, seen = [], set()
    for cell in c4.CELLS:
        for state, port in EXTRACTION_OUTPUTS:
            out.append(dict(id=f"{machine}-{seed}-x-{cell}-{state}-{port or 'cell'}", machine=machine, seed=seed, kind="extract", cell=cell,
                            state=state, port=port, isolation=cell not in seen, reuse_trip=reuse_trip))
            seen.add(cell)
    return out


def network_run(seed, machine, needs, scenario, model, extraction=None):
    noise = "none" if scenario in ("quiet", "untrained") else model
    control = dict(quiet="skew", untrained="untrained").get(scenario)
    rnd = int(scenario[1]) if scenario.startswith("n") else 0
    return dict(id=f"{machine}-{seed}-{scenario}", machine=machine, seed=seed, kind="network", needs=list(needs), control=control,
                noise=noise, round=rnd, scenario=scenario, extraction=extraction if noise == "device" else None)


def split(runs_of, items_a, items_b, limit=c4.MAX_BUDGET_S):
    """The fewest consecutive parts of each machine's list (in seed order), the j-th parts of the two machines
    together making stage j, such that every stage is within the kit's cap. Returns the list of stages."""
    for parts in range(1, max(len(items_a), len(items_b), 1) + 1):
        chunk = lambda xs, j: xs[len(xs) * j // parts:len(xs) * (j + 1) // parts]
        stages = [[r for x in chunk(items_a, j) + chunk(items_b, j) for r in runs_of(x)] for j in range(parts)]
        if all(stage_cap(s) <= limit for s in stages):
            return stages
    raise ValueError("a single instance does not fit a stage")


def stages(I, model, reuse_trip, cost, measured=None, needs=None, control=None, rehearsal=None, extractions=None):
    """Every stage of the campaign for I instances. measured: the measured seeds (default: the first
    round(0.92 I) of each machine, for sizing); needs: per measured seed (default 4 everywhere); control: the seed of
    the control instance (default the first measured seed)."""
    s = c4.seeds(I)
    lim = lambda r: with_limits(r, cost, model, rehearsal)
    if measured is None:
        m = round(c4.MEASURED_FRACTION * I)
        ma = (m + 1) // 2
        measured = s["a"][:ma] + s["b"][:m - ma]
    needs = needs or {x: (4, 4, 4, 4) for x in measured}
    control = measured[0] if control is None and measured else control
    out = []
    M = split(lambda seed: [lim(r) for r in cal_runs(seed, c4.machine_of(seed, I))], s["a"], s["b"])
    out += [(f"M{j + 1}" if len(M) > 1 else "M", x) for j, x in enumerate(M)]
    meas = dict(a=[x for x in s["a"] if x in measured], b=[x for x in s["b"] if x in measured])
    if model == "device":
        E = split(lambda seed: [lim(r) for r in extract_runs(seed, c4.machine_of(seed, I), reuse_trip)], meas["a"], meas["b"])
        out += [(f"E{j + 1}", x) for j, x in enumerate(E)]
    Q = []
    for mach in ("a", "b"):
        for seed in meas[mach]:
            Q.append(lim(network_run(seed, mach, needs[seed], "quiet", model)))
            if seed == control:
                Q.append(lim(network_run(seed, mach, needs[seed], "untrained", model)))
    out.append(("Q", Q))
    for k in (1, 2, 3):
        N = [lim(network_run(seed, mach, needs[seed], f"n{k}", model, (extractions or {}).get(seed))) for mach in ("a", "b") for seed in meas[mach]]
        out.append((f"N{k}", N))
    return out


def expected_compute(st):
    return sum(machine_expected([r for r in runs if r["machine"] == m]) for _, runs in st for m in ("a", "b"))


def size(cost, model, reuse_trip=True, rehearsal=None, I_max=15):
    rows = []
    for I in range(1, I_max + 1):
        st = stages(I, model, reuse_trip, cost, rehearsal=rehearsal)
        rows.append(dict(I=I, expected_h=expected_compute(st) / 3600, caps={n: round(stage_cap(r)) for n, r in st}))
    fit = [r for r in rows if r["expected_h"] <= c4.BUDGET_H and all(v <= c4.MAX_BUDGET_S for v in r["caps"].values())]
    return (fit[-1]["I"] if fit else 0), rows


BEFORE_M_BEGIN, BEFORE_M_END = "```json before-m", "```"


def read_before_m(path):
    """The record of BEFORE_M.md: its JSON block, and the SHA-256 of the file."""
    text = Path(path).read_text()
    i = text.index(BEFORE_M_BEGIN) + len(BEFORE_M_BEGIN)
    block = json.loads(text[i:text.index(BEFORE_M_END, i)])
    return dict(block, sha256=hashlib.sha256(text.encode()).hexdigest())


def before_m_text(b):
    """BEFORE_M.md: what PREDICTION.md (The record before stage M) lists, in words, then the same as a JSON block that
    the frozen code reads."""
    lines = ["# Campaign 4: the record before stage M", "",
             "Written by `plan.py before-m` (the frozen code), pushed alone before the first launch of stage M",
             "(PREDICTION.md, The record before stage M). Nothing in it is chosen by hand: it follows from the decisions file",
             "below, which cites its sources.", "",
             f"1. **The noise model applied**: {b['noise_model']} ({b['noise_model_source']}).",
             f"2. **The noise constants**: b = {b['constants']['between_mV']} mV between runs, w = {b['constants']['within_mV']} mV within a run,"
             f" d = {b['constants']['per_dose_mV']} mV per dose ({b['constants_source']}).",
             f"3. **The costs**: {json.dumps(b['costs'], sort_keys=True)} ({b['costs_source']}).",
             f"4. **I = {b['I']}** (machine a: seeds {b['seeds']['a']}; machine b: seeds {b['seeds']['b']}), expected compute {b['expected_compute_h']:.2f} h, stage caps "
             f"{json.dumps(b['stage_caps_s'], sort_keys=True)} s; expected {json.dumps(b['expected'], sort_keys=True)}.",
             f"5. **The reuse of the trip value**: {b['reuse_trip']} ({b['reuse_trip_source']}).", "",
             BEFORE_M_BEGIN, json.dumps(b, indent=1, sort_keys=True), BEFORE_M_END, ""]
    return "\n".join(lines)


def before_m(decisions):
    """BEFORE_M.md from the decisions file of the noise study's outcome: the model applied and its sources, the
    constants, the costs, the reuse of the trip value; then I, the expected compute, the stage caps and counts."""
    d = decisions
    model = d["noise_model"]
    assert model in ("device", "injected"), "a corrected model needs its own file and code"
    const = {k: max(c4.DECISION5[k], d.get("validated_constants", {}).get(k, 0.0)) for k in c4.DECISION5} if model == "device" else dict(c4.DECISION5)
    cost = costs(dict(costs=d.get("costs", {})))
    reuse = bool(d.get("reuse_trip", False)) if model == "device" else False
    I, rows = size(cost, model, reuse)
    row = next(r for r in rows if r["I"] == I)
    m = round(c4.MEASURED_FRACTION * I)
    return dict(what="the record before stage M of campaign 4 (PREDICTION.md, The record before stage M), written by plan.py",
                noise_model=model, noise_model_source=d["noise_model_source"], constants=const, constants_source=d.get("constants_source"),
                costs=cost, costs_source=d.get("costs_source"), reuse_trip=reuse, reuse_trip_source=d.get("reuse_trip_source"),
                I=I, seeds=c4.seeds(I), expected_compute_h=row["expected_h"], stage_caps_s=row["caps"],
                expected=dict(measured=m, eligible=round(0.6 * I, 1), noisy_runs=c4.R * m))


# ---------------------------------------------------------------------------------------------- the manifests

def argv(r, I, stage=None):
    out = ["{python}", "{repo}/" + f"{BASE}/run4.py", "--out", "{out}", "--ngspice", "{ngspice}", "--pdk", "{pdk}", "--id", r["id"],
           "--kind", r["kind"], "--seed", "none" if r["seed"] is None else str(r["seed"]), "--instances", str(I)]
    if stage is not None:
        out += ["--stage", "{repo}/" + stage_path(stage)]
    if r["kind"] == "cal":
        out += ["--guard", r["guard"]]
    elif r["kind"] == "extract" and r["state"] == "all":
        out += ["--state", "all", "--reuse-trip", str(int(r["reuse_trip"]))]
    elif r["kind"] == "extract":
        out += ["--cell", r["cell"], "--state", r["state"], "--port", str(r["port"] or "none"), "--isolation", str(int(r["isolation"])),
                "--reuse-trip", str(int(r["reuse_trip"]))]
    else:
        out += ["--needs", ",".join(map(str, calendar_needs(r["needs"]))), "--control", r["control"] or "none", "--noise", r["noise"]]
        if r["noise"] != "none":
            out += ["--round", str(r["round"])]
        if r["noise"] == "device":
            out += ["--extraction", "{repo}/" + r["extraction"]["path"], "--extraction-sha256", r["extraction"]["sha256"]]
    return out


def extra_frozen(runs):
    """The files a stage's runs follow from besides the frozen code: MEASURED.json for the extractions, the merged
    extractions for the noisy runs."""
    out = {r["extraction"]["path"] for r in runs if r.get("extraction")}
    if any(r["kind"] == "extract" and r["state"] != "all" for r in runs):
        out.add(f"{BASE}/MEASURED.json")
    return sorted(out)


def entry(r, I, scenario, stage=None):
    return dict(id=r["id"], machine=r["machine"], scenario=scenario, deck="research/circuit/cell.spice", runner=f"{BASE}/run4.py",
                argv=argv(r, I, stage), estimate_s=r["estimate_s"], timeout_s=r["timeout_s"],
                required_outputs=["extraction.json", "record.json", "noise.sha256"] if r.get("state") == "all" else OUTPUTS[r["kind"]],
                diagnostic_logs=[] if r["kind"] == "extract" else ["evidence/session.log"], noise_fingerprint="noise.sha256")


def stage_runs(name, here=HERE):
    """The runs of one stage, all from frozen files: M from BEFORE_M.md; E from MEASURED.json; Q, N1, N2, N3 from
    PREDICTED.json. Returns the runs (with their limits), the protocol file and I."""
    b = read_before_m(here / "BEFORE_M.md")
    cost, model, I = costs(b), b["noise_model"], b["I"]
    reh = json.loads((here / "REHEARSAL.json").read_text())["limits_basis"] if (here / "REHEARSAL.json").exists() else None
    if name[0] == "M":
        st = dict(x for x in stages(I, model, b["reuse_trip"], cost, rehearsal=reh) if x[0][0] == "M")
        return st[name], "PREDICTION.md", I
    if name[0] == "E":
        meas = json.loads((here / "MEASURED.json").read_text())
        assert meas["before_m_sha256"] == b["sha256"]
        ms = [x["seed"] for x in meas["instances"] if x["measured"]]
        s = c4.seeds(I)
        lim = lambda r: with_limits(r, cost, model, reh)
        E = split(lambda seed: [lim(r) for r in extract_runs(seed, c4.machine_of(seed, I), b["reuse_trip"])],
                  [x for x in s["a"] if x in ms], [x for x in s["b"] if x in ms])
        return E[int(name[1:]) - 1], "PREDICTION.md", I
    p = json.loads((here / "PREDICTED.json").read_text())
    want = dict(Q=lambda r: r["noise"] == "none", N1=lambda r: r["round"] == 1, N2=lambda r: r["round"] == 2, N3=lambda r: r["round"] == 3)[name]
    return [r for r in p["network_runs"] if want(r)], "PREDICTED.json", I


# ------------------------------------------------------------------------- the stages' protocols (amendment 5)

GOVERNING = dict(M="PREDICTION.md", E="PREDICTION.md", Q="PREDICTED.json", N="PREDICTED.json")
STAGE_BEGIN = "```json stage"
# Safeguard (ii): besides the frozen files, unchanged, a stage's source commit may differ from the frozen commit only in
# these files of the campaign's folder (fnmatch patterns, relative to it).
ALLOWED_AFTER_FREEZE = ("STAGE_*.md", "STAGE_*_RUNS.json", "BEFORE_M.md", "MEASURED.json", "PREDICTED.json", "extractions/*",
                        "Gate4.lean", "REHEARSAL.json", "INVENTORY_a.json", "INVENTORY_b.json", "CAMPAIGN_*.json", "RUN_ATTEMPT_*.json",
                        "evidence/*")


def stage_path(name):
    return f"{BASE}/STAGE_{name}.md"


def governing_of(name):
    """The governing protocol of a stage: PREDICTION.md for M, E (and the rehearsal's measure stages), PREDICTED.json for
    Q, N1 to N3 (and the rehearsal's network stages)."""
    key = dict(X="M", GUARD="M", MEMD="N", MEMI="N").get(name, name[0])
    return f"{BASE}/{GOVERNING[key]}"


def stage_file_text(name, governing, commit, digest):
    block = dict(stage=name, governing_protocol=dict(path=governing, commit=commit, sha256=digest))
    return "\n".join([f"# Campaign 4: the protocol of stage {name}", "",
                      "Written by `plan.py stage-file` (the frozen code) and pushed alone before the stage's launch (amendment 5,",
                      f"section 1). Its governing protocol is `{governing}` at commit `{commit}`, SHA-256 `{digest}`;",
                      "`run4.py` refuses every run of the stage if that file has another SHA-256 in the repository.", "",
                      STAGE_BEGIN, json.dumps(block, indent=1, sort_keys=True), "```", ""])


def read_stage(path):
    text = Path(path).read_text()
    i = text.index(STAGE_BEGIN) + len(STAGE_BEGIN)
    return json.loads(text[i:text.index("```", i)])


def check_after_freeze(frozen_commit, source_commit, root=ROOT):
    """Safeguard (ii) (amendment 5, section 1, item 3): no frozen file differs, and every other changed file is in the
    closed list. Returns the changed files; raises otherwise."""
    import fnmatch
    changed = subprocess.run(["git", "-C", str(root), "diff", "--name-only", frozen_commit, source_commit], check=True,
                             capture_output=True, text=True).stdout.split()
    bad = [f for f in changed if f in FROZEN or not f.startswith(BASE + "/")
           or not any(fnmatch.fnmatch(f[len(BASE) + 1:], p) for p in ALLOWED_AFTER_FREEZE)]
    if bad:
        raise SystemExit(f"refused (safeguard ii): the source commit differs from the frozen commit in {bad}")
    return changed


def manifest(name, runs, I, protocol_commit, protocol, source_commit, root=ROOT, frozen_commit=None):
    def blob(commit, path):
        return subprocess.run(["git", "-C", str(root), "show", f"{commit}:{path}"], check=True, capture_output=True).stdout
    if frozen_commit is not None:
        check_after_freeze(frozen_commit, source_commit, root)
    stage = name if protocol.startswith("STAGE_") else None
    entries = [entry(r, I, "stage", stage) for r in runs]
    return dict(kind="registered", campaign_id=f"learned-dnf-circuit-4-{name.lower()}", attempt=1, executor=c4.EXECUTOR,
                protocol_commit=protocol_commit, protocol_path=f"{BASE}/{protocol}",
                protocol_sha256=hashlib.sha256(blob(protocol_commit, f"{BASE}/{protocol}")).hexdigest(),
                source_commit=source_commit, launcher_path=f"{CLOSURE}/launchkit/launch.py", marker_path=f"{BASE}/RUN_ATTEMPT_{name}.json",
                spinit_path=f"{CLOSURE}/runtime/spinit", inventory_a_path=f"{BASE}/INVENTORY_a.json", inventory_b_path=f"{BASE}/INVENTORY_b.json",
                source_sha256={n: hashlib.sha256(blob(source_commit, n)).hexdigest() for n in FROZEN + [f"{BASE}/BEFORE_M.md"] + extra_frozen(runs)},
                expected_workflows=WORKFLOWS, jobs=c4.JOBS, scenario_order=["stage"], budget_s=math.ceil(stage_cap(runs)), runs=entries)


def main():
    if sys.argv[1] == "size":
        cost = costs(json.loads(Path(sys.argv[2]).read_text()) if len(sys.argv) > 2 else None)
        for model in ("device", "injected"):
            I, rows = size(cost, model)
            print(model, "I =", I)
            for r in rows:
                print(" ", r["I"], round(r["expected_h"], 2), r["caps"])
    elif sys.argv[1] == "before-m":
        print(c4.require_pinned())
        Path(sys.argv[3]).write_text(before_m_text(before_m(json.loads(Path(sys.argv[2]).read_text()))))
    elif sys.argv[1] == "measured":
        print(c4.require_pinned())
        import predicted
        b = read_before_m(HERE / "BEFORE_M.md")
        res = dict(what="the measured instances after stage M, written by plan.py measured", I=b["I"], before_m_sha256=b["sha256"],
                   instances=[{k: v for k, v in x.items() if k != "calibration"} for x in predicted.measures(b, sys.argv[2:-1])])
        Path(sys.argv[-1]).write_text(json.dumps(res, indent=1) + "\n")
    elif sys.argv[1] == "stage-file":
        print(c4.require_pinned())
        name = sys.argv[2]
        gov = governing_of(name)
        commit = subprocess.run(["git", "-C", str(ROOT), "log", "-1", "--format=%H", "--", gov], check=True, capture_output=True, text=True).stdout.strip()
        data = subprocess.run(["git", "-C", str(ROOT), "show", f"{commit}:{gov}"], check=True, capture_output=True).stdout
        assert data == (ROOT / gov).read_bytes(), "the governing protocol differs from its last commit"
        (ROOT / stage_path(name)).write_text(stage_file_text(name, gov, commit, hashlib.sha256(data).hexdigest()))
    elif sys.argv[1] == "runs":
        print(c4.require_pinned())
        name = sys.argv[2]
        runs, protocol, I = stage_runs(name)
        assert governing_of(name).endswith(protocol)
        (ROOT / f"{BASE}/STAGE_{name}_RUNS.json").write_text(json.dumps(dict(stage=name, I=I, runs=runs), indent=1) + "\n")
    elif sys.argv[1] == "manifest":
        print(c4.require_pinned())
        name, stage_commit, source_commit, frozen_commit, out = sys.argv[2:7]
        lst = json.loads((ROOT / f"{BASE}/STAGE_{name}_RUNS.json").read_text())
        m = manifest(name, lst["runs"], lst["I"], stage_commit, f"STAGE_{name}.md", source_commit, frozen_commit=frozen_commit)
        m["source_sha256"][f"{BASE}/STAGE_{name}_RUNS.json"] = hashlib.sha256((ROOT / f"{BASE}/STAGE_{name}_RUNS.json").read_bytes()).hexdigest()
        Path(out).write_text(json.dumps(m, indent=1) + "\n")


if __name__ == "__main__":
    main()
