"""Campaign 5: the runs of each stage, their costs, the sizing rule, BEFORE_M.md and the manifests of the kit.

Campaign 4's plan.py (093995b), adapted to campaign 5's PREDICTION.md: the time limit of a run is twice its expected
cost rounded up to 10 s (10.4), or the rehearsal's min(3 x, 3 580 s) (11.2), never a ratio from a rehearsal; Q and each
N stage are split by seed by the rule of M when they do not fit the kit (10.5); every stage name is mapped to its
governing protocol from a closed list (10.6); the injected model only (section 6).

  plan.py size [COSTS.json]                                  I, the expected compute and the stage caps for I = 1..20
  plan.py before-m DECISIONS.json BEFORE_M.md                 BEFORE_M.md (10.8); DECISIONS.json names the rehearsal's record
  plan.py stage-file STAGE                                    STAGE_<STAGE>.md, the stage's protocol (PREDICTION.md, 10.6)
  plan.py runs STAGE                                          STAGE_<STAGE>_RUNS.json, the stage's runs (M1, M2 from
                                                              BEFORE_M.md; Q, N1, N2, N3 and their parts from PREDICTED.json)
  plan.py manifest STAGE STAGE_COMMIT SOURCE_COMMIT FROZEN_COMMIT OUT.json   the stage's manifest of the kit, from its
                                                              run list, after safeguard (ii) on SOURCE_COMMIT

Stages, in the fixed order of PREDICTION.md (10.5): M1, M2 (the calibration decks), Q (the runs without noise with the
skew control, and the untrained control run), N1, N2, N3 (the noisy runs of round 1, 2, 3), each cut into parts by
seed if it does not fit the kit. M1 and M2 have PREDICTION.md as their governing protocol; Q and N1 to N3 have
PREDICTED.json. Nothing here is chosen at launch time: the runs follow from BEFORE_M.md and from PREDICTED.json.
The functions of campaign 4's E stages (extract_runs, the device model) are kept unchanged and unused: the runner
refuses them (PREDICTION.md, section 6).

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
# The frozen files (PREDICTION.md, 10.6): every file of the campaign's folder that the runs, the predictions, the gate,
# the analysis, the rehearsal and CI read, and the files outside it that they import or launch. A stage's source commit
# may differ from the frozen commit in none of them (safeguard ii), and every manifest binds each by its SHA-256.
FROZEN = [f"{BASE}/{n}" for n in (
    "PREDICTION.md", "c4.py", "noisemodel.py", "session4.py", "plans4.py", "reads4.py", "run4.py", "predicted.py", "gate4.py", "cases.py",
    "mirror_mutations.py", "plan.py", "analyze.py", "rehearsal.py", "collect.py", "test_campaign.py", "check.sh", "audit_cases.sh",
    "structural_compare.py", "m8_case.py", "noise/devnoise.py", "noise/model.py", "noise/pilot.py", "noise/noisegen.py", "noise/compare.py",
    "noise/README.md", "audit-cases/NativeDecl.lean", "audit-cases/NegNative.lean", "audit-cases/NegOwnAxiom.lean", "audit-cases/NegSorry.lean",
    "audit-cases/OwnAxiomDecl.lean", "expected/CASES.json", "expected/Gate5Cases.lean", "expected/Gate5CasesTargets.lean",
    "expected/MUTATIONS.json", "expected/MirrorMutations.lean", "expected/mutations.log", "expected/python.log")] + [
    "research/learned-dnf-circuit/dnf.py", "research/learned-dnf-circuit/CALIBRATION.json", "research/network-circuit/net.py",
    "research/network-circuit/router.py", "research/network-circuit/measure.py", "research/circuit/cell.spice", "research/circuit/blocks.spice",
    "research/circuit/noise.json", "research/circuit/spiceinit.txt", "research/circuit/repetition/fakepid.c", f"{CLOSURE}/launchkit/launch.py",
    f"{CLOSURE}/runtime/spinit", f"{CLOSURE}/sim.py", f"{CLOSURE}/junction/netlist.py", f"{CLOSURE}/junction/areas.csv",
    ".github/workflows/learned-dnf-circuit-campaign-5.yml"] + [f"research/learned-coincidence/{m}.lean" for m in (
    "Target", "Recognition", "TwoLayerTarget", "MonotoneTarget", "MonotoneSupport", "MonotoneRecognition", "MonotoneCharacterization",
    "MonotoneOneSidedTarget", "MonotoneOneSidedRecognition", "MonotonePremiseTargets", "MonotonePremiseCompletenessTargets",
    "MonotonePremiseSoundness", "MonotonePremiseCompleteness")]
WORKFLOWS = ["Learned DNF circuit campaign 5"]


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


ceil10 = c4.ceil10


def run_kind(run):
    """The kind of a run for its time limit: cal, extract, quiet, untrained, noisy_device, noisy_injected."""
    if run["kind"] == "extract":
        return "extract_reuse" if run.get("reuse_trip") else "extract_noreuse"
    if run["kind"] != "network":
        return run["kind"]
    if run["control"] == "untrained":
        return "untrained"
    return "quiet" if run["noise"] == "none" else "noisy_" + run["noise"]


def with_limits(run, cost, model, rehearsal=False):
    """expected_s: the cost model's expected cost (it sizes I and the expected compute). timeout_s: the campaign's limit,
    10 ceil(2 x expected / 10) (PREDICTION.md, 10.4), or, for a run of the rehearsal, min(10 ceil(3 x expected / 10),
    3 580 s) (11.2); campaign_limit_s: the campaign's limit in both cases, against which the 0.75 rule judges a
    rehearsal run (11.4). estimate_s: the expected cost rounded up to 10 s, never above the limit. No ratio from any
    run enters a limit."""
    e = expected(run, cost, model)
    campaign = c4.limit(e)
    limit = c4.rehearsal_limit(e) if rehearsal else campaign
    return dict(run, estimate_s=min(ceil10(e), limit), timeout_s=limit, campaign_limit_s=campaign, expected_s=e)


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
    assert model == "injected", "the injected model only (PREDICTION.md, section 6)"
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


def stages(I, model, reuse_trip, cost, measured=None, needs=None, control=None, rehearsal=False, extractions=None):
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
    if model != "injected":
        raise ValueError("the injected model only (PREDICTION.md, section 6)")
    meas = dict(a=[x for x in s["a"] if x in measured], b=[x for x in s["b"] if x in measured])
    def q_of(seed):
        mach = c4.machine_of(seed, I)
        r = [lim(network_run(seed, mach, needs[seed], "quiet", model))]
        return r + ([lim(network_run(seed, mach, needs[seed], "untrained", model))] if seed == control else [])
    out += parts("Q", split(q_of, meas["a"], meas["b"]))
    for k in (1, 2, 3):
        n_of = lambda seed, k=k: [lim(network_run(seed, c4.machine_of(seed, I), needs[seed], f"n{k}", model))]
        out += parts(f"N{k}", split(n_of, meas["a"], meas["b"]))
    return out


def parts(name, pieces):
    """The stage's name, or its parts' names (name.1, name.2, ...) when the rule of split cut it (PREDICTION.md, 10.5)."""
    return [(name if len(pieces) == 1 else f"{name}.{j + 1}", x) for j, x in enumerate(pieces)]


def expected_compute(st):
    return sum(machine_expected([r for r in runs if r["machine"] == m]) for _, runs in st for m in ("a", "b"))


def size(cost, model="injected", reuse_trip=False, rehearsal=False, I_max=20):
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
    """BEFORE_M.md: what PREDICTION.md (10.8) lists, in words, then the same as a JSON block that the frozen code reads."""
    lim = b["limits"]
    lines = ["# Campaign 5: the record before stage M", "",
             "Written by `plan.py before-m` (the frozen code), pushed alone after the rehearsal's record and before the first launch",
             "of M1 (PREDICTION.md, 10.8). Nothing in it is chosen by hand.", "",
             f"1. **The noise model**: {b['noise_model']} ({b['noise_model_source']}).",
             f"2. **The noise constants**: b = {b['constants']['between_mV']} mV between runs, w = {b['constants']['within_mV']} mV within a run,"
             f" d = {b['constants']['per_dose_mV']} mV per dose ({b['constants_source']}).",
             f"3. **The costs**: {json.dumps(b['costs'], sort_keys=True)} ({b['costs_source']}).",
             f"4. **I = {b['I']}** (machine a: seeds {b['seeds']['a']}; machine b: seeds {b['seeds']['b']}), expected compute "
             f"{b['expected_compute_s']:.2f} s = {b['expected_compute_h']:.4f} h; expected {json.dumps(b['expected'], sort_keys=True)}.",
             f"5. **The time limits**: {lim['rule']}. At need 4: {json.dumps(lim['need4_s'], sort_keys=True)} s; at need 7: "
             f"{json.dumps(lim['need7_s'], sort_keys=True)} s. The exact limits and caps of the stages of M, which depend on no need and are"
             f" those their manifests hold: {json.dumps(b['measure_stages'], sort_keys=True)}. The caps of Q and N1 to N3 at need 4, which the"
             f" frozen code recomputes from the needs of PREDICTED.json (and splits by the rule of 10.5 if they exceed 14 400 s):"
             f" {json.dumps(b['network_stage_caps_need4_s'], sort_keys=True)} s.",
             f"6. **The rehearsal's record**: `{b['rehearsal']['path']}` at commit `{b['rehearsal']['commit']}`, SHA-256 "
             f"`{b['rehearsal']['sha256']}`, verdict: {b['rehearsal']['verdict']}.", "",
             BEFORE_M_BEGIN, json.dumps(b, indent=1, sort_keys=True), BEFORE_M_END, ""]
    return "\n".join(lines)


def limits_record(cost):
    """The time limits as the code uses them (PREDICTION.md, 10.4), at need 4 and need 7."""
    out = {}
    for tag, needs in (("need4_s", (4, 4, 4, 4)), ("need7_s", (7, 7, 7, 7))):
        r = dict(calibration_deck=c4.limit(cost["calibration_deck_s"]))
        for key, sc in (("quiet_with_skew", "quiet"), ("noisy", "n1"), ("untrained", "untrained")):
            r[key] = with_limits(network_run(c4.FIRST_SEED, "a", needs, sc, "injected"), cost, "injected")["timeout_s"]
        out[tag] = r
    return dict(rule="a run's time limit is 10 x ceil(2 x expected / 10), its expected cost computed on its own calendar (PREDICTION.md, 10.4)", **out)


def before_m(decisions):
    """BEFORE_M.md (PREDICTION.md, 10.8) from the decisions file, which names the rehearsal's record (path, commit,
    SHA-256, verdict); the noise model is the injected one, fixed by PREDICTION.md."""
    d = decisions
    assert d.get("noise_model", "injected") == "injected", "the injected model only (PREDICTION.md, section 6)"
    cost = costs(dict(costs=d.get("costs", {})))
    I, rows = size(cost)
    st = stages(I, "injected", False, cost)
    m = round(c4.MEASURED_FRACTION * I)
    ex = expected_compute(st)
    meas = {n: dict(cap_s=stage_cap(r), runs=len(r), limits_s=sorted({x["timeout_s"] for x in r})) for n, r in st if n[0] == "M"}
    net = {n: stage_cap(r) for n, r in st if n[0] != "M"}
    return dict(what="the record before stage M of campaign 5 (PREDICTION.md, 10.8), written by plan.py",
                noise_model="injected", noise_model_source="PREDICTION.md, section 6 (decision D5-3): the injected model only",
                constants=dict(c4.DECISION5), constants_source="decision 5, PREDICTION.md 4.2 (D5-3)",
                costs=cost, costs_source="PREDICTION.md, 10.3", I=I, seeds=c4.seeds(I), expected_compute_s=ex, expected_compute_h=ex / 3600,
                expected=dict(measured=m, noisy_runs=c4.R * m), limits=limits_record(cost), measure_stages=meas,
                network_stage_caps_need4_s=net, rehearsal=d["rehearsal"])


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
    """The runs of one stage, all from frozen files: M (M1, M2) from BEFORE_M.md; Q, N1, N2, N3 and their parts (Q.1,
    N1.1, ...) from PREDICTED.json, cut by the rule of split (PREDICTION.md, 10.5). Returns the runs (with their
    limits), the protocol file and I."""
    import re
    b = read_before_m(here / "BEFORE_M.md")
    cost, model, I = costs(b), b["noise_model"], b["I"]
    assert model == "injected", "the injected model only (PREDICTION.md, section 6)"
    if re.fullmatch(r"M[12]?", name):
        st = dict(x for x in stages(I, model, False, cost) if x[0][0] == "M")
        return st[name], "PREDICTION.md", I
    m = re.fullmatch(r"(Q|N[123])(?:\.(\d+))?", name)
    assert m, f"refused: {name} is not a stage of the campaign"
    p = json.loads((here / "PREDICTED.json").read_text())
    base, part = m.group(1), m.group(2)
    want = (lambda r: r["noise"] == "none") if base == "Q" else (lambda r, k=int(base[1]): r["round"] == k)
    runs = [r for r in p["network_runs"] if want(r)]
    s = c4.seeds(I)
    seeds = {mach: [x for x in s[mach] if any(r["seed"] == x for r in runs)] for mach in ("a", "b")}
    pieces = split(lambda seed: [r for r in runs if r["seed"] == seed], seeds["a"], seeds["b"])
    named = dict(parts(base, pieces))
    assert name in named, f"refused: {name} is not one of the parts {sorted(named)} of stage {base}"
    return named[name], "PREDICTED.json", I


# ----------------------------------------------------------------------------- the rehearsal (PREDICTION.md, 11)

REHEARSAL_STAGES = ("RC", "RM", "RQ", "RN", "RMEM")
STOPPED_LIMIT_S = 120                                   # RC's deck limited to 120 s, so that it stops at its limit (11.2)


def both(runs):
    """The same runs on machines a and b (PREDICTION.md, 11.2): each run's id carries its machine."""
    return [dict(r, id=f"{m}-{r['id']}", machine=m) for m in ("a", "b") for r in runs]


def dev_slots(dev):
    """The development instances that RQ, RN and RMEM use: those measured, in seed order, with their needs (a missing
    need counts as 7); if none is measured, every development seed at need 4 (PREDICTION.md, 11.2)."""
    if dev is None:
        return [(s, (4, 4, 4, 4)) for s in c4.DEV_SEEDS], None, True
    xs = [x for x in dev["instances"] if x.get("measured")]
    if not xs:
        return [(s, (4, 4, 4, 4)) for s in c4.DEV_SEEDS], None, True
    nd = lambda x: calendar_needs((x["needs"]["a"], x["needs"]["b"], x["needs"]["c1"], x["needs"]["c2"]))
    return [(x["seed"], nd(x)) for x in sorted(xs, key=lambda x: x["seed"])], dev.get("control_instance"), False


def rehearsal_runs(name, dev=None, cost=None):
    """The runs of a rehearsal stage, the same on both machines, with the rehearsal's limits (11.2). dev: the
    development instances' PREDICTED.json (RQ, RN, RMEM). Slots: the measured development instances in seed order,
    repeated if fewer than three are measured (a not-measured instance is replaced by the next one, 11.2). RQ: three
    runs without noise, one at need 7 of the first, the untrained control run. RN: round 1 of each slot (round 2, 3 for
    a repeated instance), then a second run of round 1 of the first. RMEM: the same at need 7, then round 2 of the
    first (with three measured: round 1 of 7691, 7692, 7693 and round 2 of 7691)."""
    cost = cost or costs()
    lim = lambda r: with_limits(r, cost, "injected", rehearsal=True)
    plain = lambda r: {k: v for k, v in r.items() if k != "machine"}
    if name == "RC":
        runs = [lim(dict(id=f"None-cal-{g}", machine="a", seed=None, kind="cal", guard=g)) for g in ("on", "off")]
        stopped = lim(dict(id="None-cal-stopped", machine="a", seed=None, kind="cal", guard="on"))
        runs.append(dict(stopped, timeout_s=STOPPED_LIMIT_S, estimate_s=STOPPED_LIMIT_S, stopped_on_purpose=True))
        for sc in ("quiet", "untrained", "n1"):
            r = lim(network_run(None, "a", (4, 4, 4, 4), sc, "injected"))
            runs.append(dict(r, id=f"None-{sc}", noise_seed=c4.noise_seed(None, 1) if sc == "n1" else None))
        return both([plain(r) for r in runs])
    if name == "RM":
        return both([plain(lim(r)) for s in c4.DEV_SEEDS for r in cal_runs(s, "a") for r in [dict(r, id=r["id"][2:])]])
    slots, control, fallback = dev_slots(dev)
    first = slots[0]
    cycle = lambda n: [slots[j % len(slots)] for j in range(n)]

    def net(s, nd, sc, tag):
        r = lim(network_run(s, "a", nd, sc, "injected"))
        return plain(dict(r, id=f"{s}-{tag}", noise_seed=c4.noise_seed(s, r["round"]) if r["round"] else None))

    def noisy(seq, nd_of, suffix=""):
        """Round 1 for a seed's first slot, 2 and 3 for its next ones, then round 1 again as a repeat."""
        out, seen = [], {}
        for s, nd in seq:
            j = seen[s] = seen.get(s, 0) + 1
            rnd = j if j <= 3 else 1
            out.append(net(s, nd_of(nd), f"n{rnd}", f"n{rnd}{suffix}" + ("" if j <= 3 else f"-repeat{j - 3}")))
        return out
    if name == "RQ":
        runs, seen = [], {}
        for s, nd in cycle(3):
            j = seen[s] = seen.get(s, 0) + 1
            runs.append(net(s, nd, "quiet", "quiet" if j == 1 else f"quiet-{j}"))
        runs.append(net(first[0], (7, 7, 7, 7), "quiet", "quiet-need7"))
        ctl = control if control is not None else first[0]
        runs.append(net(ctl, dict(slots)[ctl], "untrained", "untrained"))
        return both(runs)
    if name == "RN":
        runs = noisy(cycle(3), lambda nd: nd)
        runs.append(net(first[0], first[1], "n1", "n1-repeat"))
        return both(runs)
    if name == "RMEM":
        return both(noisy(cycle(3) + [first], lambda nd: (7, 7, 7, 7), "-need7"))
    raise SystemExit(f"refused: {name} is not a rehearsal stage (PREDICTION.md, 11.2)")


# ------------------------------------------------------------------------- the stages' protocols (PREDICTION.md, 10.6)

STAGE_BEGIN = "```json stage"
# Safeguard (ii) (PREDICTION.md, 10.6): besides the frozen files, unchanged, a stage's source commit may differ from the
# frozen commit only in these files of the campaign's folder (fnmatch patterns, relative to it): the closed list.
ALLOWED_AFTER_FREEZE = ("STAGE_*.md", "STAGE_*_RUNS.json", "BEFORE_M.md", "PREDICTED.json", "Gate4.lean", "REHEARSAL.json",
                        "INVENTORY_a.json", "INVENTORY_b.json", "CAMPAIGN_*.json", "RUN_ATTEMPT_*.json", "evidence/*",
                        "AMENDMENT_*.md", "REPORT.md")


def stage_path(name):
    return f"{BASE}/STAGE_{name}.md"


def governing_of(name):
    """The governing protocol of a stage, from the closed list of stage names of PREDICTION.md (10.6): PREDICTION.md for
    M, M1, M2 and the rehearsal's RC and RM; PREDICTED.json for Q, N1, N2, N3 and their parts, and the rehearsal's RQ,
    RN and RMEM (in the rehearsal's own clone, the development instances' PREDICTED.json). Any other name is refused;
    nothing is inferred from a first letter."""
    import re
    if re.fullmatch(r"M[12]?|RC|RM", name):
        return f"{BASE}/PREDICTION.md"
    if re.fullmatch(r"(Q|N[123])(\.\d+)?|RQ|RN|RMEM", name):
        return f"{BASE}/PREDICTED.json"
    raise SystemExit(f"refused: {name} is not a stage name of PREDICTION.md (10.6)")


def stage_file_text(name, governing, commit, digest):
    block = dict(stage=name, governing_protocol=dict(path=governing, commit=commit, sha256=digest))
    return "\n".join([f"# Campaign 5: the protocol of stage {name}", "",
                      "Written by `plan.py stage-file` (the frozen code) and pushed alone before the stage's launch (PREDICTION.md,",
                      f"10.6). Its governing protocol is `{governing}` at commit `{commit}`, SHA-256 `{digest}`;",
                      "`run4.py` refuses every run of the stage if that file has another SHA-256 in the repository.", "",
                      STAGE_BEGIN, json.dumps(block, indent=1, sort_keys=True), "```", ""])


def read_stage(path):
    text = Path(path).read_text()
    i = text.index(STAGE_BEGIN) + len(STAGE_BEGIN)
    return json.loads(text[i:text.index("```", i)])


def check_after_freeze(frozen_commit, source_commit, root=ROOT):
    """Safeguard (ii) (PREDICTION.md, 10.6): no frozen file differs, and every other changed file is in the
    closed list. Returns the changed files; raises otherwise."""
    import fnmatch
    changed = subprocess.run(["git", "-C", str(root), "diff", "--name-only", frozen_commit, source_commit], check=True,
                             capture_output=True, text=True).stdout.split()
    bad = [f for f in changed if f in FROZEN or not f.startswith(BASE + "/")
           or not any(fnmatch.fnmatch(f[len(BASE) + 1:], p) for p in ALLOWED_AFTER_FREEZE)]
    if bad:
        raise SystemExit(f"refused (safeguard ii): the source commit differs from the frozen commit in {bad}")
    return changed


def manifest(name, runs, I, protocol_commit, protocol, source_commit, root=ROOT, frozen_commit=None, extra=None):
    def blob(commit, path):
        return subprocess.run(["git", "-C", str(root), "show", f"{commit}:{path}"], check=True, capture_output=True).stdout
    if frozen_commit is not None:
        check_after_freeze(frozen_commit, source_commit, root)
    stage = name if protocol.startswith("STAGE_") else None
    entries = [entry(r, I, "stage", stage) for r in runs]
    rehearsal = name in REHEARSAL_STAGES
    cid = ("learned-dnf-circuit-5-rehearsal-" if rehearsal else "learned-dnf-circuit-5-") + name.lower().replace(".", "-")
    bound = [f"{BASE}/BEFORE_M.md"] if not rehearsal else []
    return dict(kind="registered", campaign_id=cid, attempt=1, executor=c4.EXECUTOR,
                protocol_commit=protocol_commit, protocol_path=f"{BASE}/{protocol}",
                protocol_sha256=hashlib.sha256(blob(protocol_commit, f"{BASE}/{protocol}")).hexdigest(),
                source_commit=source_commit, launcher_path=f"{CLOSURE}/launchkit/launch.py", marker_path=f"{BASE}/RUN_ATTEMPT_{name}.json",
                spinit_path=f"{CLOSURE}/runtime/spinit", inventory_a_path=f"{BASE}/INVENTORY_a.json", inventory_b_path=f"{BASE}/INVENTORY_b.json",
                source_sha256={n: hashlib.sha256(blob(source_commit, n)).hexdigest() for n in FROZEN + bound + list(extra or []) + extra_frozen(runs)},
                expected_workflows=WORKFLOWS, jobs=c4.JOBS, scenario_order=["stage"], budget_s=math.ceil(stage_cap(runs)), runs=entries)


def main():
    if sys.argv[1] == "size":
        cost = costs(json.loads(Path(sys.argv[2]).read_text()) if len(sys.argv) > 2 else None)
        I, rows = size(cost)
        st = stages(I, "injected", False, cost)
        print(json.dumps(dict(I=I, expected_compute_s=expected_compute(st))))
        for r in rows:
            print(" ", r["I"], round(r["expected_h"], 4), r["caps"])
    elif sys.argv[1] == "before-m":
        print(c4.require_pinned())
        Path(sys.argv[3]).write_text(before_m_text(before_m(json.loads(Path(sys.argv[2]).read_text()))))
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
