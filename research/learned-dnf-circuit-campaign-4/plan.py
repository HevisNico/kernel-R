"""Campaign 4: the runs of each stage, their costs, the sizing rule, BEFORE_M.json and the manifests of the kit.

  plan.py size [COSTS.json]                                  the expected compute and stage caps for I = 1..15
  plan.py before-m DECISIONS.json BEFORE_M.json               BEFORE_M.json from the noise study's outcome
  plan.py manifest STAGE PROTOCOL_COMMIT SOURCE_COMMIT [M1|M2|E1|...]    a manifest of the kit, printed

Stages, in the fixed order of PREDICTION.md: M (M1, M2 if needed: the calibration decks), E1, E2, ... (the
extraction per cell, state and output, device model only), Q (the runs without noise with the skew control, and the
untrained control run), N1, N2, N3 (the noisy runs of round 1, 2, 3). M and E have PREDICTION.md as their protocol;
Q and N1 to N3 have PREDICTED.json. Nothing here is chosen at launch time: the runs follow from BEFORE_M.json,
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
# The costs known when PREDICTION.md was pushed (BEFORE_M.json replaces the noisy run's and the extraction's).
COSTS = dict(quiet_need4_s=814.0, noisy_need4_s=dict(device=1033.0, injected=1316.0), calibration_deck_s=925.0, untrained_s=369.2,
             extraction_s=dict(hold=100.0, window=260.0, fire=290.0, pulse=95.0), isolation_per_instance_s=40.0)
OUTPUTS = dict(cal=["evidence/input.spice", "evidence/session.log", "evidence/trace.raw", "evidence/result.json", "record.json", "noise.sha256"],
               network=["evidence/input.spice", "evidence/session.log", "evidence/trace.raw", "evidence/result.json", "record.json", "noise.sha256"],
               extract=["part.json", "record.json", "noise.sha256"])
FROZEN = [f"{BASE}/{n}" for n in ("PREDICTION.md", "c4.py", "noisemodel.py", "session4.py", "plans4.py", "reads4.py", "run4.py", "predicted.py",
                                   "gate4.py", "plan.py", "analyze.py", "rehearsal.py", "test_campaign.py", "check.sh",
                                   "noise/devnoise.py", "noise/model.py", "noise/pilot.py", "noise/noisegen.py", "noise/README.md")] + [
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
        return cost["extraction_s"][run["state"]] + (cost["isolation_per_instance_s"] / 3 if run["isolation"] else 0.0)
    slots = dnf.calendar(*calendar_needs(run["needs"]), run["control"])
    if run["control"] == "untrained":
        return cost["untrained_s"]
    base = cost["noisy_need4_s"][model] if run["noise"] != "none" else cost["quiet_need4_s"]
    return base * dcost(slots) / REF


def ceil10(x):
    return 10 * math.ceil(x / 10 - 1e-9)


def with_limits(run, cost, model, rehearsal=None):
    """estimate: the expected cost; time limit: 1.3 times the rehearsal's measured time for that run kind, scaled
    as the cost model scales it, and never above 1.3 times the cost model."""
    e = expected(run, cost, model)
    limit = c4.MARGIN * e
    if rehearsal:
        kind = run["kind"] if run["kind"] != "network" else ("untrained" if run["control"] == "untrained" else ("noisy" if run["noise"] != "none" else "quiet"))
        measured = rehearsal.get(kind)
        if measured is not None:
            limit = min(limit, c4.MARGIN * measured * e / rehearsal["model_" + kind])
    return dict(run, estimate_s=ceil10(e), timeout_s=max(ceil10(limit), ceil10(e)), expected_s=e)


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


def before_m(decisions):
    """BEFORE_M.json from the decisions file of the noise study's outcome: the model applied and its sources, the
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

def argv(r, I):
    out = ["{python}", "{repo}/" + f"{BASE}/run4.py", "--out", "{out}", "--ngspice", "{ngspice}", "--pdk", "{pdk}", "--id", r["id"],
           "--kind", r["kind"], "--seed", str(r["seed"]), "--instances", str(I)]
    if r["kind"] == "cal":
        out += ["--guard", r["guard"]]
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


def entry(r, I, scenario):
    return dict(id=r["id"], machine=r["machine"], scenario=scenario, deck="research/circuit/cell.spice", runner=f"{BASE}/run4.py",
                argv=argv(r, I), estimate_s=r["estimate_s"], timeout_s=r["timeout_s"], required_outputs=OUTPUTS[r["kind"]],
                diagnostic_logs=[] if r["kind"] == "extract" else ["evidence/session.log"], noise_fingerprint="noise.sha256")


def manifest(name, runs, I, protocol_commit, protocol, source_commit, root=ROOT):
    def blob(commit, path):
        return subprocess.run(["git", "-C", str(root), "show", f"{commit}:{path}"], check=True, capture_output=True).stdout
    entries = [entry(r, I, "stage") for r in runs]
    return dict(kind="registered", campaign_id=f"learned-dnf-circuit-4-{name.lower()}", attempt=1, executor=c4.EXECUTOR,
                protocol_commit=protocol_commit, protocol_path=f"{BASE}/{protocol}",
                protocol_sha256=hashlib.sha256(blob(protocol_commit, f"{BASE}/{protocol}")).hexdigest(),
                source_commit=source_commit, launcher_path=f"{CLOSURE}/launchkit/launch.py", marker_path=f"{BASE}/RUN_ATTEMPT_{name}.json",
                spinit_path=f"{CLOSURE}/runtime/spinit", inventory_a_path=f"{BASE}/INVENTORY_a.json", inventory_b_path=f"{BASE}/INVENTORY_b.json",
                source_sha256={n: hashlib.sha256(blob(source_commit, n)).hexdigest() for n in FROZEN + [f"{BASE}/BEFORE_M.json"]},
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
        Path(sys.argv[3]).write_text(json.dumps(before_m(json.loads(Path(sys.argv[2]).read_text())), indent=1) + "\n")


if __name__ == "__main__":
    main()
