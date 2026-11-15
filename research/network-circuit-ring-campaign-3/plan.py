"""The runs of campaign 3, exactly as PREDICTION.md lists them, and the two manifests of the launch kit.

  plan.py measures                                              prints the measure runs, for reading
  plan.py manifest measures PROTOCOL_COMMIT SOURCE_COMMIT       prints CAMPAIGN_M.json
  plan.py manifest runs PROTOCOL_COMMIT SOURCE_COMMIT           prints CAMPAIGN_R.json, from the committed PREDICTED.json

Two launches per machine. The measures have PREDICTION.md as their protocol. The network runs have PREDICTED.json
as theirs: the launcher then refuses to start them unless that file is published and unchanged. Nothing here can be
chosen at launch time: the measure runs follow from the constants below, which the tests compare with PREDICTION.md,
and the network runs, with their laps and limits, from the list that `predicted.py` wrote in PREDICTED.json.
"""
import hashlib
import json
import math
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
BASE = "research/network-circuit-ring-campaign-3"
RING = "research/network-circuit-ring"
NET = "research/network-circuit"
CLOSURE = "research/sky130-supervisor-closure"
sys.path.insert(0, str(ROOT / RING))
import ring

N = 3
SEEDS = dict(a=[7401, 7402, 7403, 7404, 7405, 7406], b=[7407, 7408, 7409, 7410, 7411, 7412])
SECTION = "tt_mm"
PORTS = ring.ports(N)                                   # a1, b1, c1, a2: the order of the chain
CELLS = ring.cells(N)
UNUSED = [c + "2" for c in CELLS[1:]]                   # b2, c2: never pulsed
READS = 10                                              # reads per port in the train
NOISY_RUNS = 1                                          # noisy network runs per measured instance
GUARD = ring.SEPARATION                                 # 16 units
AFTER_QUIET, AFTER_NOISY = 10, 3                        # laps after the predicted freeze
ESTIMATE_S = dict(scan=400, train=570)
TIMEOUT_S = dict(scan=860, train=730)                   # the scan limit of amendment 3
COST = dict(per_cell_ms_s=3.7746, per_cell_pulse_s=3.9820, noise=1.3861, margin=1.3)
JOBS = 4
CLEANUP_S = 10                                          # the allowance of the launch kit per run
MAX_BUDGET_S = 14400                                    # per manifest, the two machines together
EXECUTOR = "a Claude Code cloud session on behalf of the owner, on two cloud containers whose inventories are recorded"
OUTPUTS = ["evidence/input.spice", "evidence/session.log", "evidence/trace.raw", "evidence/result.json", "evidence/record.json", "evidence/noise.sha256"]
FROZEN = [f"{BASE}/PREDICTION.md", f"{BASE}/COMMITMENT.md", f"{BASE}/AMENDMENT_1.md", f"{BASE}/AMENDMENT_2.md", f"{BASE}/AMENDMENT_3.md", f"{BASE}/ROBUST_SCAN_REHEARSAL.json",
          f"{BASE}/run.py", f"{BASE}/plan.py", f"{BASE}/predicted.py", f"{BASE}/analyze.py", f"{BASE}/check.sh", f"{BASE}/robustscan.py",
          f"{RING}/ring.py", f"{RING}/RingNetwork.lean",
          f"{NET}/net.py", f"{NET}/router.py", f"{NET}/measure.py",
          f"{NET}/phase1/collect.py", f"{NET}/phase1/constants.py",
          f"{NET}/phase1/CircuitNetwork.lean", f"{NET}/phase1/DatedOrder.lean",
          "research/network-stability/RoutedCalendar.lean", "research/network-stability/AutonomousFeedback.lean",
          "research/self-certifying-learning/SelfCertifyingLearning/Budget.lean", "research/self-certifying-learning/SelfCertifyingLearning/Composition.lean",
          f"{CLOSURE}/launchkit/launch.py", f"{CLOSURE}/runtime/spinit", f"{CLOSURE}/sim.py", f"{CLOSURE}/junction/netlist.py", f"{CLOSURE}/junction/areas.csv",
          "research/circuit/cell.spice", "research/circuit/blocks.spice", "research/circuit/noise.json", "research/circuit/spiceinit.txt"]
WORKFLOWS = ["Ring circuit campaign 3"]
STAGES = dict(measures=dict(campaign_id="network-circuit-ring-3-measures", protocol="PREDICTION.md", marker="RUN_ATTEMPT_M.json", scenario="measure"),
              runs=dict(campaign_id="network-circuit-ring-3-runs", protocol="PREDICTED.json", marker="RUN_ATTEMPT_R.json", scenario="network"))


def instances():
    """The six instances, in order, with the machine that measures and runs each."""
    return [dict(seed=seed, machine=machine) for machine in ("a", "b") for seed in SEEDS[machine]]


def measure_runs(which=None):
    """Per machine: the scans of its instances (four ports each), then their trains without noise."""
    which = instances() if which is None else which
    out = []
    for machine in ("a", "b"):
        seeds = [i["seed"] for i in which if i["machine"] == machine]
        out += [dict(id=f"{machine}-{seed}-scan-{port}", machine=machine, seed=seed, kind="scan", port=port, noise=0) for seed in seeds for port in PORTS]
        out += [dict(id=f"{machine}-{seed}-train", machine=machine, seed=seed, kind="train", noise=0) for seed in seeds]
    return out


def calendar(name, laps):
    return ring.control(N, laps) if name == "control" else ring.ring(N, laps)


def ceil10(seconds):
    return 10 * math.ceil(seconds / 10 - 1e-9)


def expected_s(calendar_, pulses, noise):
    """The cost model of phase 0 (`../network-circuit-ring/cost.py`), with its constants as PREDICTION.md writes them."""
    ms = calendar_["horizon"] * 0.02
    return N * (COST["per_cell_ms_s"] * ms + COST["per_cell_pulse_s"] * pulses) * (COST["noise"] if noise else 1.0)


def laps(needs):
    """Laps of the run without noise and of the control, and of the noisy runs."""
    return sum(needs) + AFTER_QUIET, sum(needs) + AFTER_NOISY


def network_run(machine, seed, scenario, needs, k=None):
    quiet, noisy = laps(needs)
    L = noisy if scenario == "noisy" else quiet
    name = "control" if scenario == "control" else "ring"
    pulses = sum(map(len, ring.zero_error(list(needs), L)["words"]))
    e = expected_s(calendar(name, L), pulses, scenario == "noisy")
    return dict(id=f"{machine}-{seed}-ring-{scenario}{k or ''}", machine=machine, seed=seed, kind="network", scenario=scenario, noise=int(scenario == "noisy"),
                calendar=name, laps=L, guard=0 if scenario == "control" else GUARD, pulses=pulses, expected_s=round(e, 1),
                estimate_s=ceil10(e), timeout_s=ceil10(COST["margin"] * e))


def machine_cap(runs):
    """The bound of the launch kit on one machine: sum of (limit + 10 s) / jobs + the largest (limit + 10 s)."""
    caps = [r["timeout_s"] + CLEANUP_S for r in runs]
    return sum(caps) / JOBS + max(caps) if caps else 0.0


def caps(runs):
    return {m: machine_cap([r for r in runs if r["machine"] == m]) for m in ("a", "b")}


def network_runs(needs, control, which=None):
    """Per machine: one run without noise per measured instance, in the order of the seeds; the control run if its
    instance is there; then one noisy run per measured instance, in the order of the seeds.
    `needs` maps each measured seed to the needs of its four ports, `control` is the seed of the control instance or
    None. Returns (the runs, the noisy runs removed for the budget)."""
    which = instances() if which is None else which
    runs = []
    for machine in ("a", "b"):
        mine = [i["seed"] for i in which if i["machine"] == machine and i["seed"] in needs]
        runs += [network_run(machine, seed, "quiet", needs[seed]) for seed in mine]
        runs += [network_run(machine, seed, "control", needs[seed]) for seed in mine if seed == control]
        runs += [network_run(machine, seed, "noisy", needs[seed], k) for k in range(1, NOISY_RUNS + 1) for seed in mine]
    removed = []
    while sum(caps(runs).values()) > MAX_BUDGET_S:
        c = caps(runs)
        machine = "a" if c["a"] >= c["b"] else "b"
        noisy = [r for r in runs if r["machine"] == machine and r["scenario"] == "noisy"]
        if not noisy:
            break
        runs.remove(noisy[-1])
        removed.append(noisy[-1])
    return runs, removed


def argv(r, section=SECTION):
    out = ["{python}", "{repo}/" + f"{BASE}/run.py", "--out", "{out}/evidence", "--ngspice", "{ngspice}", "--pdk", "{pdk}", "--id", r["id"],
           "--kind", r["kind"], "--section", section, "--seed", str(r["seed"]), "--noise", str(r["noise"])]
    if r["kind"] == "scan":
        out += ["--port", r["port"]]
    elif r["kind"] == "train":
        out += ["--reads", str(READS)]
    else:
        out += ["--calendar", r["calendar"], "--laps", str(r["laps"]), "--guard", str(r["guard"])]
    return out


def entry(r, scenario, section=SECTION):
    estimate, timeout = (r["estimate_s"], r["timeout_s"]) if r["kind"] == "network" else (ESTIMATE_S[r["kind"]], TIMEOUT_S[r["kind"]])
    return dict(id=r["id"], machine=r["machine"], scenario=scenario, deck="research/circuit/cell.spice", runner=f"{BASE}/run.py", argv=argv(r, section),
                estimate_s=estimate, timeout_s=timeout, required_outputs=OUTPUTS, diagnostic_logs=["evidence/session.log"],
                noise_fingerprint="evidence/noise.sha256")


def manifest(stage, protocol_commit, source_commit, runs=None, section=SECTION, root=ROOT):
    """The manifest of one stage. `runs`, `section` and `root` are for the rehearsal; the campaign uses the defaults."""
    def blob(commit, name):
        return subprocess.run(["git", "-C", str(root), "show", f"{commit}:{name}"], check=True, capture_output=True).stdout
    s = STAGES[stage]
    protocol = f"{BASE}/{s['protocol']}"
    if runs is None:
        runs = measure_runs() if stage == "measures" else json.loads(blob(protocol_commit, protocol))["network_runs"]
    entries = [entry(r, s["scenario"], section) for r in runs]
    return dict(kind="registered", campaign_id=s["campaign_id"], attempt=1, executor=EXECUTOR,
                protocol_commit=protocol_commit, protocol_path=protocol, protocol_sha256=hashlib.sha256(blob(protocol_commit, protocol)).hexdigest(),
                source_commit=source_commit, launcher_path=f"{CLOSURE}/launchkit/launch.py", marker_path=f"{BASE}/{s['marker']}",
                spinit_path=f"{CLOSURE}/runtime/spinit", inventory_a_path=f"{BASE}/INVENTORY_a.json", inventory_b_path=f"{BASE}/INVENTORY_b.json",
                source_sha256={name: hashlib.sha256(blob(source_commit, name)).hexdigest() for name in FROZEN},
                expected_workflows=WORKFLOWS, jobs=JOBS, scenario_order=[s["scenario"]], budget_s=math.ceil(sum(caps(entries).values())),
                runs=entries)


def main():
    if sys.argv[1] == "measures":
        for r in measure_runs():
            print(r["id"], r["kind"], r.get("port", ""))
    else:
        print(json.dumps(manifest(sys.argv[2], sys.argv[3], sys.argv[4]), indent=1))


if __name__ == "__main__":
    main()
