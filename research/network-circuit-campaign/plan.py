"""The runs of the campaign, exactly as PREDICTION.md lists them, and the two manifests of the launch kit.

  plan.py measures                                              prints the measure runs, for reading
  plan.py manifest measures PROTOCOL_COMMIT SOURCE_COMMIT       prints CAMPAIGN_M.json
  plan.py manifest runs PROTOCOL_COMMIT SOURCE_COMMIT           prints CAMPAIGN_R.json, from the committed PREDICTED.json

Two launches per machine. The measures have PREDICTION.md as their protocol. The network runs have PREDICTED.json
as theirs: the launcher then refuses to start them unless that file is published and unchanged. Nothing here can be
chosen at launch time: the measure runs follow from the constants below, which the tests compare with PREDICTION.md,
and the network runs from the list that `predicted.py` wrote in PREDICTED.json.
"""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
BASE = "research/network-circuit-campaign"
NET = "research/network-circuit"
CLOSURE = "research/sky130-supervisor-closure"

SEEDS = dict(a=[7201, 7202, 7203], b=[7204, 7205, 7206])
SECTION = "tt_mm"
PORTS = ["a1", "a2", "b1", "b2"]
READS = 10                      # reads per port in a train
NOISY_TRAINS = 3                # per instance, each in its own simulator process
NOISY_RUNS = 2                  # noisy network runs per measured instance
GUARD = 16
ESTIMATE_S = dict(scan=300, train=560, network=690)
TIMEOUT_S = dict(scan=375, train=700, network=860)
JOBS = 4
BUDGET_S = dict(measures=7990, runs=6410)       # together 14 400 s
EXECUTOR = "a Claude Code cloud session on behalf of the owner, on two cloud containers whose inventories are recorded"
OUTPUTS = ["evidence/input.spice", "evidence/session.log", "evidence/trace.raw", "evidence/result.json", "evidence/record.json", "evidence/noise.sha256"]
FROZEN = [f"{BASE}/PREDICTION.md", f"{BASE}/run.py", f"{BASE}/plan.py", f"{BASE}/predicted.py", f"{BASE}/analyze.py", f"{BASE}/check.sh",
          f"{NET}/net.py", f"{NET}/router.py", f"{NET}/measure.py",
          f"{NET}/phase1/cellscan.py", f"{NET}/phase1/noisechar.py", f"{NET}/phase1/collect.py", f"{NET}/phase1/constants.py", f"{NET}/phase1/predict.py",
          f"{NET}/phase1/model.py", f"{NET}/phase1/calendars.py", f"{NET}/phase1/CircuitNetwork.lean", f"{NET}/phase1/DatedOrder.lean",
          f"{CLOSURE}/launchkit/launch.py", f"{CLOSURE}/runtime/spinit", f"{CLOSURE}/sim.py", f"{CLOSURE}/junction/netlist.py", f"{CLOSURE}/junction/areas.csv",
          "research/circuit/cell.spice", "research/circuit/blocks.spice", "research/circuit/noise.json", "research/circuit/spiceinit.txt"]
WORKFLOWS = ["Network circuit campaign"]
STAGES = dict(measures=dict(campaign_id="network-circuit-1-measures", protocol="PREDICTION.md", marker="RUN_ATTEMPT_M.json", scenario="measure"),
              runs=dict(campaign_id="network-circuit-1-runs", protocol="PREDICTED.json", marker="RUN_ATTEMPT_R.json", scenario="network"))


def instances():
    """The six instances, in order, with the machine that measures and runs each."""
    return [dict(seed=seed, machine=machine) for machine in ("a", "b") for seed in SEEDS[machine]]


def measure_runs(which=None):
    """Per machine: the scans of its instances, then their trains without noise, then their noisy trains."""
    which = instances() if which is None else which
    out = []
    for machine in ("a", "b"):
        seeds = [i["seed"] for i in which if i["machine"] == machine]
        out += [dict(id=f"{machine}-{seed}-scan-{port}", machine=machine, seed=seed, kind="scan", port=port, noise=0) for seed in seeds for port in PORTS]
        out += [dict(id=f"{machine}-{seed}-quiet", machine=machine, seed=seed, kind="train", noise=0) for seed in seeds]
        out += [dict(id=f"{machine}-{seed}-noisy{k}", machine=machine, seed=seed, kind="train", noise=1) for k in range(1, NOISY_TRAINS + 1) for seed in seeds]
    return out


def network_runs(measured, control, which=None):
    """Per machine: one run without noise per measured instance, the control run if its instance is there, then the
    noisy runs. `measured` is the list of measured seeds, `control` the seed of the control instance or None."""
    which = instances() if which is None else which
    out = []
    for machine in ("a", "b"):
        mine = [i["seed"] for i in which if i["machine"] == machine and i["seed"] in measured]
        out += [dict(id=f"{machine}-{seed}-net-quiet", machine=machine, seed=seed, kind="network", scenario="quiet", noise=0, spacing=18, guard=GUARD) for seed in mine]
        out += [dict(id=f"{machine}-{seed}-net-control", machine=machine, seed=seed, kind="network", scenario="control", noise=0, spacing=8, guard=0) for seed in mine if seed == control]
        out += [dict(id=f"{machine}-{seed}-net-noisy{k}", machine=machine, seed=seed, kind="network", scenario="noisy", noise=1, spacing=18, guard=GUARD)
                for k in range(1, NOISY_RUNS + 1) for seed in mine]
    return out


def argv(r, section=SECTION):
    out = ["{python}", "{repo}/" + f"{BASE}/run.py", "--out", "{out}/evidence", "--ngspice", "{ngspice}", "--pdk", "{pdk}", "--id", r["id"],
           "--kind", r["kind"], "--section", section, "--seed", str(r["seed"]), "--noise", str(r["noise"])]
    if r["kind"] == "scan":
        out += ["--port", r["port"]]
    elif r["kind"] == "train":
        out += ["--reads", str(READS)]
    else:
        out += ["--spacing", str(r["spacing"]), "--guard", str(r["guard"])]
    return out


def entry(r, scenario, section=SECTION):
    return dict(id=r["id"], machine=r["machine"], scenario=scenario, deck="research/circuit/cell.spice", runner=f"{BASE}/run.py", argv=argv(r, section),
                estimate_s=ESTIMATE_S[r["kind"]], timeout_s=TIMEOUT_S[r["kind"]], required_outputs=OUTPUTS, diagnostic_logs=["evidence/session.log"],
                noise_fingerprint="evidence/noise.sha256")


def manifest(stage, protocol_commit, source_commit, runs=None, section=SECTION, root=ROOT):
    """The manifest of one stage. `runs`, `section` and `root` are for the rehearsal; the campaign uses the defaults."""
    def blob(commit, name):
        return subprocess.run(["git", "-C", str(root), "show", f"{commit}:{name}"], check=True, capture_output=True).stdout
    s = STAGES[stage]
    protocol = f"{BASE}/{s['protocol']}"
    if runs is None:
        runs = measure_runs() if stage == "measures" else json.loads(blob(protocol_commit, protocol))["network_runs"]
    return dict(kind="registered", campaign_id=s["campaign_id"], attempt=1, executor=EXECUTOR,
                protocol_commit=protocol_commit, protocol_path=protocol, protocol_sha256=hashlib.sha256(blob(protocol_commit, protocol)).hexdigest(),
                source_commit=source_commit, launcher_path=f"{CLOSURE}/launchkit/launch.py", marker_path=f"{BASE}/{s['marker']}",
                spinit_path=f"{CLOSURE}/runtime/spinit", inventory_a_path=f"{BASE}/INVENTORY_a.json", inventory_b_path=f"{BASE}/INVENTORY_b.json",
                source_sha256={name: hashlib.sha256(blob(source_commit, name)).hexdigest() for name in FROZEN},
                expected_workflows=WORKFLOWS, jobs=JOBS, scenario_order=[s["scenario"]], budget_s=BUDGET_S[stage],
                runs=[entry(r, s["scenario"], section) for r in runs])


def main():
    if sys.argv[1] == "measures":
        for r in measure_runs():
            print(r["id"], r["kind"], r.get("port", ""), "noise" if r["noise"] else "quiet")
    else:
        print(json.dumps(manifest(sys.argv[2], sys.argv[3], sys.argv[4]), indent=1))


if __name__ == "__main__":
    main()
