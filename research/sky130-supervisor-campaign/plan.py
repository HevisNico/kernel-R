"""The 124 runs of the campaign, exactly as PREDICTION.md lists them, and the manifest of the launch kit.

  plan.py runs                                         prints the runs, for reading
  plan.py manifest PROTOCOL_COMMIT SOURCE_COMMIT       prints CAMPAIGN.json; the two commits are checked by the launcher

The manifest is written only at launch time, when the commit of the frozen implementation exists.
Nothing here can be chosen then: the runs follow from the constants below, which the tests compare
with PREDICTION.md.
"""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
BASE = "research/sky130-supervisor-campaign"
CLOSURE = "research/sky130-supervisor-closure"

MAIN = ["tt27", "ss27", "ff27", "sf27", "fs27", "tt125", "mm2001", "mm2002"]
ORDER = ["main-" + c for c in MAIN] + ["quiet", "outside", "self"]
QUIET = dict(a=["tt27", "ss27", "ff27", "sf27", "fs27"], b=["tt-40", "tt125", "mm2001", "mm2002", "tt27"])
OTHER = dict(a=["tt27", "ss27", "ff27", "sf27", "fs27"], b=["tt125", "mm2001", "mm2002", "tt27", "ss27"])
RUNS_PER_MACHINE = 62
SERVICES = 24
INSIDE, INSIDE_COLD, OUTSIDE = 3e-11, 2e-11, 2e-10
FIRST_SEED = dict(a=10000, b=20000)
INSTANCE = dict(mm2001=2001, mm2002=2002)
ESTIMATE_S, TIMEOUT_S, JOBS, BUDGET_S = 280, 420, 4, 14400
EXECUTOR = "a Claude Code cloud session on behalf of the owner, on two cloud containers whose inventories are recorded"
OUTPUTS = ["evidence/input.spice", "evidence/session.log", "evidence/head.raw", "evidence/noise.sha256", "evidence/trace.raw", "evidence/result.json"]
FROZEN = [f"{BASE}/PREDICTION.md", f"{BASE}/run.py", f"{BASE}/plan.py", f"{BASE}/analyze.py",
          f"{CLOSURE}/launchkit/launch.py", f"{CLOSURE}/runtime/spinit", f"{CLOSURE}/sim.py", f"{CLOSURE}/extract.py", f"{CLOSURE}/kernel.py",
          f"{CLOSURE}/configs.json", f"{CLOSURE}/BOUNDS_JUNCTION.json", f"{CLOSURE}/junction/netlist.py", f"{CLOSURE}/junction/areas.csv",
          "research/circuit/cell.spice", "research/circuit/blocks.spice", "research/circuit/noise.json", "research/circuit/spiceinit.txt"]
WORKFLOWS = ["SKY130 supervisor campaign"]


def runs():
    out = []
    for machine in ("a", "b"):
        seen = {}
        for i in range(RUNS_PER_MACHINE):
            scenario = ORDER[i % len(ORDER)]
            j = seen.get(scenario, 0)                       # occurrence of this scenario on this machine
            seen[scenario] = j + 1
            if scenario.startswith("main-"):
                config, mode, noise, jump = scenario[5:], "supervised", 1, INSIDE
            elif scenario == "quiet":
                config, mode, noise = QUIET[machine][j], "supervised", 0
                jump = INSIDE_COLD if config == "tt-40" else INSIDE
            elif scenario == "outside":
                config, mode, noise, jump = OTHER[machine][j], "supervised", 0, OUTSIDE
            else:
                config, mode, noise, jump = OTHER[machine][j], "self", 1, INSIDE
            number = FIRST_SEED[machine] + i
            out.append(dict(id=f"{machine}{i:02d}-{scenario}" + ("" if scenario.startswith("main-") else "-" + config), machine=machine, index=i,
                            scenario=scenario, config=config, mode=mode, noise=noise, jump_S=jump, version=0 if config == "tt-40" else 2,
                            number=number, seed=INSTANCE.get(config, number), services=SERVICES))
    return out


def manifest(protocol_commit, source_commit):
    def blob(commit, name):
        return subprocess.run(["git", "-C", str(ROOT), "show", f"{commit}:{name}"], check=True, capture_output=True).stdout
    entries = []
    for r in runs():
        argv = ["{python}", "{repo}/" + f"{BASE}/run.py", "--out", "{out}/evidence", "--ngspice", "{ngspice}", "--pdk", "{pdk}",
                "--id", r["id"], "--scenario", r["scenario"], "--config", r["config"], "--mode", r["mode"], "--noise", str(r["noise"]),
                "--jump", repr(r["jump_S"]), "--version", str(r["version"]), "--seed", str(r["seed"]), "--services", str(SERVICES)]
        entries.append(dict(id=r["id"], machine=r["machine"], scenario=r["scenario"], deck="research/circuit/cell.spice", runner=f"{BASE}/run.py", argv=argv,
                            estimate_s=ESTIMATE_S, timeout_s=TIMEOUT_S, required_outputs=OUTPUTS, diagnostic_logs=["evidence/session.log"],
                            noise_fingerprint="evidence/noise.sha256"))
    return dict(kind="registered", campaign_id="sky130-supervisor-1", attempt=1, executor=EXECUTOR,
                protocol_commit=protocol_commit, protocol_path=f"{BASE}/PREDICTION.md",
                protocol_sha256=hashlib.sha256(blob(protocol_commit, f"{BASE}/PREDICTION.md")).hexdigest(), source_commit=source_commit,
                launcher_path=f"{CLOSURE}/launchkit/launch.py", marker_path=f"{BASE}/RUN_ATTEMPT.json", spinit_path=f"{CLOSURE}/runtime/spinit",
                inventory_a_path=f"{BASE}/INVENTORY_a.json", inventory_b_path=f"{BASE}/INVENTORY_b.json",
                source_sha256={name: hashlib.sha256(blob(source_commit, name)).hexdigest() for name in FROZEN},
                expected_workflows=WORKFLOWS, jobs=JOBS, scenario_order=ORDER, budget_s=BUDGET_S, runs=entries)


def main():
    if sys.argv[1] == "runs":
        for r in runs():
            print(r["id"], r["mode"], "noise" if r["noise"] else "quiet", r["jump_S"], "version", r["version"], "seed", r["seed"])
    else:
        print(json.dumps(manifest(sys.argv[2], sys.argv[3]), indent=1))


if __name__ == "__main__":
    main()
