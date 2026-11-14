"""Execution of stage P on two machines, by the rules of ../AMENDMENT_2.md.

  python3 -I p_execute.py plan
  python3 -I p_execute.py launch --machine A --go      on machine A
  python3 -I p_execute.py launch --machine B --go      on machine B, once A has pushed the marker

The rules are those of execute.py, whose `launch` is used as it is: one marker for both machines
(RUN_ATTEMPT_P.json, written and pushed by machine A before the first run), the name of each run
pushed as started before it begins, a run found started and without a result recorded as lost and
never run again, the nominal schematic run of each machine compared byte for byte with the
committed result before anything else, results pushed as each group of four runs ends.

What changes for stage P is given here: the queues of p_plan.py, the files the marker pins, the
check of p_manifest.json, p_run.one, which makes a run, and a preflight that also checks what the
harness needs on the machine.
"""
import json
import os
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import execute
import p_plan

QUEUES = {m: [r["name"] for r in q] for m, q in p_plan.queues().items()}
PINNED = ["PREDICTION.md", "AMENDMENT_1.md", "AMENDMENT_2.md", "AMENDMENT_3.md", "AMENDMENT_4.md",
          "phase1/SCOPE_P.json", "phase1/p_manifest.json", "phase1/execute.py", "phase1/p_execute.py", "phase1/p_plan.py",
          "phase1/p_run.py", "phase1/p_shim/ngspice", "phase1/p_analyze.py", "phase1/netlist.py", "phase1/p_areas.csv",
          "phase1/p_caps_primary.csv", "phase1/p_caps.csv", "phase1/ref_p/nom_read.csv"]


def configure():
    execute.STAGE, execute.SPLIT, execute.PINNED = "P", QUEUES, PINNED


def check_manifest():
    stored = json.loads((HERE / "p_manifest.json").read_text())
    now = p_plan.manifest(os.environ.get("P1_NGSPICE", "/usr/bin/ngspice"),
                          Path(os.environ["MODELS"]) if os.environ.get("MODELS") else None)
    bad = [k for k in stored if stored[k] != now[k]]
    if bad:
        sys.exit("the manifest of stage P does not match the inputs: " + ", ".join(bad))
    scope = json.loads((HERE / "SCOPE_P.json").read_text())["scope"]
    if scope != stored["scope"]:
        sys.exit(f"the scope of SCOPE_P.json is {scope}; the queues are those of the scope {stored['scope']}")


def run_one(name):
    import p_run
    return p_run.one(name)


def preflight():
    """The nominal schematic run of execute.py, and what the harness needs on this machine: the
    preload that fixes the noise must build and must work, and numpy must be there. A machine that
    lacks one of them runs nothing: no run is then marked as started."""
    import subprocess
    import tempfile
    result = execute.stage_preflight()
    problems = []
    try:
        import numpy  # noqa: F401
    except ImportError:
        problems.append("numpy is missing")
    with tempfile.TemporaryDirectory() as d:
        so = Path(d) / "fakepid.so"
        src = HERE.parent.parent / "circuit" / "repetition" / "fakepid.c"
        try:
            subprocess.run(["gcc", "-shared", "-fPIC", "-O2", "-o", str(so), str(src)], check=True, capture_output=True)
            p = subprocess.run([os.environ.get("P1_NGSPICE", "/usr/bin/ngspice"), "--version"], capture_output=True, text=True,
                               env=dict(os.environ, LD_PRELOAD=str(so), FAKEPID="4242"))
            if p.returncode != 0:
                problems.append("the simulator does not start under the preload")
            p = subprocess.run(["sh", "-c", "echo $$"], capture_output=True, text=True, env=dict(os.environ, LD_PRELOAD=str(so), FAKEPID="4242"))
        except (OSError, subprocess.CalledProcessError) as e:
            problems.append(f"the preload does not build: {type(e).__name__}")
    if not os.access(HERE / "p_shim" / "ngspice", os.X_OK) or not Path("/usr/bin/python3").exists():
        problems.append("the shim cannot be executed")
    result["harness"] = "; ".join(problems) if problems else "ready"
    result["identical"] = bool(result["identical"]) and not problems
    return result


if __name__ == "__main__":
    args = sys.argv[1:]
    configure()
    if not args or args[0] == "plan":
        for m in ("A", "B"):
            print("machine", m, f"({len(QUEUES[m])} runs):", " ".join(QUEUES[m]))
    elif args[0] == "launch":
        machine = args[args.index("--machine") + 1] if "--machine" in args else ""
        execute.launch(machine, run_one=run_one, preflight=preflight, verify=check_manifest, go="--go" in args)
    else:
        sys.exit(__doc__)
