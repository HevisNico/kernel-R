"""Launcher of the campaign, with exit statuses checked.

campaign.py holds the list of runs and the launcher that ran the campaign. It is kept byte for byte
as recorded in PREDICTION_PROVENANCE.md. Its launcher does not read the exit status of a run and
always ends with status 0. This one uses the same list and the same command for each run, records
a run whose command fails as failed, and ends with a status that is not zero when a run fails.

  python3 launch.py        (from research/circuit)
"""
import os, subprocess, sys
from concurrent.futures import ThreadPoolExecutor

from campaign import LIMIT_S, jobs


def run(j):
    name, mode, sec, opts = j
    if os.path.exists(f"results/{name}.csv") or os.path.exists(f"results/{name}.failed"):
        return f"{name} already there"
    try:
        p = subprocess.run([sys.executable, "-I", "run.py", mode, name, sec] + opts, capture_output=True, text=True, timeout=LIMIT_S)
    except subprocess.TimeoutExpired:
        subprocess.run(["pkill", "-f", f"ngspice -b work/{name}.spice"])
        with open(f"results/{name}.failed", "w") as fh:
            fh.write("stopped at the time limit\n")
        out = f"{name} FAILED time limit"
    else:
        out = (p.stdout.strip().splitlines() or [name + " NO OUTPUT"])[-1]
        if p.returncode != 0:
            if not os.path.exists(f"results/{name}.failed"):
                tail = "\n".join(p.stderr.strip().splitlines()[-20:])
                with open(f"results/{name}.failed", "w") as fh:
                    fh.write(f"run.py exited with status {p.returncode}\n{tail}\n")
            out = f"{name} FAILED exit status {p.returncode}"
    print(out, flush=True)
    return out


def main(plan=jobs):
    """Run the plan. The exit status is not zero when a run fails."""
    with ThreadPoolExecutor(os.cpu_count() or 4) as ex:
        out = list(ex.map(run, plan))
    failed = sum("FAILED" in o or "NO OUTPUT" in o for o in out)
    print(len(out), "runs,", failed, "failed")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
