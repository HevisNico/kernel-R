"""Launcher of one stage of the certification campaign. Ends with a status that is not zero when a run fails.

  cert_launch.py STAGE [FIRST LAST]

Runs the runs FIRST to LAST (from 0, LAST excluded) of the stage, in the order of manifest.json, four at a
time. A run that already has a result or a failure is not run again.
"""
import json
import os
from pathlib import Path
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor

HERE = Path(__file__).resolve().parent


def main():
    stage = sys.argv[1]
    runs = json.loads((HERE / "manifest.json").read_text())["stages"][stage]
    if len(sys.argv) > 2:
        runs = runs[int(sys.argv[2]):int(sys.argv[3])]

    def one(run):
        p = subprocess.run([sys.executable, "-B", str(HERE / "cert_run.py"), stage, run["name"]], capture_output=True, text=True)
        out = (p.stdout.strip().splitlines() or [run["name"] + " NO OUTPUT"])[-1]
        folder = HERE / "results" / stage
        if p.returncode != 0 and not (folder / f"{run['name']}.failed").exists():
            folder.mkdir(parents=True, exist_ok=True)
            (folder / f"{run['name']}.failed").write_text(f"cert_run.py exited with status {p.returncode}\n" + p.stderr[-3000:])
            out = f"{run['name']} FAILED exit status {p.returncode}"
        print(out, flush=True)
        return out

    with ThreadPoolExecutor(os.cpu_count() or 4) as ex:
        list(ex.map(one, runs))
    failed = [r["name"] for r in runs if (HERE / "results" / stage / f"{r['name']}.failed").exists()]
    missing = [r["name"] for r in runs if not (HERE / "results" / stage / f"{r['name']}.json").exists() and r["name"] not in failed]
    print(len(runs), "runs,", len(failed), "failed,", len(missing), "without a result")
    return 1 if failed or missing else 0


if __name__ == "__main__":
    sys.exit(main())
