"""Launcher of the repetition campaign. Ends with a status that is not zero when a run fails.

  rep_launch.py STAGE          every run of the stage, in the order of manifest.json
  rep_launch.py repeat REP     the runs of repetition REP

One run per processor at a time. A run that already has a result or a failure is not run again.
"""
import json
import os
from pathlib import Path
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import rep_run


def main():
    stage = sys.argv[1]
    runs = json.loads((HERE / "manifest.json").read_text())["stages"][stage]
    if len(sys.argv) > 2:
        runs = [r for r in runs if r["rep"] == int(sys.argv[2])]

    def one(run):
        p = subprocess.run([sys.executable, "-B", str(HERE / "rep_run.py"), stage, run["name"]], capture_output=True, text=True)
        line = (p.stdout.strip().splitlines() or [run["name"] + " NO OUTPUT"])[-1]
        folder = rep_run.folders(stage, run)[0]
        if p.returncode != 0 and not (folder / f"{run['name']}.failed").exists():
            folder.mkdir(parents=True, exist_ok=True)
            (folder / f"{run['name']}.failed").write_text(f"rep_run.py exited with status {p.returncode}\n" + p.stderr[-3000:])
            line = f"{run['name']} FAILED exit status {p.returncode}"
        print(line, flush=True)

    with ThreadPoolExecutor(os.cpu_count() or 4) as ex:
        list(ex.map(one, runs))
    failed = [r["name"] for r in runs if (rep_run.folders(stage, r)[0] / f"{r['name']}.failed").exists()]
    missing = [r["name"] for r in runs if not (rep_run.folders(stage, r)[0] / f"{r['name']}.json").exists() and r["name"] not in failed]
    print(len(runs), "runs,", len(failed), "failed,", len(missing), "without a result")
    return 1 if failed or missing else 0


if __name__ == "__main__":
    sys.exit(main())
