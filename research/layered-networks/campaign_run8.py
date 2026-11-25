"""campaign_run7.py with the top-level SHA256SUMS written last (the defect K07 found at verify, 2026-11-25).
Development only. campaign_run7.py and the earlier drivers are kept as they are.

The defect: campaign_run2.cmd_run writes RESULT.json and hashes it into OUTROOT/SHA256SUMS. Then the wrappers add keys
to RESULT.json after that: campaign_run3 adds `core_budget`, campaign_run4 adds `remote_duplicates` and campaign_run5
adds `stopped_for_disk`. `campaign_run.py verify OUTROOT` then prints "BROKEN: RESULT.json". No other file is
affected: the per-instance SHA256SUMS are written before, and nothing rewrites them.

The fix: once campaign_run7.cmd_run has returned (every post-write done), OUTROOT/SHA256SUMS is written again over
campaign_run2's list. That is */SHA256SUMS, RESULT.json, PLAN.json, trees.json, DUP_*/duplicate.json and
U_*/untrained.json, plus DUPX_*/duplicate_here.json (campaign_run4's remote duplicates, written after campaign_run2's
list was made). The previous top-level sums are kept as SHA256SUMS.pre_post_writes. The difference between the two
files is then only the RESULT.json line, and the new DUPX lines.

  campaign_run8.py launch | run | wait | status ...     as campaign_run7.py
  campaign_run8.py rehash OUTROOT                        the rewrite alone, on a finished OUTROOT
"""
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import campaign_run as CR  # noqa: E402
import campaign_run2 as C2  # noqa: E402
import campaign_run7 as C7  # noqa: E402


def top_files(root):
    root = Path(root)
    files = sorted(p for p in root.glob("*/SHA256SUMS")) + [root / "RESULT.json", root / "PLAN.json", root / "trees.json"]
    files += sorted(root.glob("DUP_*/duplicate.json")) + sorted(root.glob("U_*/untrained.json"))
    files += sorted(root.glob("DUPX_*/duplicate_here.json"))
    return [p for p in files if p.exists()]


def rewrite_top_sums(root):
    root = Path(root)
    sums = root / "SHA256SUMS"
    if not sums.exists():                          # campaign_run2 did not reach its end: nothing to rewrite
        return False
    pre = root / "SHA256SUMS.pre_post_writes"
    if not pre.exists():
        pre.write_bytes(sums.read_bytes())
    sums.write_text("".join(f"{CR.sha(p)}  {p.relative_to(root)}\n" for p in top_files(root)))
    return True


def cmd_run(plan_path, root, *rest):
    try:
        return C7.cmd_run(plan_path, root, *rest)
    finally:
        rewrite_top_sums(root)


def cmd_launch(plan_path, root, *rest):
    import subprocess
    root = Path(root).resolve()
    n = subprocess.run(["pgrep", "-c", "ngspice"], capture_output=True, text=True).stdout.strip()
    if n not in ("", "0"):
        raise SystemExit(f"refused: {n} ngspice process(es) running")
    if root.exists() and any(root.iterdir()):
        raise SystemExit(f"refused: {root} exists and is not empty (no run folders before a launch)")
    plan = json.loads(Path(plan_path).read_text())
    root.mkdir(parents=True, exist_ok=True)
    (root / "INVENTORY_START").write_text(C2.inventory(plan))
    log = (root / "driver.log").open("w")
    p = subprocess.Popen(["nohup", CR.PY, "-B", str(HERE / "campaign_run8.py"), "run", str(Path(plan_path).resolve()),
                          str(root), *rest], stdout=log, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL,
                         start_new_session=True, cwd=HERE)
    (root / "DRIVER_PID").write_text(f"{p.pid}\n")
    print(f"launched pid {p.pid}")
    return True


if __name__ == "__main__":
    c, *a = sys.argv[1:] or ["help"]
    if c == "run":
        sys.exit(0 if cmd_run(*a) else 1)
    elif c == "launch":
        sys.exit(0 if cmd_launch(*a) else 1)
    elif c == "wait":
        sys.exit(0 if C2.cmd_wait(*a) else 3)
    elif c == "status":
        C2.cmd_status(*a)
    elif c == "rehash":                            # an already finished OUTROOT (keeps SHA256SUMS.pre_post_writes)
        sys.exit(0 if rewrite_top_sums(*a) else 1)
    else:
        sys.exit(__doc__)
