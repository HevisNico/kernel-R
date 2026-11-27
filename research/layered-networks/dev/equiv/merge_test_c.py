"""Test (c) split over K07–K12 (RUNBOOK_C.md), a record helper: one TEST_C.json from the six machines' records.

  merge_test_c.py OUT.json COMMIT [REMOTE]

The case list is tests/test_campaign.py's at COMMIT. Fetches evidence/devtest-K07 … K12 by branch name from REMOTE (default: this clone's origin), reads each
c_K<nn>/TEST_C.json, COMMIT and envcheck.out, and writes OUT.json: every case once, with the machine it ran on.
Refuses (exit 1, nothing written) when a machine's COMMIT is not COMMIT, its envcheck is not ok or its checked values
("got") differ from another machine's, a case of tests/test_campaign.py is missing, or a case ran on two machines.
It changes nothing and is not part of the campaign's code.
"""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parents[2]
MACHINES = [f"K{k:02d}" for k in range(7, 13)]


def cases_of_test_c(commit=None):
    """The case names tests/test_campaign.py's main() runs, in order, at COMMIT (default: the working tree)."""
    text = (HERE / "tests" / "test_campaign.py").read_text() if commit is None else git(
        "show", f"{commit}:research/layered-networks/tests/test_campaign.py", cwd=HERE).stdout.decode()
    main = text[text.index("def main(wd, *only):"):]
    return re.findall(r'run\("([a-z0-9_]+)"', main)


def git(*a, cwd):
    return subprocess.run(["git", *a], cwd=cwd, check=True, capture_output=True)


def main(out, commit, remote=None):
    remote = remote or git("remote", "get-url", "origin", cwd=HERE).stdout.decode().strip()
    want = cases_of_test_c(commit)
    merged, machines, bad = {}, {}, []
    with tempfile.TemporaryDirectory() as w:
        git("init", "-q", cwd=w)
        for m in MACHINES:
            git("fetch", "-q", remote, f"refs/heads/evidence/devtest-{m}", cwd=w)
            tip = git("rev-parse", "FETCH_HEAD", cwd=w).stdout.decode().strip()
            show = lambda f: git("show", f"FETCH_HEAD:c_{m}/{f}", cwd=w).stdout
            c = show("COMMIT").decode().strip()
            env = json.loads(show("envcheck.out"))
            tc = json.loads(show("TEST_C.json"))
            got = {k: v.get("got") for k, v in sorted((env.get("checks") or {}).items())}
            machines[m] = dict(branch=f"evidence/devtest-{m}", tip=tip, commit=c, envcheck_ok=env.get("ok"),
                               envcheck_got_sha256=hashlib.sha256(json.dumps(got, sort_keys=True).encode()).hexdigest(),
                               test_c_sha256=hashlib.sha256(show("TEST_C.json")).hexdigest(), all_pass=tc.get("all_pass"))
            if c != commit:
                bad.append(f"{m}: commit {c}, not {commit}")
            if env.get("ok") is not True:
                bad.append(f"{m}: envcheck not ok")
            for name, v in tc.items():
                if not isinstance(v, dict):
                    continue
                if name in merged:
                    bad.append(f"{name}: run on {merged[name]['machine']} and {m}")
                merged[name] = dict(v, machine=m)
    if len({x["envcheck_got_sha256"] for x in machines.values()}) != 1:
        bad.append("the machines' envcheck values differ: " + json.dumps({m: x["envcheck_got_sha256"][:12] for m, x in machines.items()}))
    missing = [c for c in want if c not in merged]
    extra = [c for c in merged if c not in want]
    if missing or extra:
        bad.append(f"cases missing {missing}, not of test (c) {extra}")
    if bad:
        print("REFUSED: " + "; ".join(bad))
        return False
    report = {k: merged[k] for k in want}
    report.update(all_pass=all(v["ok"] for v in report.values()), merged=dict(
        format="layered-test-c-merge/1", commit=commit, machines=machines, cases=len(want),
        script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()))
    Path(out).write_text(json.dumps(report, indent=1, sort_keys=True) + "\n")
    print(f"{sum(1 for k in want if report[k]['ok'])} of {len(want)} cases pass; all_pass {report['all_pass']}")
    return report["all_pass"]


if __name__ == "__main__":
    sys.exit(0 if main(*sys.argv[1:]) else 1)
