"""The versioned stage-N entry point of the campaign pipeline: noise3's stage N (noise2's R-cell noise, the C5
inverters' budgeted noise, controls2's skew slots) and controls2's untrained run, each refusing to start without a
seal-log commit, which it records inside its record. Development only. New file.

  controls3.py stagen    SPEC OUT SEED ROUND seal_log=<40-hex> seal_branch=<branch> [scale=1] [overlay=FILE]
  controls3.py untrained SPEC OUT SEED       seal_log=<40-hex> seal_branch=<branch> [overlay=FILE]

Refusal: when seal_log is absent or is not 40 lowercase hexadecimal characters, or seal_branch is absent or empty, the
command prints why and exits with status 2 before any simulator session starts (OUT is not created).
Record: OUT/noisy_record.json (stagen) or OUT/untrained_record.json (untrained), each with a top-level
"seal_log": {"commit": <40-hex>, "branch": <branch>}. A duplicate (identity rerun) passes the original's seal_log, so
the two records stay identical under tests/check_duplicate.py.
The commit is recorded as given; that it is pushed and is the run's seal is the pipeline driver's check
(campaign_run.py, research/layered-stage-d).
"""
import json
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

HEX40 = re.compile(r"[0-9a-f]{40}")


def seal(kw):
    c, b = kw.get("seal_log"), kw.get("seal_branch")
    if c is None or not HEX40.fullmatch(c):
        return None, f"refused: seal_log must be a 40-character lowercase hexadecimal commit, got {c!r}"
    if not b:
        return None, "refused: seal_branch is required"
    return dict(commit=c, branch=b), None


def main(argv):
    if not argv or argv[0] not in ("stagen", "untrained"):
        print(__doc__)
        return 2
    cmd, *a = argv
    kw = dict(x.split("=", 1) for x in a if "=" in x)
    pos = [x for x in a if "=" not in x]
    s, why = seal(kw)
    if why:
        print(why)
        return 2
    if cmd == "stagen":
        if len(pos) != 4:
            print("refused: stagen needs SPEC OUT SEED ROUND")
            return 2
        import noise3
        r = noise3.stagen(*pos, scale=float(kw.get("scale", 1)), overlay=kw.get("overlay"), extra=dict(seal_log=s))
        print(json.dumps(dict(status=r["status"], noise_seed=r["noise_seed"], seal_log=r["seal_log"], cost=r["cost"]), indent=1))
        return 0 if r["status"] == "done" else 1
    if len(pos) != 3:
        print("refused: untrained needs SPEC OUT SEED")
        return 2
    import controls2
    r = controls2.untrained(*pos, overlay=kw.get("overlay"))
    r["seal_log"] = s
    (Path(pos[1]) / "untrained_record.json").write_text(json.dumps(r, indent=1, default=str) + "\n")
    print(json.dumps(dict(status=r["status"], seal_log=s, cost=r["cost"]), indent=1))
    return 0 if r["status"] == "done" else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
