"""Driver of the calibration instrument (M2). Development only.

  lcal.py run    SPEC OUT SEED     train, test every pattern, then the scans, in one session (OUT/record.json),
                                   then the score readout (OUT/scores.json)
  lcal.py scores SPEC OUT          the score readout of an existing record
  lcal.py test                     the tests (no simulation)

A new driver beside lnet.py: the pushed lnet.py is not modified (owner rule). It uses the same config.json, plus
calibration.json.
"""
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import spec as specmod  # noqa: E402

CFG = json.loads((HERE / "config.json").read_text())


def cmd_run(spec_path, out, seed):
    import instrument
    import scores
    r = instrument.cal_run(specmod.load(spec_path), CFG, out, int(seed))
    print(json.dumps(dict(status=r["status"], cost=r["cost"], words=r["words"]), indent=1))
    scores.main(spec_path, out)
    return r["status"] == "done"


def cmd_scores(spec_path, out):
    import scores
    scores.main(spec_path, out)


def cmd_test():
    return subprocess.run([sys.executable, "-B", str(HERE / "tests" / "test_cal.py")]).returncode == 0


if __name__ == "__main__":
    a = sys.argv[1:]
    r = dict(run=cmd_run, scores=cmd_scores, test=cmd_test)[a[0]](*a[1:])
    sys.exit(0 if r in (None, True) else 1)
