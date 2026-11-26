"""stage_d.py under a selected testError rule for the either cell (fit3.py; DECISIONS_3.md). Development only.

  stage_d3.py run     SPEC OUT SEED [rule=one-port|max] [stage_d.py's flags]
  stage_d3.py predict SPEC OUT [rule=one-port|max] [inverters=...]
  stage_d3.py deck | seal | verify ...          as stage_d.py

stage_d.py is pushed and kept as it is. Here its `run` and `predict` run inside `fit3.rule(rule)` (default one-port,
the rule for the claims), and the prediction record gets `testError_rule` and the format
layered-stage-d-prediction/2, written in the same canonical bytes.
"""
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import fit3  # noqa: E402
import stage_d  # noqa: E402

FORMAT = "layered-stage-d-prediction/2"


def stamp(out, rule):
    p = json.loads((Path(out) / "prediction.json").read_bytes())
    p.update(format=FORMAT, testError_rule=rule)
    p["code"]["fit3.py"] = stage_d.sha256_file(HERE / "fit3.py")
    p["code"]["stage_d3.py"] = stage_d.sha256_file(HERE / "stage_d3.py")
    (Path(out) / "prediction.json").write_bytes(stage_d.canon(p))
    return p


def main(argv):
    cmd, *a = argv or ["help"]
    rule = next((x.split("=", 1)[1] for x in a if x.startswith("rule=")), "one-port")
    a = [x for x in a if not x.startswith("rule=")]
    if cmd in ("run", "predict"):
        with fit3.rule(rule):
            ok = stage_d.cmd_run(*a) if cmd == "run" else (stage_d.cmd_predict(*a) or True)
        p = stamp(a[1], rule)
        print(json.dumps(dict(testError_rule=rule, eligible_K0=p["eligible_K0"], room_K3=p["room_K3"])))
        return ok
    if cmd == "deck":
        stage_d.cmd_deck(*a)
        return True
    if cmd in ("seal", "verify"):
        import seal
        return getattr(seal, cmd)(*a)
    sys.exit(__doc__)


if __name__ == "__main__":
    sys.exit(0 if main(sys.argv[1:]) else 1)
