"""stage_d4.py with the environment's provenance in the sealed prediction (coordinator, 2026-11-24). Development only.

  stage_d5.py run | predict | deck | seal | verify ...     as stage_d4.py

stage_d4.py is pushed and kept as it is. The prediction record gets `env_sha256`: the sha256 of the OUTROOT's ENV.json
(envcheck_layered.py env), given by the driver in the environment variable LAYERED_ENV_SHA256, or null when run by hand.
The seal (one file per instance) therefore carries it.
"""
import json
import os
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import stage_d  # noqa: E402
import stage_d3  # noqa: E402
import stage_d4  # noqa: E402,F401  (replaces stage_d.read_masks and stage_d3.stamp)

_stamp = stage_d3.stamp


def stamp(out, rule):
    _stamp(out, rule)
    p = json.loads((Path(out) / "prediction.json").read_bytes())
    p["env_sha256"] = os.environ.get("LAYERED_ENV_SHA256")
    p["code"]["stage_d5.py"] = stage_d.sha256_file(HERE / "stage_d5.py")
    (Path(out) / "prediction.json").write_bytes(stage_d.canon(p))
    return p


stage_d3.stamp = stamp

if __name__ == "__main__":
    sys.exit(0 if stage_d3.main(sys.argv[1:]) else 1)
