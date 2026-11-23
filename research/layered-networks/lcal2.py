"""Driver of the calibration instrument with a versioned config overlay. Development only.

  lcal2.py run    SPEC OUT SEED [solo=1] [overlay=config_inverter_c5.json]
  lcal2.py scores SPEC OUT

lcal.py's `run`, with config.json's entries replaced by those of an overlay file (default config_inverter_c5.json:
the C5 inverter). New file: lcal.py, config.json and instrument.py stay as pushed. The run records the overlay used in
OUT/overlay.json.
"""
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import spec as specmod  # noqa: E402

DEFAULT_OVERLAY = "config_inverter_c5.json"
OVERLAY_KEYS = ("inverter",)


def config(overlay=DEFAULT_OVERLAY):
    """config.json with the overlay's entries (only OVERLAY_KEYS) put in place."""
    cfg = json.loads((HERE / "config.json").read_text())
    ov = json.loads((HERE / overlay).read_text())
    extra = set(ov) - set(OVERLAY_KEYS) - {"what", "source"}
    if extra:
        raise ValueError(f"overlay {overlay}: unexpected entries {sorted(extra)}")
    for k in OVERLAY_KEYS:
        if k in ov:
            cfg[k] = ov[k]
    return cfg, ov


def cmd_run(spec_path, out, seed, *flags):
    import instrument
    import scores
    solo = "solo=1" in flags
    overlay = next((f.split("=", 1)[1] for f in flags if f.startswith("overlay=")), DEFAULT_OVERLAY)
    cfg, ov = config(overlay)
    Path(out).mkdir(parents=True, exist_ok=True)
    (Path(out) / "overlay.json").write_text(json.dumps(dict(file=overlay, **ov), indent=1) + "\n")
    r = instrument.cal_run(specmod.load(spec_path), cfg, out, int(seed), solo=solo)
    print(json.dumps(dict(status=r["status"], cost=r["cost"], words=r["words"]), indent=1))
    scores.main(spec_path, out)
    return r["status"] == "done"


if __name__ == "__main__":
    cmd, *args = sys.argv[1:]
    if cmd == "run":
        sys.exit(0 if cmd_run(*args) else 1)
    elif cmd == "scores":
        import scores
        scores.main(*args)
    else:
        sys.exit(__doc__)
