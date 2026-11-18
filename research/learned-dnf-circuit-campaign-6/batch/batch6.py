"""Campaign 6's development batch (BATCH_SPEC.md): its constants, its seed guard, its limits, and its calibration
runner. New code; it imports campaign 5's frozen modules and edits none.

  batch6.py cal OUT SEED|none on|off NGSPICE PDK        one of campaign 5's two calibration decks on one instance

The calibration run is campaign 5's `run4.py --kind cal` path, called through the same frozen functions
(`plans4.calibration`, `net.deck`, `session4.play`, `run4.trnoise_fingerprint`), writing the same deck and the same
record, key for key, plus one key `batch` (test_batch.Equivalence shows it without a simulator). `run4.py`
itself cannot be run on these seeds: its seed guard accepts only campaign 5's seeds. This file's guard accepts only
7701 to 7710, plus the nominal cell (`none`) for the declared smokes.
"""
from fractions import Fraction as F
import hashlib
import json
import math
from pathlib import Path
import resource
import sys
import time

HERE = Path(__file__).resolve().parent
C5 = HERE.parent.parent / "learned-dnf-circuit-campaign-5"
sys.path.insert(0, str(C5))
import c4                                               # noqa: E402  (campaign 5, frozen)

SEEDS = tuple(range(7701, 7711))                        # the stopping rule: exactly these ten, never extended
MACHINE_OF = {s: ("a" if s <= 7705 else "b") for s in SEEDS}
DELTAS = (F(1, 4), F(1, 2))                             # the ascent step: 1/4 for option B, 1/2 for option C
CAP_S = 3580
EXPECTED_S = dict(cal=925, scan=785, onesided=250)      # BATCH_SPEC.md section 1
MISMATCH = F(151, 100)                                  # the stopping rule's factor for mismatch, applied to the smokes


def require_debug():
    if not __debug__:
        raise SystemExit("refused: the batch does not run with optimisation (python -O or PYTHONOPTIMIZE): its guards are asserts")


def guard_seed(text):
    """7701 to 7710, or `none` (the nominal cell, for the declared smokes only). Every other seed is refused."""
    if text == "none":
        return None
    seed = int(text)
    assert seed in SEEDS, f"refused: seed {seed} is not one of the batch's 7701 to 7710"
    return seed


def limit_s(kind):
    """min(10 ceil(3 e / 10), 3 580) s, exactly (BATCH_SPEC.md section 1)."""
    return min(10 * math.ceil(F(3 * EXPECTED_S[kind]) / 10), CAP_S)


def run_header(seed, cell, kind):
    return dict(batch="learned-dnf-circuit-campaign-6 development batch", seed=seed, machine=MACHINE_OF.get(seed), cell=cell, kind=kind,
                interpreter=c4.interpreter())


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def cal(out, seed, guard, ngspice, pdk):
    """Campaign 5's calibration deck on one instance, as run4.run's cal branch."""
    import plans4
    import run4
    import session4
    from session4 import net
    began = time.time()
    out = Path(out)
    section = "tt" if seed is None else c4.SECTION
    plan, reads = plans4.calibration()
    text = net.deck(cells=c4.CELLS, section=section)
    result, tr = session4.play(out / "evidence", plan, text, ngspice, pdk, seed=seed, guard_off=guard == "off")
    (out / "evidence" / "pdk").unlink()
    reached = bool(tr.t[-1] >= result["horizon_s"] - 1e-9)
    mark = run4.trnoise_fingerprint(tr, c4.CELLS)
    ev = out / "evidence"
    rec = dict(id=out.name, kind="cal", section=section, seed=seed, stage=None, guard=guard, reads=reads)     # run4.run's order
    rec.update(noise=dict(model="none"), reached_its_last_date=reached, horizon_s=result["horizon_s"], waveform_ends_s=result["waveform_ends_s"],
               points=result["points"], files={x: sha(ev / x) for x in ("input.spice", "session.log", "trace.raw", "result.json")})
    rec.update(noise_fingerprint=mark, wall_s=time.time() - began, peak_rss_MB=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss / 1024)
    rec["batch"] = run_header(seed, None, f"cal-{guard}")                                                   # the only added key
    (out / "noise.sha256").write_text(mark + "\n")
    (out / "record.json").write_text(json.dumps(rec, indent=1) + "\n")
    assert reached, "the waveform ends before the last date of the run"
    return rec


def main(argv=None):
    a = sys.argv[1:] if argv is None else argv
    require_debug()
    assert a[0] == "cal", __doc__
    seed = guard_seed(a[2])
    print(c4.require_pinned())
    assert a[3] in ("on", "off")
    rec = cal(Path(a[1]), seed, a[3], Path(a[4]), Path(a[5]))
    print(json.dumps(dict(id=rec["id"], reached_its_last_date=rec["reached_its_last_date"], wall_s=round(rec["wall_s"]))))


if __name__ == "__main__":
    main()
