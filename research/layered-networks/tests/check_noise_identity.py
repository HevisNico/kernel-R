"""Identity checks of the noise path (noise2.py). No simulation: it compares records.

  check_noise_identity.py same A B        A and B are noisy_record.json folders: every field equal except EXCEPT
  check_noise_identity.py pipeline A REC  A's training and test slots equal to the same slots of an instrument record
                                          (REC/record.json, the pipeline without noise), field for field

EXCEPT, fixed before the checks: cost (wall and CPU times), round, noise_seed, noise_scale and input_spice_sha256
(the deck's noise source lines carry the trnoise amplitudes, zero or not; the rest of the deck is compared line by
line, except those lines).
"""
import json
from pathlib import Path
import sys

EXCEPT = ("cost", "round", "noise_seed", "noise_scale", "input_spice_sha256")


def deck_lines(d):
    return [l for l in (Path(d) / "input.spice").read_text().splitlines()
            if not any(f".{n} " in l for n in ("vnzc", "vnzo", "vnzi", "vnzm"))]


def same(a, b):
    ra = json.loads((Path(a) / "noisy_record.json").read_text())
    rb = json.loads((Path(b) / "noisy_record.json").read_text())
    diffs = [k for k in sorted(set(ra) | set(rb)) if k not in EXCEPT and ra.get(k) != rb.get(k)]
    deck = deck_lines(a) == deck_lines(b)
    first = None
    if "slots" in diffs:
        first = next((i for i, (x, y) in enumerate(zip(ra["slots"], rb["slots"])) if x != y), min(len(ra["slots"]), len(rb["slots"])))
    ok = not diffs and deck
    print(f"{a} vs {b}: fields differing (outside EXCEPT): {diffs or 'none'}; deck outside noise lines equal: {deck}"
          + (f"; first differing slot {first}" if first is not None else ""))
    return ok


def pipeline(a, rec_dir):
    ra = json.loads((Path(a) / "noisy_record.json").read_text())
    rp = json.loads((Path(rec_dir) / "record.json").read_text())
    n = len(ra["slots"])
    slots = ra["slots"] == rp["slots"][:n]
    words = ra["words"] == rp["words"]
    tests = ra["tests"] == rp["tests"] and ra["lessons"] == rp["lessons"]
    first = None if slots else next((i for i, (x, y) in enumerate(zip(ra["slots"], rp["slots"])) if x != y), n)
    print(f"{a} vs {rec_dir} (first {n} slots): slots equal {slots}, words equal {words}, lessons and tests equal {tests}"
          + ("" if slots else f"; first differing slot {first}"))
    return slots and words and tests


if __name__ == "__main__":
    cmd, x, y = sys.argv[1:4]
    sys.exit(0 if (same(x, y) if cmd == "same" else pipeline(x, y)) else 1)
