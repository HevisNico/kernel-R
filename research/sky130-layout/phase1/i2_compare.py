"""Comparisons of the identity test I2 (../AMENDMENT_1.md).

  i2_compare.py rows NAME RESULT.csv REFERENCE.csv
      I2 passes on a run if every FIRE flag, steering flag and count is identical, every time is
      identical, every stored voltage is within 2 uV and the lowest voltage of the main capacitor
      within 20 uV.
  i2_compare.py decks DECK.spice CAPS_A.csv CAPS_B.csv
      the two lists of capacitors, every value at 0 F, give the same deck (run in the folder of a
      run, where blocks.spice is).
"""
import csv
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

SAME = ["pulse", "port", "fired", "steered1", "steered2", "second_rise"]
TIMES = ["fire_latency", "reopen", "entry1", "exit1", "entry2", "exit2"]
STORED, LOWEST = ["vmem1", "vmem2"], "vq_min"
STORED_LIMIT, LOWEST_LIMIT = 2e-6, 20e-6


def rows(name, result, reference):
    with open(result, newline="") as fh:
        a = list(csv.DictReader(fh))
    with open(reference, newline="") as fh:
        b = list(csv.DictReader(fh))
    flags = len(a) == len(b) and all(x[k] == y[k] for x, y in zip(a, b) for k in SAME)
    times = len(a) == len(b) and all(x[k] == y[k] for x, y in zip(a, b) for k in TIMES)
    stored = max((abs(float(x[k]) - float(y[k])) for x, y in zip(a, b) for k in STORED), default=float("inf"))
    lowest = max((abs(float(x[LOWEST]) - float(y[LOWEST])) for x, y in zip(a, b)), default=float("inf"))
    step = max((abs(float(x[k]) - float(y[k])) for x, y in zip(a, b) for k in ("step1_mV", "step2_mV")), default=float("inf"))
    differ = sum(x != y for x, y in zip(a, b))
    ok = flags and times and stored <= STORED_LIMIT + 1e-12 and lowest <= LOWEST_LIMIT + 1e-12
    print(f"I2 {name}: {len(a)} rows against {len(b)}; rows that differ {differ}; flags and counts "
          f"{'identical' if flags else 'DIFFER'}; times {'identical' if times else 'DIFFER'}; "
          f"stored voltage within {stored * 1e6:.1f} uV (limit 2); lowest voltage of the main capacitor within "
          f"{lowest * 1e6:.1f} uV (limit 20); step within {step:.3f} mV: {'PASSES' if ok else 'FAILS'}")
    return ok


def decks(deck, caps_a, caps_b):
    import netlist
    text = open(deck).read()
    blocks = open("blocks.spice").read()
    a, _ = netlist.build(text, blocks, zero=True, caps=netlist.read_caps(caps_a))
    b, _ = netlist.build(text, blocks, zero=True, caps=netlist.read_caps(caps_b))
    print("the two lists at 0 F give " + ("the same deck" if a == b else "DIFFERENT decks"))
    return a == b


if __name__ == "__main__":
    ok = rows(*sys.argv[2:5]) if sys.argv[1] == "rows" else decks(*sys.argv[2:5])
    sys.exit(0 if ok else 1)
