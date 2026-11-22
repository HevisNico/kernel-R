"""The family campaign's draw (PREDICTION.md section 1). Standard library only; no random generator.

  python3 draw.py        writes DRAW.json next to this file and prints the table

The seeds 8501..8515 are sorted by SHA-256("kernel-R family draw 1|" + str(seed)) (hex digest), and members are
assigned in the declared order X1, X2, F4, F2, F3, repeated. The only inputs are the seed list and the salt.
"""
import hashlib
import json
from pathlib import Path

SALT = "kernel-R family draw 1|"
SEEDS = list(range(8501, 8516))
MEMBERS = ["X1", "X2", "F4", "F2", "F3"]


def key(seed):
    return hashlib.sha256((SALT + str(seed)).encode("ascii")).hexdigest()


def draw():
    order = sorted(SEEDS, key=key)
    return {seed: MEMBERS[i % len(MEMBERS)] for i, seed in enumerate(order)}


if __name__ == "__main__":
    d = draw()
    out = dict(salt=SALT, seeds=SEEDS, members=MEMBERS,
               sorted=[dict(seed=s, sha256=key(s), member=d[s]) for s in sorted(SEEDS, key=key)],
               draw={str(s): d[s] for s in SEEDS},
               by_member={m: [s for s in SEEDS if d[s] == m] for m in MEMBERS})
    (Path(__file__).resolve().parent / "DRAW.json").write_text(json.dumps(out, indent=1) + "\n")
    for m in MEMBERS:
        print(m, ", ".join(str(s) for s in out["by_member"][m]))
