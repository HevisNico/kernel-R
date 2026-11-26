"""The zero-amplitude identity, version 2: the owner's criterion of 2026-11-25 (defect 4 of the pre-freeze dry run).
No simulation. tests/check_noise3_identity.py (controls tree) is kept as it is.

  check_noise_identity2.py OFF ZERO

OFF is round 0 (noise off). ZERO is a noisy round at scale=0: every noise source present, at zero amplitude. Each folder
holds noisy_record.json and input.spice.

CRITERION (all must hold; exit 0 iff they do):
1. The decks are equal line for line once the noise lines are removed. The noise lines are: the R cells'
   vnzc/vnzo/vnzi/vnzm; the inverters' vnzm; and noise3's added lines (vkw*, vnzh*, rnzh*, vnzj*, rnzj*, bnz*, and its
   comment line), as in check_noise3_identity.py.
2. Equal outcomes: words, lessons, tests and skews equal, the same number of slots, and every routed emission equal
   (R-cell reads and inverter reads, slot by slot).
3. Every stored voltage u equal to within ±1 in the record's last digit. The record prints u to 7 decimals
   (1e-7 V), and that resolution is checked: every u must be a multiple of 1e-7 V to within 1e-12 V. The bound is
   |u_zero - u_off| <= 1e-7 V + 1e-12 V. A difference of two or more digits fails.

LISTED, NOT JUDGED: every u that differs (slot, kind, cell, port, both values); every latch date that differs (slot,
read, both dates, the shift in ns); every inverter x reading that differs (slot, inverter, field, both values).
Every difference is printed, whether it is judged or not.
"""
import json
from pathlib import Path
import sys

NOISE_NAMES = (".vnzc ", ".vnzo ", ".vnzi ", ".vnzm ")
ADDED = ("vkw", "vnzh", "rnzh", "vnzj", "rnzj", "bnz", "* the two mirrors' shot noise")
DIGIT = 1e-7
EPS = 1e-12


def deck(d):
    return [l for l in (Path(d) / "input.spice").read_text().splitlines()
            if not any(n in l for n in NOISE_NAMES) and not l.startswith(ADDED)]


def on_grid(u):
    return abs(u / DIGIT - round(u / DIGIT)) * DIGIT <= EPS


def main(off, zero):
    a = json.loads((Path(off) / "noisy_record.json").read_text())
    b = json.loads((Path(zero) / "noisy_record.json").read_text())
    ok = True
    same_deck = deck(off) == deck(zero)
    print(f"1. decks equal outside the noise lines: {same_deck}")
    ok &= same_deck
    for k in ("words", "lessons", "tests", "skews"):
        e = a.get(k) == b.get(k)
        print(f"2. {k}: {'equal' if e else 'DIFFER'}")
        ok &= e
    n_slots = len(a["slots"]) == len(b["slots"])
    print(f"2. slots: {len(a['slots'])} and {len(b['slots'])}")
    ok &= n_slots
    em, du, off_grid, lat, n_u = [], [], [], [], 0
    for i, (x, y) in enumerate(zip(a["slots"], b["slots"])):
        for c in x["u"]:
            for p in (0, 1):
                u, v = x["u"][c][p], y["u"][c].__getitem__(p) if c in y["u"] else None
                if u is None and v is None:
                    continue
                n_u += 1
                if u is None or v is None:
                    du.append((i, x.get("kind"), c, p, u, v, None))
                    continue
                for w in (u, v):
                    if not on_grid(w):
                        off_grid.append((i, c, p, w))
                if u != v:
                    du.append((i, x.get("kind"), c, p, u, v, abs(u - v)))
        for j, (r, s) in enumerate(zip(x["reads"] + x.get("inv", []), y["reads"] + y.get("inv", []))):
            if r.get("emission") != s.get("emission"):
                em.append((i, j, r.get("emission"), s.get("emission")))
            if r.get("latch") != s.get("latch"):
                lat.append((i, j, r.get("latch"), s.get("latch")))
    print(f"2. emissions differing: {len(em)}")
    for e in em:
        print(f"   slot {e[0]} read {e[1]}: {e[2]} against {e[3]}")
    ok &= not em
    beyond = [d for d in du if d[6] is None or d[6] > DIGIT + EPS]
    print(f"3. u values: {n_u}; differing: {len(du)}; beyond ±1 in the last digit (1e-7 V): {len(beyond)}; "
          f"not on the 1e-7 V grid: {len(off_grid)}")
    for d in du:
        print(f"   slot {d[0]} {d[1]} {d[2]} port {d[3]}: {d[4]!r} against {d[5]!r}"
              + ("" if d[6] is None else f" ({d[6] / DIGIT:.3f} digit)"))
    for g in off_grid:
        print(f"   NOT ON THE GRID: slot {g[0]} {g[1]} port {g[2]}: {g[3]!r}")
    ok &= not beyond and not off_grid
    print(f"listed: latch dates differing: {len(lat)}")
    for l_ in lat:
        sh = "" if l_[2] is None or l_[3] is None else f" (shift {l_[3] - l_[2]} ns)"
        print(f"   slot {l_[0]} read {l_[1]}: {l_[2]} against {l_[3]}{sh}")
    dx = [(i, k, f, p[k][f], q[k][f]) for i, (p, q) in enumerate(zip(a.get("inverter_x", []), b.get("inverter_x", [])))
          for k in p if k in q for f in ("x_tau", "x_D") if f in p[k] and f in q[k] and p[k][f] != q[k][f]]
    print(f"listed: inverter x readings differing: {len(dx)}"
          + (f", max |difference| {max(abs(d[3] - d[4]) for d in dx):.5f} x" if dx else ""))
    for d in dx:
        print(f"   slot {d[0]} {d[1]} {d[2]}: {d[3]!r} against {d[4]!r}")
    print("ZERO-NOISE IDENTITY (v2) PASS" if ok else "ZERO-NOISE IDENTITY (v2) FAIL")
    return ok


if __name__ == "__main__":
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    sys.exit(0 if main(sys.argv[1], sys.argv[2]) else 1)
