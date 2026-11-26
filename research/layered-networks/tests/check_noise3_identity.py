"""Zero-amplitude identity of noise3.py against the no-noise path. No simulation: it compares two noisy_record.json
folders, OFF (round 0, the pushed deck) and ZERO (a noisy round with scale=0: every noise source present, at zero).

  check_noise3_identity.py OFF ZERO

1. The decks are equal line for line once the noise lines are removed: the R cells' vnzc/vnzo/vnzi/vnzm, the
   inverters' vnzm, and noise3's added lines (vkw*, vnzh*, rnzh*, vnzj*, rnzj*, bnz*, and its comment line).
2. The records: every stored voltage u, every routed emission, every word, lesson, test and skew equal. The latch
   dates and the inverter x readings may differ, and every difference is listed: the added sources add time points
   (the trnoise grid of 0.4 us, the window edges), which move a latch's interpolated crossing by a few ns, and x is
   read by interpolation between time points up to 200 ns apart.
Exit 0 iff 1 holds and every u, emission, word, lesson, test and skew is equal.
"""
import json
from pathlib import Path
import sys

NOISE_NAMES = (".vnzc ", ".vnzo ", ".vnzi ", ".vnzm ")
ADDED = ("vkw", "vnzh", "rnzh", "vnzj", "rnzj", "bnz", "* the two mirrors' shot noise")


def deck(d):
    return [l for l in (Path(d) / "input.spice").read_text().splitlines()
            if not any(n in l for n in NOISE_NAMES) and not l.startswith(ADDED)]


def main(off, zero):
    a = json.loads((Path(off) / "noisy_record.json").read_text())
    b = json.loads((Path(zero) / "noisy_record.json").read_text())
    same_deck = deck(off) == deck(zero)
    print(f"decks equal outside the noise lines: {same_deck}")
    ok = same_deck
    for k in ("words", "lessons", "tests", "skews"):
        e = a.get(k) == b.get(k)
        print(f"{k}: {'equal' if e else 'DIFFER'}")
        ok &= e
    du, lat, em = 0.0, [], 0
    for x, y in zip(a["slots"], b["slots"]):
        for c in x["u"]:
            for p in (0, 1):
                if x["u"][c][p] is not None:
                    du = max(du, abs(x["u"][c][p] - y["u"][c][p]))
        for r, s in zip(x["reads"] + x["inv"], y["reads"] + y["inv"]):
            em += r.get("emission") != s.get("emission")
            if r.get("latch") is not None and s.get("latch") is not None and r["latch"] != s["latch"]:
                lat.append(s["latch"] - r["latch"])
    n_slots = len(a["slots"]) == len(b["slots"])
    print(f"slots: {len(a['slots'])} and {len(b['slots'])}; max |u_zero - u_off| = {du} V; emissions differing: {em}")
    print(f"latch dates differing: {len(lat)}, shifts {sorted(set(lat))} ns (listed, allowed)")
    dx = [abs(p[k][f] - q[k][f]) for p, q in zip(a.get("inverter_x", []), b.get("inverter_x", [])) for k in p
          for f in ("x_tau", "x_D") if k in q]
    if dx:
        print(f"inverter x readings: {len(dx)}, max |difference| = {max(dx):.5f} x (interpolation; listed, allowed)")
    ok &= n_slots and du == 0 and em == 0
    print("ZERO-NOISE IDENTITY HOLDS (u, emissions, words, lessons, tests, skews)" if ok else "ZERO-NOISE IDENTITY FAILS")
    return ok


if __name__ == "__main__":
    sys.exit(0 if main(sys.argv[1], sys.argv[2]) else 1)
