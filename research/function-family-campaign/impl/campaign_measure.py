"""The family campaign's measure runner: one measure run, by kind, through the frozen wrappers that measured B2 and
the top-up, with the campaign's seed guard in place of theirs. New code; it edits nothing.

  campaign_measure.py KIND REPO OUT SEED [ARGS...] NGSPICE PDK

  cal-on | cal-off                      batch2x.cal (B2's plain deck)
  cal-on-unary | cal-off-unary          topup.cal (the deck with the unary reads)
  pair CELL D1 D2 | line P D1 D2 | bothfire D1 D2 | onesided CELL BOUND D1 D2      batch2x.scan (scan6.main)
  unary-scan CELL P D1 D2 | preset CELL D1 D2                                       topup.scan_kind

The guard accepts the campaign's seeds 8501 to 8515 only (PREDICTION.md section 1). batch2x's and topup's own guards
(8301 to 8310) are replaced for the time of the run by `unittest.mock.patch.object`, as topup.py itself replaces
batch6's. The design point (twice the dose, 1e-5), the decks, the scans and the records are the wrappers', unchanged.
"""
import sys
from unittest import mock

import campaign_common as CC

SCAN_DELTA = "1/2"


def guard_seed(text):
    seed = int(text)
    assert str(seed) == str(text) and seed in CC.SEEDS, f"refused: {text!r} is not one of the campaign's seeds 8501 to 8515"
    return seed


def run(kind, repo, out, seed, args, ngspice, pdk):
    assert __debug__, "refused: not with python -O, the guards are asserts"
    guard_seed(str(seed))
    import batch2x
    import topup
    topup.paths(repo)
    with mock.patch.object(batch2x, "guard_seed", guard_seed), mock.patch.object(topup, "guard_seed", guard_seed):
        if kind in ("cal-on", "cal-off"):
            assert not args
            return batch2x.cal(repo, out, seed, kind[4:], ngspice, pdk)
        if kind in ("cal-on-unary", "cal-off-unary"):
            assert not args
            return topup.cal(repo, out, seed, kind[4:-6], ngspice, pdk)
        if kind == "pair":
            cell, d1, d2 = args
            assert cell in ("a", "b")
            return batch2x.scan(repo, out, seed, [cell, "pair", SCAN_DELTA, d1, d2, ngspice, pdk])
        if kind == "line":
            p, d1, d2 = args
            assert p in ("1", "2")
            return batch2x.scan(repo, out, seed, ["c", f"line{p}", SCAN_DELTA, d1, d2, ngspice, pdk])
        if kind == "bothfire":
            d1, d2 = args
            return batch2x.scan(repo, out, seed, ["c", "bothfire", d1, d2, ngspice, pdk])
        if kind == "onesided":
            cell, bound, d1, d2 = args
            assert cell in ("a", "b")
            return batch2x.scan(repo, out, seed, [cell, "onesided", bound, bound, d1, d2, ngspice, pdk])
        if kind == "unary-scan":
            cell, p, d1, d2 = args
            assert cell in ("a", "b") and p in ("1", "2")
            return topup.scan_kind(repo, out, seed, cell, f"line{p}", [SCAN_DELTA, d1, d2], ngspice, pdk)
        if kind == "preset":
            cell, d1, d2 = args
            assert cell in ("a", "b")
            return topup.scan_kind(repo, out, seed, cell, "onesided", ["0", "0", d1, d2], ngspice, pdk)
    raise SystemExit(f"refused: unknown kind {kind!r}")


if __name__ == "__main__":
    a = sys.argv[1:]
    if len(a) < 6:
        raise SystemExit(__doc__)
    run(a[0], a[1], a[2], a[3], a[4:-2], a[-2], a[-1])
