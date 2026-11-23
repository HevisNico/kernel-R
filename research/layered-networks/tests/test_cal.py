"""Tests of the calibration instrument without a simulator: python3 -B tests/test_cal.py"""
from fractions import Fraction as F
import json
from pathlib import Path
import random
import sys

HERE = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(HERE))
import instrument  # noqa: E402
import scores  # noqa: E402
import spec as specmod  # noqa: E402

CFG = json.loads((HERE / "config.json").read_text())
SC = instrument.CAL["scan"]
THETA = scores.THETA


def test_deck_leaks():
    for name, n_cells in (("not1", 1), ("andor3", 4), ("xor3", 4)):
        s = specmod.load(HERE / "specs" / f"{name}.json")
        t = instrument.deck_text_1x(s, CFG)               # the hierarchical deck before the design point and areas
        assert t.count(".subckt rcell vdd vr0 vfire vreopen vcm vhi vlo vpre gl1 gl2 ") == 1
        assert t.count(" gl1 rport") == 1 and t.count(" gl2 rport") == 1
        assert sum(1 for l in t.splitlines() if l.startswith("vglc")) == 2 * n_cells
        assert "vgl gl 0 dc 0" in t                        # the shared node stays, unused by the cells
        f = instrument.deck_text(s, CFG)                   # the run's deck: flattened, the per-port leaks kept
        assert sum(1 for l in f.splitlines() if l.startswith("vglc")) == 2 * n_cells
        assert ".param vhi=0.7" in f.replace(" = ", "=") or "vhi=0.7" in f


class FakeCell:
    """A port pair on a path: a dose lowers u by D (times a spread), a leak raises it by a fraction of the asked volts;
    the read fires when the mean s of the moving ports is at least s_true."""

    def __init__(self, s_true, D, u0, start_s, rng):
        self.s_true, self.D, self.u0, self.rng = s_true, D, u0, rng
        self.u = {p: u0[p] - start_s * D[p] for p in (1, 2)}

    def apply(self, a):
        if a[0] == "dose":
            for p in a[1]:
                self.u[p] -= self.D[p] * self.rng.uniform(0.97, 1.03)
        elif a[0] == "leak":
            for p, v in a[1].items():
                self.u[p] += v * self.rng.uniform(0.9, 1.0)

    def read(self, ports):
        s = sum((self.u0[p] - self.u[p]) / self.D[p] for p in ports) / len(ports)
        # a history effect: after a FIRE the crossing moves up by hyst (0 by default)
        shift = getattr(self, "hyst", 0) if getattr(self, "last", None) else 0
        self.last = s >= self.s_true + shift
        return self.last


def run_fake(groups, s_true, start_s, seed, repeats=False, hysteresis=F(0)):
    rng = random.Random(seed)
    D = {1: 1.35e-3, 2: 1.32e-3}
    u0 = {1: 0.3895, 2: 0.3893}
    fake = FakeCell(s_true, D, u0, start_s, rng)
    fake.hyst, fake.last = hysteresis, None
    sc = instrument.ScanCell("c", groups, u0, D, SC["tol_V"], SC["bracket_V"], SC["step_V"], SC["max_slots"], repeats)
    slots = 0
    while True:
        a = sc.action(dict(fake.u))
        if a is None:
            break
        slots += 1
        if a[0] == "read":
            sc.result(fake.read(a[1]), dict(fake.u))
        else:
            fake.apply(a)
    return sc.results, slots


def check_native(res):
    """Rule D3: the bracket ends are states read by the scan itself."""
    reads = res["reads"]
    lo, hi = (F(x) for x in res["bracket"])
    assert any(not r["fired"] and F(r["s"]) == lo for r in reads), "the lower end is a silent read of the scan"
    assert any(r["fired"] and F(r["s"]) == hi for r in reads), "the upper end is a FIRE of the scan"


def test_scan_brackets_the_crossing():
    for seed in range(30):
        rng = random.Random(100 + seed)
        n = rng.randint(2, 6)
        # the crossing usually inside the training bracket, sometimes above the stop or below the last silence
        s_true = F(n - 1) + F(rng.randint(-400, 1400), 1000)
        res, slots = run_fake([dict(group=0, ports=[1, 2], lo=F(n - 1), hi=F(n), offsets={})], s_true, n, seed)
        assert len(res) == 1 and res[0]["ok"], res
        lo, hi = (F(x) for x in res[0]["bracket"])
        assert lo < s_true <= hi, (lo, s_true, hi)
        assert (hi - lo) * F(1.35e-3) <= F(SC["bracket_V"])
        check_native(res[0])
        assert slots <= SC["max_slots"], slots


def test_scan_groups_in_order_and_missing_bracket():
    res, _ = run_fake([dict(group=0, ports=[1], lo=None, hi=None, why="never fired"),
                       dict(group=1, ports=[2], lo=F(2), hi=F(3), offsets={})], F(5, 2), 3, 1)
    assert [r["group"] for r in res] == [0, 1] and not res[0]["ok"] and res[1]["ok"]


def test_anchors_put_theta_at_the_crossing():
    s, h = F(855, 512), F(1, 512)
    for gate, ports in (("both", (1, 2)), ("copy", (1,))):
        an = scores.anchors(gate, {0: (s, h)})
        Z = scores.score(an, {p: s for p in (1, 2)}, ports)
        assert abs(Z - THETA) <= an["K"] + len(ports), (gate, Z)     # the rounding of d, as predict6.anchors
        assert scores.score(an, {p: s - 1 for p in (1, 2)}, ports) < THETA - an["H"]
    an = scores.anchors("either", {0: (F(3, 2), h), 1: (F(5, 2), h)})
    assert abs(scores.score(an, {1: F(3, 2), 2: F(0)}, (1,)) - THETA) <= 1
    assert abs(scores.score(an, {1: F(0), 2: F(5, 2)}, (2,)) - THETA) <= 1
    assert scores.score(an, {1: F(0), 2: F(0)}, ()) == 0


def test_decoder_rule():
    H = 100
    assert scores.decoder_ok(THETA + 50, False, H)          # inside the band: undecided, not a failure
    assert not scores.decoder_ok(THETA + 500, False, H)
    assert not scores.decoder_ok(THETA - 500, True, H)
    assert scores.decoder_ok(THETA - 500, False, H) and scores.decoder_ok(THETA + 500, True, H)


def test_training_path_and_bracket():
    s = specmod.load(HERE / "specs" / "not1.json")
    D = 1.3e-3
    u = lambda k: {"c1_0": [0.3895 - k * D, 0.3895]}
    word = "sssFF"
    slots, lessons = [], []
    for r, ch in enumerate(word):
        k = min(r, 3)
        read = dict(layer=1, index=0, arrivals=[1000 + r, None], emission=2000 + r if ch == "F" else None)
        slots.append(dict(kind="lesson", u=u(k), reads=[read]))
        lessons.append(dict(layer=1, cell=0, group=0, round=r, slot=r))
    rec = dict(slots=slots, lessons=lessons, u_end=u(3))
    u0, Dm, groups = instrument.training_path(s, rec)
    assert abs(Dm[("c1_0", 1)] - D) < 1e-12
    lo, hi, why = instrument.bracket(groups[("c1_0", 0)])
    assert why == "" and abs(float(lo) - 2) < 1e-9 and abs(float(hi) - 3) < 1e-9


if __name__ == "__main__":
    n = 0
    for name, f in list(globals().items()):
        if name.startswith("test_") and callable(f):
            f()
            n += 1
            print("ok", name)
    print(n, "tests passed")


def test_repeats_read_each_end_from_the_other_side():
    for seed in range(20):
        rng = random.Random(300 + seed)
        n = rng.randint(2, 6)
        s_true = F(n - 1) + F(rng.randint(100, 900), 1000)
        res, _ = run_fake([dict(group=0, ports=[1, 2], lo=F(n - 1), hi=F(n), offsets={})], s_true, n, seed, repeats=True)
        r = res[0]
        assert r["ok"] and r["repeats_agree"] and len(r["repeats"]) == 2, r
        assert {x["end"] for x in r["repeats"]} == {"L", "U"}
        assert {x["after"] for x in r["repeats"]} == {"after FIRE", "after silence"}
        lo, hi = (F(x) for x in r["bracket"]); assert lo < s_true <= hi


def test_repeats_widen_a_disputed_bracket():
    # a history shift larger than the bracket: L read after a FIRE stays silent, but U read after a FIRE would not
    # fire; the repeat of U is after silence so it fires; make the shift negative to dispute L instead
    seen = 0
    for seed in range(20):
        rng = random.Random(500 + seed)
        n = rng.randint(2, 6)
        s_true = F(n - 1) + F(rng.randint(100, 900), 1000)
        res, _ = run_fake([dict(group=0, ports=[1, 2], lo=F(n - 1), hi=F(n), offsets={})], s_true, n, seed,
                          repeats=True, hysteresis=F(-1, 100))
        r = res[0]
        if r["ok"] and not r["repeats_agree"]:
            seen += 1
            lo, hi = (F(x) for x in r["bracket"])
            L0, U0 = (F(x) for x in r["bracket_before_repeats"])
            assert lo <= L0 and hi >= U0 and F(r["half_bracket"]) == (hi - lo) / 2
    assert seen > 0
