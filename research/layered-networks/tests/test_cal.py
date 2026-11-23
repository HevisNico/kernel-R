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
        t = instrument.deck_text(specmod.load(HERE / "specs" / f"{name}.json"), CFG)
        assert t.count(".subckt rcell vdd vr0 vfire vreopen vcm vhi vlo vpre gl1 gl2 ") == 1
        assert t.count(" gl1 rport") == 1 and t.count(" gl2 rport") == 1
        assert sum(1 for l in t.splitlines() if l.startswith("vglc")) == 2 * n_cells
        assert "vgl gl 0 dc 0" in t                        # the shared node stays, unused by the cells


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
        return s >= self.s_true


def run_fake(groups, s_true, start_s, seed):
    rng = random.Random(seed)
    D = {1: 1.35e-3, 2: 1.32e-3}
    u0 = {1: 0.3895, 2: 0.3893}
    fake = FakeCell(s_true, D, u0, start_s, rng)
    sc = instrument.ScanCell("c", groups, u0, D, SC["tol_V"], SC["bracket_V"], SC["step_V"], SC["max_slots"])
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


def test_scan_brackets_the_crossing():
    for seed in range(20):
        rng = random.Random(100 + seed)
        n = rng.randint(2, 6)
        s_true = F(n - 1) + F(rng.randint(1, 999), 1000)
        res, slots = run_fake([dict(group=0, ports=[1, 2], lo=F(n - 1), hi=F(n), offsets={})], s_true, n, seed)
        assert len(res) == 1 and res[0]["ok"], res
        lo, hi = (F(x) for x in res[0]["bracket"])
        assert lo < s_true <= hi or abs(float(s_true - lo)) < 2e-3 or abs(float(hi - s_true)) < 2e-3, (lo, s_true, hi)
        assert (hi - lo) * F(1.35e-3) <= F(SC["bracket_V"])
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
