"""Tests of noise_constants.py on synthetic rows where b, w and d are known. No simulation, no run read.

  python -B test_noise_constants.py
"""
import math
import random
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import noise_constants as NC                     # noqa: E402

L0, SLOPE, DOSE = 0.8, -0.05, 2.0               # latency units, units per mV, mV
PORTS = ("a1", "a2", "b1", "b2", "c1", "c2")


def read(fire, latency, step, p, u=-10.0):
    return dict(fire=fire, latency=latency if fire else None,
                ports={str(q): dict(move_mV=step if q == int(p) else 0.0, u_before_mV=u) for q in (1, 2)})


def rows(need, fires, latency_of, step_of, ports=PORTS):
    """One run: per port, `need` silent reads (step step_of(i)) then `fires` FIREs (latency latency_of(j)); layer 1 for
    a and b, the layer-2 slots of each line for c."""
    out = []
    for i in range(need + fires):
        reads = {}
        for c in "ab":
            ps = [p for p in ports if p[0] == c]
            if not ps:
                continue
            f = i >= need
            r = read(f, latency_of(c, i - need) if f else None, step_of(c, i), ps[0][1])
            for p in ps:                                            # both ports of a pair cell: the same read
                r["ports"][p[1]]["move_mV"] = step_of(p, i) if not f else 0.0
            reads[c] = r
        out.append(dict(stage="layer 1", reads=reads))
    for i in range(need + fires):
        for line in (1, 2):
            if f"c{line}" not in ports:
                continue
            f = i >= need
            r = read(f, latency_of(f"c{line}", i - need) if f else None, step_of(f"c{line}", i), line)
            r["arrivals"] = [dict(port=line)]
            out.append(dict(stage="layer 2", reads={"c": r}))
    return out


class Exact(unittest.TestCase):
    """Offsets of exactly +b and -b, within-run deviations of exactly w, steps of exactly DOSE +/- d."""

    def test_b_w_d(self):
        b, w, d, need, fires = 0.111, 0.094, 0.009, 2, 4
        a = w * math.sqrt(3) / 2 * abs(SLOPE)                # 4 FIREs at +/-a: sum of squares 3 w^2 slope^2
        quiet = rows(need, fires, lambda p, j: L0, lambda p, i: DOSE)
        noisy = {}
        for r in range(4):
            off = b if r % 2 == 0 else -b
            noisy[f"n{r}"] = rows(need, fires, lambda p, j, off=off: L0 - off * SLOPE + (a if j % 2 == 0 else -a),
                                  lambda p, i, r=r: DOSE + (d if (i + r) % 2 == 0 else -d))
        v = NC.values({"8303": dict(quiet=quiet, noisy=noisy, slopes={p: SLOPE for p in PORTS}, doses={p: DOSE for p in PORTS})})
        P = v["pooled"]
        self.assertAlmostEqual(P["between_mV"], b, places=12)
        self.assertAlmostEqual(P["within_mV"], w, places=12)
        self.assertAlmostEqual(P["per_dose_mV"], d, places=12)
        self.assertEqual(P["run_offsets"], 4 * len(PORTS))
        self.assertEqual(P["doses"], 4 * len(PORTS) * need)
        i = v["per_instance"]["8303"]
        self.assertAlmostEqual(i["noise_between_runs_mV"], b, places=12)
        self.assertAlmostEqual(i["ports"]["c2"]["within_run_mV"], w, places=12)

    def test_offset_sign(self):
        """[C3a] offset = (latency without noise - mean noisy latency) / slope: a noisy run that fires later, with a
        negative slope, has a positive offset (a lower gain)."""
        quiet = rows(2, 3, lambda p, j: L0, lambda p, i: DOSE, ports=("a1",))
        noisy = {"n": rows(2, 3, lambda p, j: L0 + 0.01, lambda p, i: DOSE, ports=("a1",))}
        p = NC.port_noise(NC.pulses(quiet, "a1"), {"n": NC.pulses(noisy["n"], "a1")}, SLOPE, DOSE)
        self.assertAlmostEqual(p["run_offsets_mV"][0], -0.01 / SLOPE)
        self.assertGreater(p["run_offsets_mV"][0], 0)


class Rules(unittest.TestCase):
    def test_other_word_excluded(self):
        """[C3a] a noisy run whose word differs, or with fewer than 3 FIREs, gives no offset and no scatter; its silent
        reads still give doses."""
        quiet = rows(2, 4, lambda p, j: L0, lambda p, i: DOSE, ports=("a1",))
        late = rows(3, 3, lambda p, j: L0, lambda p, i: DOSE + 0.01, ports=("a1",))         # one more write
        short = rows(2, 2, lambda p, j: L0, lambda p, i: DOSE, ports=("a1",))               # 2 FIREs only
        p = NC.port_noise(NC.pulses(quiet, "a1"), {"late": NC.pulses(late, "a1"), "short": NC.pulses(short, "a1")}, SLOPE, DOSE)
        self.assertEqual([e["same_word_as_without_noise"] for e in p["noisy_runs"]], [False, False])
        self.assertEqual(p["run_offsets_mV"], [])
        self.assertEqual(len(p["noisy_doses_mV"]), 5)
        self.assertNotIn("within_run_mV", p)

    def test_within_needs_8(self):
        """[C3a] a port's within value needs a count of at least 8 (FIREs minus one, summed over counted runs)."""
        quiet = rows(2, 3, lambda p, j: L0, lambda p, i: DOSE, ports=("a1",))
        mk = lambda k: {f"n{r}": NC.pulses(rows(2, 3, lambda p, j: L0 + 0.001 * j, lambda p, i: DOSE, ports=("a1",)), "a1") for r in range(k)}
        self.assertNotIn("within_run_mV", NC.port_noise(NC.pulses(quiet, "a1"), mk(3), SLOPE, DOSE))       # 3 x 2 = 6
        self.assertIn("within_run_mV", NC.port_noise(NC.pulses(quiet, "a1"), mk(4), SLOPE, DOSE))          # 4 x 2 = 8

    def test_c_lines_by_arrival(self):
        """[reading] a port of c takes the layer-2 slots whose arrival is on that line only."""
        r = rows(2, 3, lambda p, j: {"c1": 0.5, "c2": 0.9}.get(p, L0), lambda p, i: DOSE)
        self.assertEqual({x["latency"] for x in NC.pulses(r, "c1") if x["fire"]}, {0.5})
        self.assertEqual({x["latency"] for x in NC.pulses(r, "c2") if x["fire"]}, {0.9})
        self.assertEqual(len(NC.pulses(r, "a1")), 5)

    def test_quiet_word_required(self):
        quiet = rows(2, 1, lambda p, j: L0, lambda p, i: DOSE, ports=("a1",))
        with self.assertRaises(AssertionError):
            NC.port_noise(NC.pulses(quiet, "a1"), {}, SLOPE, DOSE)


class Random(unittest.TestCase):
    """Drawn with known b, w, d: the estimates come within 15 % with 2 instances x 40 runs x 6 ports."""

    def test_recovers(self):
        rng = random.Random(83031)
        b, w, d, need, fires = 0.111, 0.094, 0.009, 2, 3
        per = {}
        for k in ("8303", "8306"):
            quiet = rows(need, fires, lambda p, j: L0, lambda p, i: DOSE)
            noisy = {}
            for r in range(40):
                off = {p: rng.gauss(0, b) for p in PORTS + ("a", "b")}
                noisy[f"n{r}"] = rows(need, fires, lambda p, j, off=off: L0 - off[p] * SLOPE + rng.gauss(0, w) * SLOPE,
                                      lambda p, i: DOSE + rng.gauss(0, d))
            per[k] = dict(quiet=quiet, noisy=noisy, slopes={p: SLOPE for p in PORTS}, doses={p: DOSE for p in PORTS})
        P = NC.values(per)["pooled"]
        for got, want in ((P["between_mV"], b), (P["within_mV"], w), (P["per_dose_mV"], d)):
            self.assertLess(abs(got - want) / want, 0.15, (got, want))


def cal_row(cell, read_name, u, fire=True, slope=SLOPE, u0=-10.0):
    """A calibration read with latency linear in u: L0 + slope (u - u0)."""
    return dict(cell=cell, read=read_name, fire=fire, latency=L0 + slope * (u - u0) if fire else None,
                ports={"1": dict(u_before_mV=u), "2": dict(u_before_mV=u)})


class Mapping(unittest.TestCase):
    """The slope from the guard-on decks' fired reads at the trained level, the dose from the run without noise."""

    def test_secant_as_campaign_3(self):
        """[C3a] the reused secant gives campaign 3's value: exact on a line, and the two points around u otherwise."""
        pts = [(-12.0 + i * 0.5, L0 + SLOPE * i * 0.5) for i in range(6)]
        self.assertAlmostEqual(NC.secant(pts, -10.7), SLOPE)
        bent = [(-12.0, 1.0), (-11.0, 0.9), (-10.0, 0.6)]
        self.assertAlmostEqual(NC.secant(bent, -10.5), -0.3)
        self.assertAlmostEqual(NC.secant(bent, -11.5), -0.1)
        self.assertAlmostEqual(NC.secant(bent + [(-10.005, 0.6)], -10.5), -0.3 / 0.9975)   # within 0.02 mV: one state, u averaged

    def test_reads_chosen_by_kind(self):
        rows = [cal_row("a", "both", -11.0), cal_row("a", "both", -10.0), cal_row("a", "port 1", -11.0, slope=9),
                cal_row("b", "port 2 at 1.0", -11.0, slope=-0.2), cal_row("b", "port 2 at 1.0", -10.0, slope=-0.2),
                cal_row("c", "port 1", -11.0, slope=-0.3), cal_row("c", "port 1", -10.0, slope=-0.3), cal_row("c", "both", -11.0, slope=7),
                cal_row("a", "both", -9.0, fire=False)]
        self.assertEqual(len(NC.calibration_points(rows, "a1", "pair")), 2)
        self.assertAlmostEqual(NC.secant(NC.calibration_points(rows, "a2", "pair"), -10.5), SLOPE)
        self.assertAlmostEqual(NC.secant(NC.calibration_points(rows, "b2", "unary"), -10.5), -0.2)
        self.assertAlmostEqual(NC.secant(NC.calibration_points(rows, "c1", "line"), -10.5), -0.3)

    def test_inputs_F3(self):
        """F3: a unary on port 2 (from the unary deck), b a pair (both reads), lines c1 and c2 (port P of c)."""
        import family_predict  # noqa: F401  (FP.kinds, FP.LINE_PORT)
        plain = [cal_row(c, r, u) for u in (-11.0, -10.5, -10.0) for c, r in (("b", "both"), ("c", "port 1"), ("c", "port 2"))]
        unary = [cal_row("a", "port 2 at 1.0", u, slope=-0.2) for u in (-11.0, -10.5, -10.0)]
        quiet = rows(2, 3, lambda p, j: L0, lambda p, i: DOSE + (0.1 if p == "c2" else 0.0), ports=("a2", "b1", "b2", "c1", "c2"))
        got = NC.inputs("F3", {"a": 2}, quiet, plain, unary)
        self.assertEqual(set(got), {"a2", "b1", "b2", "c1", "c2"})
        self.assertAlmostEqual(got["a2"][0], -0.2)
        self.assertAlmostEqual(got["b1"][0], SLOPE)
        self.assertAlmostEqual(got["c2"][0], SLOPE)
        self.assertAlmostEqual(got["c2"][1], DOSE + 0.1)
        self.assertAlmostEqual(got["a2"][1], DOSE)
        with self.assertRaises(AssertionError):
            NC.inputs("F3", {"a": 2}, quiet, plain, None)                       # a unary cell needs its unary deck


if __name__ == "__main__":
    unittest.main(verbosity=2)
