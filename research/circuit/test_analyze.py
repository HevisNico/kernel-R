"""Tests of analyze.py on synthetic campaigns.

Each test writes a whole campaign of synthetic results, runs the analysis and checks that the
full report is written with the right status and the right reason. One campaign passes every
check. The others each break one thing: the nominal cell never fires, the joint read never
fires, no port fires in the refresh runs, no relapse under a leak, runs are missing, the guard
has something to report, a firing pulse writes.

  python3 -B -m unittest test_analyze        (from research/circuit)
"""
import json, os, random, sys, tempfile, unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import analyze
from campaign import jobs

DOSE = 1.3465e-3                 # V
V0 = 0.3895
HOLDS, FAILS, NA = analyze.HOLDS, analyze.FAILS, analyze.NA
IDS = ["C1", "C2", "C3", "C4", "C5"] + [f"P{i}" for i in range(1, 20)]


def write(folder, name, rows):
    with open(f"{folder}/{name}.csv", "w") as fh:
        fh.write(",".join(analyze.COLS) + "\n")
        for r in rows:
            fh.write("%d,%d,%d,%.5f,%.4f,%.4f,%.4f,%d,%.4f,%.4f,%d,%.7f,%.7f,%.5f,%d,%.5f,%.5f\n" % tuple(r))


def cell_rows(rng, silent=(4, 4), kp=10, joint=0.2675, noise=0.0, relapse=(False, False), fire=True, joint_fire=True,
              first_lat=None, joint_writes=False):
    """A cell run: kp pulses on port 1, kp on port 2, one on both. noise is the sigma of one read, in volts."""
    v = [None, V0, V0]
    read = lambda: [v[1] + rng.gauss(0, noise), v[2] + rng.gauss(0, noise)]
    prev = read()
    rows, k = [], 0
    for q in (1, 2):
        for i in range(kp):
            late = relapse[q - 1]
            fired = fire and i >= silent[q - 1] and not (late and i == silent[q - 1] + 1)
            if not fired:
                v[q] -= DOSE
            lat = (first_lat if first_lat is not None else 0.98 if late else 0.90) if i == silent[q - 1] else 0.88
            now = read()
            ent = (1.777, 2.040) if q == 1 else (-1, -1)
            ent2 = (1.777, 2.040) if q == 2 else (-1, -1)
            rows.append([k, q, fired, lat if fired else -1, 5.59 if fired else -1, ent[0], ent[1], q == 1 and not fired, ent2[0], ent2[1],
                         q == 2 and not fired, now[0], now[1], 0.80 if fired else 0.85, 0, 1e3 * (prev[0] - now[0]), 1e3 * (prev[1] - now[1])])
            prev, k = now, k + 1
    if not joint_fire:
        v[1] -= DOSE; v[2] -= DOSE
    now = read()
    w = joint_writes or not joint_fire
    rows.append([k, 0, joint_fire, joint if joint_fire else -1, 5.59 if joint_fire else -1, 1.777, 2.040, w, 1.777, 2.040, w,
                 now[0], now[1], 0.80 if joint_fire else 0.85, 0, 1e3 * (prev[0] - now[0]), 1e3 * (prev[1] - now[1])])
    return rows


def refresh_rows(rng, n, stop=4, every=None, at=(), noise=0.0, fire=True):
    """A refresh run: n pulses on port 1. With every=N the stored voltage leaks by one dose in N periods,
    and a pulse is silent when a whole dose has leaked. With at=(...) the silent pulses are given."""
    v = V0
    read = lambda: [v + rng.gauss(0, noise), V0 + rng.gauss(0, noise)]
    prev = read()
    drift = DOSE / every if every else 0.0
    lost = 0.0
    rows = []
    for k in range(n):
        if fire and k >= stop:
            lost += drift
            v += drift
        fired = fire and k >= stop and not (lost >= DOSE - 1e-12 or k in at)
        if not fired:
            v -= DOSE
            lost = max(lost - DOSE, 0.0) if k >= stop else 0.0
        now = read()
        rows.append([k, 1, fired, 0.90 if fired else -1, 5.59 if fired else -1, 1.777, 2.040, not fired, -1, -1, 0,
                     now[0], now[1], 0.80 if fired else 0.85, 0, 1e3 * (prev[0] - now[0]), 1e3 * (prev[1] - now[1])])
        prev = now
    return rows


def campaign(folder, **change):
    """Write a campaign that passes every check, with the changes asked for."""
    rng = random.Random(7)
    read_noise = 0.075e-3 / 2 ** 0.5                    # a step is the difference of two reads
    corner = dict(pvt_ss_27=4, pvt_ff_27=4, pvt_sf_27=4, pvt_fs_27=4, pvt_tt_m40=2, pvt_tt_125=7)
    counts = [3, 4, 4, 5, 4, 3, 5, 4, 2, 6, 4, 5]
    fire_nom = not change.get("nominal_never_fires")
    jf = not change.get("joint_never_fires")
    rfire = not change.get("refresh_never_fires")
    leak = not change.get("no_relapse_under_leak")
    for i, (name, mode, section, opts) in enumerate(jobs):
        if name in change.get("skip", ()):
            continue
        if name == "nom":
            rows = cell_rows(rng, fire=fire_nom, joint_fire=jf and fire_nom)
        elif name == "nom_long":
            rows = cell_rows(rng, kp=26, joint_fire=jf)
        elif name in corner:
            rows = cell_rows(rng, silent=(corner[name],) * 2, joint_fire=jf)
        elif name.startswith("nz_"):
            rows = cell_rows(rng, noise=read_noise, joint=round(rng.gauss(0.2675, 0.0008) / 0.0005) * 0.0005, joint_fire=jf)
        elif name.startswith("mc_"):
            a, b = counts[i % 12], counts[(i + 5) % 12]
            j = min(0.279, max(0.256, round(rng.gauss(0.2675, 0.0033) / 0.0005) * 0.0005))
            rows = cell_rows(rng, silent=(a, b), noise=read_noise, joint=j, relapse=(i % 11 == 0, False), joint_fire=jf,
                             first_lat=change.get("first_lat", {}).get(name), joint_writes=name in change.get("firing_pulse_writes", ()))
        elif name == "refresh_none":
            rows = refresh_rows(rng, 150, fire=rfire)
        elif name == "refresh_none_nz":
            rows = refresh_rows(rng, 150, noise=0.04e-3, fire=rfire)
        elif name == "refresh_lk11":
            rows = refresh_rows(rng, 150, every=22.5 if leak else None, fire=rfire)
        elif name == "refresh_lk12":
            rows = refresh_rows(rng, 560, at=(93, 314, 535) if leak else (), fire=rfire)
        elif name == "refresh_lk11_nz":
            rows = refresh_rows(rng, 150, every=22.5 if leak else None, noise=0.04e-3, fire=rfire)
        elif name.startswith("refresh_mm_"):
            rows = refresh_rows(rng, 100, every=22.5 if leak else None, noise=0.04e-3, fire=rfire)
        else:
            raise AssertionError("run of the plan without a synthetic result: " + name)
        write(folder, name, rows)


class Analysis(unittest.TestCase):
    def run_on(self, figures=False, prepare=None, **change):
        """Write a campaign, analyse it, and return the verdicts by id. The report must be complete."""
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        res, out = tmp.name + "/results", tmp.name + "/out"
        os.makedirs(res)
        if change.get("empty") is None:
            campaign(res, **change)
        if prepare:
            prepare(res)
        code = analyze.main(["--results", res, "--out", out] + ([] if figures else ["--no-figures"]))
        self.assertEqual(code, 0, "the analysis reported an error of its own")
        with open(out + "/VERDICTS.md") as fh:
            report = fh.read()
        with open(res + "/summary.json") as fh:
            data = json.load(fh)
        v = {x["id"]: x for x in data["verdicts"]}
        self.assertEqual(sorted(v), sorted(IDS))
        for pid in IDS:
            self.assertIn(f"| {pid} |", report)
            self.assertIn(v[pid]["status"], (HOLDS, FAILS, NA))
            if v[pid]["status"] != HOLDS:
                self.assertTrue(v[pid]["reason"], pid + " has no reason")
            self.assertNotIn("None", v[pid]["measured"])
            self.assertNotIn("nan", v[pid]["measured"])
        self.assertEqual(sum(data["counts"].values()), len(IDS))
        self.assertIn(f"{data['counts'][HOLDS]} hold, {data['counts'][FAILS]} fail, {data['counts'][NA]} not evaluable, of {len(IDS)}", report)
        self.report = report
        return v

    def expect(self, v, want, others=HOLDS):
        for pid in IDS:
            status, reason = want.get(pid, (others, ""))
            self.assertEqual(v[pid]["status"], status, f"{pid}: {v[pid]}")
            self.assertIn(reason, v[pid]["reason"], f"{pid}: {v[pid]}")

    def test_everything_holds(self):
        v = self.run_on(figures=True)
        self.expect(v, {})
        self.assertIn(f"The plan of `campaign.py` has {len(jobs)} runs", self.report)

    def test_nominal_cell_never_fires(self):
        v = self.run_on(figures=True, nominal_never_fires=True)
        self.expect(v, {"C1": (FAILS, "port 1 never fires"), "C3": (NA, "no FIRE"),
                        "C4": (NA, "no FIRE: the end of the protection is not measured"), "C5": (NA, "joint read without a FIRE")})
        self.assertIn("no FIRE on the joint pulse", v["C1"]["reason"])
        self.assertIn("—", v["C4"]["measured"])

    def test_joint_read_never_fires(self):
        v = self.run_on(figures=True, joint_never_fires=True)
        self.expect(v, {"C1": (FAILS, "no FIRE on the joint pulse"), "C5": (NA, "joint read without a FIRE"),
                        "P2": (FAILS, "20 runs without a joint FIRE"), "P7": (FAILS, "100 cells without a joint FIRE"),
                        "P12": (FAILS, "joint read without a FIRE")})
        self.assertIn("—", v["P2"]["measured"])

    def test_no_fire_in_the_refresh_runs(self):
        v = self.run_on(figures=True, refresh_never_fires=True)
        self.expect(v, {p: (FAILS, "never fires") for p in ("P13", "P14", "P15", "P16", "P17", "P18")})

    def test_no_relapse_under_a_leak(self):
        v = self.run_on(figures=True, no_relapse_under_leak=True)
        self.expect(v, {"P15": (FAILS, "no relapse observed: relapses were predicted"), "P16": (FAILS, "no relapse observed: relapses were predicted"),
                        "P17": (FAILS, "no relapse observed: relapses were predicted"), "P18": (FAILS, "fewer than two relapses, relapses were predicted")})

    def test_no_result_at_all(self):
        v = self.run_on(figures=True, empty=True)
        self.expect(v, {}, others=NA)
        self.assertIn(f"{len(jobs)} runs missing", v["P19"]["reason"])
        self.assertIn(f"| not evaluable: run missing | {len(jobs)} |", self.report)

    def test_missing_failed_and_unreadable_runs(self):
        def prepare(res):
            os.remove(res + "/nom_long.csv")
            for name, text in (("nz_105.failed", "aborted\n"), ("pvt_ff_27.csv", "pulse,port\n0,1\n"), ("extra_run.csv", "pulse,port\n0,1\n")):
                with open(f"{res}/{name}", "w") as fh:
                    fh.write(text)
        v = self.run_on(prepare=prepare, skip=("mc_2050",))
        self.expect(v, {"P1": (NA, "failed: nz_105"), "P2": (NA, "failed: nz_105"), "P3": (NA, "measured on the others"), "P4": (NA, ""), "P5": (NA, ""),
                        "P6": (NA, "missing: mc_2050"), "P7": (NA, ""), "P8": (NA, ""), "P9": (NA, ""), "P10": (NA, "runs without a result"),
                        "P11": (NA, "missing: nom_long"), "P12": (NA, "unreadable: pvt_ff_27"), "P19": (FAILS, "1 runs failed")})
        self.assertIn("3 runs missing or not readable", v["P19"]["reason"])
        self.assertIn("mc_2050 (run missing)", self.report)
        self.assertIn("pvt_ff_27 (column absent", self.report)
        self.assertIn("Results that are not in the plan, not used: extra_run", self.report)

    def test_the_guard_reports_and_keeps_or_leaves_out(self):
        v = self.run_on(first_lat={"mc_2003": 0.0, "mc_2004": 1.05})
        self.expect(v, {"P6": (NA, "left out: mc_2003"), "P7": (NA, ""), "P8": (NA, ""), "P9": (NA, ""),
                        "P19": (FAILS, "1 runs with a protection that is not a FIRE")})
        self.assertIn("1 runs with an event against the mechanism", v["P19"]["reason"])
        self.assertIn("mc_2004 (FIRE after the end of the pulse", self.report)
        self.assertIn("left out by the guard | 1 | mc_2003", self.report)

    def test_a_firing_pulse_that_writes(self):
        v = self.run_on(firing_pulse_writes=("mc_2010",))
        self.expect(v, {"P10": (FAILS, "a firing pulse writes: mc_2010 pulse 20")})

    def test_a_firing_pulse_that_writes_in_a_run_left_out_by_the_guard(self):
        v = self.run_on(firing_pulse_writes=("mc_2003",), first_lat={"mc_2003": 0.0})
        self.assertEqual(v["P10"]["status"], FAILS)
        self.assertIn("mc_2003", v["P10"]["reason"])


if __name__ == "__main__":
    unittest.main()
