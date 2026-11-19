"""Tests of diskcheck.py on manifests built by stages6 (no repository commit needed: the run lists only).

  python -B -m unittest test_diskcheck        (from this folder, with the pinned venv)
"""
from pathlib import Path
import json
import sys
import tempfile
import unittest
from unittest import mock

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent / "campaign6"))
import diskcheck                                         # noqa: E402
import stages6                                           # noqa: E402


def manifest(stage, data=None):
    runs = stages6.stage_runs(stage, data)
    return dict(campaign_id=f"test-{stage.lower()}", runs=[stages6.entry(stage, r, "t1", f"{stages6.attempt_dir('t1')}/INPUTS_{stage}.json") for r in runs])


class DiskCheck(unittest.TestCase):
    def test_footprints(self):
        m1 = manifest("M1")
        self.assertEqual(diskcheck.footprint_mb(m1, "a"), 2 * 3 * (85 + 75))      # 7801-7803 on a, each cal-on and cal-off
        self.assertEqual(diskcheck.footprint_mb(m1, "b"), 2 * 2 * (85 + 75))
        allow = dict(instances={str(s): {} for s in range(7801, 7806)})
        with tempfile.TemporaryDirectory() as d:
            f = Path(d) / "INPUTS_M2.json"
            f.write_text(json.dumps(allow))
            m2 = manifest("M2", f)
        kinds = sorted({diskcheck.kind(r) for r in m2["runs"]})
        self.assertEqual(kinds, ["bothfire", "line", "pair"])
        on_a = [diskcheck.kind(r) for r in m2["runs"] if r["machine"] == "a"]
        self.assertEqual(len(on_a), 13)                                          # amendment 1: 13 runs on a, 12 on b
        self.assertEqual(diskcheck.footprint_mb(m2, "a"), 2 * sum(diskcheck.MB[k] for k in on_a))
        self.assertEqual(diskcheck.footprint_mb(m2, "a"), 1780)

    def test_m3_and_network_kinds(self):
        """M3's one-sided scans and a network stage (the coordinator's review, N2); an unknown kind refuses."""
        allow = dict(instances={str(s): {} for s in range(7801, 7806)})
        with tempfile.TemporaryDirectory() as d:
            f = Path(d) / "INPUTS_M3.json"
            f.write_text(json.dumps(allow))
            m3 = manifest("M3", f)
        self.assertEqual({diskcheck.kind(r) for r in m3["runs"]}, {"onesided"})
        self.assertEqual(diskcheck.footprint_mb(m3, "a"), 2 * 30 * sum(r["machine"] == "a" for r in m3["runs"]))
        import predicted6
        xs = [dict(seed=s, measured=True, eligible=True, gate_K0=True, needs=dict(a=4, b=4, c1=4, c2=4)) for s in (7801, 7804)]
        with tempfile.TemporaryDirectory() as d:
            f = Path(d) / "PREDICTED.json"
            f.write_text(json.dumps(dict(instances=xs, network_runs=predicted6.network_runs(xs))))
            q = manifest("Q", f)
        self.assertEqual({diskcheck.kind(r) for r in q["runs"]}, {"network"})
        self.assertEqual(diskcheck.footprint_mb(q, "a"), 2 * 130 * sum(r["machine"] == "a" for r in q["runs"]))
        bad = json.loads(json.dumps(m3["runs"][0]))
        bad["argv"][7] = "line3"
        with self.assertRaises(AssertionError):
            diskcheck.kind(bad)
        bad["argv"][1] = "{repo}/other.py"
        with self.assertRaises(AssertionError):
            diskcheck.kind(bad)

    def test_refuses_below_margin_and_writes_its_report(self):
        m1 = manifest("M1")
        with tempfile.TemporaryDirectory() as d:
            f = Path(d) / "CAMPAIGN_M1.json"
            f.write_text(json.dumps(m1))
            need = diskcheck.footprint_mb(m1, "a") + 500
            with mock.patch.object(diskcheck.shutil, "disk_usage", lambda p: mock.Mock(free=(need - 1) * 1e6)):
                with self.assertRaises(SystemExit) as e:
                    diskcheck.main([str(f), "a", d])
                self.assertEqual(e.exception.code, 1)
                self.assertIn("REFUSED", (Path(d) / "DISK_CHECK_test-m1_a.txt").read_text())
            with mock.patch.object(diskcheck.shutil, "disk_usage", lambda p: mock.Mock(free=(need + 1) * 1e6)):
                with self.assertRaises(SystemExit) as e:
                    diskcheck.main([str(f), "a", d])
                self.assertEqual(e.exception.code, 0)
                report = (Path(d) / "DISK_CHECK_test-m1_a.txt").read_text()
                for key in ("df: ", "uptime -s: ", "MemAvailable: ", "VERDICT: PASSED"):
                    self.assertIn(key, report)


if __name__ == "__main__":
    unittest.main()
