"""Tests of marker_check.py on real manifests built by stages6 at a throwaway local commit on top of the marker (never
pushed): equal accepted; a missing path, an extra path, a wrong hash, a non-descendant commit, a missing inputs file and
a wrong stage file each refused; python -O refused, and an unexpected error of the stage check refused; a dirty tree
and a tree that differs from source_commit refused; RN (90 frozen paths and its stage file) accepted, an extra path refused.

  python -B -m unittest test_marker_check        (from this folder, with the pinned venv, in a full clone of -impl)
"""
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent.parent
sys.path.insert(0, str(HERE))
import marker_check                                     # noqa: E402

MARKER_COMMIT = "b88144f5999bda8fe5672d20af791608fa3d7693"
FROZEN_COMMIT = "55e5560ee55cad0638632f1f5a3279231cd6fefc"
BASE = marker_check.BASE


def git(repo, *a):
    return subprocess.run(["git", "-C", str(repo), *a], check=True, capture_output=True, text=True).stdout.strip()


class MarkerCheck(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = Path(tempfile.mkdtemp(prefix="c6-markercheck-"))
        cls.wt = cls.tmp / "wt"
        git(ROOT, "worktree", "add", "-q", "--detach", str(cls.wt), MARKER_COMMIT)
        sys.path.insert(0, str(cls.wt / BASE / "campaign6"))
        import stages6
        cls.stages6 = stages6
        for stage in ("RM1", "M2", "RN"):
            (cls.wt / stages6.stage_path(stage)).write_text(stages6.stage_file_text(stage))
        allow = dict(stage="M2", instances={str(s): dict(D_V={c: ["0.001", "0.001"] for c in "abc"}) for s in range(7801, 7806)})
        (cls.wt / BASE / "INPUTS_M2.json").write_text(json.dumps(allow, indent=1, sort_keys=True) + "\n")
        git(cls.wt, "add", BASE)
        git(cls.wt, "-c", "user.name=test", "-c", "user.email=test@invalid", "commit", "-q", "-m", "test: stage files (never pushed)")
        cls.src = git(cls.wt, "rev-parse", "HEAD")
        cls.manifests = {}
        for stage, path in (("RM1", None), ("M2", f"{BASE}/INPUTS_M2.json"), ("RN", f"{BASE}/rehearsal/PREDICTIONS_BATCH.json")):
            runs = stages6.stage_runs(stage, None if path is None else cls.wt / path)
            m = stages6.manifest(stage, runs, cls.src, path if stage == "M2" else None, root=cls.wt)
            f = cls.tmp / f"CAMPAIGN_{stage}.json"
            f.write_text(json.dumps(m, indent=1) + "\n")
            cls.manifests[stage] = f

    @classmethod
    def tearDownClass(cls):
        git(ROOT, "worktree", "remove", "--force", str(cls.wt))
        git(ROOT, "worktree", "prune")
        shutil.rmtree(cls.tmp, ignore_errors=True)

    def variant(self, stage, change):
        m = json.loads(self.manifests[stage].read_text())
        change(m)
        f = self.tmp / f"variant_{stage}.json"
        f.write_text(json.dumps(m, indent=1) + "\n")
        return f

    def run_check(self, stage, f):
        return marker_check.check(stage, f, MARKER_COMMIT, self.wt)

    def test_equal_accepted(self):
        for stage in ("RM1", "M2"):
            ok, lines = self.run_check(stage, self.manifests[stage])
            self.assertTrue(ok, lines)

    def test_missing_path_refused(self):
        f = self.variant("RM1", lambda m: m["source_sha256"].pop("research/learned-dnf-circuit-campaign-6/campaign6/c6.py"))
        ok, lines = self.run_check("RM1", f)
        self.assertFalse(ok)
        self.assertTrue(any("missing" in x and "c6.py" in x for x in lines), lines)

    def test_extra_path_refused(self):
        f = self.variant("RM1", lambda m: m["source_sha256"].__setitem__("research/learned-dnf-circuit-campaign-6/drafts/MAPPING_U.md", "0" * 64))
        ok, lines = self.run_check("RM1", f)
        self.assertFalse(ok)
        self.assertTrue(any("not allowed" in x for x in lines), lines)

    def test_wrong_hash_refused(self):
        f = self.variant("RM1", lambda m: m["source_sha256"].__setitem__("research/learned-dnf-circuit-campaign-6/campaign6/net6.py", "1" * 64))
        ok, lines = self.run_check("RM1", f)
        self.assertFalse(ok)
        self.assertTrue(any("another hash" in x for x in lines), lines)

    def test_non_descendant_commit_refused(self):
        f = self.variant("RM1", lambda m: m.__setitem__("source_commit", FROZEN_COMMIT))     # an ancestor of the marker, not a descendant
        ok, lines = self.run_check("RM1", f)
        self.assertFalse(ok)
        self.assertTrue(any("does not descend" in x for x in lines), lines)

    def test_missing_inputs_refused(self):
        f = self.variant("M2", lambda m: m["source_sha256"].pop(f"{BASE}/INPUTS_M2.json"))
        ok, lines = self.run_check("M2", f)
        self.assertFalse(ok)
        self.assertTrue(any("declared data file missing" in x for x in lines), lines)

    def test_optimized_python_refused(self):
        """Under python -O the script refuses (and writes its file) even when the stage file is broken in the checkout."""
        stage_file = self.wt / self.stages6.stage_path("RM1")
        good = stage_file.read_text()
        out = self.tmp / "opt"
        out.mkdir(exist_ok=True)
        f = out / "CAMPAIGN_RM1.json"
        f.write_text(self.manifests["RM1"].read_text())
        try:
            stage_file.write_text("not a stage file\n")
            r = subprocess.run([sys.executable, "-O", "-B", str(HERE / "marker_check.py"), "RM1", str(f), MARKER_COMMIT, str(self.wt)],
                               capture_output=True, text=True)
        finally:
            stage_file.write_text(good)
        self.assertEqual(r.returncode, 1, r.stdout + r.stderr)
        report = (out / "MARKER_CHECK_RM1.txt").read_text()
        self.assertIn("python -O", report)
        self.assertIn("VERDICT: REFUSED", report)

    def test_unexpected_stage_check_error_refused(self):
        """An exception outside the usual ones raised by the stage check is a refusal, not a crash."""
        import c6
        with mock.patch.object(c6, "stage_check", side_effect=RuntimeError("unexpected")):
            ok, lines = self.run_check("RM1", self.manifests["RM1"])
        self.assertFalse(ok)
        self.assertTrue(any("does not pass c6.stage_check: RuntimeError: unexpected" in x for x in lines), lines)

    def test_dirty_tree_refused(self):
        extra = self.wt / BASE / "untracked.txt"
        try:
            extra.write_text("x\n")
            ok, lines = self.run_check("RM1", self.manifests["RM1"])
        finally:
            extra.unlink()
        self.assertFalse(ok)
        self.assertTrue(any("not clean" in x for x in lines), lines)
        self.assertTrue(any("stage check is not run" in x for x in lines), lines)

    def test_tree_differs_from_source_refused(self):
        """A clean tree at a later commit that changes a frozen file is refused."""
        f = self.wt / "research/learned-dnf-circuit-campaign-5/smoke/README.md"
        try:
            f.write_text(f.read_text() + "changed\n")
            git(self.wt, "-c", "user.name=test", "-c", "user.email=test@invalid", "commit", "-q", "-am", "test: change (never pushed)")
            ok, lines = self.run_check("RM1", self.manifests["RM1"])
        finally:
            git(self.wt, "checkout", "-q", "--detach", self.src)
        self.assertFalse(ok)
        self.assertTrue(any("differs from source_commit" in x for x in lines), lines)
        self.assertTrue(any(x.startswith("REPO ") and "HEAD" in x for x in lines), lines)

    def test_rn_accepted_and_extra_refused(self):
        m = json.loads(self.manifests["RN"].read_text())
        self.assertEqual(len(m["source_sha256"]), 91)
        self.assertIn(f"{BASE}/STAGE_RN.md", m["source_sha256"])
        ok, lines = self.run_check("RN", self.manifests["RN"])
        self.assertTrue(ok, lines)
        f = self.variant("RN", lambda m: m["source_sha256"].__setitem__(f"{BASE}/PREDICTED.json", "0" * 64))
        ok, lines = self.run_check("RN", f)
        self.assertFalse(ok)
        self.assertTrue(any("not allowed" in x and "PREDICTED.json" in x for x in lines), lines)

    def test_wrong_stage_refused(self):
        ok, lines = self.run_check("M2", self.manifests["RM1"])       # RM1's manifest checked as M2
        self.assertFalse(ok)


if __name__ == "__main__":
    unittest.main()
