"""Tests of marker_check.py on real manifests built by stages6 at a throwaway local commit on top of the marker (never
pushed): equal accepted; a missing path, an extra path, a wrong hash, a non-descendant commit, a missing inputs file and
a wrong stage file each refused.

  python -B -m unittest test_marker_check        (from this folder, with the pinned venv, in a full clone of -impl)
"""
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

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
        for stage in ("RM1", "M2"):
            (cls.wt / stages6.stage_path(stage)).write_text(stages6.stage_file_text(stage))
        allow = dict(stage="M2", instances={str(s): dict(D_V={c: ["0.001", "0.001"] for c in "abc"}) for s in range(7801, 7806)})
        (cls.wt / BASE / "INPUTS_M2.json").write_text(json.dumps(allow, indent=1, sort_keys=True) + "\n")
        git(cls.wt, "add", BASE)
        git(cls.wt, "-c", "user.name=test", "-c", "user.email=test@invalid", "commit", "-q", "-m", "test: stage files (never pushed)")
        cls.src = git(cls.wt, "rev-parse", "HEAD")
        cls.manifests = {}
        for stage, path in (("RM1", None), ("M2", f"{BASE}/INPUTS_M2.json")):
            runs = stages6.stage_runs(stage, None if path is None else cls.wt / path)
            m = stages6.manifest(stage, runs, cls.src, path, root=cls.wt)
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

    def test_wrong_stage_refused(self):
        ok, lines = self.run_check("M2", self.manifests["RM1"])       # RM1's manifest checked as M2
        self.assertFalse(ok)


if __name__ == "__main__":
    unittest.main()
