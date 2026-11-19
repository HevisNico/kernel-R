"""Tests of marker_check.py (marker 2, the stages/ layout) on real manifests built by stages6, in a throwaway worktree
on top of marker 2's commit, with local commits never pushed: a protocol commit adding the stage files of RM1, M2 and
RN, then a source commit adding their run lists and M2's inputs.

Accepted: a measure stage without inputs (RM1), one with inputs (M2), the network stage (RN). Refused, each in its own
test: a missing frozen path, an extra path, a wrong hash, a source commit not after the marker, a missing inputs file, a
missing run list, a wrong stage, a top-level STAGE_<S>.md, protocol_path not the stage file, a wrong protocol_sha256, a
protocol_commit that is not the commit adding the stage file, a protocol_commit before marker 2, a source_commit equal
to its protocol_commit, marker 2's commit not after PREDICTION.md's, python -O, an unexpected error of the stage check,
a dirty tree, a tree differing from the source commit, another marker, a MARKER_COMMIT before marker 2, a marker missing
from the tree.

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

MARKER_COMMIT = marker_check.MARKER_INTRODUCED                           # 7eda858, marker 2
BEFORE_MARKER = "6d8e4d73564bdb83363ed37f5d092607203ee319"               # the README commit just before marker 2
FROZEN_COMMIT = "6f29fe659d8759a5e1bf23c1f5a0e299176f1c7c"
BASE = marker_check.BASE
STAGES = marker_check.STAGES
IDENT = ["-c", "user.name=test", "-c", "user.email=test@invalid"]


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
        (cls.wt / STAGES).mkdir(parents=True, exist_ok=True)
        for stage in ("RM1", "M2", "RN"):
            (cls.wt / stages6.stage_path(stage)).write_text(stages6.stage_file_text(stage))
        git(cls.wt, "add", STAGES)
        git(cls.wt, *IDENT, "commit", "-q", "-m", "test: stage files (never pushed)")
        cls.proto = git(cls.wt, "rev-parse", "HEAD")
        inputs = f"{STAGES}/INPUTS_M2.json"
        allow = dict(stage="M2", instances={str(s): dict(D_V={c: ["0.001", "0.001"] for c in "abc"}) for s in range(7801, 7806)})
        (cls.wt / inputs).write_text(json.dumps(allow, indent=1, sort_keys=True) + "\n")
        data = dict(RM1=None, M2=cls.wt / inputs, RN=cls.wt / stages6.REHEARSAL_PREDICTIONS)
        cls.runs = {s: stages6.stage_runs(s, p) for s, p in data.items()}
        for s, runs in cls.runs.items():
            (cls.wt / stages6.runs_path(s)).write_text(stages6.runs_text(s, runs))
        git(cls.wt, "add", STAGES)
        git(cls.wt, *IDENT, "commit", "-q", "-m", "test: run lists and inputs (never pushed)")
        cls.src = git(cls.wt, "rev-parse", "HEAD")
        cls.manifests = {}
        for s, runs in cls.runs.items():
            m = stages6.manifest(s, runs, cls.src, inputs if s == "M2" else None, root=cls.wt)
            f = cls.tmp / f"CAMPAIGN_{s}.json"
            f.write_text(json.dumps(m, indent=1) + "\n")
            cls.manifests[s] = f

    @classmethod
    def tearDownClass(cls):
        git(ROOT, "worktree", "remove", "--force", str(cls.wt))
        git(ROOT, "worktree", "prune")
        shutil.rmtree(cls.tmp, ignore_errors=True)

    def tearDown(self):
        git(self.wt, "checkout", "-q", "--detach", self.src)

    def variant(self, stage, change):
        m = json.loads(self.manifests[stage].read_text())
        change(m)
        f = self.tmp / f"variant_{stage}.json"
        f.write_text(json.dumps(m, indent=1) + "\n")
        return f

    def run_check(self, stage, f, marker_commit=MARKER_COMMIT):
        return marker_check.check(stage, f, marker_commit, self.wt)

    def refused(self, stage, f, text, marker_commit=MARKER_COMMIT):
        ok, lines = self.run_check(stage, f, marker_commit)
        self.assertFalse(ok, lines)
        self.assertTrue(any(x.startswith("REFUSED") and text in x for x in lines), lines)
        return lines

    # accepted
    def test_new_layout_accepted(self):
        for stage, data in (("RM1", 2), ("M2", 3), ("RN", 2)):
            ok, lines = self.run_check(stage, self.manifests[stage])
            self.assertTrue(ok, lines)
            m = json.loads(self.manifests[stage].read_text())
            self.assertEqual((m["protocol_path"], m["protocol_commit"]), (f"{STAGES}/STAGE_{stage}.md", self.proto))
            self.assertTrue(any(f"(90 frozen, {data} data)" in x for x in lines), lines)
            self.assertTrue(any("the 90 frozen paths, the stage file and the run list" in x for x in lines), lines)

    # the frozen set and the declared data
    def test_missing_path_refused(self):
        f = self.variant("RM1", lambda m: m["source_sha256"].pop(f"{BASE}/campaign6/c6.py"))
        self.refused("RM1", f, "frozen path missing")

    def test_extra_path_refused(self):
        f = self.variant("RM1", lambda m: m["source_sha256"].__setitem__(f"{BASE}/drafts/MAPPING_U.md", "0" * 64))
        self.refused("RM1", f, "not allowed")

    def test_wrong_hash_refused(self):
        f = self.variant("RM1", lambda m: m["source_sha256"].__setitem__(f"{BASE}/campaign6/net6.py", "1" * 64))
        self.refused("RM1", f, "another hash")

    def test_missing_inputs_refused(self):
        f = self.variant("M2", lambda m: m["source_sha256"].pop(f"{STAGES}/INPUTS_M2.json"))
        self.refused("M2", f, "declared data file missing")

    def test_missing_run_list_refused(self):
        f = self.variant("RN", lambda m: m["source_sha256"].pop(f"{STAGES}/RUNS_RN.json"))
        self.refused("RN", f, "declared data file missing")

    def test_top_level_stage_file_refused(self):
        top = f"{BASE}/STAGE_RM1.md"                      # the first rehearsal's, still in the tree
        import hashlib
        h = hashlib.sha256((self.wt / top).read_bytes()).hexdigest()
        f = self.variant("RM1", lambda m: m["source_sha256"].__setitem__(top, h))
        self.refused("RM1", f, "superseded layout")

    def test_wrong_stage_refused(self):
        ok, lines = self.run_check("M2", self.manifests["RM1"])
        self.assertFalse(ok)

    def test_non_descendant_source_refused(self):
        f = self.variant("RM1", lambda m: m.__setitem__("source_commit", FROZEN_COMMIT))
        self.refused("RM1", f, "does not descend from the marker's commit")

    # the kit's protocol fields
    def test_protocol_path_not_stage_file_refused(self):
        f = self.variant("RM1", lambda m: m.__setitem__("protocol_path", f"{BASE}/PREDICTION.md"))
        self.refused("RM1", f, "is not the stage file")

    def test_wrong_protocol_sha256_refused(self):
        f = self.variant("RM1", lambda m: m.__setitem__("protocol_sha256", "2" * 64))
        self.refused("RM1", f, "is not the stage file's SHA-256")

    def test_protocol_commit_not_the_adding_commit_refused(self):
        f = self.variant("RM1", lambda m: m.__setitem__("protocol_commit", MARKER_COMMIT))
        self.refused("RM1", f, "is not the only commit adding the stage file")

    def test_source_equal_to_protocol_refused(self):
        f = self.variant("RM1", lambda m: m.__setitem__("source_commit", self.proto))
        self.refused("RM1", f, "must differ from protocol_commit")

    def test_protocol_commit_before_marker_2_refused(self):
        """A stage file and run list committed on top of the commit before marker 2."""
        git(self.wt, "checkout", "-q", "--detach", BEFORE_MARKER)
        (self.wt / STAGES).mkdir(parents=True, exist_ok=True)
        (self.wt / self.stages6.stage_path("RM1")).write_text(self.stages6.stage_file_text("RM1"))
        git(self.wt, "add", STAGES)
        git(self.wt, *IDENT, "commit", "-q", "-m", "test: stage file before marker 2 (never pushed)")
        (self.wt / self.stages6.runs_path("RM1")).write_text(self.stages6.runs_text("RM1", self.runs["RM1"]))
        git(self.wt, "add", STAGES)
        git(self.wt, *IDENT, "commit", "-q", "-m", "test: run list (never pushed)")
        m = self.stages6.manifest("RM1", self.runs["RM1"], git(self.wt, "rev-parse", "HEAD"), root=self.wt)
        f = self.tmp / "early_RM1.json"
        f.write_text(json.dumps(m, indent=1) + "\n")
        self.refused("RM1", f, "does not descend from marker 2's commit")

    def test_marker_2_not_after_prediction_refused(self):
        orphan = git(self.wt, *IDENT, "commit-tree", git(self.wt, "hash-object", "-t", "tree", "-w", "/dev/null"), "-m", "test: orphan (never pushed)")
        with mock.patch.object(marker_check, "PROTOCOL_COMMIT", orphan):
            self.refused("RM1", self.manifests["RM1"], "does not descend from PREDICTION.md's commit")

    # the marker
    def test_other_marker_refused(self):
        f = self.wt / marker_check.MARKER
        f.write_text(f.read_text() + "\n")
        git(self.wt, *IDENT, "commit", "-q", "-am", "test: other marker (never pushed)")
        self.refused("RM1", self.manifests["RM1"], "not the pinned", marker_commit=git(self.wt, "rev-parse", "HEAD"))

    def test_marker_commit_before_introduction_refused(self):
        self.refused("RM1", self.manifests["RM1"], "does not descend from 7eda858", marker_commit=FROZEN_COMMIT)

    def test_marker_missing_from_tree_refused(self):
        (self.wt / marker_check.MARKER).unlink()
        try:
            self.refused("RM1", self.manifests["RM1"], "missing from REPO's tree")
        finally:
            git(self.wt, "checkout", "-q", "--", marker_check.MARKER)

    # REPO's tree, python -O and the stage check
    def test_dirty_tree_refused(self):
        extra = self.wt / BASE / "untracked.txt"
        extra.write_text("x\n")
        try:
            lines = self.refused("RM1", self.manifests["RM1"], "not clean")
            self.assertTrue(any("stage check is not run" in x for x in lines), lines)
        finally:
            extra.unlink()

    def test_tree_differs_from_source_refused(self):
        f = self.wt / "research/learned-dnf-circuit-campaign-5/smoke/README.md"
        f.write_text(f.read_text() + "changed\n")
        git(self.wt, *IDENT, "commit", "-q", "-am", "test: change (never pushed)")
        lines = self.refused("RM1", self.manifests["RM1"], "differs from source_commit")
        self.assertTrue(any(x.startswith("REPO ") and "HEAD" in x for x in lines), lines)

    def test_optimized_python_refused(self):
        out = self.tmp / "opt"
        out.mkdir(exist_ok=True)
        f = out / "CAMPAIGN_RM1.json"
        f.write_text(self.manifests["RM1"].read_text())
        r = subprocess.run([sys.executable, "-O", "-B", str(HERE / "marker_check.py"), "RM1", str(f), MARKER_COMMIT, str(self.wt)],
                           capture_output=True, text=True)
        self.assertEqual(r.returncode, 1, r.stdout + r.stderr)
        report = (out / "MARKER_CHECK_RM1.txt").read_text()
        self.assertIn("python -O", report)
        self.assertIn("VERDICT: REFUSED", report)

    def test_unexpected_stage_check_error_refused(self):
        import c6
        with mock.patch.object(c6, "stage_check", side_effect=RuntimeError("unexpected")):
            self.refused("RM1", self.manifests["RM1"], "does not pass c6.stage_check: RuntimeError: unexpected")


if __name__ == "__main__":
    unittest.main()
