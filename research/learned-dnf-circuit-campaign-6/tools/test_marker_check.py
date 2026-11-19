"""Tests of marker_check.py (the candidate for marker 3: attempts, the record binding, F1, F2), on real manifests
built by stages6 in a throwaway worktree, with local commits never pushed: a stand-in marker 3 (the frozen files'
SHA-256 at HEAD), then for attempt t1 the stage files of RM1, M2, RN and Q, RN's and Q's records alone with their gate
files, then the run lists and M2's inputs. The pins are patched to the stand-in, and PREDICTION.md's commit to HEAD's
(so that the tests run in CI's depth-1 checkout).

  python -B -m unittest test_marker_check        (from this folder, with the pinned venv)
"""
import hashlib
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

BASE = marker_check.BASE
ATT = "t1"
IDENT = ["-c", "user.name=test", "-c", "user.email=test@invalid"]
WORKFLOW = ".github/workflows/learned-dnf-circuit-campaign-6.yml"


def git(repo, *a):
    return subprocess.run(["git", "-C", str(repo), *a], check=True, capture_output=True, text=True).stdout.strip()


class MarkerCheck(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = Path(tempfile.mkdtemp(prefix="c6-markercheck-"))
        cls.wt = cls.tmp / "wt"
        git(ROOT, "worktree", "add", "-q", "--detach", str(cls.wt), "HEAD")
        cls.base = git(cls.wt, "rev-parse", "HEAD")
        sys.path.insert(0, str(cls.wt / BASE / "campaign6"))
        import stages6
        import predicted6
        cls.stages6 = stages6
        files = {p: hashlib.sha256((cls.wt / p).read_bytes()).hexdigest() for p in stages6.frozen()}
        (cls.wt / marker_check.MARKER).write_text(json.dumps(dict(marker="test stand-in for marker 3", files=files), indent=1) + "\n")
        cls.commit("test: stand-in marker 3", marker_check.MARKER)
        cls.marker = git(cls.wt, "rev-parse", "HEAD")
        cls.pins = dict(MARKER_SHA256=hashlib.sha256((cls.wt / marker_check.MARKER).read_bytes()).hexdigest(),
                        MARKER_INTRODUCED=cls.marker, PROTOCOL_COMMIT=cls.base)
        a = stages6.attempt_dir(ATT)
        (cls.wt / a).mkdir(parents=True)
        # the records, alone with their gate files: RN's (round 1) and Q's (one eligible campaign instance)
        xs_rn = [dict(seed=s, measured=True, eligible=True, gate_K0=True, needs=n) for s, n in
                 ((7701, dict(a=4, b=4, c1=5, c2=4)), (7706, dict(a=4, b=4, c1=4, c2=5)))]
        rn = dict(what="test", instances=xs_rn, network_runs=predicted6.network_runs(xs_rn, rounds=(1,)))
        (cls.wt / f"{a}/PREDICTED_RN.json").write_text(predicted6.text(rn))
        for s in (7701, 7706):
            (cls.wt / f"{a}/Gate6_{s}.lean").write_text(f"-- test gate {s}\n")
        cls.commit("test: RN's record alone", f"{a}/PREDICTED_RN.json", f"{a}/Gate6_7701.lean", f"{a}/Gate6_7706.lean")
        xs_q = [dict(seed=7801, measured=True, eligible=True, gate_K0=True, needs=dict(a=4, b=4, c1=4, c2=4))] + \
               [dict(seed=s, measured=False, eligible=False, gate_K0=False) for s in (7802, 7803, 7804, 7805)]
        q = dict(what="test", instances=xs_q, network_runs=predicted6.network_runs(xs_q))
        (cls.wt / f"{a}/PREDICTED.json").write_text(predicted6.text(q))
        (cls.wt / f"{a}/Gate6_7801.lean").write_text("-- test gate 7801\n")
        cls.commit("test: Q's record alone", f"{a}/PREDICTED.json", f"{a}/Gate6_7801.lean")
        for stage in ("RM1", "M2", "RN", "Q"):
            (cls.wt / stages6.stage_path(stage, ATT)).write_text(stages6.stage_file_text(stage, ATT))
        cls.commit("test: stage files", a)
        cls.proto = git(cls.wt, "rev-parse", "HEAD")
        allow = dict(stage="M2", instances={str(s): dict(D_V={c: ["0.001", "0.001"] for c in "abc"}) for s in range(7801, 7806)})
        (cls.wt / stages6.data_path("M2", ATT)).write_text(json.dumps(allow, indent=1, sort_keys=True) + "\n")
        cls.runs = {}
        for stage in ("RM1", "M2", "RN", "Q"):
            d = stages6.data_path(stage, ATT)
            cls.runs[stage] = stages6.stage_runs(stage, None if d is None else cls.wt / d)
            (cls.wt / stages6.runs_path(stage, ATT)).write_text(stages6.runs_text(stage, cls.runs[stage]))
        cls.commit("test: run lists and inputs", a)
        cls.src = git(cls.wt, "rev-parse", "HEAD")
        cls.manifests = {}
        for stage in ("RM1", "M2", "RN", "Q"):
            m = stages6.manifest(stage, cls.runs[stage], cls.src, ATT, root=cls.wt)
            f = cls.tmp / f"CAMPAIGN_{stage}.json"
            f.write_text(json.dumps(m, indent=1) + "\n")
            cls.manifests[stage] = f

    @classmethod
    def commit(cls, msg, *paths):
        git(cls.wt, "add", *paths)
        git(cls.wt, *IDENT, "commit", "-q", "-m", msg)

    @classmethod
    def tearDownClass(cls):
        git(ROOT, "worktree", "remove", "--force", str(cls.wt))
        git(ROOT, "worktree", "prune")
        shutil.rmtree(cls.tmp, ignore_errors=True)

    def setUp(self):
        self.patches = [mock.patch.object(marker_check, k, v) for k, v in self.pins.items()]
        for p in self.patches:
            p.start()

    def tearDown(self):
        for p in self.patches:
            p.stop()
        git(self.wt, "checkout", "-q", "--detach", self.src)

    def variant(self, stage, change):
        m = json.loads(self.manifests[stage].read_text())
        change(m)
        f = self.tmp / f"variant_{stage}.json"
        f.write_text(json.dumps(m, indent=1) + "\n")
        return f

    def run_check(self, stage, f, marker_commit=None):
        return marker_check.check(stage, ATT, f, marker_commit or self.marker, self.wt)

    def refused(self, stage, f, text, marker_commit=None):
        ok, lines = self.run_check(stage, f, marker_commit)
        self.assertFalse(ok, lines)
        self.assertTrue(any(x.startswith("REFUSED") and text in x for x in lines), lines)
        return lines

    def test_accepted(self):
        """A measure stage without data (RM1), with inputs (M2), RN with its record, Q with its record."""
        for stage, data in (("RM1", 2), ("M2", 3), ("RN", 3), ("Q", 3)):
            ok, lines = self.run_check(stage, self.manifests[stage])
            self.assertTrue(ok, lines)
            n = len(self.stages6.frozen())
            self.assertTrue(any(f"({n} frozen, {data} data)" in x for x in lines), (stage, lines))
        ok, lines = self.run_check("Q", self.manifests["Q"])
        self.assertTrue(any(x.startswith("record ") and "PREDICTED.json" in x and "gate files" in x for x in lines), lines)

    def test_frozen_set(self):
        self.refused("RM1", self.variant("RM1", lambda m: m["source_sha256"].pop(f"{BASE}/campaign6/c6.py")), "frozen path missing")
        self.refused("RM1", self.variant("RM1", lambda m: m["source_sha256"].__setitem__(f"{BASE}/drafts/MAPPING_U.md", "0" * 64)), "not allowed")
        self.refused("RM1", self.variant("RM1", lambda m: m["source_sha256"].__setitem__(WORKFLOW, "1" * 64)), "another hash")

    def test_data_required(self):
        self.refused("M2", self.variant("M2", lambda m: m["source_sha256"].pop(self.stages6.data_path("M2", ATT))), "declared data file missing")
        self.refused("Q", self.variant("Q", lambda m: m["source_sha256"].pop(self.stages6.data_path("Q", ATT))), "declared data file missing")
        self.refused("RN", self.variant("RN", lambda m: m["source_sha256"].pop(self.stages6.runs_path("RN", ATT))), "declared data file missing")

    def test_superseded_stage_files_refused(self):
        for top in (f"{BASE}/STAGE_RM1.md", f"{BASE}/stages/STAGE_RM1.md"):
            self.refused("RM1", self.variant("RM1", lambda m: m["source_sha256"].__setitem__(top, "2" * 64)), "outside an attempt's folder")

    def test_protocol_fields(self):
        self.refused("RM1", self.variant("RM1", lambda m: m.__setitem__("protocol_path", f"{BASE}/PREDICTION.md")), "is not the stage file")
        self.refused("RM1", self.variant("RM1", lambda m: m.__setitem__("protocol_sha256", "3" * 64)), "is not the stage file's SHA-256")
        self.refused("RM1", self.variant("RM1", lambda m: m.__setitem__("protocol_commit", self.marker)), "is not the only commit adding")
        self.refused("RM1", self.variant("RM1", lambda m: m.__setitem__("source_commit", self.proto)), "must differ from protocol_commit")

    def test_attempt(self):
        ok, lines = marker_check.check("RM1", "Bad Id", self.manifests["RM1"], self.marker, self.wt)
        self.assertFalse(ok)
        ok, lines = marker_check.check("RM1", "t2", self.manifests["RM1"], self.marker, self.wt)
        self.assertFalse(ok, lines)

    def test_manifest_inside_repo_refused(self):
        """F1."""
        inside = self.wt / "CAMPAIGN_RM1.json"
        try:
            shutil.copy(self.manifests["RM1"], inside)
            self.refused("RM1", inside, "inside REPO")
        finally:
            inside.unlink()

    def test_head_beyond_kit_allowance_refused(self):
        """F2: REPO's head changes a file the kit would refuse after the source commit."""
        f = self.wt / f"{BASE}/campaign6/README.md"
        f.write_text(f.read_text() + "changed\n")
        git(self.wt, *IDENT, "commit", "-q", "-am", "test: README after the source commit (never pushed)")
        self.refused("RM1", self.manifests["RM1"], "more than the kit allows")

    def test_record_must_be_alone(self):
        """Finding 11: a record committed with other files, or without the gate of a measured instance, refuses."""
        a = self.stages6.attempt_dir(ATT)
        rec = git(self.wt, "show", f"{self.src}:{a}/PREDICTED.json")
        git(self.wt, "checkout", "-q", "--detach", self.marker)                    # a new history on top of the marker
        (self.wt / a).mkdir(parents=True, exist_ok=True)
        (self.wt / f"{a}/PREDICTED.json").write_text(rec + "\n")
        (self.wt / f"{a}/NOTES.txt").write_text("not a gate file\n")            # no Gate6_7801.lean, and an extra file
        self.commit("test: Q's record with another file (never pushed)", a)
        (self.wt / self.stages6.stage_path("Q", ATT)).write_text(self.stages6.stage_file_text("Q", ATT))
        self.commit("test: Q's stage file (never pushed)", a)
        runs = self.stages6.stage_runs("Q", self.wt / self.stages6.data_path("Q", ATT))
        (self.wt / self.stages6.runs_path("Q", ATT)).write_text(self.stages6.runs_text("Q", runs))
        self.commit("test: Q's run list (never pushed)", a)
        m = self.stages6.manifest("Q", runs, git(self.wt, "rev-parse", "HEAD"), ATT, root=self.wt)
        f = self.tmp / "bad_Q.json"
        f.write_text(json.dumps(m, indent=1) + "\n")
        lines = self.refused("Q", f, "adds more than the record and its gate files")
        self.assertTrue(any("no gate file for measured instances [7801]" in x for x in lines), lines)

    def test_marker(self):
        self.refused("RM1", self.manifests["RM1"], "does not descend from", marker_commit=self.base)
        with mock.patch.object(marker_check, "MARKER_SHA256", "4" * 64):
            self.refused("RM1", self.manifests["RM1"], "not the pinned")
        orphan = git(self.wt, *IDENT, "commit-tree", git(self.wt, "hash-object", "-t", "tree", "-w", "/dev/null"), "-m", "test: orphan")
        with mock.patch.object(marker_check, "PROTOCOL_COMMIT", orphan):
            self.refused("RM1", self.manifests["RM1"], "does not descend from PREDICTION.md's commit")

    def test_tree_and_stage_check(self):
        extra = self.wt / BASE / "untracked.txt"
        extra.write_text("x\n")
        try:
            self.refused("RM1", self.manifests["RM1"], "not clean")
        finally:
            extra.unlink()
        import c6
        with mock.patch.object(c6, "stage_check", side_effect=RuntimeError("unexpected")):
            self.refused("RM1", self.manifests["RM1"], "does not pass c6.stage_check: RuntimeError: unexpected")
        out = self.tmp / "opt"
        out.mkdir(exist_ok=True)
        f = out / "CAMPAIGN_RM1.json"
        f.write_text(self.manifests["RM1"].read_text())
        code = ("import sys; sys.path.insert(0, sys.argv[1]); import marker_check as mc; "
                f"mc.MARKER_SHA256, mc.MARKER_INTRODUCED, mc.PROTOCOL_COMMIT = {self.pins['MARKER_SHA256']!r}, {self.marker!r}, {self.base!r}; "
                "mc.main(sys.argv[2:])")
        r = subprocess.run([sys.executable, "-O", "-B", "-c", code, str(HERE), "RM1", ATT, str(f), self.marker, str(self.wt)], capture_output=True, text=True)
        self.assertEqual(r.returncode, 1, r.stdout + r.stderr)
        self.assertIn("python -O", (out / "MARKER_CHECK_RM1.txt").read_text())


if __name__ == "__main__":
    unittest.main()
