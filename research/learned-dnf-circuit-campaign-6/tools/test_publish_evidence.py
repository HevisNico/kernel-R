"""Tests of publish_evidence.py on a throwaway repository and a local bare remote (no network).

  python -B -m unittest test_publish_evidence        (from this folder)

Each refusal case checks that the remote has no new branch: the failing step stops before any push.
"""
from pathlib import Path
import hashlib
import io
import json
import subprocess
import sys
import tempfile
import unittest
from contextlib import redirect_stdout
from unittest import mock

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import publish_evidence as pe                                  # noqa: E402

E = "evidence/stage/a"


def run(*args, cwd):
    subprocess.run(args, cwd=cwd, check=True, capture_output=True)


class Publish(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        t = Path(self.tmp.name)
        self.repo, self.bare = t / "repo", t / "bare.git"
        run("git", "init", "-q", str(self.bare), "--bare", cwd=t)
        run("git", "init", "-q", str(self.repo), cwd=t)
        for k, v in (("user.name", "Owner"), ("user.email", "owner@example.invalid")):
            run("git", "config", k, v, cwd=self.repo)
        (self.repo / "README").write_text("base\n")
        run("git", "add", "README", cwd=self.repo)
        run("git", "commit", "-q", "-m", "base", cwd=self.repo)
        self.base = subprocess.run(["git", "rev-parse", "HEAD"], cwd=self.repo, capture_output=True,
                                   text=True).stdout.strip()
        run("git", "push", "-q", str(self.bare), "HEAD:refs/heads/base", cwd=self.repo)
        self.src = t / "collected"
        (self.src / "run1" / "evidence").mkdir(parents=True)
        self.files = {"STATE.json": b'{"status": "complete"}\n', "run1/evidence/trace.raw": b"x" * 2500,
                      "run1/stdout.log": b"ok\n"}
        for rel, b in self.files.items():
            (self.src / rel).write_bytes(b)
        self.write_collected()
        self.t = t

    def tearDown(self):
        self.tmp.cleanup()

    def write_collected(self, files=None):
        files = self.files if files is None else files
        (self.src / "COLLECTED.json").write_text(json.dumps({"files": [
            {"path": k, "bytes": len(v), "sha256": hashlib.sha256(v).hexdigest()} for k, v in sorted(files.items())]}))

    def publish(self, branch="ev", work="w", extra=(), author="Owner"):
        argv = ["--collected", str(self.src), "--repo", str(self.repo), "--base", self.base, "--evidence-path", E,
                "--branch", branch, "--message", "evidence", "--work", str(self.t / work), "--remote", str(self.bare)]
        for x in extra:
            argv += ["--extra", x]
        if author:
            argv += ["--expect-author", author]
        out = io.StringIO()
        with redirect_stdout(out):
            rc = pe.main(argv)
        return rc, out.getvalue().strip()

    def remote_branches(self):
        r = subprocess.run(["git", "ls-remote", "--heads", str(self.bare)], capture_output=True, text=True)
        return sorted(line.split("\t")[1] for line in r.stdout.splitlines())

    def test_publishes_and_verifies_with_parts(self):
        with mock.patch.object(pe, "LIMIT", 1000), mock.patch.object(pe, "PART", 900):
            rc, out = self.publish(extra=[str(self.src / "STATE.json") + "=state_copy.json"])
        self.assertEqual(rc, 0, out)
        self.assertTrue(out.startswith("PUBLISHED-VERIFIED "))
        tree = subprocess.run(["git", "ls-tree", "-r", "--name-only", "refs/heads/ev"], cwd=self.bare,
                              capture_output=True, text=True).stdout.split()
        self.assertIn(f"{E}/run1/evidence/trace.raw.part-000", tree)
        self.assertIn(f"{E}/run1/evidence/trace.raw.part-002", tree)
        self.assertNotIn(f"{E}/run1/evidence/trace.raw", tree)
        self.assertIn(f"{E}/PARTS.json", tree)
        self.assertIn(f"{E}/state_copy.json", tree)
        parts = json.loads(subprocess.run(["git", "show", f"refs/heads/ev:{E}/PARTS.json"], cwd=self.bare,
                                          capture_output=True).stdout)
        self.assertEqual(list(parts), ["rule", "files"])
        self.assertEqual([q["bytes"] for q in parts["files"]["run1/evidence/trace.raw"]["parts"]], [900, 900, 700])
        self.assertTrue((self.src / "run1" / "evidence" / "trace.raw").exists())          # nothing deleted

    def test_refuses_missing_file_before_push(self):
        (self.src / "run1" / "stdout.log").unlink()
        rc, out = self.publish()
        self.assertEqual(rc, 1)
        self.assertIn("REFUSED collected file missing", out)
        self.assertEqual(self.remote_branches(), ["refs/heads/base"])

    def test_refuses_sha_mismatch_before_push(self):
        (self.src / "run1" / "stdout.log").write_bytes(b"no\n")
        rc, out = self.publish()
        self.assertEqual(rc, 1)
        self.assertIn("differs from COLLECTED.json", out)
        self.assertEqual(self.remote_branches(), ["refs/heads/base"])

    def test_refuses_unlisted_file_before_push(self):
        (self.src / "stray.txt").write_text("stray\n")
        rc, out = self.publish()
        self.assertEqual(rc, 1)
        self.assertIn("not in COLLECTED.json", out)
        self.assertEqual(self.remote_branches(), ["refs/heads/base"])

    def test_refuses_blob_over_limit_before_push(self):
        # an extra file over the limit is not split: the evidence folder check refuses it
        big = self.t / "big.log"
        big.write_bytes(b"y" * 1200)
        with mock.patch.object(pe, "LIMIT", 1000), mock.patch.object(pe, "PART", 900):
            rc, out = self.publish(extra=[str(big)])
        self.assertEqual(rc, 1)
        self.assertIn("100 MiB or more", out)
        self.assertEqual(self.remote_branches(), ["refs/heads/base"])

    def test_refuses_commit_blob_over_limit_before_push(self):
        # the commit-level guard alone, the folder-level check bypassed
        with mock.patch.object(pe, "LIMIT", 1000), mock.patch.object(pe, "PART", 2000), \
                mock.patch.object(pe, "stage_tree", side_effect=lambda src, listed, dst, extras: (
                    dst.mkdir(parents=True), (dst / "trace.raw").write_bytes(b"x" * 2500), {})[-1]):
            rc, out = self.publish()
        self.assertEqual(rc, 1)
        self.assertIn("a blob of 100 MiB or more", out)
        self.assertEqual(self.remote_branches(), ["refs/heads/base"])

    def test_refuses_wrong_author_before_push(self):
        rc, out = self.publish(author="Someone Else")
        self.assertEqual(rc, 1)
        self.assertIn("expected author", out)
        self.assertEqual(self.remote_branches(), ["refs/heads/base"])

    def test_refuses_existing_branch(self):
        self.assertEqual(self.publish()[0], 0)
        rc, out = self.publish(work="w2")
        self.assertEqual(rc, 1)
        self.assertIn("already exists", out)

    def test_refuses_existing_work_dir(self):
        (self.t / "w").mkdir()
        rc, out = self.publish()
        self.assertEqual(rc, 1)
        self.assertIn("exists", out)
        self.assertEqual(self.remote_branches(), ["refs/heads/base"])


if __name__ == "__main__":
    unittest.main()
