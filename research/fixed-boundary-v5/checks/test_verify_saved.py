"""Temporary-repository controls for publication verification; no real raw edits."""
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

from verify_saved import (EvidenceError, EXPECTED_COUNT, MANIFEST_PATH, POSTRUN_PATH,
                          RAW_PREFIX, decode_json, manifest_entries, verify_saved_manifest)


class SavedEvidenceTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='v5-publication-test-')
        self.repo = Path(self.temp.name)
        self.git('init', '-q')
        self.git('config', 'user.name', 'Synthetic verifier fixture')
        self.git('config', 'user.email', 'fixture@example.invalid')
        self.git('config', 'commit.gpgsign', 'false')
        self.entries = []
        for n in range(EXPECTED_COUNT):
            path = RAW_PREFIX+f'saved-{n:02d}.bin'
            data = b'raw\r\n\x00'+bytes([n])+b'\xff\n'
            self.entries.append(dict(path=path, bytes=len(data), sha256=hashlib.sha256(data).hexdigest()))
        self.manifest = dict(status='pending fixture', attempt=1, files=self.entries)
        self.write_json(MANIFEST_PATH, self.manifest)
        self.write_json(POSTRUN_PATH, dict(raw_evidence_committed=False))
        self.git('add', MANIFEST_PATH, POSTRUN_PATH)
        self.git('commit', '-qm', 'published authorization fixture')
        self.authorization = self.git('rev-parse', 'HEAD').strip()
        for n, item in enumerate(self.entries):
            path = self.repo/item['path']
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(b'raw\r\n\x00'+bytes([n])+b'\xff\n')
        self.git('add', RAW_PREFIX)
        self.git('commit', '-qm', 'dedicated raw fixture')
        self.raw_commit = self.git('rev-parse', 'HEAD').strip()
        self.postrun = dict(raw_evidence_committed=True, raw_evidence_commit=self.raw_commit)
        self.write_json(POSTRUN_PATH, self.postrun)
        self.git('add', POSTRUN_PATH)
        self.git('commit', '-qm', 'publication metadata fixture')

    def tearDown(self):
        self.temp.cleanup()

    def git(self, *args):
        return subprocess.check_output(['git', *args], cwd=self.repo,
                                       stderr=subprocess.PIPE, text=True)

    def write_json(self, path, value):
        target = self.repo/path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(json.dumps(value, indent=2)+'\n')

    def verify(self):
        return verify_saved_manifest(self.repo, self.authorization)

    def test_exact_authorized_binary_bytes_and_dedicated_commit_pass(self):
        result = self.verify()
        self.assertEqual(result['files'], 50)
        self.assertEqual(result['raw_evidence_commit'], self.raw_commit)
        self.assertEqual(result['bytes'], sum(item['bytes'] for item in self.entries))

    def test_same_length_corruption_rejected_by_sha256(self):
        path = self.repo/self.entries[0]['path']
        data = path.read_bytes()
        path.write_bytes(b'X'+data[1:])
        with self.assertRaisesRegex(EvidenceError, 'Local SHA256 differs'):
            self.verify()

    def test_truncated_bytes_rejected(self):
        path = self.repo/self.entries[0]['path']
        path.write_bytes(path.read_bytes()[:-1])
        with self.assertRaisesRegex(EvidenceError, 'Local byte count differs'):
            self.verify()

    def test_missing_file_rejected(self):
        (self.repo/self.entries[0]['path']).unlink()
        with self.assertRaisesRegex(EvidenceError, 'inventory differs; missing='):
            self.verify()

    def test_unlisted_extra_file_rejected(self):
        (self.repo/RAW_PREFIX/'not-authorized.bin').write_bytes(b'extra')
        with self.assertRaisesRegex(EvidenceError, 'inventory differs'):
            self.verify()

    def test_path_escape_rejected_before_file_lookup(self):
        bad = json.loads(json.dumps(self.manifest))
        bad['files'][0]['path'] = RAW_PREFIX+'../outside.bin'
        self.write_json(MANIFEST_PATH, bad)
        with self.assertRaisesRegex(EvidenceError, 'Unsafe or noncanonical'):
            self.verify()

    def test_symlink_substitution_rejected(self):
        path = self.repo/self.entries[0]['path']
        data = path.read_bytes()
        target = self.repo/'outside-copy.bin'
        target.write_bytes(data)
        path.unlink()
        path.symlink_to(target)
        with self.assertRaisesRegex(EvidenceError, 'Symlink in evidence inventory'):
            self.verify()

    def test_hash_and_manifest_joint_manipulation_rejected(self):
        path = self.repo/self.entries[0]['path']
        path.write_bytes(b'manipulated')
        bad = json.loads(json.dumps(self.manifest))
        bad['files'][0]['bytes'] = len(path.read_bytes())
        bad['files'][0]['sha256'] = hashlib.sha256(path.read_bytes()).hexdigest()
        self.write_json(MANIFEST_PATH, bad)
        with self.assertRaisesRegex(EvidenceError, 'differs from the authorized file entries'):
            self.verify()

    def test_false_publication_flag_rejected(self):
        self.postrun['raw_evidence_committed'] = False
        self.write_json(POSTRUN_PATH, self.postrun)
        with self.assertRaisesRegex(EvidenceError, 'does not confirm raw evidence publication'):
            self.verify()

    def test_postrun_cannot_point_to_followup_commit(self):
        self.postrun['raw_evidence_commit'] = self.git('rev-parse', 'HEAD').strip()
        self.write_json(POSTRUN_PATH, self.postrun)
        with self.assertRaisesRegex(EvidenceError, 'sole parent'):
            self.verify()

    def test_raw_commit_with_unrelated_extra_addition_rejected(self):
        # Construct an alternate temporary raw commit from the authorization
        # parent while retaining the fixture's exactly matching disk evidence.
        self.git('checkout', '-q', '--detach', self.raw_commit)
        (self.repo/'unrelated.txt').write_text('not an authorized raw file\n')
        self.git('add', 'unrelated.txt')
        self.git('commit', '--amend', '-qm', 'raw plus forbidden unrelated addition')
        altered = self.git('rev-parse', 'HEAD').strip()
        self.write_json(POSTRUN_PATH, dict(raw_evidence_committed=True, raw_evidence_commit=altered))
        with self.assertRaisesRegex(EvidenceError, 'change exactly 50 files'):
            self.verify()

    def test_fifty_changes_including_modification_are_not_fifty_additions(self):
        self.git('checkout', '-q', '--detach', self.raw_commit)
        self.git('rm', '--cached', self.entries[-1]['path'])
        self.write_json(POSTRUN_PATH, dict(raw_evidence_committed=False, altered_in_raw_commit=True))
        self.git('add', POSTRUN_PATH)
        self.git('commit', '--amend', '-qm', '49 additions and one forbidden modification')
        altered = self.git('rev-parse', 'HEAD').strip()
        self.write_json(POSTRUN_PATH, dict(raw_evidence_committed=True, raw_evidence_commit=altered))
        with self.assertRaisesRegex(EvidenceError, 'non-addition'):
            self.verify()

    def test_executable_blob_mode_is_not_regular_evidence_mode(self):
        self.git('checkout', '-q', '--detach', self.raw_commit)
        self.git('update-index', '--chmod=+x', self.entries[0]['path'])
        self.git('commit', '--amend', '-qm', 'unexpected executable evidence mode')
        altered = self.git('rev-parse', 'HEAD').strip()
        self.write_json(POSTRUN_PATH, dict(raw_evidence_committed=True, raw_evidence_commit=altered))
        with self.assertRaisesRegex(EvidenceError, 'nonregular evidence file'):
            self.verify()

    def test_wrong_committed_blob_rejected_even_when_local_bytes_are_correct(self):
        self.git('checkout', '-q', '--detach', self.raw_commit)
        path = self.repo/self.entries[0]['path']
        original = path.read_bytes()
        path.write_bytes(b'X'+original[1:])
        self.git('add', self.entries[0]['path'])
        self.git('commit', '--amend', '-qm', 'wrong committed raw bytes')
        altered = self.git('rev-parse', 'HEAD').strip()
        path.write_bytes(original)
        self.write_json(POSTRUN_PATH, dict(raw_evidence_committed=True, raw_evidence_commit=altered))
        with self.assertRaisesRegex(EvidenceError, 'Committed SHA256 differs'):
            self.verify()

    def test_manifest_shape_and_duplicate_keys_rejected(self):
        with self.assertRaisesRegex(EvidenceError, 'Duplicate JSON key'):
            decode_json(b'{"attempt":1,"attempt":2}')
        bad = json.loads(json.dumps(self.manifest))
        bad['files'][1] = bad['files'][0]
        with self.assertRaisesRegex(EvidenceError, 'Duplicate evidence path'):
            manifest_entries(bad)
        bad = json.loads(json.dumps(self.manifest))
        bad['files'][0]['bytes'] = True
        with self.assertRaisesRegex(EvidenceError, 'Invalid byte count'):
            manifest_entries(bad)

    def test_status_text_may_change_without_changing_authorized_files(self):
        self.manifest['status'] = 'committed fixture'
        self.write_json(MANIFEST_PATH, self.manifest)
        self.assertEqual(self.verify()['files'], 50)


if __name__ == '__main__':
    unittest.main()
