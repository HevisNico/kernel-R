"""Regression controls for preserved evidence and complete campaign publication."""
import gzip
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

import campaign_io as io
import validate as local
from birth import validate as birth
from latency import validate as latency
from periodic import validate as periodic

HERE = Path(__file__).resolve().parent
REPOSITORY = HERE.parents[1]
RUNTIME = dict(python='test', numpy='test', scipy='test')
SOURCES = {'source.py': 'test-source-hash'}


class CampaignPublication(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.previous = self.root / 'previous'
        self.previous.mkdir()
        (self.previous / 'validation.json').write_bytes(b'previous PASS report')
        (self.previous / 'traces.jsonl.gz').write_bytes(b'previous valid trace')
        self.old = {p.name: p.read_bytes() for p in self.previous.iterdir()}

    def assert_preserved(self):
        self.assertEqual({p.name: p.read_bytes() for p in self.previous.iterdir()}, self.old)

    def write_pair(self, path):
        (path / 'traces.jsonl.gz').write_bytes(gzip.compress(b'{"case":1}\n', mtime=0))
        report = dict(status='PASS_TEST_FIXTURE', environment=RUNTIME, source_sha256=SOURCES,
                      trace_sha256=io.sha256(path / 'traces.jsonl.gz'))
        (path / 'validation.json').write_text(json.dumps(report))

    def verify(self, path):
        return io.verify_record(path, HERE, SOURCES, RUNTIME)

    def test_success_publishes_a_verified_pair_and_manifest_together(self):
        out = self.root / 'complete'
        with io.publish_run(out, campaign='fixture', verify=self.verify) as staged:
            self.write_pair(staged)
            self.assertFalse(out.exists())
        report = self.verify(out)
        self.assertEqual(report['publication'], dict(schema_version=1, campaign='fixture', quick=False))
        self.assertEqual({p.name for p in out.iterdir()}, {'validation.json', 'traces.jsonl.gz', 'MANIFEST.json'})
        self.assert_preserved()

    def test_failure_before_or_after_trace_writes_never_publishes(self):
        for lines in (0, 3):
            out = self.root / f'failed-{lines}'
            with self.subTest(lines=lines), self.assertRaisesRegex(RuntimeError, 'solver failed'):
                with io.publish_run(out, campaign='fixture', verify=self.verify) as staged:
                    with gzip.open(staged / 'traces.jsonl.gz', 'wt') as trace:
                        for index in range(lines):
                            trace.write(json.dumps(dict(case=index)) + '\n')
                    raise RuntimeError('solver failed')
            self.assertFalse(out.exists())
            failures = list(self.root.glob(out.name + '.FAILED-*.json'))
            self.assertEqual(len(failures), 1)
            self.assertEqual(json.loads(failures[0].read_text())['status'], 'FAILED')
            self.assertFalse(list(self.root.glob('.' + out.name + '-*')))
            self.assert_preserved()

    def test_verification_failure_prevents_publication(self):
        out = self.root / 'invalid'
        with self.assertRaisesRegex(ValueError, 'Trace hash differs'):
            with io.publish_run(out, campaign='fixture', verify=self.verify) as staged:
                self.write_pair(staged)
                (staged / 'traces.jsonl.gz').write_bytes(b'truncated')
        self.assertFalse(out.exists())
        self.assert_preserved()

    def test_existing_output_is_refused_without_modification(self):
        for output in (self.previous, self.previous / 'validation.json'):
            with self.subTest(output=output), self.assertRaisesRegex(ValueError, 'Output already exists'):
                with io.publish_run(output, campaign='fixture', verify=self.verify):
                    self.fail('Existing evidence must be refused before any work')
        self.assert_preserved()

    def test_quick_uses_a_separate_directory_and_explicit_metadata(self):
        out = self.root / 'quick'
        with io.publish_run(out, campaign='local', quick=True, verify=self.verify) as staged:
            self.write_pair(staged)
        self.assertTrue(self.verify(out)['publication']['quick'])
        self.assert_preserved()

    def test_manifest_detects_report_changes_and_its_own_removal(self):
        out = self.root / 'complete'
        with io.publish_run(out, campaign='fixture', verify=self.verify) as staged:
            self.write_pair(staged)
        report_path = out / 'validation.json'
        original = report_path.read_bytes()
        report = json.loads(original)
        report['publication']['quick'] = True
        report_path.write_text(json.dumps(report))
        with self.assertRaisesRegex(ValueError, 'manifest mismatch'):
            self.verify(out)
        report_path.write_bytes(original)
        (out / 'MANIFEST.json').unlink()
        with self.assertRaisesRegex(ValueError, 'missing MANIFEST'):
            self.verify(out)

    def test_missing_trace_has_actionable_guidance(self):
        with self.assertRaisesRegex(ValueError, 'RECORDINGS.md'):
            self.verify(self.root)

    def test_no_implicit_output_directory(self):
        with patch.object(sys, 'argv', ['validate.py']), patch('sys.stderr'), self.assertRaises(SystemExit) as error:
            io.main(lambda out: self.fail('runner must not start'), HERE, lambda: SOURCES, lambda: RUNTIME)
        self.assertEqual(error.exception.code, 2)

    def test_each_real_validator_preserves_archived_reports_on_solver_failure(self):
        modules = ((local, 'run_chain'), (birth, 'run_chain'), (latency, 'run_chain'), (periodic, 'simulate_chain'))
        archived = [HERE / 'evidence/validation.json'] + [HERE / layer / 'evidence/validation.json'
                    for layer in ('birth', 'latency', 'periodic')]
        before = {p: p.read_bytes() for p in archived}
        for index, (module, simulator) in enumerate(modules):
            out = self.root / f'campaign-{index}'
            with self.subTest(module=module.__name__), patch.object(module, simulator, side_effect=RuntimeError('injected solver failure')):
                with self.assertRaisesRegex(RuntimeError, 'injected solver failure'):
                    module.run(out)
            self.assertFalse(out.exists())
            self.assertEqual(before, {p: p.read_bytes() for p in archived})
            self.assertEqual(len(list(self.root.glob(out.name + '.FAILED-*.json'))), 1)

    def test_local_failure_after_one_written_case_keeps_previous_publication(self):
        out = self.root / 'partial'
        # Choose a non-refined scenario so the second solver call is the next
        # case, after its predecessor has already been written to the trace.
        with patch.object(local, 'SCENARIOS', ('slow_positive',)), patch.object(local, 'run_chain', side_effect=[{}, RuntimeError('second case failed')]), patch.object(local, 'audit', return_value={}):
            with self.assertRaisesRegex(RuntimeError, 'second case failed'):
                local.run(out)
        self.assertFalse(out.exists())
        self.assert_preserved()

    def test_restore_refuses_corrupt_archive_before_creating_output(self):
        spec = importlib.util.spec_from_file_location('restore_robust', REPOSITORY / 'tools/restore_robust_recordings.py')
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        out = self.root / 'restored'
        with self.assertRaisesRegex(ValueError, 'SHA-256'):
            module.restore(b'not the release archive', out)
        self.assertFalse(out.exists())
        with self.assertRaisesRegex(ValueError, 'fresh --out'):
            module.restore(b'anything', self.previous)
        self.assert_preserved()


if __name__ == '__main__':
    unittest.main()
