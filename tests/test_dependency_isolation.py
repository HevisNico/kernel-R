"""Unlisted source, package and bytecode modules must never execute in replay."""
from pathlib import Path
import importlib.util
import json
import py_compile
import shutil
import subprocess
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]


def load_dependency(kind):
    spec = importlib.util.spec_from_file_location(kind + '_dependency', ROOT / 'certify' / kind / 'dependency.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class DependencyIsolation(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.marker = self.root / 'EXECUTED'
        self.local = self.root / 'local'
        self.entry = self.root / 'entry'
        shutil.copytree(ROOT / 'certify/reciprocal_learning', self.local, ignore=shutil.ignore_patterns('__pycache__'))
        shutil.copytree(ROOT / 'certify/reciprocal_entry', self.entry, ignore=shutil.ignore_patterns('__pycache__'))
        self.local_cert = ROOT / 'results/reciprocal_learning/eps1e-1/certificate.json'
        self.entry_cert = ROOT / 'results/reciprocal_entry/eps1e-1/certificate.json'

    def trap(self, directory, kind):
        payload = f"from pathlib import Path\nPath({str(self.marker)!r}).write_text('executed')\nraise RuntimeError('unlisted module executed')\n"
        if kind == 'source':
            (directory / 'json.py').write_text(payload)
            (directory / 'sitecustomize.py').write_text(payload)
        elif kind == 'package':
            (directory / 'json').mkdir()
            (directory / 'json/__init__.py').write_text(payload)
        else:
            source = self.root / 'payload.py'
            source.write_text(payload)
            target = directory / 'json.pyc' if kind == 'bytecode' else directory / '__pycache__/json.pyc'
            target.parent.mkdir(exist_ok=True)
            py_compile.compile(str(source), cfile=str(target), doraise=True)

    def test_local_dependency_ignores_all_unlisted_modules(self):
        dependency = load_dependency('reciprocal_entry')
        for kind in ['source', 'package', 'bytecode', 'cache']:
            with self.subTest(kind=kind):
                code = self.root / ('local_' + kind)
                shutil.copytree(self.local, code)
                self.trap(code, kind)
                _, identity = dependency.verify_dependency('0.1', self.local_cert, code)
                self.assertEqual(identity['independent_check']['status'], 'VERIFIED_WITH_INDEPENDENT_INTEGER_ARITHMETIC')
                self.assertFalse(self.marker.exists())

    def test_entry_and_nested_local_dependency_ignore_unlisted_modules(self):
        for wrapper in ['reciprocal_cadence', 'reciprocal_composition']:
            dependency = load_dependency(wrapper)
            for kind in ['source', 'package', 'bytecode', 'cache']:
                with self.subTest(kind=kind):
                    entry = self.root / (wrapper + '_entry_' + kind)
                    local = self.root / (wrapper + '_nested_' + kind)
                    shutil.copytree(self.entry, entry)
                    shutil.copytree(self.local, local)
                    self.trap(entry, kind)
                    self.trap(local, kind)
                    identity = dependency.verify_dependency('0.1', self.entry_cert, entry, self.local_cert, local)
                    self.assertEqual(identity['independent_check']['status'], 'VERIFIED_ENTRY_AND_COMPOSITION_WITH_INTEGER_ARITHMETIC')
                    self.assertFalse(self.marker.exists())

    def test_authenticated_bytes_and_certificate_are_frozen_before_execution(self):
        dependency = load_dependency('reciprocal_entry')
        certificate = self.root / 'certificate.json'
        certificate.write_bytes(self.local_cert.read_bytes())
        real_run = subprocess.run
        snapshots = []

        def mutate_then_run(args, **kwargs):
            clean = Path(args[6])
            snapshots.append(clean.parent)
            expected = set(json.loads(self.local_cert.read_text())['source_sha256'])
            self.assertEqual({p.name for p in clean.iterdir()}, expected)
            self.assertNotEqual(clean, self.local)
            self.assertEqual(Path(kwargs['cwd']), clean.parent)
            self.assertEqual(args[1:4], ['-I', '-S', '-B'])
            (self.local / 'verify.py').write_text('raise RuntimeError("changed after authentication")')
            certificate.write_text('{}')
            return real_run(args, **kwargs)

        with patch.object(dependency.subprocess, 'run', side_effect=mutate_then_run):
            dependency.verify_dependency('0.1', certificate, self.local)
        self.assertTrue(snapshots)
        self.assertTrue(all(not path.exists() for path in snapshots))

    def test_changed_authenticated_source_is_rejected_before_execution(self):
        dependency = load_dependency('reciprocal_entry')
        (self.local / 'verify.py').write_text('raise RuntimeError("tampered")')
        with patch.object(dependency.subprocess, 'run') as run:
            with self.assertRaisesRegex(RuntimeError, 'source identity mismatch'):
                dependency.verify_dependency('0.1', self.local_cert, self.local)
            run.assert_not_called()


if __name__ == '__main__':
    unittest.main()
