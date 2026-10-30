"""Lean extraction must reject incomplete or inconsistent adaptive provenance."""
from pathlib import Path
import importlib.util
import json
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'proof/lean/scripts'))
spec = importlib.util.spec_from_file_location('adaptive_evidence', ROOT / 'proof/lean/scripts/generate_evidence.py')
emitter = importlib.util.module_from_spec(spec)
spec.loader.exec_module(emitter)


class AdaptiveEvidence(unittest.TestCase):
    def setUp(self):
        self.bundle = emitter.verify_bundle()
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.output = Path(self.tmp.name)

    def extract(self):
        with patch.object(emitter, 'verify_bundle', return_value=self.bundle), patch.object(emitter, 'OUTPUT', self.output):
            return emitter.adaptive()

    def test_complete_reproduced_evidence_is_accepted(self):
        result = self.extract()
        self.assertTrue((self.output / 'KernelR/Recorded.lean').exists())
        metadata = next(iter(result.values()))
        self.assertEqual(metadata['source_manifest_version'], 2)
        self.assertEqual(set(metadata['runtime_versions']), {'python', 'numpy', 'scipy'})

    def test_legacy_manifest_is_rejected(self):
        path = '08_Adaptive_Lessons/plan.json'
        plan = json.loads(self.bundle[path]); plan.pop('source_manifest_version')
        self.bundle[path] = json.dumps(plan).encode()
        with self.assertRaisesRegex(ValueError, 'complete source manifest'):
            self.extract()

    def test_modified_bundled_engine_is_rejected(self):
        self.bundle['02_R_Simulation/engine.py'] += b'\n# altered\n'
        with self.assertRaisesRegex(ValueError, 'source identity mismatch'):
            self.extract()

    def test_missing_numerical_runtime_is_rejected(self):
        path = '08_Adaptive_Lessons/plan.json'
        plan = json.loads(self.bundle[path]); del plan['runtime_versions']['scipy']
        self.bundle[path] = json.dumps(plan).encode()
        with self.assertRaisesRegex(ValueError, 'runtime identity is missing'):
            self.extract()

    def test_different_learned_policy_is_rejected(self):
        path = '08_Adaptive_Lessons/policies.json'
        policies = json.loads(self.bundle[path])
        next(p for p in policies if p['arm'] == 'actual_credit')['choices'] = [0, 0, 0]
        self.bundle[path] = json.dumps(policies).encode()
        with self.assertRaisesRegex(ValueError, 'differs from the formalized stopping rule'):
            self.extract()


if __name__ == '__main__':
    unittest.main()
