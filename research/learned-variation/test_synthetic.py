"""Unit fixtures for the actual Lean stream; no plant trajectory or campaign."""
import json
from pathlib import Path
import subprocess
import unittest

ROOT = Path(__file__).resolve().parent


def stream(readings, *, horizon=2, cap=10, window=2, budget=20):
    command = f'init {horizon} {cap} {window} 0 {budget}\n'
    command += ''.join(' '.join(map(str, item)) + '\n' if isinstance(item, tuple)
                       else item + '\n' for item in readings)
    run = subprocess.run(['lake', 'env', 'lean', '--run', 'Bridge.lean'], cwd=ROOT,
                         input=command, text=True, capture_output=True, timeout=20)
    if run.returncode:
        raise AssertionError(run.stdout + run.stderr)
    return [json.loads(line) for line in run.stdout.splitlines()]


class LearnerTests(unittest.TestCase):
    def test_fixed_prospective_window_and_definite_refutation(self):
        rows = stream([(0, 10, 0), (1, 10, 0), (2, 10, 0),
                       (3, 15, 0), (4, 15, 0), (5, 15, 0)])
        self.assertIsNone(rows[2]['proposal'])
        self.assertEqual(rows[3]['proposal']['through'], 2)
        self.assertEqual((rows[4]['bound'], rows[4]['remaining'], rows[4]['window_start']), (5, 2, 3))
        self.assertTrue(rows[4]['annotations'][0]['demonstrated'])
        self.assertIsNone(rows[5]['proposal'])
        self.assertEqual(rows[6]['proposal'], {'bound': 5, 'horizon': 2, 'from': 3, 'through': 5})
        self.assertEqual(rows[6]['attempts'], 6)
        self.assertTrue(all(not r['future_guarantee'] for r in rows))

    def test_noise_only_widening_is_ambiguous(self):
        rows = stream([(0, 9, 1), (1, 11, 1)])
        self.assertEqual(rows[-1]['bound'], 4)
        self.assertFalse(rows[-1]['annotations'][0]['demonstrated'])
        self.assertEqual(rows[-1]['remaining'], 2)

    def test_compares_all_eligible_pairs(self):
        rows = stream([(0, 0, 0), (1, 4, 0), (2, 8, 0)])
        self.assertEqual(rows[-1]['bound'], 8)
        self.assertEqual(rows[-1]['refinements'], 2)
        self.assertTrue(any(w['time'] == 0 for w in rows[-1]['annotations'][-1]['witnesses']))

    def test_cap_exhaustion_preserves_trigger_and_previous_annotations(self):
        rows = stream([(0, 0, 0), (1, 4, 0), (2, 20, 0), (3, 0, 0)])
        self.assertEqual(len(rows), 4)
        self.assertEqual(rows[-1]['mode'], 'exhausted-unguaranteed')
        self.assertFalse(rows[-1]['can_observe'])
        self.assertIsNone(rows[-1]['proposal'])
        self.assertEqual(rows[-1]['annotations'][:-1], rows[-2]['annotations'])
        self.assertEqual(rows[-1]['annotations'][-1]['trigger']['time'], 2)
        self.assertEqual(rows[-1]['annotations'][-1]['required'], 20)
        self.assertEqual(rows[-1]['bound'], 4)

    def test_missing_stale_skipped_and_malformed_probes_stop_and_are_paid(self):
        for bad in ['missing', (0, 10, 0), (2, 10, 0), '-1 10 0', 'init 2 10 2 0 20']:
            with self.subTest(reading=bad):
                rows = stream([(0, 10, 0), bad, (2, 10, 0)])
                self.assertEqual(len(rows), 3)
                self.assertEqual(rows[-1]['mode'], 'fault-unguaranteed')
                self.assertEqual(rows[-1]['attempts'], 2)
                self.assertFalse(rows[-1]['can_observe'])

    def test_total_budget_stops_stream_without_refill(self):
        rows = stream([(t, 10, 0) for t in range(20)], budget=3)
        self.assertEqual(len(rows), 4)
        self.assertEqual((rows[-1]['credit'], rows[-1]['attempts']), (0, 3))
        self.assertFalse(rows[-1]['can_observe'])
        self.assertEqual(len(stream([(0, 10, 0)], budget=0)), 1)

    def test_ordinary_monitoring_does_not_restart_validation(self):
        rows = stream([(t, 10, 0) for t in range(8)])
        self.assertEqual(rows[-1]['validation_steps'], 2)
        self.assertEqual(rows[-1]['remaining'], 0)
        self.assertEqual(rows[-1]['proposal']['through'], 2)
        self.assertEqual(rows[-1]['attempts'], 8)

    def test_default_full_horizon_window(self):
        rows = stream([(t, 10, 0) for t in range(42)], horizon=41, window=41, budget=42)
        self.assertIsNone(rows[-2]['proposal'])
        self.assertEqual(rows[-1]['proposal']['through'], 41)
        self.assertEqual(rows[-1]['validation_steps'], 41)

    def test_eof_is_finite_prefix_not_an_autonomous_missing_probe_detector(self):
        rows = stream([(0, 10, 0)])
        self.assertEqual(len(rows), 2)
        self.assertEqual(rows[-1]['attempts'], 1)
        self.assertTrue(rows[-1]['can_observe'])
        self.assertFalse(rows[-1]['future_guarantee'])


if __name__ == '__main__':
    unittest.main()
