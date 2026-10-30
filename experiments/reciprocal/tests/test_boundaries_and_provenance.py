"""Numerical scheduler boundary and full adaptive-manifest regression tests."""
from pathlib import Path
import copy
import importlib.util
import math
import shutil
import sys
import tempfile
import unittest
from unittest.mock import patch

SOURCE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SOURCE))
sys.path.insert(0, str(SOURCE / 'adaptive'))
import numpy as np
import engine
import model
import provenance


def device(gain=.3):
    return engine.Device([engine.NOMINAL.tolist() for _ in range(3)], .1,
                         [.025] * 3, np.log([gain] * 3).tolist(), .18, [0] * 3)


class FinalBoundaries(unittest.TestCase):
    def run_cell(self, end, arrivals=None, dev=None):
        return engine.simulate(arrivals or [[0.], [], []], dev or device(), end,
                               mode='fixed', checkpoints=[end])

    def test_raw_off_at_end_and_checkpoint(self):
        result = self.run_cell(1.)
        self.assertFalse(any(result['final_state']['raw_active']))
        self.assertEqual(result['snapshots']['1.0'], result['final_state'])

    def test_auxiliary_end_is_ready_and_can_be_carried(self):
        dev = device()
        end = max(e[0] for e in engine.prepare_auxiliary([[0.], [], []], dev))
        result = self.run_cell(end, dev=dev)
        self.assertEqual(result['final_state']['aux_modes'], [0, 0, 0])
        self.assertEqual(result['final_state']['aux_charge'][0], engine.RM)
        self.assertEqual(result['snapshots'][str(end)], result['final_state'])
        carried = model.carry(dev, result)
        continued = engine.simulate([[], [], []], carried, 2., mode='fixed')
        whole = self.run_cell(end + 2., dev=dev)
        self.assertAlmostEqual(continued['final_state']['q'], whole['final_state']['q'], places=12)

    def test_initial_and_final_raw_on_are_applied(self):
        initial = self.run_cell(0.)
        final = self.run_cell(1., arrivals=[[1.], [], []])
        for result, end in [(initial, 0.), (final, 1.)]:
            self.assertTrue(result['final_state']['raw_active'][0])
            self.assertEqual(result['snapshots'][str(end)], result['final_state'])

    def test_just_after_end_events_are_not_consumed(self):
        before = math.nextafter(1., -math.inf)
        result = self.run_cell(before)
        self.assertTrue(result['final_state']['raw_active'][0])
        result = self.run_cell(1., arrivals=[[math.nextafter(1., math.inf)], [], []])
        self.assertFalse(any(result['final_state']['raw_active']))

    def test_zero_duration_initial_error_transition(self):
        dev = device(); dev.initial_aux[0] = 3
        result = self.run_cell(0., arrivals=[[], [], []], dev=dev)
        self.assertEqual(result['final_state']['aux_modes'], [0, 0, 0])

    def test_main_transition_at_end_precedes_snapshot(self):
        dev = device(2.)
        whole = self.run_cell(20., dev=dev)
        for event in whole['main_events']:
            with self.subTest(event=event['event']):
                result = self.run_cell(event['time'], dev=dev)
                want = {'fire': 1, 'fast_end': 2, 'reopen': 0}[event['event']]
                self.assertEqual(result['final_state']['main_mode'], want)
                self.assertEqual(result['snapshots'][str(event['time'])], result['final_state'])

    def test_fast_end_just_after_cut_is_not_applied_early(self):
        dev = device(2.)
        events = self.run_cell(20., dev=dev)['main_events']
        end = next(e['time'] for e in events if e['event'] == 'fast_end')
        result = self.run_cell(math.nextafter(end, -math.inf), dev=dev)
        self.assertEqual(result['final_state']['main_mode'], 1)

    def test_interior_checkpoints_follow_all_simultaneous_events(self):
        dev = device()
        finish = max(e[0] for e in engine.prepare_auxiliary([[0.], [], []], dev))
        result = engine.simulate([[0.], [], []], dev, 3., mode='fixed', checkpoints=[0., 1., finish])
        self.assertTrue(result['snapshots']['0.0']['raw_active'][0])
        self.assertFalse(result['snapshots']['1.0']['raw_active'][0])
        self.assertEqual(result['snapshots'][str(finish)]['aux_modes'], [0, 0, 0])


class AdaptiveProvenance(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(); self.addCleanup(self.tmp.cleanup)
        self.here = Path(self.tmp.name) / 'adaptive'; self.here.mkdir()
        for name in provenance.SOURCES:
            shutil.copyfile(SOURCE / 'adaptive' / name, self.here / name)
        self.plan = provenance.capture(self.here)

    def test_complete_manifest_matches(self):
        self.assertEqual(provenance.verify(self.plan, self.here), self.plan)

    def test_either_engine_change_is_rejected(self):
        for name in ['../engine.py', '../simulate.py']:
            with self.subTest(source=name):
                path = self.here / name; original = path.read_bytes()
                path.write_bytes(original + b'\n# changed equations\n')
                with self.assertRaisesRegex(RuntimeError, 'locked source identity mismatch'):
                    provenance.verify(self.plan, self.here)
                path.write_bytes(original)

    def test_missing_engine_or_legacy_manifest_is_rejected(self):
        for name in ['../engine.py', '../simulate.py']:
            plan = copy.deepcopy(self.plan); del plan['source_sha256'][name]
            with self.assertRaisesRegex(RuntimeError, 'both simulation engines'):
                provenance.verify(plan, self.here)
        with self.assertRaisesRegex(RuntimeError, 'incomplete legacy provenance'):
            provenance.verify({'source_sha256': {k: self.plan['source_sha256'][k]
                               for k in ['model.py', 'run.py']}}, self.here)

    def test_runtime_version_change_is_rejected(self):
        for dependency in ['python', 'numpy', 'scipy']:
            plan = copy.deepcopy(self.plan); plan['runtime_versions'][dependency] = 'different'
            with self.assertRaisesRegex(RuntimeError, 'runtime mismatch'):
                provenance.verify(plan, self.here)

    def test_validation_refuses_legacy_plan_before_dynamics(self):
        out = Path(self.tmp.name) / 'run'; out.mkdir(); (out / 'plan.json').write_text('{}')
        for name, entry in [('validate', 'validate'), ('live_validate', 'validate_live')]:
            with self.subTest(validator=name):
                spec = importlib.util.spec_from_file_location('adaptive_' + name, SOURCE / 'adaptive' / (name + '.py'))
                module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
                with patch.object(model, 'MemoryBank') as replay:
                    with self.assertRaisesRegex(RuntimeError, 'incomplete legacy provenance'):
                        getattr(module, entry)(out)
                    replay.assert_not_called()

    def test_new_run_locks_engines_and_runtime_before_training(self):
        import json
        spec = importlib.util.spec_from_file_location('adaptive_run', SOURCE / 'adaptive/run.py')
        runner = importlib.util.module_from_spec(spec); spec.loader.exec_module(runner)
        out = Path(self.tmp.name) / 'fresh'
        with patch.object(model, 'make_learner', side_effect=RuntimeError('test stops before training')):
            with self.assertRaisesRegex(RuntimeError, 'test stops before training'):
                runner.run(out, replicates=1, training_students=1)
        plan = json.loads((out / 'plan.json').read_text())
        provenance.verify(plan)
        self.assertEqual(set(plan['source_sha256']), set(provenance.SOURCES))
        self.assertEqual(set(plan['runtime_versions']), {'python', 'numpy', 'scipy'})


if __name__ == '__main__':
    unittest.main()
