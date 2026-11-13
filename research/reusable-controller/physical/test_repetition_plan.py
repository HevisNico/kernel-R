"""Synthetic ledger/statistical checks only; no simulated evidence is generated."""
import copy
import math
import unittest

import repetition_plan as R


class BoundsTests(unittest.TestCase):
    def test_zero_and_all_successes(self):
        for alpha in (.05, .05 / 37):
            self.assertEqual(R.cp_lower(0, 100, alpha), 0)
            self.assertAlmostEqual(R.cp_lower(100, 100, alpha), alpha ** .01, places=13)

    def test_intermediate_enumerated_polynomials(self):
        # P[Bin(2,p)>=1] = 2p-p²; P[Bin(3,p)>=2] = 3p²-2p³.
        self.assertAlmostEqual(R.cp_lower(1, 2), 1 - math.sqrt(.95), places=14)
        p = .2
        self.assertAlmostEqual(R.cp_lower(2, 3, 3*p*p-2*p*p*p), p, places=14)
        self.assertAlmostEqual(R.binomial_upper_tail(3, 2, p), .104, places=14)

    def test_bonferroni_is_lower(self):
        for s in (1, 50, 99, 100):
            self.assertLess(R.cp_lower(s, 100, .05 / 37), R.cp_lower(s, 100, .05))

    def test_invalid_counts(self):
        for args in ((101, 100), (-1, 100), (0, 0), (True, 100)):
            with self.assertRaises(R.PlanError):
                R.cp_lower(*args)


class LedgerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.plan = R.make_plan(R.frozen_source())
        records = []
        for run in cls.plan['runs']:
            records.append(dict(run, status='done', runtime=cls.plan['runtime'],
                                trace_sha256=R.sha(('synthetic trace ' + run['trial_id']).encode()),
                                noise_waveform_sha256=R.sha(('synthetic noise ' + run['trial_id']).encode()),
                                outcomes=[dict(port=p, count_agreement=True,
                                               measured_residual_success=True)
                                          for p in run['eligible_ports']]))
        cls.payload = dict(plan_sha256=R.sha(R.canonical(cls.plan)),
                           endpoint_extractor_sha256='c'*64, records=records)

    def test_grouping_and_frozen_cohort(self):
        self.assertEqual(len(self.plan['runs']), 3500)
        self.assertEqual(sum(len(r['eligible_ports']) for r in self.plan['runs']), 3700)
        self.assertEqual(len({r['noise_seed'] for r in self.plan['runs']}), 3500)
        self.assertNotIn([6004, 1], self.plan['eligible_keys'])
        self.assertEqual(self.plan['status'], 'NOT_STARTED')
        self.assertFalse(self.plan['noise']['seed_supported_by_existing_simulator_wrapper'])

    def test_all_success_and_mean_not_pooled(self):
        result = R.analyse(self.plan, self.payload)
        self.assertEqual(len(result['per_port']), 37)
        expected = (.05 / 37) ** .01
        self.assertAlmostEqual(result['mean_simultaneous_lower95']['joint_success'], expected, places=13)
        self.assertLess(expected, .05 ** (1 / 3700))

    def test_count_agreement_does_not_imply_residual_success(self):
        payload = copy.deepcopy(self.payload)
        payload['records'][0]['outcomes'][0]['measured_residual_success'] = False
        result = R.analyse(self.plan, payload)['per_port'][0]['endpoints']
        self.assertEqual(result['count_agreement']['successes'], 100)
        self.assertEqual(result['measured_residual_success']['successes'], 99)
        self.assertEqual(result['joint_success']['successes'], 99)

    def test_failed_run_counts_against_both_ports(self):
        payload = copy.deepcopy(self.payload)
        row = next(r for r in payload['records'] if r['cell'] == 6032)
        row.update(status='failed', reason='synthetic solver timeout', outcomes=[])
        result = R.analyse(self.plan, payload)
        self.assertEqual(len(result['failed_runs']), 1)
        for row in result['per_port']:
            if row['cell'] == 6032:
                self.assertEqual(row['endpoints']['joint_success']['successes'], 99)

    def test_missing_duplicate_wrong_identity_refused(self):
        mutations = [lambda p: p['records'].pop(),
                     lambda p: p['records'].__setitem__(1, p['records'][0]),
                     lambda p: p['records'][0].update(noise_seed=-1),
                     lambda p: p['records'][0].update(outcomes=[]),
                     lambda p: p['records'][1].update(noise_waveform_sha256=p['records'][0]['noise_waveform_sha256']),
                     lambda p: p['records'][0]['outcomes'][0].pop('measured_residual_success'),
                     lambda p: p.update(plan_sha256='0'*64)]
        for mutate in mutations:
            payload = copy.deepcopy(self.payload)
            mutate(payload)
            with self.assertRaises(R.PlanError):
                R.analyse(self.plan, payload)


if __name__ == '__main__':
    unittest.main()
