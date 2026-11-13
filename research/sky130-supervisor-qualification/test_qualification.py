import unittest
import numpy as np

from calibrate import analyze,make_deck,SIGNALS
from noise_bounds import lower_success,summarize


class QualificationTests(unittest.TestCase):
    def test_no_95_percent_actuator(self):
        with self.assertRaises(AssertionError):make_deck(dict(actions=[.95]))

    def test_clock_only_and_joint_inputs_remain_distinct(self):
        c=dict(name='synthetic',actions=[1,0,1],vinit=.384,vinit2=.383,rlk=1e11,section='ss',temperature_C=125,noise=False,joint=False)
        s,starts,stop=make_deck(c)
        self.assertIn('.lib "pdk/models/sky130.lib.spice" ss',s)
        self.assertIn('.option temp=125',s)
        self.assertIn('vinit2 vinit2 0 0.383',s)
        self.assertIn('ta=1 tb=1 tj=2',s)
        self.assertAlmostEqual(starts[2]-starts[0],440e-6)

    def test_noisy_deck_is_not_deterministic_evidence(self):
        c=dict(name='synthetic',actions=[0],vinit=.384,rlk=1e11,section='tt_mm',temperature_C=27,noise=True,seed=2001)
        s,_,_=make_deck(c)
        self.assertEqual(s.count('trnoise('),4)
        self.assertIn('setseed 2001',s)

    def test_incomplete_trace_rejected(self):
        d=np.zeros((2,len(SIGNALS)+1));d[:,0]=[0,.0001]
        with self.assertRaises(AssertionError):analyze(d,{},[],.001)

    def test_exact_cp_edges_and_independent_reference(self):
        self.assertEqual(lower_success(0,5),0)
        self.assertAlmostEqual(lower_success(3,3),.05**(1/3))
        # Published SciPy two-sided95% example k7/n50: lower tail alpha=.025.
        self.assertAlmostEqual(lower_success(7,50,.025),.05819170033997342,places=12)
        self.assertGreater(lower_success(1999,2000),.99)

    def test_interruption_not_filtered_and_pooling_rejected(self):
        t=[dict(trial_id='a',stratum='same-cell',completed=True,all_services_pass=True),
           dict(trial_id='b',stratum='same-cell',completed=False,all_services_pass=True)]
        r=summarize(t);self.assertEqual((r['successes'],r['trials']),(1,2))
        t[1]['stratum']='another-cell'
        with self.assertRaises(ValueError):summarize(t)

    def test_zero_repeats_and_duplicate_ids_rejected(self):
        with self.assertRaises(ValueError):lower_success(0,0)
        t=dict(trial_id='a',stratum='s',completed=True,all_services_pass=True)
        with self.assertRaises(ValueError):summarize([t,t])


if __name__=='__main__':unittest.main()
