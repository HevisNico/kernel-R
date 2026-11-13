"""Independent arithmetic controls for the exploratory study; no old runner."""
import itertools
import unittest
from unittest.mock import patch
from study import (SERVICE, DOSE, CAPACITY, INITIAL, N, Controller, Observation,
                   fresh_lower, next_lower, wait_limit, leakage, reserve_error,
                   oracle, simulate)


def forward_optimum(hard, horizon, rates, errors):
    """Independent forward relaxation; explicit physical ticks on every edge."""
    layers = [dict() for _ in range(horizon+1)]
    layers[0][(INITIAL, INITIAL+errors(0)-2)] = 1
    for t in range(horizon):
        for (actual, certified), cost in layers[t].items():
            choices = [('write', 1)]
            choices += [('wait', d) for d in range(1, min(40,horizon-t)+1)
                        if certified-hard*d >= SERVICE+hard]
            for action, duration in choices:
                true, bound = actual, certified
                for tick in range(t+1,t+duration+1):
                    true -= rates(tick)
                    bound -= hard
                    assert true >= SERVICE
                    if action == 'write':
                        true, bound = min(CAPACITY,true+DOSE), min(CAPACITY,bound+DOSE)
                end = t+duration
                # A clipped pulse needs its pre-delivery measurement, not a
                # fictitious error applied after clipping.
                before = actual-rates(end) if action == 'write' else true
                measured = before+errors(end)-2
                if action == 'write':
                    measured = min(CAPACITY, measured+DOSE)
                new = (true,max(bound,measured))
                candidate = cost+1+10*(action=='write')
                previous = layers[end].get(new)
                if previous is None or candidate < previous:
                    layers[end][new] = candidate
    return min(layers[horizon].values())


class StudyTests(unittest.TestCase):
    def test_robust_guard_preserves_service_and_readiness(self):
        for hard in (140,150):
            for lower in range(SERVICE+hard,CAPACITY+1):
                for loss in range(hard+1):
                    self.assertGreaterEqual(lower-loss,SERVICE)
                    self.assertGreaterEqual(min(CAPACITY,lower-loss+DOSE),SERVICE+hard)
                for delay in range(1,wait_limit(lower,hard)+1):
                    self.assertGreaterEqual(lower-hard*delay,SERVICE+hard)

    def test_fresh_lower_sound_even_across_saturation(self):
        for pre in range(-220,CAPACITY+1):
            for error,delivered in itertools.product(range(-2,3),(False,True)):
                actual = min(CAPACITY,pre+DOSE) if delivered else pre
                lower = fresh_lower(pre+error,delivered)
                self.assertLessEqual(lower,actual)
                self.assertGreaterEqual(lower,actual-4)

    def test_hard_violation_requires_lower_exceedance(self):
        for hard in (140,150):
            for error in (-1,0,1):
                c = Controller(hard,'hard_max_wait')
                self.assertNotEqual(c.decide(Observation(0,500,hard+error,False))[0],'refuse')
                c = Controller(hard,'hard_max_wait')
                self.assertEqual(c.decide(Observation(0,500,hard+3+error,False))[0],'refuse')
            c = Controller(hard,'hard_max_wait')
            self.assertNotEqual(c.decide(Observation(0,500,hard,False))[0],'refuse')

    def test_candidate_rejection_is_measurement_justified_and_irreversible(self):
        c = Controller(150,'optimistic_shield')
        c.decide(Observation(0,440,10,False))
        c.decide(Observation(1,430,140,False))
        c.decide(Observation(2,420,10,False))
        self.assertEqual(c.candidate,'hard')
        self.assertEqual(len(c.revisions),1)
        self.assertGreater(c.revisions[0]['measured_lower'],c.revisions[0]['refuted_upper'])

    def test_safety_mutations_are_detected(self):
        mutations = (
            ('study.wait_limit', lambda lower,hard: min(40,max(0,(lower-SERVICE)//hard))),
            ('study.next_lower', lambda lower,hard,action,delay:
                min(CAPACITY,lower-20+DOSE) if action=='write' else lower-20*delay),
            ('study.fresh_lower', lambda report,delivered:
                min(CAPACITY,report+DOSE) if delivered else report),
        )
        for name, altered in mutations:
            with self.subTest(mutation=name), patch(name,altered):
                with self.assertRaises(AssertionError):
                    simulate(150,'hard_max_wait')

    def test_dynamic_program_matches_independent_forward_solver(self):
        for hard in (140,150):
            rates = lambda t: 10 if t<5 else 140
            errors = lambda t: 2 if t%2 else -2
            for horizon in (1,2,6,12,30):
                self.assertEqual(oracle(hard,horizon,rates,errors)['cost'],
                                 forward_optimum(hard,horizon,rates,errors))

    def test_full_horizon_optima_agree_in_both_directions(self):
        for hard in (140,150):
            self.assertEqual(oracle(hard)['cost'],forward_optimum(hard,N,leakage,reserve_error))

    def test_recorded_policy_paths_safe_and_learning_adds_no_gain_here(self):
        for hard in (140,150):
            fixed,trace = simulate(hard,'hard_max_wait')
            adaptive,other = simulate(hard,'optimistic_shield')
            self.assertEqual(trace,other)
            self.assertEqual(len(adaptive['revisions']),1)
            for policy in ('prudent_hard','hard_fill'):
                result,_ = simulate(hard,policy)
                self.assertFalse(result['unsafe_pre'] or result['unsafe_post'] or result['refusals'])
            self.assertFalse(fixed['unsafe_pre'] or fixed['unsafe_post'] or fixed['refusals'])


if __name__ == '__main__':
    unittest.main()
