"""Independent controls for the declared exploratory grid."""
from functools import lru_cache
import json
from pathlib import Path
import unittest
from sweep import ROOT, reference, noise, rate, simulate, action_difference, forward_oracle


def backward_oracle(capacity,scenario,probe_price,write_price=100,horizon=264):
    """Separate backward recurrence; explicit step-by-step loss summation."""
    @lru_cache(None)
    def solve(time,actual,certified):
        if time==horizon:
            return probe_price
        choices=[]
        for duration in range(1,min(40,horizon-time)+1):
            if certified-150*duration<250:
                continue
            true=actual
            bound=certified
            for k in range(1,duration+1):
                true-=rate(scenario,time+k)
                bound-=150
            observed=true+noise(time+duration)-2
            choices.append(probe_price+solve(time+duration,true,max(observed,bound)))
        before=actual-rate(scenario,time+1)
        delivered=min(capacity,before+220)
        fresh=min(capacity,before+noise(time+1)-2+220)
        carry=min(capacity,certified-150+220)
        choices.append(probe_price+write_price+solve(time+1,delivered,max(fresh,carry)))
        return min(choices)
    initial=min(440,capacity)
    return solve(0,initial,initial+noise(0)-2)


class SweepTests(unittest.TestCase):
    def test_forward_backward_agree_short_and_full_cases(self):
        for capacity,scenario,horizon in [(300,'jump',20),(440,'high',20),
                                          (660,'jump',264),(660,'high',264),
                                          (1500,'jump',20),(6600,'high',20)]:
            prices=(1,10,100,1000)
            forward=forward_oracle(capacity,scenario,prices,horizon=horizon)['costs']
            backward=tuple(backward_oracle(capacity,scenario,p,horizon=horizon) for p in prices)
            self.assertEqual(forward,backward)

    def test_high_capacity_expensive_probe_headline_independently(self):
        forward=forward_oracle(6600,'jump',(10,1000))['costs']
        backward=tuple(backward_oracle(6600,'jump',p) for p in (10,1000))
        self.assertEqual(forward,backward)

    def test_low_jump_action_identity_is_not_just_log_identity(self):
        ref=reference()
        for capacity in (300,660,6600):
            fixed,a=simulate(ref,capacity,'jump','hard_max_wait')
            adaptive,b=simulate(ref,capacity,'jump','optimistic_shield')
            self.assertEqual(action_difference(a,b)['differing_periods'],0)
            self.assertEqual((fixed['probes'],fixed['writes']),(adaptive['probes'],adaptive['writes']))
            self.assertEqual(len(adaptive['revisions']),1)

    def test_guard_family_covers_capacity_range(self):
        ref=reference()
        for capacity in (300,440,660,1000,1500,3000,6600):
            for scenario in ('jump','high'):
                for policy in ('hard_max_wait','optimistic_shield','hard_fill'):
                    result,_=simulate(ref,capacity,scenario,policy)
                    self.assertFalse(result['unsafe_pre'] or result['unsafe_post'] or result['refusals'])

    def test_price_axis_reweights_recorded_traces(self):
        saved=json.loads((ROOT/'RESULTS.json').read_text())
        self.assertEqual(len(saved['cases']),14)
        self.assertEqual(len(saved['cells']),56)
        cases={(x['scenario'],x['capacity']):x for x in saved['cases']}
        for cell in saved['cells']:
            case=cases[(cell['scenario'],cell['capacity'])]
            price=round(cell['probe_over_write']*100)
            for name,column in [('hard_max_wait','fixed_cost'),('optimistic_shield','optimistic_cost'),('hard_fill','fill_cost')]:
                p=case['policies'][name]
                self.assertEqual(cell[column],price*p['probes']+100*p['writes'])
                self.assertGreaterEqual(cell[column],cell['oracle_cost'])


if __name__=='__main__':
    unittest.main()
