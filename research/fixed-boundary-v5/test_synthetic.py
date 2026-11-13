"""Isolated kernels, guards and source gate; no registered inputs are generated."""
import tempfile
import unittest
from common import DEPENDENCY,check_gate
from kernel import Kernel
from comparators import STUDY,FORWARD


def reference(policy,report,rate,delivered,carry):
    fresh=min(660,report-2+220) if delivered else report-2
    upper=min(660,report+2+220) if delivered else report+2
    if rate-1>150:
        return ('refuse',0,fresh,upper,0)
    lower=max(fresh,carry or 0)
    if not 250<=lower<=660:
        return ('refuse',0,lower,upper,0)
    d=min(40,max(0,(lower-250)//150))
    if policy=='early' and upper+220<=660:
        d=0
    if d:
        d=1 if policy=='prudent' else d
        return ('wait',d,lower,upper,lower-150*d)
    return ('write',1,lower,upper,min(660,lower-150+220))


class SyntheticTests(unittest.TestCase):
    def test_independent_observation_kernels(self):
        with tempfile.TemporaryFile(mode='w+') as errors:
            for policy in ('early','prudent'):
                kernel=Kernel(policy,errors)
                try:
                    for lower in (0,100,249,250,251,399,400,401,436,437,438,549,550,551,660,661):
                        for delivered in (False,True):
                            report=lower+2-(220 if delivered else 0)
                            for carry in (None,250,550):
                                got=tuple(kernel.decide(report,149,delivered,carry))
                                self.assertEqual(got,reference(policy,report,149,delivered,carry))
                finally:
                    kernel.close()
            errors.seek(0)
            self.assertEqual(errors.read(),'')

    def test_rate_violation_discards_carry_without_false_fresh_claim(self):
        with tempfile.TemporaryFile(mode='w+') as errors:
            kernel=Kernel('early',errors)
            try:
                self.assertEqual(tuple(kernel.decide(50,153,False,550)),('refuse',0,48,52,0))
                self.assertNotEqual(kernel.decide(500,151,False,None)[0],'refuse')
            finally:
                kernel.close()

    def test_two_frozen_oracles_agree_on_unregistered_tiny_fixture(self):
        rates=lambda t: 40 if t%3 else 130
        errors=lambda t: -2 if t%2 else 2
        for n in (1,3,9,19):
            self.assertEqual(STUDY.oracle(150,n,rates,errors)['cost'],
                             FORWARD.forward_optimum(150,n,rates,errors))

    def test_gate_rejects_wrong_head_missing_job_and_cancelled_job(self):
        names=('Fixed boundary cost study','R research checks','Kernel R Lean proofs',
               'Robust birth and latency evidence','Circuit simulation analysis')
        gate=dict(head_sha=DEPENDENCY,pr_head_sha=DEPENDENCY,runs=[
            dict(name=name,head_sha=DEPENDENCY,status='completed',conclusion='success',run_attempt=1,
                 jobs=[dict(status='completed',conclusion='success')]) for name in names])
        self.assertFalse(check_gate(gate))
        gate['pr_head_sha']='wrong'
        self.assertTrue(check_gate(gate))
        gate['pr_head_sha']=DEPENDENCY
        gate['runs'][0]['jobs']=[]
        self.assertTrue(check_gate(gate))
        gate['runs'][0]['jobs']=[dict(status='completed',conclusion='cancelled')]
        self.assertTrue(check_gate(gate))


if __name__=='__main__':
    unittest.main()
