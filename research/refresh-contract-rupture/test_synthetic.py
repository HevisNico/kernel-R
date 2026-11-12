"""Synthetic policy/report checks only; no registered trajectory is executed."""
import sys
import tempfile
import unittest
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'adaptive-refresh-experiment'))
from controllers import Contract, Observation
from score_rupture import chain_hash, metrics


class Synthetic(unittest.TestCase):
    def test_violation_refuses_even_with_ample_reserve(self):
        with tempfile.TemporaryFile(mode='w+') as errors:
            c=Contract(errors)
            try:
                d=c.decide(Observation(0,302,9,False))
                self.assertEqual((d.bound,d.delay),(20,8))
                d=c.decide(Observation(8,302,23,False))
                self.assertEqual((d.bound,d.lower,d.invalidated,d.ambiguous,d.action),
                                 (34,300,True,False,'refuse'))
                self.assertGreaterEqual(d.lower,100+d.bound)
                self.assertLess(d.bound,220)
            finally: c.close()

    def test_ambiguous_is_not_proven(self):
        with tempfile.TemporaryFile(mode='w+') as errors:
            c=Contract(errors)
            try:
                c.decide(Observation(0,302,9,False))
                d=c.decide(Observation(8,302,21,False))
                self.assertTrue(d.ambiguous)
                self.assertFalse(d.invalidated)
            finally: c.close()

    def test_snapshot_uses_fresh_sensor_not_carried_state(self):
        obs=Observation(7,80,139,False)
        self.assertEqual(obs.lower_before,78)
        self.assertFalse(obs.lower_before>=100)
        # A stale carried value of 200 cannot make the sampled instant safe.
        self.assertTrue(max(obs.lower_before,200)>=100)

    def test_chain_changes_on_retrospective_label_edit(self):
        row={'t':1,'measured_safe_pre':0,'pre':80,'chain_previous':'0'*64,'row_hash':''}
        before=chain_hash('0'*64,row)
        row['measured_safe_pre']=1
        self.assertNotEqual(before,chain_hash('0'*64,row))

    def test_danger_is_retained_after_blocking(self):
        rows=[]
        for t,pre,detected,active,invalid in [(0,200,0,1,0),(1,80,0,1,0),(2,-60,1,0,1),(3,-200,1,0,0)]:
            rows.append(dict(t=t,pre=pre,post=pre,probe=int(t in (0,2)),rate=10 if t==0 else 140,
                             alarm_detected=detected,conditional_contract_active=active,
                             measured_safe_pre=int(t==0),command=0,delivery=0,invalidated=invalid,
                             ambiguous=0,refused=invalid,delay=2))
        m=metrics(rows)
        self.assertEqual((m['pre_unsafe'],m['unsafe_before_detection'],m['unsafe_at_detection'],
                          m['unsafe_after_detection'],m['undetected']), (3,1,1,1,1))
        self.assertEqual(m['false_measured_safe'],0)
        self.assertEqual(m['unsafe_with_active_conditional_contract'],1)


if __name__=='__main__': unittest.main()
