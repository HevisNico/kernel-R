"""Certificate tampering, target-section regression and analytic MARK-dose tests."""
from pathlib import Path
from fractions import Fraction as F
import copy,json,math,subprocess,sys,tempfile,unittest
ROOT=Path(__file__).resolve().parents[1];HERE=Path(__file__).resolve().parent;sys.path.insert(0,str(ROOT))
from birth.verify import verify
from birth.obligations import derive
from birth.simulator import History,initial_state,simulate
from integer_intervals import Q
from bounds import Refusal
P=HERE/'certificates/eps0.1_nu0.002_alpha0.json'

class Entry(unittest.TestCase):
    def test_all_points_replay(self):
        files=list((HERE/'certificates').glob('*.json'));self.assertEqual(len(files),8)
        for p in files:self.assertEqual(verify(p,emit=False)['strict_obligations'],48)
    def test_original_narrow_section_is_not_reused(self):
        b,_=derive(Q,'0.1','0.002','0')
        self.assertGreater(b['entry_q'].hi,F('.10001'))
        self.assertLess(b['entry_recovery'].lo,F('.17999'))
        self.assertGreater(b['entry_recovery'].hi,F('.18001'))
        self.assertEqual(b['entry_recovery'].lo,b['local.b'].lo)
        self.assertEqual(b['entry_recovery'].hi,b['local.b'].hi)
    def test_zero_noise_recovers_exact_MARK(self):
        b,_=derive(Q,'0.1','0','0')
        self.assertEqual(b['protected_MARK_dose'].lo,F('.1'));self.assertEqual(b['protected_MARK_dose'].hi,F('.1'))
    def test_large_noise_refused(self):
        with self.assertRaisesRegex(RuntimeError,'main_reopens_before_next_input'):derive(Q,'0.1','.003','0')
    def bad(self,mutate):
        c=json.loads(P.read_text());mutate(c)
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'bad.json';p.write_text(json.dumps(c))
            with self.assertRaises((Refusal,ValueError,TypeError,KeyError)):verify(p,emit=False)
    def test_empty_manifest(self):self.bad(lambda c:c.update(source_sha256={}))
    def test_changed_protocol(self):self.bad(lambda c:c['protocol'].update(resets='reset to prepared state'))
    def test_changed_section(self):self.bad(lambda c:c['entry'].update(b=['.17999','.18001']))
    def test_wrong_count(self):self.bad(lambda c:c['entry'].update(warmup_emissions_per_cell=13))
    def test_redirected_obligation(self):self.bad(lambda c:c['obligations'][-1].update(left='local.nu',right='local.epsilon'))
    def test_removed_obligation(self):self.bad(lambda c:c['obligations'].pop())
    def test_optimized_execution_refused(self):
        r=subprocess.run([sys.executable,'-B','-O',str(HERE/'verify.py'),str(P)],capture_output=True)
        self.assertNotEqual(r.returncode,0)
    def test_analytic_signed_MARK(self):
        for history,sign in [('slow_positive',1),('fast_negative',-1)]:
            nu=.002;h=History(.1,nu,0,history)
            r=simulate([(8*j,0) for j in range(16)],h,end=160,rtol=1e-12,atol=1e-14,max_step=.08)
            mark=[m for m in r['marks'] if m['dose']>1e-5]
            self.assertEqual(len(mark),1)
            rate=math.log(1.25)/.02*(.9 if sign==1 else 1.1);w=sign*nu
            duration=math.log((1-w/rate)/(.8-w/rate))/rate
            self.assertAlmostEqual(mark[0]['end']-mark[0]['start'],duration,places=10)
            self.assertAlmostEqual(mark[0]['dose'],.1+.5*w*duration,places=10)
            self.assertEqual(len(r['outputs']),12)
            self.assertEqual(r['state'][6],r['initial'][6])

if __name__=='__main__':unittest.main()
