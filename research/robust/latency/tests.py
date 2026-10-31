from pathlib import Path
from fractions import Fraction as F
import json,sys,tempfile,unittest
ROOT=Path(__file__).resolve().parents[1];HERE=Path(__file__).resolve().parent;sys.path.insert(0,str(ROOT))
from latency.verify import verify
from latency.obligations import derive
from latency.chain import contract
from integer_intervals import Q
from bounds import Refusal
P=HERE/'certificates/eps0.1_nu0.002_alpha0.json'

class Latency(unittest.TestCase):
    def test_all_certificates_replay(self):
        files=list((HERE/'certificates').glob('*.json'));self.assertEqual(len(files),8)
        for p in files:verify(p,emit=False)
    def test_zero_noise_recovers_zero_radius(self):
        for e in ('0.003','0.1'):
            r=verify(HERE/f'certificates/eps{e}_nu0_alpha0.json',emit=False)
            self.assertEqual(F(r['parameters']['delta']),0)
    def test_noisy_32_cell_period_eight(self):
        c=contract(P,32,104,period='8')
        self.assertEqual(F(c['minimum_period']),F('7.96376'));self.assertEqual(c['root_outputs'],8)
    def test_wire_jitter_accumulates(self):
        c=contract(P,8,32,'.05')
        self.assertEqual(F(c['minimum_period']),F('8.30472'))
    def test_undersized_period_refused(self):
        with self.assertRaisesRegex(Refusal,'phase budget'):contract(P,32,104,period='7.9')
    def test_three_milliseconds_is_not_uniformly_sound(self):
        # Exact interval checks on an admissible learned cell after long +noise silence.
        a=Q(4).ln();k=Q('.5');g=Q('.3')*Q('1.8').exp()
        h=lambda t:a/(a-k)*((-k*Q(t)).exp()-(-a*Q(t)).exp())
        ref=Q('.1')+g*h('.653')
        noisy=Q('.1')+g*h('.65')+Q('.004')-Q('.00001')*(-k*Q('.65')).exp()
        self.assertLess(ref.hi,1);self.assertGreater(noisy.lo,1)
        # Thus ell_ref>.653 and ell_noisy<.650: deviation is strictly >.003.
    def bad(self,change):
        c=json.loads(P.read_text());change(c)
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'bad.json';p.write_text(json.dumps(c))
            with self.assertRaises((Refusal,ValueError,KeyError,TypeError)):verify(p,emit=False)
    def test_wrong_reference_refused(self):self.bad(lambda c:c.update(reference='nominal-gain latency'))
    def test_tampered_birth_dependency(self):self.bad(lambda c:c['birth_certificate'].update(sha256='0'*64))
    def test_empty_source_set(self):self.bad(lambda c:c.update(source_sha256={}))
    def test_too_small_radius_refused(self):self.bad(lambda c:c['parameters'].update(delta='.003'))
    def test_obligation_redirect_refused(self):self.bad(lambda c:c['obligations'][-1].update(left='nu',right='reference_upper'))

if __name__=='__main__':unittest.main()
