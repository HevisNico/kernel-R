"""Adversarial certificate regressions and analytic hybrid-flow oracles."""
import json, math, tempfile, unittest
from pathlib import Path
from fractions import Fraction as F
from bounds import Refusal
from chain import contract, schedule
from verify import verify
from simulate_events import History, initial_state, simulate, A
HERE=Path(__file__).resolve().parent
CERT=HERE/'results/eps0.1/nu0.002_alpha0.json'


class CertificateRegressions(unittest.TestCase):
    def check_bad(self, change):
        c=json.loads(CERT.read_text()); change(c)
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'bad.json'; p.write_text(json.dumps(c))
            with self.assertRaises((Refusal,ValueError,TypeError,KeyError)): verify(p,emit=False)
    def test_empty_manifest(self): self.check_bad(lambda c:c.update(source_sha256={}))
    def test_missing_source(self): self.check_bad(lambda c:c['source_sha256'].pop('bounds.py'))
    def test_changed_digest(self): self.check_bad(lambda c:c['source_sha256'].update({'bounds.py':'0'*64}))
    def test_extra_source_path(self): self.check_bad(lambda c:c['source_sha256'].update({'../untrusted.py':'0'*64}))
    def test_conclusion(self): self.check_bad(lambda c:c['conclusion'].update(A_emissions=999))
    def test_protocol(self): self.check_bad(lambda c:c['protocol'].update(B_source='no inputs'))
    def test_model(self): self.check_bad(lambda c:c['model'].update(noise='unbounded noise'))
    def test_section(self): self.check_bad(lambda c:c['section'].update(E=['0','0']))
    def test_obligation_relation(self): self.check_bad(lambda c:c['obligations'][0].update(relation='greater_than'))
    def test_redirected_false_inequality(self):
        def change(c):
            name='learned_above_threshold_by_0.9'
            c['bounds'][name+'.right'][0]='0'
            for o in c['obligations']:
                if o['name']==name: o.update(left='nu',right='epsilon')
        self.check_bad(change)
    def test_widened_bound_that_loses_margin(self):
        self.check_bad(lambda c:c['bounds']['learned_above_threshold_by_0.9.right'].__setitem__(0,'0'))
    def test_extra_field(self): self.check_bad(lambda c:c.update(unchecked_conclusion=True))
    def test_non_exact_parameter(self): self.check_bad(lambda c:c['parameters'].update(noise_bound=.002))


class ChainContracts(unittest.TestCase):
    def test_original_two_cell_counts(self):
        c=contract(CERT,2,16)
        self.assertEqual(c['period'],'8'); self.assertEqual([x['emissions'] for x in c['nodes']],[13,10])
    def test_many_depths_exact_arithmetic(self):
        for n in (1,2,3,4,8,16,32,100,1000,10**6):
            p=schedule(n,3*n+8)
            self.assertGreaterEqual(p-F(n-1,2),F(15,2))
            if n<=1000:
                k=3*n+8
                self.assertEqual(sum(k-3*(i+1) for i in range(n)),n*k-3*n*(n+1)//2)
    def test_fixed_eight_refused_at_depth_three(self):
        with self.assertRaisesRegex(Refusal,'period too short'): schedule(3,17,'8')
    def test_insufficient_inputs(self):
        with self.assertRaises(Refusal): schedule(8,24)
    def test_bad_depth(self):
        for n in (0,-1,1.5,True):
            with self.assertRaises(Refusal): schedule(n,20)


class AnalyticOracles(unittest.TestCase):
    def test_error_endpoint_dose_with_signed_noise(self):
        for scenario,nu,sign in [('slow_positive',0,1),('slow_positive',.002,1),('fast_negative',.002,-1)]:
            h=History(.1,nu,0,scenario); y=initial_state(); y[1:4]=.1
            result=simulate([],h,end=.3,state=y,modes=(0,[3,3,3]),rtol=1e-12,atol=1e-14)
            rate=A/.15*(.9 if scenario=='slow_positive' else 1.1); w=sign*nu
            exact_t=math.log((.1-w/rate)/(.025-w/rate))/rate; exact_d=.6+8*w*exact_t
            self.assertEqual(len(result['errors']),3)
            for e in result['errors']:
                self.assertAlmostEqual(e['end'],exact_t,places=10)
                self.assertAlmostEqual(e['dose'],exact_d,places=10)
                self.assertAlmostEqual(e['dose'],e['physical_dose'],places=10)
    def test_fast_exit_time_with_signed_noise(self):
        for scenario,sign in [('slow_positive',1),('fast_negative',-1)]:
            nu=.002; y=initial_state(); y[0]=1
            r=simulate([],History(.1,nu,0,scenario),end=1.1,state=y,modes=(1,[0,0,0]),rtol=1e-12,atol=1e-14)
            expected=math.log((1-sign*nu/A)/(.25-sign*nu/A))/A
            transitions=[x for x in r['transitions'] if x['coordinate']=='q']
            self.assertAlmostEqual(transitions[0]['time'],expected,places=10)
            self.assertEqual(transitions[0]['new'],2)
    def test_long_initial_silence(self):
        r=simulate([],History(.1,.002,0,'slow_positive'),end=100,state=initial_state(1))
        self.assertEqual(r['outputs'],[]); self.assertEqual(r['main'],0); self.assertEqual(r['aux'],[0,0,0])
        self.assertAlmostEqual(r['state'][0],.104,places=10)
        self.assertEqual(r['state'][4:8],r['initial'][4:8])
    def test_legacy_endpoint_overshoot_is_detected(self):
        m=.1; dose=0.; rate=A/.15; step=1e-4
        while m>.025: dose+=8*rate*m*step; m-=rate*m*step
        self.assertGreater(dose-.6,1e-4)


if __name__=='__main__': unittest.main()
