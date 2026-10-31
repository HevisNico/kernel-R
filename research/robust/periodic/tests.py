import sys,unittest
from pathlib import Path
from fractions import Fraction as F
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from bounds import Refusal
from periodic.certify_chain import contract
PATH=ROOT/'results/eps0.1/nu0_alpha0.json'

class Periodic(unittest.TestCase):
    def test_constant_period_large_depth(self):
        for n in (1,2,8,32,100,1000):
            c=contract(PATH,n,3*n+8,'7.5')
            self.assertEqual(c['root_emissions'],8)
            self.assertEqual(c['minimum_period'],'15/2')
    def test_global_jitter_budget(self):
        c=contract(PATH,32,104,'7.8',[F(3,620)]*31)
        self.assertEqual(c['total_jitter'],'3/20')
        self.assertEqual(c['minimum_period'],'39/5')
    def test_factor_two_is_required_by_envelope(self):
        with self.assertRaisesRegex(Refusal,'twice'): contract(PATH,8,32,'7.85',[F(1,20)]*7)
    def test_positive_residual(self):
        c=contract(PATH,2,16)
        p=c['positive_residual_comparison'];self.assertLess(F(p['left']),F(p['right_lower']))
    def test_noise_rejected(self):
        with self.assertRaisesRegex(Refusal,'zero noise'):
            contract(ROOT/'results/eps0.1/nu0.002_alpha0.json',2,16)
    def test_amplitude_variation_rejected(self):
        with self.assertRaisesRegex(Refusal,'identical waveforms'):
            contract(ROOT/'results/eps0.1/nu0_alpha0.09.json',2,16)
    def test_invalid_jitter_rejected(self):
        for sigma in (['-.01'],['.06'],[]):
            with self.assertRaisesRegex(Refusal,'jitter'):contract(PATH,2,16,sigmas=sigma)

if __name__=='__main__':unittest.main()
