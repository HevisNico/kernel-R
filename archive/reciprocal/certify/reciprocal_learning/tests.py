"""Positive certificates and deliberate refusal/tamper tests, standard library only."""
from pathlib import Path
from fractions import Fraction
import unittest,tempfile,json,sys,subprocess,hashlib,copy,contextlib,io,argparse
import certify as producer
import verify as checker
from integer_intervals import Q
from decimal_intervals import I

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]


class LocalProofTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temporary=tempfile.TemporaryDirectory(dir=HERE)
        cls.path=Path(cls.temporary.name)
        cls.certificates={}
        with contextlib.redirect_stdout(io.StringIO()):
            for eps in ['0.003','0.1']:
                path=cls.path/(eps+'.json');producer.certify(eps,path);checker.verify(path)
                cls.certificates[eps]=json.loads(path.read_text())
    @classmethod
    def tearDownClass(cls):cls.temporary.cleanup()
    def reject(self,document):
        path=self.path/'tampered.json';path.write_text(json.dumps(document))
        with self.assertRaises((checker.Refusal,KeyError,ValueError,TypeError)):
            with contextlib.redirect_stdout(io.StringIO()):checker.verify(path)
    def test_both_supported_boxes_verified(self):
        for eps,certificate in self.certificates.items():
            self.assertEqual(len(certificate['obligations']),31)
            self.assertEqual(certificate['epsilon_relative'],eps)
    def test_inherited_decimal_source_is_byte_identical(self):
        original=ROOT/'engine_eps3e-3/kernel/R_cycle_local_A20_2026-10-18/intervalles_decimaux.py'
        copied=(HERE/'decimal_intervals.py').read_bytes()
        if original.exists():self.assertEqual(copied,original.read_bytes())
        self.assertEqual(hashlib.sha256(copied).hexdigest(),'b7797c2be191b6baff61fd4d1e3087999aca097bf871c3452d801be7741ec444')
    def test_float_endpoints_rejected(self):
        for cls in [I,Q]:
            with self.assertRaises(TypeError):cls(.1)
    def test_integer_rational_arithmetic_all_signs(self):
        values=[Fraction(-7,3),Fraction(-1,5),Fraction(0),Fraction(2,7),Fraction(5,2)]
        for a in values:
            for b in values:
                for result,want in [(Q(a)+Q(b),a+b),(Q(a)-Q(b),a-b),(Q(a)*Q(b),a*b)]:
                    self.assertLessEqual(result.lo,want);self.assertGreaterEqual(result.hi,want)
                if b:
                    result=Q(a)/Q(b);self.assertLessEqual(result.lo,a/b);self.assertGreaterEqual(result.hi,a/b)
        with self.assertRaises(ZeroDivisionError):Q(1)/Q(-1,1)
    def test_integer_transcendentals_round_trip_and_exact_cases(self):
        self.assertEqual(Q(0).exp().lo,Fraction(1));self.assertEqual(Q(1).ln().hi,Fraction(0))
        for value in ['0.3','0.5','1.25','2','2.5','4','8']:
            x=Q(value);roundtrip=x.ln().exp()
            self.assertLessEqual(roundtrip.lo,x.lo);self.assertGreaterEqual(roundtrip.hi,x.hi)
    def test_wrong_gain_bound_refused(self):
        document=copy.deepcopy(self.certificates['0.1']);document['bounds']['learned_gain']=['1.8','1.81'];self.reject(document)
    def test_missing_obligation_refused(self):
        document=copy.deepcopy(self.certificates['0.1']);document['obligations'].pop();self.reject(document)
    def test_wrong_section_refused(self):
        document=copy.deepcopy(self.certificates['0.1']);document['section']['b']=['0.08','0.08'];self.reject(document)
    def test_wrong_protocol_refused(self):
        document=copy.deepcopy(self.certificates['0.1']);document['protocol']['other_inputs']='A->B also open';self.reject(document)
    def test_changed_parameter_box_refused(self):
        document=copy.deepcopy(self.certificates['0.003']);document['epsilon_relative']='0.1';self.reject(document)
    def test_changed_source_identity_refused(self):
        document=copy.deepcopy(self.certificates['0.1']);document['source_sha256']['certify.py']='0'*64;self.reject(document)
    def test_full_network_scope_substitution_refused(self):
        document=copy.deepcopy(self.certificates['0.1']);document['scope']='Entire reciprocal prototype certified from t=0';self.reject(document)
    def test_failed_sufficient_condition_is_refusal(self):
        with self.assertRaises(producer.Refusal):producer.derive('0.5')
    def test_optimized_execution_refused(self):
        destination=self.path/'optimized.json'
        result=subprocess.run([sys.executable,'-O',str(HERE/'certify.py'),'--epsilon','0.1','--out',str(destination)],capture_output=True,text=True)
        self.assertNotEqual(result.returncode,0);self.assertFalse(destination.exists())
        path=self.path/'0.1.json'
        result=subprocess.run([sys.executable,'-O',str(HERE/'verify.py'),str(path)],capture_output=True,text=True)
        self.assertNotEqual(result.returncode,0)

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--report',type=Path);a=parser.parse_args()
    suite=unittest.defaultTestLoader.loadTestsFromTestCase(LocalProofTests)
    result=unittest.TextTestRunner(verbosity=2).run(suite)
    if a.report:a.report.write_text(json.dumps(dict(tests=result.testsRun,failures=len(result.failures),errors=len(result.errors),passed=result.wasSuccessful(),scope='Positive interval certificates and arithmetic/metadata/refusal checks, not a full proof-assistant verification'),indent=2)+'\n')
    sys.exit(0 if result.wasSuccessful() else 1)
