"""Positive composition plus deliberate statement, arithmetic and dependency refusals."""
from pathlib import Path
import argparse,contextlib,copy,hashlib,io,json,subprocess,sys,tempfile,unittest
import certify as producer
import verify as checker
from dependency import verify_dependency
from integer_intervals import Q
from decimal_intervals import I

HERE=Path(__file__).resolve().parent
LINK_CODE=None
LINK_CERTIFICATES={}


class EntryProofTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp=tempfile.TemporaryDirectory(dir=HERE);cls.path=Path(cls.temp.name);cls.documents={}
        with contextlib.redirect_stdout(io.StringIO()):
            for epsilon,link in LINK_CERTIFICATES.items():
                p=cls.path/(epsilon+'.json')
                cls.documents[epsilon]=producer.certify(epsilon,link,LINK_CODE,p)
                checker.verify(p,link,LINK_CODE)
    @classmethod
    def tearDownClass(cls):cls.temp.cleanup()
    def reject(self,doc,epsilon='0.1'):
        p=self.path/'bad.json';p.write_text(json.dumps(doc))
        with self.assertRaises((RuntimeError,ValueError,KeyError,TypeError)):
            with contextlib.redirect_stdout(io.StringIO()):checker.verify(p,LINK_CERTIFICATES[epsilon],LINK_CODE)
    def test_both_boxes_composed(self):
        for eps,d in self.documents.items():
            self.assertEqual(len(d['obligations']),59)
            self.assertEqual(d['composed_conclusion']['A_total_emissions_through_cut'],38)
            self.assertEqual(d['entry_conclusion']['b'],['0.17999','0.18001'])
    def test_core_arithmetic_modules_unchanged(self):
        for name in ['decimal_intervals.py','integer_intervals.py']:
            self.assertEqual((HERE/name).read_bytes(),(LINK_CODE/name).read_bytes())
    def test_both_arithmetics_reject_floats(self):
        for arithmetic in [I,Q]:
            with self.assertRaises(TypeError):arithmetic(.1)
    def test_wrong_recovery_bound_refused(self):
        d=copy.deepcopy(self.documents['0.1']);d['bounds']['entry_b']=['0.08','0.08'];self.reject(d)
    def test_omitted_protected_error_obligation_refused(self):
        d=copy.deepcopy(self.documents['0.1']);d['obligations']=[o for o in d['obligations'] if o['name']!='whole_mark_and_error_of_protected_input_stay_protected'];self.reject(d)
    def test_birth_recovery_changed_refused(self):
        d=copy.deepcopy(self.documents['0.1']);d['birth_family']['b']=['0.18','0.18'];self.reject(d)
    def test_settings_copy_variant_substitution_refused(self):
        d=copy.deepcopy(self.documents['0.1']);d['protocol']['settings_copies']='copy at 160';self.reject(d)
    def test_open_reciprocal_phase_scope_substitution_refused(self):
        d=copy.deepcopy(self.documents['0.1']);d['scope']='All later recurrent and pedagogical phases certified';self.reject(d)
    def test_box_substitution_refused(self):
        d=copy.deepcopy(self.documents['0.003']);d['epsilon_relative']='0.1';self.reject(d)
    def test_changed_source_identity_refused(self):
        d=copy.deepcopy(self.documents['0.1']);d['source_sha256']['verify.py']='0'*64;self.reject(d)
    def test_dependency_certificate_tampering_refused(self):
        d=json.loads(LINK_CERTIFICATES['0.1'].read_text());d['section']['b']=['0.08','0.08']
        p=self.path/'tampered_link.json';p.write_text(json.dumps(d))
        with self.assertRaises(RuntimeError):verify_dependency('0.1',p,LINK_CODE)
    def test_wrong_dependency_box_refused(self):
        with self.assertRaises(RuntimeError):verify_dependency('0.1',LINK_CERTIFICATES['0.003'],LINK_CODE)
    def test_modified_dependency_code_refused_before_execution(self):
        fake=self.path/'fake_code';fake.mkdir()
        for p in LINK_CODE.glob('*.py'):(fake/p.name).write_bytes(p.read_bytes())
        (fake/'verify.py').write_text('raise SystemExit(0)\n')
        with self.assertRaises(RuntimeError):verify_dependency('0.1',LINK_CERTIFICATES['0.1'],fake)
    def test_optimized_certifier_and_checker_refused(self):
        dest=self.path/'optimized.json';base=['--link-certificate',str(LINK_CERTIFICATES['0.1']),'--link-code',str(LINK_CODE)]
        r=subprocess.run([sys.executable,'-O',str(HERE/'certify.py'),'--epsilon','0.1',*base,'--out',str(dest)],capture_output=True,text=True)
        self.assertNotEqual(r.returncode,0);self.assertFalse(dest.exists())
        r=subprocess.run([sys.executable,'-O',str(HERE/'verify.py'),str(self.path/'0.1.json'),*base],capture_output=True,text=True)
        self.assertNotEqual(r.returncode,0)
    def test_exact_protected_mark_dose(self):
        self.assertEqual(self.documents['0.1']['bounds']['mark_dose'],['0.1000000000000000000000000000000000000000']*2)
    def test_strict_margins_survive_outward_publication(self):
        for doc in self.documents.values():
            for o in doc['obligations']:
                from fractions import Fraction
                left=Fraction(doc['bounds'][o['left']][1]);right=Fraction(doc['bounds'][o['right']][0])
                self.assertLess(left,right) if o['relation']=='strict_lt' else self.assertLessEqual(left,right)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--link-code',required=True,type=Path);p.add_argument('--link-003',required=True,type=Path);p.add_argument('--link-01',required=True,type=Path);p.add_argument('--report',type=Path);a=p.parse_args()
    LINK_CODE=a.link_code.resolve();LINK_CERTIFICATES={'0.003':a.link_003.resolve(),'0.1':a.link_01.resolve()}
    result=unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(EntryProofTests))
    if a.report:a.report.write_text(json.dumps(dict(tests=result.testsRun,failures=len(result.failures),errors=len(result.errors),passed=result.wasSuccessful(),scope='Birth-to-section/composition positive cases, exact arithmetic, metadata, dependency and fail-closed tests'),indent=2)+'\n')
    sys.exit(0 if result.wasSuccessful() else 1)
