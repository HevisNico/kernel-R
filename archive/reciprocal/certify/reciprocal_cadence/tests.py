"""Cadence induction, retained competence and adversarial certificate checks."""
from pathlib import Path
from types import SimpleNamespace
import argparse,ast,contextlib,copy,io,json,subprocess,sys,tempfile,unittest
import zipfile
from fractions import Fraction
import certify as producer
import verify as checker
from dependency import verify_dependency

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]

def dependencies(epsilon):
    box={'0.003':'eps3e-3','0.1':'eps1e-1'}[epsilon]
    if not (ROOT/'results').exists():
        return SimpleNamespace(entry_certificate=ROOT/'10_Certified_Section_Entry'/box/'certificate.json',
            entry_code=ROOT/'10_Certified_Section_Entry/code',
            local_certificate=ROOT/'09_Certified_A_Learns_From_B'/box/'certificate.json',
            local_code=ROOT/'09_Certified_A_Learns_From_B/code')
    return SimpleNamespace(entry_certificate=ROOT/'results/reciprocal_entry'/box/'certificate.json',
        entry_code=ROOT/'certify/reciprocal_entry',local_certificate=ROOT/'results/reciprocal_learning'/box/'certificate.json',
        local_code=ROOT/'certify/reciprocal_learning')

class CadenceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp=tempfile.TemporaryDirectory(prefix='r_cadence_')
        cls.path=Path(cls.temp.name);cls.documents={}
        with contextlib.redirect_stdout(io.StringIO()):
            for epsilon in ['0.003','0.1']:
                p=cls.path/(epsilon+'.json')
                cls.documents[epsilon]=producer.certify(epsilon,dependencies(epsilon),p)
                checker.verify(p,dependencies(epsilon))
    @classmethod
    def tearDownClass(cls): cls.temp.cleanup()
    def reject(self,document,epsilon='0.1'):
        p=self.path/'bad.json';p.write_text(json.dumps(document))
        with self.assertRaises((RuntimeError,ValueError,KeyError,TypeError)):
            with contextlib.redirect_stdout(io.StringIO()): checker.verify(p,dependencies(epsilon))
    def test_both_boxes_and_actual_pulse_pattern(self):
        for doc in self.documents.values():
            self.assertEqual(doc['summary']['teaching_emissions'],dict(B=16,C=14))
            self.assertEqual(doc['summary']['fast_emissions'],dict(A=16,B=18,C=20))
            for cell in ['A','B','C']:
                cases=[row['case'] for row in doc['pulse_trace'] if row['pulse'].startswith(cell+'.fast_')]
                self.assertEqual(cases.count('protected_MARK_only'),1)
                self.assertEqual(cases.count('protected_MARK_then_full_ERROR'),1)
                self.assertEqual(doc['summary']['added_fast_MARK_doses'][cell],2)
                for previous,current in zip(cases,cases[1:]):
                    if current.startswith('protected_'): self.assertEqual(previous,'strong_firing')
    def test_canonical_recovery_and_retained_probe(self):
        for doc in self.documents.values():
            for cell in ['A','B','C']:
                self.assertEqual(doc['bounds'][cell+'.final_b'],['0.3799900000000000000000000000000000000000','0.3800100000000000000000000000000000000000'])
            self.assertEqual(doc['conclusion']['probe']['before'],dict(A='4/8',B='4/8',C='0/8'))
            self.assertEqual(doc['conclusion']['probe']['after'],dict(A='8/8',B='8/8',C='8/8'))
    def test_nominal_recording_inside_all_certified_emission_hulls(self):
        if (ROOT/'04_Results/impulsions.json').exists():
            record=json.loads((ROOT/'04_Results/impulsions.json').read_text())
        else:
            with zipfile.ZipFile(ROOT/'downloads/R_Reciprocal_Prototype.zip') as archive:
                record=json.loads(archive.read('R_Reciprocal_Prototype/04_Results/impulsions.json'))
        doc=self.documents['0.003']
        for cell,phase,node,lo,hi in [('B','teach',1,480,640),('Cteach','teach',2,480,640),
                ('C','fast',2,640,780),('B','fast',1,640,780),('A','fast',0,640,780)]:
            pulses=[row['pulse'] for row in doc['pulse_trace'] if row['pulse'].startswith(cell+'.'+phase+'_') and row['case']=='strong_firing']
            actual=[Fraction(str(row['time'])) for row in record['outputs'] if row['node']==node and lo<=row['time']<hi]
            self.assertEqual(len(pulses),len(actual))
            for pulse,t in zip(pulses,actual):
                lower,upper=map(Fraction,doc['bounds'][pulse+'.emission'])
                with self.subTest(pulse=pulse): self.assertTrue(lower<=t<=upper)
    def test_integer_checker_never_imports_decimal_producer(self):
        tree=ast.parse((HERE/'verify.py').read_text())
        modules={node.module for node in ast.walk(tree) if isinstance(node,ast.ImportFrom)}
        modules.update(alias.name for node in ast.walk(tree) if isinstance(node,ast.Import) for alias in node.names)
        self.assertTrue(modules.isdisjoint({'certify','decimal','decimal_intervals','numpy','scipy'}))
    def test_interval_cores_unchanged_from_prefix(self):
        for name in ['decimal_intervals.py','integer_intervals.py']:
            self.assertEqual((HERE/name).read_bytes(),(dependencies('0.1').entry_code/name).read_bytes())
    def test_forged_root_witness_refused(self):
        doc=copy.deepcopy(self.documents['0.1'])
        key=next(k for k in doc['bounds'] if k.startswith('A.fast_') and k.endswith('.root_latency'))
        doc['bounds'][key]=['0.01','0.02'];self.reject(doc)
    def test_forged_early_reopen_refused(self):
        doc=copy.deepcopy(self.documents['0.1'])
        key=next(k for k in doc['bounds'] if k.startswith('A.fast_') and k.endswith('.reopen'))
        doc['bounds'][key]=['0.01','0.02'];self.reject(doc)
    def test_missing_mark_obligation_refused(self):
        doc=copy.deepcopy(self.documents['0.1'])
        doc['obligations']=[o for o in doc['obligations'] if not o['name'].endswith('.whole_MARK_protected')]
        self.reject(doc)
    def test_pulse_trace_tampering_refused(self):
        doc=copy.deepcopy(self.documents['0.1']);doc['pulse_trace'][0]['case']='weak_full_ERROR';self.reject(doc)
    def test_wrong_cadence_refused(self):
        doc=copy.deepcopy(self.documents['0.1']);doc['protocol']['C_port0_sources']='640,648,...,736';self.reject(doc)
    def test_settings_copy_scope_refused(self):
        doc=copy.deepcopy(self.documents['0.1']);doc['protocol']['settings_copies']='at 480';self.reject(doc)
    def test_open_recurrence_scope_refused(self):
        doc=copy.deepcopy(self.documents['0.1']);doc['scope']='All future open recurrence certified';self.reject(doc)
    def test_probe_overclaim_refused(self):
        doc=copy.deepcopy(self.documents['0.1']);doc['conclusion']['probe']['before']['C']='4/8';self.reject(doc)
    def test_box_substitution_refused(self):
        doc=copy.deepcopy(self.documents['0.003']);doc['epsilon_relative']='0.1';self.reject(doc)
    def test_dependency_tamper_and_wrong_box_refused(self):
        args=dependencies('0.1');document=json.loads(args.entry_certificate.read_text());document['scope']='changed'
        p=self.path/'tampered_prefix.json';p.write_text(json.dumps(document))
        with self.assertRaises(RuntimeError): verify_dependency('0.1',p,args.entry_code,args.local_certificate,args.local_code)
        with self.assertRaises(RuntimeError): verify_dependency('0.003',args.entry_certificate,args.entry_code,args.local_certificate,args.local_code)
    def test_dependency_source_rejected_before_execution(self):
        args=dependencies('0.1');fake=self.path/'fake_prefix';fake.mkdir(exist_ok=True)
        for p in args.entry_code.glob('*.py'): (fake/p.name).write_bytes(p.read_bytes())
        (fake/'verify.py').write_text('raise SystemExit(0)\n')
        with self.assertRaises(RuntimeError): verify_dependency('0.1',args.entry_certificate,fake,args.local_certificate,args.local_code)
    def test_changed_source_identity_refused(self):
        doc=copy.deepcopy(self.documents['0.1']);doc['source_sha256']['verify.py']='0'*64;self.reject(doc)
    def test_optimized_execution_refused(self):
        args=dependencies('0.1')
        flags=['--entry-certificate',str(args.entry_certificate),'--entry-code',str(args.entry_code),
            '--local-certificate',str(args.local_certificate),'--local-code',str(args.local_code)]
        dest=self.path/'optimized.json'
        for command in [[sys.executable,'-O',str(HERE/'certify.py'),'--epsilon','0.1','--out',str(dest),*flags],
            [sys.executable,'-O',str(HERE/'verify.py'),str(self.path/'0.1.json'),*flags]]:
            self.assertNotEqual(subprocess.run(command,capture_output=True).returncode,0)
        self.assertFalse(dest.exists())

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--report',type=Path);args=parser.parse_args()
    result=unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(CadenceTests))
    if args.report: args.report.write_text(json.dumps(dict(tests=result.testsRun,failures=len(result.failures),errors=len(result.errors),passed=result.wasSuccessful()),indent=2)+'\n')
    sys.exit(0 if result.wasSuccessful() else 1)
