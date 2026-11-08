"""Uniform contract, symbolic induction, budgets and deliberate proof refusals."""
from pathlib import Path
from types import SimpleNamespace
from fractions import Fraction
import argparse,ast,contextlib,copy,io,json,subprocess,sys,tempfile,unittest
import certify as producer
import verify as checker
from algebra import normal,identities,instantiate
from dependency import verify_dependency

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]

def dependencies(epsilon):
    box={'0.003':'eps3e-3','0.1':'eps1e-1'}[epsilon]
    if (ROOT/'results').exists():
        return SimpleNamespace(entry_certificate=ROOT/'results/reciprocal_entry'/box/'certificate.json',entry_code=ROOT/'certify/reciprocal_entry',
            local_certificate=ROOT/'results/reciprocal_learning'/box/'certificate.json',local_code=ROOT/'certify/reciprocal_learning')
    return SimpleNamespace(entry_certificate=ROOT/'10_Certified_Section_Entry'/box/'certificate.json',entry_code=ROOT/'10_Certified_Section_Entry/code',
        local_certificate=ROOT/'09_Certified_A_Learns_From_B'/box/'certificate.json',local_code=ROOT/'09_Certified_A_Learns_From_B/code')

class CompositionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp=tempfile.TemporaryDirectory();cls.path=Path(cls.temp.name);cls.documents={}
        with contextlib.redirect_stdout(io.StringIO()):
            for eps in ['0.003','0.1']:
                p=cls.path/(eps+'.json');cls.documents[eps]=producer.certify(eps,dependencies(eps),p)
                checker.verify(p,dependencies(eps))
    @classmethod
    def tearDownClass(cls): cls.temp.cleanup()
    def reject(self,doc,epsilon='0.1'):
        p=self.path/'bad.json';p.write_text(json.dumps(doc))
        with self.assertRaises((RuntimeError,ValueError,KeyError,TypeError)):
            with contextlib.redirect_stdout(io.StringIO()): checker.verify(p,dependencies(epsilon))
    def test_both_physical_boxes_have_same_uniform_local_obligations(self):
        for doc in self.documents.values():
            self.assertEqual(len(doc['obligations']),81)
            self.assertEqual(len(doc['symbolic_identities']),12)
            self.assertEqual(doc['bounds']['final_recovery'],['0.3799900000000000000000000000000000000000','0.3800100000000000000000000000000000000000'])
    def test_third_cell_case_and_original_source_length(self):
        d=instantiate(3,25,'1/20')
        self.assertEqual(d['root_total_emissions'],16)
        self.assertEqual(d['root_fast_tail'],9)
        self.assertEqual(d['total_fast_block_emissions'],54)
    def test_large_N_is_instantiated_without_enumerating_cells(self):
        n=10**100;d=instantiate(n)
        self.assertEqual(d['root_fast_tail'],8)
        self.assertEqual(d['root_total_emissions'],2*n+9)
        self.assertEqual(d['total_fast_block_emissions'],3*n*n+8*n)
        self.assertEqual(Fraction(d['total_jitter']),Fraction(3,20))
    def test_zero_jitter_supports_arbitrary_depth_at_full_fixed_delay_range(self):
        d=instantiate(10**100,jitter='0')
        self.assertEqual(d['allowed_fixed_delay_centres'],['3/10','2/5'])
    def test_original_per_hop_jitter_supported_through_four_cells(self):
        self.assertEqual(instantiate(4,jitter='0.05')['total_jitter'],'3/20')
        with self.assertRaises(ValueError): instantiate(5,jitter='0.05')
    def test_source_budget_is_not_silently_kept_at_25(self):
        with self.assertRaises(ValueError): instantiate(4,pulses=25)
    def test_invalid_chain_and_inexact_budget_refused(self):
        for n in [0,-1,True,1.5]:
            with self.assertRaises(ValueError): instantiate(n)
        for jitter in [-1,'1/10',0.05,True]:
            with self.assertRaises((ValueError,TypeError)): instantiate(5,jitter=jitter)
    def test_polynomial_step_checked_as_identity_not_N_samples(self):
        self.assertEqual(normal('3+2*(j+1)'),normal('(3+2*j)+2'))
        self.assertNotEqual(normal('3+2*(j+1)'),normal('(3+2*j)+3'))
        self.assertEqual(len(identities()),12)
    def test_polynomial_parser_rejects_code_and_non_polynomials(self):
        for expression in ['__import__("os")','N/0','N**N','N[0]','0.1*N']:
            with self.assertRaises(ValueError): normal(expression)
    def test_integer_checker_imports_no_decimal_producer(self):
        tree=ast.parse((HERE/'verify.py').read_text())
        modules={x.module for x in ast.walk(tree) if isinstance(x,ast.ImportFrom)}
        modules.update(a.name for x in ast.walk(tree) if isinstance(x,ast.Import) for a in x.names)
        self.assertTrue(modules.isdisjoint({'certify','decimal','decimal_intervals','numpy','scipy'}))
    def test_interval_cores_remain_identical_to_authenticated_prefix(self):
        for name in ['decimal_intervals.py','integer_intervals.py']:
            self.assertEqual((HERE/name).read_bytes(),(dependencies('0.1').entry_code/name).read_bytes())
    def test_forged_return_bound_refused(self):
        doc=copy.deepcopy(self.documents['0.1']);doc['bounds']['relay.second_miss.return']=['0.01','0.02'];self.reject(doc)
    def test_missing_second_low_firing_ERROR_guard_refused(self):
        doc=copy.deepcopy(self.documents['0.1']);doc['obligations']=[o for o in doc['obligations'] if o['name']!='relay.low_root_at_b2.ERROR_entirely_protected'];self.reject(doc)
    def test_symbolic_transition_tampering_refused(self):
        doc=copy.deepcopy(self.documents['0.1']);doc['symbolic_identities'][2]['right']='3+2*j+3';self.reject(doc)
    def test_unlimited_jitter_claim_refused(self):
        doc=copy.deepcopy(self.documents['0.1']);doc['protocol']['jitter_sum']='unlimited';self.reject(doc)
    def test_fixed_short_training_claim_refused(self):
        doc=copy.deepcopy(self.documents['0.1']);doc['composition']['minimum_K']='25 for every N';self.reject(doc)
    def test_general_graph_claim_refused(self):
        doc=copy.deepcopy(self.documents['0.1']);doc['scope']='All directed graphs with cycles';self.reject(doc)
    def test_wrong_source_identity_refused(self):
        doc=copy.deepcopy(self.documents['0.1']);doc['source_sha256']['algebra.py']='0'*64;self.reject(doc)
    def test_dependency_tamper_refused(self):
        a=dependencies('0.1');doc=json.loads(a.entry_certificate.read_text());doc['scope']='changed'
        p=self.path/'bad_prefix.json';p.write_text(json.dumps(doc))
        with self.assertRaises(RuntimeError): verify_dependency('0.1',p,a.entry_code,a.local_certificate,a.local_code)
    def test_box_substitution_refused(self):
        doc=copy.deepcopy(self.documents['0.003']);doc['epsilon_relative']='0.1';self.reject(doc)
    def test_optimized_execution_refused(self):
        a=dependencies('0.1');flags=['--entry-certificate',str(a.entry_certificate),'--entry-code',str(a.entry_code),
            '--local-certificate',str(a.local_certificate),'--local-code',str(a.local_code)]
        p=self.path/'optimized.json'
        commands=[[sys.executable,'-O',str(HERE/'certify.py'),'--epsilon','0.1','--out',str(p),*flags],
            [sys.executable,'-O',str(HERE/'verify.py'),str(self.path/'0.1.json'),*flags]]
        for command in commands: self.assertNotEqual(subprocess.run(command,capture_output=True).returncode,0)
        self.assertFalse(p.exists())

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--report',type=Path);args=p.parse_args()
    result=unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(CompositionTests))
    if args.report: args.report.write_text(json.dumps(dict(tests=result.testsRun,failures=len(result.failures),errors=len(result.errors),passed=result.wasSuccessful()),indent=2)+'\n')
    sys.exit(0 if result.wasSuccessful() else 1)
