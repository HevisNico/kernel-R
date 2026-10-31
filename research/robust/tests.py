"""Tests of the robust local certificates: acceptance, refusals and tampering."""
from pathlib import Path
import contextlib, copy, io, json, subprocess, sys, tempfile, unittest
from decimal_intervals import I
from integer_intervals import Q
from bounds import derive, Refusal
import certify as producer
import verify as checker

HERE = Path(__file__).resolve().parent


def quiet(f, *args):
    with contextlib.redirect_stdout(io.StringIO()):
        return f(*args)


class Robust(unittest.TestCase):
    def test_published_certificates_verify(self):
        files = sorted((HERE / 'results').glob('*/*.json'))
        self.assertEqual(len(files), 8)
        for f in files:
            self.assertEqual(quiet(checker.verify, f)["strict_obligations"], 36)

    def test_drift_only_keeps_exact_dose(self):
        for Iv in (I, Q):
            b, _ = derive(Iv, '0.1', '0', '0', '0.03')
            self.assertEqual(b['gain_log_dose'].lo, b['gain_log_dose'].hi)

    def test_noise_beyond_budget_is_refused(self):
        with self.assertRaisesRegex(Refusal, 'main_reopens_before_next_input'):
            derive(I, '0.1', '0.0026', '0', '0.03')

    def test_amplitude_beyond_budget_is_refused(self):
        with self.assertRaisesRegex(Refusal, 'learned_above_threshold_by_0.9'):
            derive(I, '0.1', '0', '0.1', '0.03')

    def test_noise_dominating_slow_decay_is_refused(self):
        with self.assertRaisesRegex(Refusal, 'dominates_noise'):
            derive(Q, '0.1', '0.02', '0', '0.03')

    def test_tampered_bound_is_refused(self):
        src = HERE / 'results' / 'eps0.1' / 'nu0.002_alpha0.json'
        cert = json.loads(src.read_text())
        bad = copy.deepcopy(cert)
        bad['bounds']['gain_log_dose'][1] = bad['bounds']['gain_log_dose'][0]
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / 'bad.json'; p.write_text(json.dumps(bad))
            with self.assertRaisesRegex(Refusal, 'outside published'):
                quiet(checker.verify, p)
            bad = copy.deepcopy(cert); bad['parameters']['noise_bound'] = '0.0021'
            p.write_text(json.dumps(bad))
            with self.assertRaises(Refusal):
                quiet(checker.verify, p)
            bad = copy.deepcopy(cert); bad['obligations'] = bad['obligations'][:-1]
            p.write_text(json.dumps(bad))
            with self.assertRaisesRegex(Refusal, 'obligation definitions'):
                quiet(checker.verify, p)

    def test_optimized_execution_is_refused(self):
        src = HERE / 'results' / 'eps0.1' / 'nu0_alpha0.json'
        result = subprocess.run([sys.executable, '-O', str(HERE / 'verify.py'), str(src)], capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)


if __name__ == '__main__':
    unittest.main()
