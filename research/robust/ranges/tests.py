"""Range certificates: consistency with the pinned points, refusals and tampering."""
from pathlib import Path
from fractions import Fraction
import contextlib, copy, io, json, sys, tempfile, unittest
HERE = Path(__file__).resolve().parent
ROBUST = HERE.parent
sys.path.insert(0, str(ROBUST)); sys.path.insert(0, str(HERE))
from decimal_intervals import I
from integer_intervals import Q
from birth.certify import rounded
from load import derivations, LATENCY_OLD_ZERO
from schema import pieces, evaluate, cuts
import importlib.util


def _load(name):
    spec = importlib.util.spec_from_file_location('range_' + name, HERE / (name + '.py'))
    module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    return module


producer = _load('certify')
checker = _load('verify')
CERTIFICATES = sorted((HERE / 'certificates').glob('*.json'))


def quiet(f, *args):
    with contextlib.redirect_stdout(io.StringIO()):
        return f(*args)


class Ranges(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        _, birth, latency = derivations()
        cls.birth, cls.latency = staticmethod(birth), staticmethod(latency)

    def test_zero_width_ranges_reproduce_published_points(self):
        for path in sorted((ROBUST / 'latency' / 'certificates').glob('*.json')):
            point = json.loads(path.read_text())
            p = point['parameters']
            birth_cert = json.loads((ROBUST / point['birth_certificate']['path']).read_text())
            piece = dict(nu=[p['nu'], p['nu']], alpha=[p['alpha'], p['alpha']],
                         reference_lo=p['reference_lo'], reference_hi=p['reference_hi'])
            bounds, obligations = evaluate(I, self.birth, self.latency, p['epsilon'], piece, p['delta'])
            for name, value in bounds.items():
                layer, key = name.split('.', 1)
                published = (birth_cert if layer == 'birth' else point)['bounds'][key]
                self.assertEqual(rounded(value), published, path.name + ' ' + name)
            names = [o['name'] for o in obligations]
            self.assertEqual(names, ['birth.' + o['name'] for o in birth_cert['obligations']]
                             + ['latency.' + o['name'] for o in point['obligations']])

    def test_six_range_certificates_verify(self):
        self.assertEqual(len(CERTIFICATES), 6)
        for path in CERTIFICATES:
            report = quiet(checker.verify, path)
            self.assertEqual(report['status'], 'VERIFIED_RANGES_WITH_INTEGER_ARITHMETIC')

    def test_noise_range_radius_is_not_zero(self):
        # The pinned zero-disturbance branch tested nu.lo; on [0, nu_max] it must not apply.
        self.assertIn('nu.lo==0', LATENCY_OLD_ZERO)
        cert = json.loads((HERE / 'certificates' / 'eps0.1_nu0-0.002_alpha0-0.json').read_text())
        first = cert['pieces'][0]
        self.assertEqual(first['nu'], ['0', '0.0005'])
        refs = (first['reference_lo'], first['reference_hi'])
        nu = I(*first['nu'])
        self.latency(I, '0.1', nu, I(0), *refs, cert['parameters']['delta'])   # the published radius passes
        with self.assertRaisesRegex(RuntimeError, 'dominates_perturbation'):
            self.latency(I, '0.1', nu, I(0), *refs, '0')

    def test_ranges_beyond_the_budget_are_refused(self):
        with self.assertRaises(RuntimeError):
            producer.design('0.1', '0:0.0025', '0:0', self.birth, self.latency)

    def test_pieces_cover_the_range_with_shared_cuts(self):
        parts = cuts('0:0.002', 4)
        self.assertEqual(parts[0][0], '0'); self.assertEqual(parts[-1][1], '0.002')
        for left, right in zip(parts, parts[1:]):
            self.assertEqual(left[1], right[0])
        self.assertEqual(len(pieces('0:0.0015', '0:0.05', 2)), 4)
        self.assertEqual(len(pieces('0:0.002', '0:0', 4)), 4)

    def test_tampering_is_refused(self):
        source = HERE / 'certificates' / 'eps0.1_nu0-0.002_alpha0-0.json'
        good = json.loads(source.read_text())
        edits = []
        bad = copy.deepcopy(good); bad['parameters']['delta'] = '0.007'; edits.append(bad)
        bad = copy.deepcopy(good); bad['parameters']['nu'] = '0:0.0021'; edits.append(bad)
        bad = copy.deepcopy(good); bad['pieces'] = bad['pieces'][:-1]; edits.append(bad)
        bad = copy.deepcopy(good); bad['parameters']['split'] = '3'; edits.append(bad)
        bad = copy.deepcopy(good)
        key = 'latency.late_reference_separation_dominates_perturbation.left'
        bad['pieces'][0]['bounds'][key][1] = bad['pieces'][0]['bounds'][key][0]; edits.append(bad)
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / 'bad.json'
            for doc in edits:
                p.write_text(json.dumps(doc))
                with self.assertRaises((RuntimeError, ValueError, KeyError, TypeError)):
                    quiet(checker.verify, p)


if __name__ == '__main__':
    unittest.main()
