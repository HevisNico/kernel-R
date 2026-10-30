"""Integer-arithmetic replay of a range certificate. Run a trusted copy of this verifier."""
from pathlib import Path
from fractions import Fraction as F
import argparse, hashlib, json, sys
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent)); sys.path.insert(0, str(HERE))
from integer_intervals import Q
from bounds import Refusal, require
from load import derivations, source_hashes
from schema import SOURCES, metadata, pieces, evaluate


def verify(path, emit=True):
    require(__debug__, 'optimized execution forbidden')
    raw = Path(path).read_bytes(); c = json.loads(raw); m = metadata()
    require(set(c) == set(m) | {'parameters', 'pinned_sources', 'source_sha256', 'pieces'}, 'schema differs')
    for k, v in m.items():
        require(c[k] == v, 'metadata differs: ' + k)
    require(c['pinned_sources'] == source_hashes(), 'pinned robust source differs')
    require(set(c['source_sha256']) == set(SOURCES), 'source manifest differs')
    for name in SOURCES:
        require(hashlib.sha256((HERE / name).read_bytes()).hexdigest() == c['source_sha256'][name], 'source changed: ' + name)
    p = c['parameters']
    require(set(p) == {'epsilon', 'nu', 'alpha', 'split', 'delta'} and all(type(v) is str for v in p.values()),
            'parameter schema differs')
    n = int(p['split'])
    require(n >= 1 and n & (n - 1) == 0 and str(n) == p['split'], 'split must be a power of two')
    expected = pieces(p['nu'], p['alpha'], n)
    require([(tuple(x['nu']), tuple(x['alpha'])) for x in c['pieces']] == expected,
            'pieces do not cover the stated ranges in order')
    _, birth_derive, latency_derive = derivations()
    total = 0
    for piece in c['pieces']:
        require(set(piece) == {'nu', 'alpha', 'reference_lo', 'reference_hi', 'bounds', 'obligations'}, 'piece schema differs')
        bounds, obligations = evaluate(Q, birth_derive, latency_derive, p['epsilon'], piece, p['delta'])
        require(piece['obligations'] == obligations, 'obligation definitions differ')
        require(set(piece['bounds']) == set(bounds), 'bound names differ')
        published = {}
        for k, v in bounds.items():
            x = piece['bounds'][k]
            require(type(x) is list and len(x) == 2 and all(type(y) is str for y in x), 'bound schema differs')
            low, high = map(F, x)
            require(low <= v.lo and v.hi <= high, 'replay outside published: ' + k)
            published[k] = (low, high)
        for o in obligations:
            require(published[o['left']][1] < published[o['right']][0], 'published inequality fails: ' + o['name'])
        total += len(obligations)
    report = dict(status='VERIFIED_RANGES_WITH_INTEGER_ARITHMETIC', parameters=p, pieces=len(c['pieces']),
                  strict_obligations=total, certificate_sha256=hashlib.sha256(raw).hexdigest())
    if emit:
        print(json.dumps(report))
    return report


if __name__ == '__main__':
    a = argparse.ArgumentParser(); a.add_argument('certificate'); args = a.parse_args()
    try:
        verify(args.certificate)
    except (RuntimeError, ValueError, TypeError, KeyError, OSError, ZeroDivisionError) as exc:
        print('REFUSED:', exc, file=sys.stderr); sys.exit(1)
