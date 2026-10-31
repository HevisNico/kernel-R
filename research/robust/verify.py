"""Integer replay with exact schema checks. Run a trusted copy of this verifier.
Embedded hashes detect source mismatch; they do not sign or authenticate code.
"""
from pathlib import Path
from fractions import Fraction
import argparse, hashlib, json, sys
from integer_intervals import Q
from bounds import derive, Refusal, require
from contract import SOURCES, metadata
HERE = Path(__file__).resolve().parent


def verify(path, emit=True):
    require(__debug__, 'optimized execution (-O) is forbidden')
    raw = Path(path).read_bytes()
    cert = json.loads(raw)
    expected = metadata()
    require(set(cert) == set(expected) | {'parameters','bounds','obligations','source_sha256'}, 'certificate schema differs')
    for key, value in expected.items():
        require(cert[key] == value, 'metadata differs: ' + key)
    require(set(cert['source_sha256']) == set(SOURCES), 'source manifest differs')
    for name in SOURCES:
        require(hashlib.sha256((HERE/name).read_bytes()).hexdigest() == cert['source_sha256'][name], 'source changed: ' + name)
    p = cert['parameters']
    require(set(p) == {'epsilon_relative','noise_bound','amplitude_deviation','section_excess'}, 'parameter schema differs')
    require(all(isinstance(v, str) for v in p.values()), 'parameters must be exact strings')
    bounds, obligations = derive(Q, p['epsilon_relative'], p['noise_bound'], p['amplitude_deviation'], p['section_excess'])
    require(set(cert['bounds']) == set(bounds), 'published bound names differ from the replay')
    published = {}
    for name, x in bounds.items():
        v = cert['bounds'][name]
        require(isinstance(v,list) and len(v)==2 and all(isinstance(t,str) for t in v), 'invalid bound: ' + name)
        lo, hi = map(Fraction, v)
        require(lo <= x.lo and x.hi <= hi, 'replayed enclosure outside published interval: ' + name)
        published[name] = (lo,hi)
    require(cert['obligations'] == obligations, 'obligation definitions differ')
    for o in obligations:
        require(published[o['left']][1] < published[o['right']][0], 'published obligation fails: ' + o['name'])
    report = dict(status='VERIFIED_ROBUST_WITH_INDEPENDENT_INTEGER_ARITHMETIC', parameters=p,
                  enclosures_checked=len(bounds), strict_obligations=len(obligations),
                  certificate_sha256=hashlib.sha256(raw).hexdigest())
    if emit: print(json.dumps(report))
    return report


if __name__ == '__main__':
    parser=argparse.ArgumentParser(); parser.add_argument('certificate'); args=parser.parse_args()
    try:
        verify(args.certificate)
    except (Refusal, ValueError, KeyError, TypeError, OSError, ZeroDivisionError) as exc:
        print('REFUSED:', exc, file=sys.stderr); sys.exit(1)
