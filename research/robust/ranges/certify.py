"""Range certificates: birth entry, local continuation and latency radius for every nu and alpha in ranges.

Usage: python -B ranges/certify.py --epsilon 0.1 --nu 0:0.002 --alpha 0:0 --out ranges/certificates/x.json

The ranges are split into n_nu x n_alpha closed pieces (n a power of two, so that every cut is
an exact decimal). Each piece is evaluated with nu and alpha as intervals; interval evaluation
over a piece encloses every point of it, and adjacent pieces share their cut, so the pieces
cover the ranges. One latency radius delta is required to hold on every piece. The split is the
smallest power of two that makes every piece pass. Outward Decimal intervals at 128 digits;
bounds published rounded outwards to 40 places.
"""
from pathlib import Path
from decimal import Decimal as D, ROUND_CEILING, ROUND_FLOOR
from fractions import Fraction
import argparse, hashlib, json, sys
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent)); sys.path.insert(0, str(HERE))
from decimal_intervals import I, configure
from birth.certify import rounded
from bounds import Refusal, require
from load import derivations, source_hashes
from schema import SOURCES, metadata, parse_range, pieces, evaluate

configure(128)
MAX_SPLIT = 64


def reference(birth_derive, eps, nu, alpha):
    """Bracket of the noise-free first crossing for every learned gain of this piece."""
    b, _ = birth_derive(I, eps, nu, alpha)
    g = b['local.learned_gain']; a = I(4).ln(); k = I('.5')
    h = lambda t: a / (a - k) * ((-k * I(t)).exp() - (-a * I(t)).exp())
    lo, hi = D('.5'), D('.9')
    for _ in range(45):
        m = (lo + hi) / 2
        lo, hi = (m, hi) if (I('.1') + I(g.hi) * h(m)).hi < 1 else (lo, m)
    ref_lo = str(lo.quantize(D('.000001'), rounding=ROUND_FLOOR))
    lo, hi = D('.5'), D('.9')
    for _ in range(45):
        m = (lo + hi) / 2
        lo, hi = (lo, m) if (I('.1') + I(g.lo) * h(m)).lo > 1 else (m, hi)
    return ref_lo, str(hi.quantize(D('.000001'), rounding=ROUND_CEILING))


def accepts(birth_derive, latency_derive, eps, parts, delta):
    try:
        for p in parts:
            latency_derive(I, eps, I(*p['nu']), I(*p['alpha']), p['reference_lo'], p['reference_hi'], delta)
    except RuntimeError:
        return False
    return True


def design(eps, nu_text, alpha_text, birth_derive, latency_derive):
    zero = Fraction(parse_range(nu_text)[1]) == 0 and Fraction(parse_range(alpha_text)[1]) == 0
    for n in (1, 2, 4, 8, 16, 32, MAX_SPLIT):
        parts = []
        try:
            for nu, alpha in pieces(nu_text, alpha_text, n):
                birth_derive(I, eps, I(*nu), I(*alpha))
                ref_lo, ref_hi = reference(birth_derive, eps, I(*nu), I(*alpha))
                parts.append(dict(nu=list(nu), alpha=list(alpha), reference_lo=ref_lo, reference_hi=ref_hi))
        except RuntimeError:
            continue
        if zero:
            return n, parts, '0'
        lo = D(0); hi = D('.9') - max(D(p['reference_hi']) for p in parts) - D('.000001')
        if not accepts(birth_derive, latency_derive, eps, parts, str(hi)):
            continue
        for _ in range(35):
            m = (lo + hi) / 2
            lo, hi = (lo, m) if accepts(birth_derive, latency_derive, eps, parts, str(m)) else (m, hi)
        delta = str(hi.quantize(D('.00001'), rounding=ROUND_CEILING))
        require(accepts(birth_derive, latency_derive, eps, parts, delta), 'rounded radius refused')
        return n, parts, delta
    raise Refusal(f'no split up to {MAX_SPLIT} pieces per range certifies these ranges')


def certify(eps, nu_text, alpha_text, out):
    require(__debug__, 'optimized execution forbidden')
    _, birth_derive, latency_derive = derivations()
    n, parts, delta = design(eps, nu_text, alpha_text, birth_derive, latency_derive)
    published = []
    for p in parts:
        bounds, obligations = evaluate(I, birth_derive, latency_derive, eps, p, delta)
        record = dict(p, bounds={k: rounded(v) for k, v in bounds.items()}, obligations=obligations)
        for o in obligations:
            require(D(record['bounds'][o['left']][1]) < D(record['bounds'][o['right']][0]), 'published rounding loses ' + o['name'])
        published.append(record)
    c = dict(**metadata(),
             parameters=dict(epsilon=eps, nu=nu_text, alpha=alpha_text, split=str(n), delta=delta),
             pinned_sources=source_hashes(),
             source_sha256={s: hashlib.sha256((HERE / s).read_bytes()).hexdigest() for s in SOURCES},
             pieces=published)
    out = Path(out); out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(c, indent=1) + '\n')
    return c


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--epsilon', required=True); p.add_argument('--nu', required=True)
    p.add_argument('--alpha', required=True); p.add_argument('--out', required=True)
    a = p.parse_args()
    try:
        c = certify(a.epsilon, a.nu, a.alpha, a.out)
    except Refusal as exc:
        print('REFUSED:', exc, file=sys.stderr); sys.exit(1)
    print(json.dumps(dict(status=c['status'], parameters=c['parameters'], pieces=len(c['pieces']),
                          obligations=sum(len(x['obligations']) for x in c['pieces']))))
