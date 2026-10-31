"""Pinned semantics of a range certificate, shared by producer and verifier."""
from fractions import Fraction

SOURCES = ('load.py', 'schema.py', 'certify.py', 'verify.py', 'README.md')


def parse_range(text):
    """'lo:hi' with exact decimal endpoints, 0 <= lo <= hi."""
    if not isinstance(text, str) or text.count(':') != 1:
        raise ValueError('range must be written lo:hi')
    lo, hi = text.split(':')
    if Fraction(lo) < 0 or Fraction(lo) > Fraction(hi):
        raise ValueError('range must satisfy 0 <= lo <= hi')
    return lo, hi


def decimal(x):
    """Exact decimal text of a fraction whose denominator divides a power of ten."""
    x = Fraction(x)
    for places in range(0, 60):
        scaled = x * 10 ** places
        if scaled.denominator == 1:
            whole = abs(scaled.numerator)
            sign = '-' if x < 0 else ''
            if places == 0:
                return sign + str(whole)
            text = str(whole).rjust(places + 1, '0')
            return f'{sign}{text[:-places]}.{text[-places:]}'
    raise ValueError('not an exact short decimal')


def cuts(text, n):
    lo, hi = map(Fraction, parse_range(text))
    points = [lo + (hi - lo) * i / n for i in range(n + 1)]
    return [(decimal(points[i]), decimal(points[i + 1])) for i in range(n)]


def pieces(nu_text, alpha_text, n):
    """n x n closed pieces when both ranges have width; a degenerate range is not split."""
    nus = cuts(nu_text, n if Fraction(parse_range(nu_text)[1]) > Fraction(parse_range(nu_text)[0]) else 1)
    alphas = cuts(alpha_text, n if Fraction(parse_range(alpha_text)[1]) > Fraction(parse_range(alpha_text)[0]) else 1)
    return [(nu, alpha) for nu in nus for alpha in alphas]


def evaluate(I, birth_derive, latency_derive, eps, piece, delta):
    nu, alpha = I(*piece['nu']), I(*piece['alpha'])
    birth, birth_ob = birth_derive(I, eps, nu, alpha)
    latency, latency_ob = latency_derive(I, eps, nu, alpha, piece['reference_lo'], piece['reference_hi'], delta)
    bounds = {'birth.' + k: v for k, v in birth.items()}
    bounds.update({'latency.' + k: v for k, v in latency.items()})
    obligations = [dict(o, name='birth.' + o['name'], left='birth.' + o['left'], right='birth.' + o['right']) for o in birth_ob]
    obligations += [dict(o, name='latency.' + o['name'], left='latency.' + o['left'], right='latency.' + o['right']) for o in latency_ob]
    return bounds, obligations


def metadata():
    return dict(schema_version=1, status='CERTIFIED_ROBUST_BIRTH_AND_LATENCY_OVER_PARAMETER_RANGES',
                meaning=('every obligation of the pinned birth-entry, local-continuation and latency-radius '
                         'derivations holds for every noise bound nu and every amplitude deviation alpha in the '
                         'stated closed ranges, at the stated exact epsilon, with one common radius delta'),
                method=('closed pieces covering the ranges, each evaluated with nu and alpha as intervals in the '
                        'unchanged pinned formulas; ranges/load.py lists the only textual changes'),
                chain='T >= 7.5 + 2*sum_{i=0}^{N-2}(sigma_i+delta_i), with delta the published radius',
                trust='authentic sources; integer interval replay; written hybrid proofs, not full Lean semantics')
