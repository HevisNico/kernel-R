"""Certificates of the robust local theorem (drift, bounded noise, pulse amplitude).

Outward Decimal intervals at 128 digits; published bounds rounded outwards to 40 places.
Usage: python -B certify.py --epsilon 0.1 --nu 0.002 --alpha 0 --section 0.03 --out cert.json
"""
from pathlib import Path
from decimal import Decimal, Context, ROUND_FLOOR, ROUND_CEILING
import argparse, hashlib, json, sys
from decimal_intervals import I, configure
from bounds import derive, Refusal, require

HERE = Path(__file__).resolve().parent
from contract import SOURCES, metadata
configure(128)


def rounded(x):
    scale = Decimal('1e-40')
    down = Context(prec=256, rounding=ROUND_FLOOR); up = Context(prec=256, rounding=ROUND_CEILING)
    return [str(down.quantize(x.lo, scale)), str(up.quantize(x.hi, scale))]


def certify(epsilon, nu, alpha, section, out):
    if not __debug__:
        raise Refusal('optimized execution (-O) is forbidden')
    bounds, obligations = derive(I, epsilon, nu, alpha, section)
    certificate = dict(
        **metadata(),
        parameters=dict(epsilon_relative=epsilon, noise_bound=nu, amplitude_deviation=alpha, section_excess=section),
        bounds={name: rounded(value) for name, value in bounds.items()},
        obligations=obligations,
        source_sha256={name: hashlib.sha256((HERE / name).read_bytes()).hexdigest() for name in SOURCES})
    for o in obligations:
        require(Decimal(certificate['bounds'][o['left']][1]) < Decimal(certificate['bounds'][o['right']][0]),
                'published bound loses ' + o['name'])
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(certificate, indent=2) + '\n')
    print(json.dumps(dict(file=str(out), status=certificate['status'], epsilon=epsilon, nu=nu, alpha=alpha,
                          strict_obligations=len(obligations), gain_log_dose=certificate['bounds']['gain_log_dose'])))
    return certificate


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    for name in ('epsilon', 'nu', 'alpha'):
        p.add_argument('--' + name, required=True)
    p.add_argument('--section', default='0.03'); p.add_argument('--out', type=Path, required=True)
    args = p.parse_args()
    try:
        certify(args.epsilon, args.nu, args.alpha, args.section, args.out)
    except Refusal as exc:
        print('REFUSED:', exc, file=sys.stderr); sys.exit(1)
