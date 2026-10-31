"""Produce outward Decimal certificates of robust entry and local continuation."""
from pathlib import Path
import argparse,hashlib,json,sys
from decimal import Decimal,Context,ROUND_FLOOR,ROUND_CEILING
HERE=Path(__file__).resolve().parent;sys.path.insert(0,str(HERE.parent))
from decimal_intervals import I,configure
from birth.obligations import derive
from birth.schema import SOURCES,metadata
from bounds import require
configure(128)


def rounded(x):
    d=Context(prec=256,rounding=ROUND_FLOOR);u=Context(prec=256,rounding=ROUND_CEILING);s=Decimal('1e-40')
    return [str(d.quantize(x.lo,s)),str(u.quantize(x.hi,s))]


def certify(epsilon,nu,alpha,out):
    require(__debug__,'optimized execution forbidden')
    b,ob=derive(I,epsilon,nu,alpha)
    c=dict(**metadata(),parameters=dict(epsilon=epsilon,nu=nu,alpha=alpha),
           bounds={k:rounded(v) for k,v in b.items()},obligations=ob,
           source_sha256={p:hashlib.sha256((HERE/p).read_bytes()).hexdigest() for p in SOURCES})
    for o in ob:
        require(Decimal(c['bounds'][o['left']][1])<Decimal(c['bounds'][o['right']][0]),'published rounding loses '+o['name'])
    out=Path(out);out.parent.mkdir(parents=True,exist_ok=True);out.write_text(json.dumps(c,indent=2)+'\n')
    return c


if __name__=='__main__':
    a=argparse.ArgumentParser();a.add_argument('--epsilon',required=True);a.add_argument('--nu',required=True)
    a.add_argument('--alpha',required=True);a.add_argument('--out',required=True);p=a.parse_args()
    c=certify(p.epsilon,p.nu,p.alpha,p.out)
    print(json.dumps(dict(status=c['status'],obligations=len(c['obligations']),entry_b=c['bounds']['entry_recovery'])))
