from pathlib import Path
import hashlib,json,sys
from decimal import Decimal as D,ROUND_FLOOR,ROUND_CEILING
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent;sys.path.insert(0,str(ROOT))
from decimal_intervals import I
from birth.certify import rounded
from birth.verify import verify as verify_birth
from birth.obligations import derive as birth_derive
from latency.obligations import derive
from latency.schema import SOURCES,metadata
from bounds import Refusal,require


def choose(eps,nu,alpha):
    b,_=birth_derive(I,eps,nu,alpha);g=b['local.learned_gain'];a=I(4).ln();k=I('.5')
    h=lambda t:a/(a-k)*((-k*I(t)).exp()-(-a*I(t)).exp())
    lo,hi=D('.5'),D('.9')
    for _ in range(45):
        m=(lo+hi)/2
        if (I('.1')+I(g.hi)*h(m)).hi<1:lo=m
        else:hi=m
    reflo=str(lo.quantize(D('.000001'),rounding=ROUND_FLOOR))
    lo,hi=D('.5'),D('.9')
    for _ in range(45):
        m=(lo+hi)/2
        if (I('.1')+I(g.lo)*h(m)).lo>1:hi=m
        else:lo=m
    refhi=str(hi.quantize(D('.000001'),rounding=ROUND_CEILING))
    if D(nu)==D(alpha)==0:return reflo,refhi,'0'
    lo=D(0);hi=D('.9')-D(refhi)-D('.000001')
    derive(I,eps,nu,alpha,reflo,refhi,str(hi))
    for _ in range(35):
        m=(lo+hi)/2
        try:derive(I,eps,nu,alpha,reflo,refhi,str(m))
        except Refusal:lo=m
        else:hi=m
    radius=str(hi.quantize(D('.00001'),rounding=ROUND_CEILING))
    derive(I,eps,nu,alpha,reflo,refhi,radius)
    return reflo,refhi,radius


def certify(eps,nu,alpha):
    require(__debug__,'optimized execution forbidden')
    birth=ROOT/f'birth/certificates/eps{eps}_nu{nu}_alpha{alpha}.json'
    dep=verify_birth(birth,emit=False)
    rl,rh,d=choose(eps,nu,alpha);b,obs=derive(I,eps,nu,alpha,rl,rh,d)
    c=dict(**metadata(),parameters=dict(epsilon=eps,nu=nu,alpha=alpha,reference_lo=rl,reference_hi=rh,delta=d),
           birth_certificate=dict(path=str(birth.relative_to(ROOT)),sha256=dep['certificate_sha256']),
           source_sha256={p:hashlib.sha256((HERE/p).read_bytes()).hexdigest() for p in SOURCES},
           bounds={k:rounded(v) for k,v in b.items()},obligations=obs)
    for o in obs:require(D(c['bounds'][o['left']][1])<D(c['bounds'][o['right']][0]),'published rounding fails')
    p=HERE/f'certificates/eps{eps}_nu{nu}_alpha{alpha}.json';p.write_text(json.dumps(c,indent=2)+'\n')
    return p,c
