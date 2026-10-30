"""Independent integer replay, with exact source-set and semantic checks."""
from pathlib import Path
from fractions import Fraction
import argparse,hashlib,json,sys
HERE=Path(__file__).resolve().parent;sys.path.insert(0,str(HERE.parent))
from integer_intervals import Q
from bounds import require,Refusal
from birth.obligations import derive
from birth.schema import SOURCES,metadata


def verify(path,emit=True):
    require(__debug__,'optimized execution forbidden')
    raw=Path(path).read_bytes();c=json.loads(raw);meta=metadata()
    require(set(c)==set(meta)|{'parameters','bounds','obligations','source_sha256'},'schema differs')
    for k,v in meta.items():require(c[k]==v,'metadata differs: '+k)
    require(set(c['source_sha256'])==set(SOURCES),'source manifest differs')
    for p in SOURCES:require(hashlib.sha256((HERE/p).read_bytes()).hexdigest()==c['source_sha256'][p],'source changed: '+p)
    p=c['parameters'];require(set(p)=={'epsilon','nu','alpha'} and all(type(v) is str for v in p.values()),'parameter schema differs')
    b,ob=derive(Q,p['epsilon'],p['nu'],p['alpha'])
    require(c['obligations']==ob,'obligation definitions differ')
    require(set(c['bounds'])==set(b),'bound names differ')
    published={}
    for k,v in b.items():
        pair=c['bounds'][k];require(type(pair) is list and len(pair)==2 and all(type(x) is str for x in pair),'bound schema differs')
        lo,hi=map(Fraction,pair);require(lo<=v.lo and v.hi<=hi,'replay outside published bound: '+k)
        published[k]=(lo,hi)
    for o in ob:require(published[o['left']][1]<published[o['right']][0],'published inequality fails: '+o['name'])
    result=dict(status='VERIFIED_ROBUST_BIRTH_ENTRY',parameters=p,enclosures=len(b),strict_obligations=len(ob),
                certificate_sha256=hashlib.sha256(raw).hexdigest())
    if emit:print(json.dumps(result))
    return result


if __name__=='__main__':
    a=argparse.ArgumentParser();a.add_argument('certificate');args=a.parse_args()
    try:verify(args.certificate)
    except (Refusal,ValueError,TypeError,KeyError,OSError,ZeroDivisionError) as e:
        print('REFUSED:',e,file=sys.stderr);sys.exit(1)
