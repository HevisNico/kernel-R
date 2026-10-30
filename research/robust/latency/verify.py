from pathlib import Path
from fractions import Fraction as F
import hashlib,json,sys,argparse
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent;sys.path.insert(0,str(ROOT))
from integer_intervals import Q
from bounds import require,Refusal
from birth.verify import verify as verify_birth
from latency.obligations import derive
from latency.schema import SOURCES,metadata


def verify(path,emit=True):
    require(__debug__,'optimized execution forbidden')
    c=json.loads(Path(path).read_bytes());m=metadata()
    require(set(c)==set(m)|{'parameters','birth_certificate','source_sha256','bounds','obligations'},'schema differs')
    for k,v in m.items():require(c[k]==v,'metadata differs: '+k)
    p=c['parameters'];require(set(p)=={'epsilon','nu','alpha','reference_lo','reference_hi','delta'} and all(type(v) is str for v in p.values()),'parameter schema differs')
    require(set(c['source_sha256'])==set(SOURCES),'source manifest differs')
    for name in SOURCES:require(hashlib.sha256((HERE/name).read_bytes()).hexdigest()==c['source_sha256'][name],'source changed: '+name)
    bp=f"birth/certificates/eps{p['epsilon']}_nu{p['nu']}_alpha{p['alpha']}.json"
    require(c['birth_certificate'].get('path')==bp,'birth certificate path differs')
    br=verify_birth(ROOT/bp,emit=False)
    require(c['birth_certificate']==dict(path=bp,sha256=br['certificate_sha256']),'birth certificate identity differs')
    b,o=derive(Q,p['epsilon'],p['nu'],p['alpha'],p['reference_lo'],p['reference_hi'],p['delta'])
    require(c['obligations']==o,'obligation definitions differ');require(set(c['bounds'])==set(b),'bound names differ')
    pub={}
    for k,v in b.items():
        x=c['bounds'][k];require(type(x) is list and len(x)==2 and all(type(y) is str for y in x),'bound schema differs')
        low,high=map(F,x);require(low<=v.lo and v.hi<=high,'replay outside published: '+k);pub[k]=(low,high)
    for x in o:require(pub[x['left']][1]<pub[x['right']][0],'published inequality fails')
    r=dict(status='VERIFIED_LATENCY_RADIUS',parameters=p,strict_obligations=len(o),birth_obligations=br['strict_obligations'])
    if emit:print(json.dumps(r))
    return r


if __name__=='__main__':
    a=argparse.ArgumentParser();a.add_argument('certificate');p=a.parse_args()
    try:verify(p.certificate)
    except (Refusal,ValueError,TypeError,KeyError,OSError,ZeroDivisionError) as e:
        print('REFUSED:',e,file=sys.stderr);sys.exit(1)
