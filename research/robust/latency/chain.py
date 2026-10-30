"""Exact sufficient period from a verified per-cell phase radius (uniform family)."""
from pathlib import Path
from fractions import Fraction as F
import argparse,json,sys
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from bounds import require
from latency.verify import verify


def contract(path,n,k,sigma='0',period=None):
    r=verify(path,emit=False)
    require(type(n) is int and n>=1 and type(k) is int and k>=3*n+1,'invalid N or K')
    s=F(sigma);require(0<=s<=F(1,20),'invalid jitter')
    d=F(r['parameters']['delta']);minimum=F(15,2)+2*(n-1)*(s+d)
    t=minimum if period is None else F(period)
    require(t>=minimum,'period below certified phase budget')
    return dict(N=n,K=k,sigma_each=str(s),delta_each=str(d),minimum_period=str(minimum),period=str(t),
                root_outputs=k-3*n,root_output_phase_radius=str(n*d+(n-1)*s))


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('certificate');p.add_argument('--n',type=int,required=True)
    p.add_argument('--k',type=int,required=True);p.add_argument('--sigma',default='0');p.add_argument('--period')
    a=p.parse_args();print(json.dumps(contract(a.certificate,a.n,a.k,a.sigma,a.period),indent=2))
