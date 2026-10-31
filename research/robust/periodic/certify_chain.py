"""No-noise, identical-waveform packet contraction with a global wire jitter budget."""
from pathlib import Path
import argparse, json, sys
from fractions import Fraction as F
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from bounds import require
from verify import verify
from integer_intervals import Q


def contract(path,n,k,period='8',sigmas=None):
    report=verify(path,emit=False); cert=json.loads(Path(path).read_text())
    require(F(cert['parameters']['noise_bound'])==0,'constant-latency theorem requires zero noise')
    require(F(cert['parameters']['amplitude_deviation'])==0,'constant-latency theorem requires identical waveforms')
    require(type(n) is int and n>=1,'N must be a positive integer')
    require(type(k) is int and k>=3*n+1,'K must be at least 3*N+1')
    sigmas=[F(0)]*(n-1) if sigmas is None else list(map(F,sigmas))
    require(len(sigmas)==n-1 and all(0<=s<=F(1,20) for s in sigmas),'invalid per-edge jitter budgets')
    t=F(period); jitter=sum(sigmas,F(0)); minimum=F(15,2)+2*jitter
    require(t>=minimum,'period too short for twice the accumulated phase jitter')
    # Before the first silent input q-r >= -delta. Gains never decrease.
    # Hence at raw end q-r >= -delta + g_initial_min*h(1) > 0.
    a=Q(4).ln(); h=a/(a-Q('0.5'))*((-Q('0.5')).exp()-(-a).exp())
    g=Q('0.3')*(-Q('0.00001')).exp()
    require(F('0.00001')<(g*h).lo,'positive post-silent residual not established')
    ready=F(cert['bounds']['main_reopen_bound'][1])
    return dict(status='CONDITIONAL_CONSTANT_LATENCY_CHAIN',N=n,K=k,period=str(t),
                sigma_each=list(map(str,sigmas)),total_jitter=str(jitter),minimum_period=str(minimum),
                local_certificate_sha256=report['certificate_sha256'],
                positive_residual_comparison=dict(left='1/100000',right_lower=str((g*h).lo)),
                nodes=[dict(index=i,inputs=k-3*i,emissions=k-3*(i+1)) for i in range(n)],
                root_emissions=k-3*n,total_emissions=n*k-3*n*(n+1)//2,
                all_ready_by=str((k-1)*t+F(13*(n-1),10)+ready),
                scope='zero noise; identical canonical waveforms; prepared chain; written induction')


if __name__=='__main__':
    a=argparse.ArgumentParser();a.add_argument('certificate');a.add_argument('--n',type=int,required=True)
    a.add_argument('--k',type=int,required=True);a.add_argument('--period',default='8')
    a.add_argument('--sigma-each',default='0');args=a.parse_args()
    print(json.dumps(contract(args.certificate,args.n,args.k,args.period,[args.sigma_each]*(args.n-1)),indent=2))
