"""A checked phase-latency radius about the same cell's learned-gain reference."""
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from bounds import require
from birth.obligations import derive as birth_derive


def derive(I,epsilon,noise,amplitude,reference_lo,reference_hi,radius):
    birth,_=birth_derive(I,epsilon,noise,amplitude)
    nu,alpha,d=I(noise),I(amplitude),I(radius)
    low,high=I(reference_lo),I(reference_hi)
    require(all(x.lo==x.hi for x in (nu,alpha,d,low,high)),'exact latency parameters required')
    require(0<low.lo<high.lo<1 and d.lo>=0,'latency parameter range')
    a=I(4).ln();k=I('.5');g=birth['local.learned_gain']
    h=lambda t:a/(a-k)*((-k*t).exp()-(-a*t).exp())
    hp=lambda t:a/(a-k)*(a*(-a*t).exp()-k*(-k*t).exp())
    lo=lambda x:I(x.lo);hi=lambda x:I(x.hi)
    b=dict(nu=nu,alpha=alpha,latency_radius=d,reference_lower=low,reference_upper=high,learned_gain=g)
    ob=[]
    def lt(name,left,right):
        left,right=I(left),I(right);b[name+'.left']=left;b[name+'.right']=right
        require(left.hi<right.lo,name)
        ob.append(dict(name=name,relation='strict_lt',left=name+'.left',right=name+'.right'))
    lt('reference_before_all_roots',I('.1')+hi(g)*h(low),1)
    lt('reference_after_all_roots',1,I('.1')+lo(g)*h(high))
    # h''<0 through t=1 follows from a^2/k^2 > exp(a-k).
    lt('response_strictly_concave_through_raw_window',(a-k).exp(),(a/k)*(a/k))
    if nu.lo==0 and alpha.lo==0:
        require(d.lo==0,'zero disturbance uses exactly zero radius')
        return b,ob
    lt('positive_early_time',d,low)
    lt('late_time_before_local_ERROR_gate',high+d,I('.9'))
    lt('positive_minimum_slope',0,lo(g)*hp(high+d))
    late_separation=lo(g)*(h(high+d)-h(high))
    early_separation=lo(g)*(h(high)-h(high-d))
    late_noise=nu/k+alpha*hi(g)*h(high+d)
    early_noise=nu/k+alpha*hi(g)*h(high-d)
    lt('late_reference_separation_dominates_perturbation',late_noise,late_separation)
    lt('early_reference_separation_dominates_perturbation',early_noise,early_separation)
    b.update(minimum_slope=lo(g)*hp(high+d),late_separation=late_separation,
             early_separation=early_separation,late_perturbation=late_noise,early_perturbation=early_noise)
    return b,ob
