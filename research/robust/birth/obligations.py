"""Birth warm-up and widened local section. Arithmetic class is injected."""
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from bounds import Refusal,require
from birth.local_bounds import derive as local_derive


def derive(I,epsilon,noise,amplitude):
    eps,nu=I(epsilon),I(noise)
    require(eps.lo==eps.hi and nu.lo==nu.hi and 0<eps.lo<1 and nu.lo>=0,'parameter range')
    lo=lambda x:I(x.lo);hi=lambda x:I(x.hi)
    span=lambda a,b:I(a.lo,b.hi)
    lm_min=I('1.25').ln()/I('.02')*(1-eps)
    require((nu/lo(lm_min)).hi<I('.8').lo,'MARK decay must dominate noise')
    mark_max=(1/lo(lm_min))*((1-nu/lo(lm_min))/(I('.8')-nu/lo(lm_min))).ln()
    db=I('.1')+span(-I('.5')*nu*hi(mark_max),I('.5')*nu*hi(mark_max))
    b0=I('.07999','.08001'); b1=b0+db
    local,obs=local_derive(I,epsilon,noise,amplitude,'0.03',b1)
    b={'local.'+k:v for k,v in local.items()}
    obligations=[dict(name='local.'+o['name'],relation=o['relation'],
                      left='local.'+o['left'],right='local.'+o['right']) for o in obs]
    def lt(name,left,right):
        left,right=I(left),I(right)
        b[name+'.left']=left;b[name+'.right']=right
        require(left.hi<right.lo,name)
        obligations.append(dict(name=name,relation='strict_lt',left=name+'.left',right=name+'.right'))
    def decay(x,rate,w,dt):
        e=(-rate*dt).exp()
        return x*e+(w/rate)*(1-e)
    tf=local['fast_duration']; uf=local['aux_finish']; mark=local['mark_end']
    gap=I(8); earliest=I('.5');latest=I('.9')
    lt('birth_slow_decay_dominates_noise',nu/lo(b0),I('.1'))
    lt('protected_arrival_after_FAST',latest+hi(tf),gap)
    dmax=gap-earliest-lo(tf);dmin=gap-latest-hi(tf)
    # Fastest possible decay: negative main noise, earliest FAST end,
    # maximal recovery even before the protected MARK has completed.
    q_lower_arrival=decay(I('.25'),hi(b0),-nu,dmax)
    q_lower_end=decay(q_lower_arrival,hi(b1),-nu,hi(uf))
    lt('entire_protected_MARK_and_ERROR_before_reopen',I('.1'),q_lower_end)
    # Slowest decay: positive main noise and b0 retained until latest MARK end.
    # After this, full MARK protection has established b >= b1_min.
    q_upper_mark=decay(I('.25'),lo(b0),nu,dmin+hi(mark))
    deadline=I('3.5')
    q_upper_deadline=decay(q_upper_mark,lo(b1),nu,deadline-hi(mark))
    lt('protected_input_reopens_by_deadline',q_upper_deadline,I('.1'))
    lt('protected_aux_cycle_before_deadline',hi(uf),deadline)
    lt('protected_return_before_next_input',deadline,gap)
    lt('recovery_cap_not_reached',b1,I('1.1'))
    lt('unused_port1_birth_gain_below_caps',I('1.2')*I('-.00001','.00001').exp(),lo(local['cap']))
    last_return=I(120)+hi(local['main_reopen_bound'])
    lt('warmup_returns_before_entry_cut',last_return,I('159.9'))
    radius=I('.00001')+nu/I('.5')
    lt('entry_charge_radius_inside_local_section',radius,I('.03'))
    lt('entry_aux_band_below_threshold',I('.025')+radius,I(1))
    b.update(birth_recovery=b0,protected_MARK_dose=db,entry_recovery=b1,
             entry_charge_radius=radius,entry_q=I('.1')+span(-radius,radius),
             entry_m=I('.025')+span(-radius,radius),q_lower_at_protected_arrival=q_lower_arrival,
             q_lower_through_protected_cycle=q_lower_end,q_upper_at_reopen_deadline=q_upper_deadline,
             protected_reopen_deadline=deadline,last_warmup_return=last_return)
    # The periodic proof needs a nonnegative residual after a silent raw pulse.
    a=local['a'];h=a/(a-I('.5'))*((-I('.5')).exp()-(-a).exp())
    lt('no_noise_positive_residual',I('.00001'),lo(local['initial_gain'])*h)
    return b,obligations
