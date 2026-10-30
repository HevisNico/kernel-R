"""Outward-rounded certificate for the prepared two-cell feedback-learning link.

No floating-point endpoint enters this proof. The inherited A22 Decimal interval
implementation is copied unchanged. The frozen A22 engine is not modified.
"""
from pathlib import Path
from decimal import Decimal,Context,ROUND_FLOOR,ROUND_CEILING
import argparse,json,hashlib,sys
from decimal_intervals import I,configure

HERE=Path(__file__).resolve().parent
configure(128)

class Refusal(RuntimeError):pass

def require(condition,message):
    if not condition:raise Refusal(message)


def derive(epsilon):
    eps=I(epsilon);require(eps.lo==eps.hi and 0<eps.lo<1,'epsilon must be exact and in (0,1)')
    a=I(4).ln();k=I('0.5');r=I('0.1');rm=I('0.025');delta=I('0.00001')
    qex=I('-0.00001','0.03');b=I('0.17999','0.18001')
    rel=I(1)-eps;upper=I(1)+eps
    factor=I(rel.lo,upper.hi)
    h=lambda t:a/(a-k)*((-k*I(t)).exp()-(-a*I(t)).exp())
    cap=I(4)*factor;lm=(I('1.25').ln()/I('0.02'))*factor
    ls=(I(8).ln()/I('1.06'))*factor;le=(I(4).ln()/I('0.15'))*factor
    mult=((I(1)-rm)/h('0.02'))*factor
    tau=I('0.015','0.03');time=I(0,tau.hi);m0=I('-0.00001','0.00001')
    aux=lambda t:rm+m0*(-k*I(t)).exp()+mult*h(t)
    aux_derivative=-k*m0*(-k*time).exp()+mult*a/(a-k)*(-k*(-k*time).exp()+a*(-a*time).exp())
    mark=tau+I('1.25').ln()/lm
    error=mark+I(8).ln()/ls
    finish=error+I(4).ln()/le
    dose=I(8)*(I('0.1')-rm)
    initial_gain=I('0.3')*I('-0.00001','0.00001').exp()
    learned=initial_gain*(I(3)*dose).exp()
    rootlo=I('0.5');roothi=I('0.9');delay=I('0.3','0.4')
    gap=I(8)+rootlo+I(delay.lo)-roothi-I(delay.hi)
    overlap=I(0,max(Decimal(0),(I(1)-I(error.lo)).hi))
    density=a*(-a*I(error.lo)).exp()
    reopen=roothi+I(1)+I('2.5').ln()/b
    bounds=dict(epsilon=eps,a=a,kappa=k,delta=delta,cap=cap,Lm=lm,Ls=ls,Le=le,M=mult,
      initial_gain=initial_gain,learned_gain=learned,gain_log_dose=dose,
      aux_at_early=aux(tau.lo),aux_at_late=aux(tau.hi),aux_derivative=aux_derivative,
      mark_end=mark,error_start=error,aux_finish=finish,
      raw_error_overlap_length=overlap,overlap_density_bound=density,
      min_input_gap=gap,main_reopen_bound=reopen)
    obligations=[]
    def lt(name,left,right):
        left=I(left);right=I(right);bounds[name+'.left']=left;bounds[name+'.right']=right
        require(left.hi<right.lo,name)
        obligations.append(dict(name=name,relation='strict_lt',left=name+'.left',right=name+'.right'))
    lt('initial_aux_below_threshold',rm+m0,1)
    lt('aux_early_below_threshold',bounds['aux_at_early'],1)
    lt('aux_late_above_threshold',1,bounds['aux_at_late'])
    lt('aux_first_root_is_strict',0,aux_derivative)
    lt('aux_cycle_ends_after_raw_pulse',1,I(finish.lo))
    lt('aux_cycle_ends_before_next_input',I(finish.hi),gap)
    lt('learned_gain_below_all_caps',learned,I(cap.lo))
    lt('mark_finishes_before_any_main_firing',I(mark.hi),rootlo)
    lt('main_fires_before_error_begins',roothi,I(error.lo))
    lt('error_finishes_during_main_fast',I(finish.hi),rootlo+1)
    lt('main_reopens_before_next_input',reopen,gap)
    for j in range(3):
        g=initial_gain*(I(j)*dose).exp()
        coeff=k*(qex+g*a/(a-k))
        # e^(a*t) q'(t) decreases when coeff>0, so checking t=1 suffices.
        derivative=g*a*a/(a-k)-coeff*(a-k).exp()
        frozen_end=r+qex*(-k).exp()+g*h(1)
        jump=g*(dose.exp()-1)
        peak=frozen_end+jump*density*overlap
        carry=(peak-r)*(-k*(gap-1)).exp()
        bounds.update({f'gain_before_{j}':g,f'peak_bound_{j}':peak,f'carry_bound_{j}':carry})
        lt(f'silent_{j}_positive_derivative_coefficient',0,coeff)
        lt(f'silent_{j}_frozen_flow_increases',0,derivative)
        lt(f'silent_{j}_no_first_crossing_even_with_overlap',peak,1)
        lt(f'silent_{j}_charge_returns_to_section',carry,I('0.03'))
    for label,t in [('early','0.5'),('late','0.9')]:
        bounds['learned_ready_'+label]=r+qex*(-k*I(t)).exp()+learned*h(t)
    coeff=k*(qex+learned*a/(a-k))
    derivative=learned*a*a/(a-k)-coeff*(a-k).exp()
    lt('learned_positive_derivative_coefficient',0,coeff)
    lt('learned_flow_strictly_increases',0,derivative)
    lt('learned_early_below_threshold',bounds['learned_ready_early'],1)
    lt('learned_late_above_threshold',1,bounds['learned_ready_late'])
    # Invariant reserve bound inherited from the model, checked for this box.
    W=(3*I(cap.hi)+3*I(mult.hi)+1)*a+I('1.1')+I('4.5')*I(lm.hi)+I('2.4')*I(le.hi)
    bounds['work_bound']=W;lt('reserve_gate_stays_open',W,500)
    # Calendar hulls also cover independent per-pulse delay jitter.
    bounds['B_first_emission']=I(24)+I(rootlo.lo,roothi.hi)
    bounds['A_first_arrival']=bounds['B_first_emission']+delay
    bounds['A_gain_complete_by']=I(40)+roothi+I(delay.hi)+I(finish.hi)
    bounds['A_first_emission']=I(48)+I(2)*I(rootlo.lo,roothi.hi)+delay
    bounds['A_last_emission']=I(120)+I(2)*I(rootlo.lo,roothi.hi)+delay
    bounds['A_last_return_by']=I(120)+roothi+I(delay.hi)+reopen
    bounds['B_last_return_by']=I(120)+reopen
    lt('A_learning_complete_before_first_response',bounds['A_gain_complete_by'],I(bounds['A_first_emission'].lo))
    lt('A_quiescent_before_measurement',bounds['A_last_return_by'],I('139.9'))
    lt('B_quiescent_before_measurement',bounds['B_last_return_by'],I('139.9'))
    return bounds,obligations


def rounded(interval):
    # Certificates use 40 decimal places; an independent 70-place integer replay
    # must fit inside each published enclosure rather than only agree in digits.
    scale=Decimal('1e-40')
    low=Context(prec=256,rounding=ROUND_FLOOR);high=Context(prec=256,rounding=ROUND_CEILING)
    return [str(low.quantize(interval.lo,scale)),str(high.quantize(interval.hi,scale))]


def certify(epsilon,out):
    if not __debug__:raise Refusal('optimized execution (-O) is forbidden')
    bounds,obligations=derive(epsilon)
    sources={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(HERE.glob('*.py'))}
    certificate=dict(status='CERTIFIED_LOCAL_PREPARED_SECTION',epsilon_relative=epsilon,
      arithmetic='Inherited A22 outward Decimal intervals at 128 digits; published bounds rounded outwards to 40 decimal places',
      scope='Two-cell B->A phase from an explicit prepared section, not reachability of that section from the complete earlier prototype',
      section=dict(main_mode='READY',aux_modes='all READY',q=['0.09999','0.10001'],
        m_each=['0.02499','0.02501'],active_port=2,
        active_log_gain='ln(3/10) + [-1e-5,1e-5]',b=['0.17999','0.18001'],E=['50','100'],
        other_gains='arbitrary positive values within their own caps',raw_currents='none'),
      parameters='All five original per-port parameters independently in their relative box, fixed in time; 30 physical parameters across two three-port cells',
      protocol=dict(B_source='16 canonical pulses at 0,8,...,120 on port 2',
        route='each B emission to A port 2 with delay independently in [0.3,0.4]',
        other_inputs='none; A->B route closed; no settings copies',measurement='139.9',
        interpretation='Local t=0 corresponds to prototype t=320; the prepared section is stable under silence from t=319.9'),
      conclusion=dict(B_emissions=13,A_emissions=10,A_full_error_doses=3,
        A_final_gain='g_A_initial * exp(9/5)',A_recovery='unchanged from prepared section',
        isolated_probe_before='0/8',isolated_probe_after='8/8',probe_period='20',
        probe='standardized-rest independent copy, same physical parameters and learned gain/b, plasticity disabled'),
      bounds={name:rounded(value) for name,value in bounds.items()},obligations=obligations,source_sha256=sources,
      trusted_base=['authentic execution of these sources','correct Python integer/runtime and inherited Decimal outward arithmetic',
        'written hybrid-flow and induction proof; no full Lean formalization of this new theorem'])
    # Check the published rounded bounds retain every strict inequality.
    for o in obligations:
        require(Decimal(certificate['bounds'][o['left']][1])<Decimal(certificate['bounds'][o['right']][0]),'published bound loses '+o['name'])
    out.parent.mkdir(parents=True,exist_ok=True);out.write_text(json.dumps(certificate,indent=2)+'\n')
    print(json.dumps(dict(file=str(out),status=certificate['status'],epsilon=epsilon,
      strict_obligations=len(obligations),learned_gain=certificate['bounds']['learned_gain'])),flush=True)
    return certificate

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--epsilon',required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args()
    try:certify(a.epsilon,a.out)
    except Exception as exc:
        print('REFUSED:',str(exc),file=sys.stderr);sys.exit(1)
