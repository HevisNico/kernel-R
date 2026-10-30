"""Certify entry into the local feedback-learning section from the pulses-only birth family."""
from pathlib import Path
from decimal import Decimal,Context,ROUND_FLOOR,ROUND_CEILING
import argparse,json,hashlib,sys
from decimal_intervals import I,configure
from dependency import verify_dependency

configure(128)
HERE=Path(__file__).resolve().parent

class Refusal(RuntimeError):pass

def require(condition,message):
    if not condition:raise Refusal(message)


def derive(epsilon):
    eps=I(epsilon);require(eps.lo==eps.hi and 0<eps.lo<1,'invalid exact epsilon')
    a=I(4).ln();k=I('0.5');r=I('0.1');rm=I('0.025')
    factor=I((1-eps).lo,(1+eps).hi)
    h=lambda t:a/(a-k)*((-k*I(t)).exp()-(-a*I(t)).exp())
    C=4*factor;lm=I('1.25').ln()/I('0.02')*factor
    ls=I(8).ln()/I('1.06')*factor;le=I(4).ln()/I('0.15')*factor
    M=(1-rm)/h('0.02')*factor
    eta=I('-0.00001','0.00001');qex=I('-0.00001','0.03')
    b0=I('0.07999','0.08001');mark_dose=I('0.5')*(1-I('0.8'));b1=b0+mark_dose
    dose=8*(I('0.1')-rm);tau=I('0.015','0.03');time=I(0,tau.hi)
    aux=lambda t:rm+eta*(-k*I(t)).exp()+M*h(t)
    aux_derivative=-k*eta*(-k*time).exp()+M*a/(a-k)*(-k*(-k*time).exp()+a*(-a*time).exp())
    mark=tau+I('1.25').ln()/lm;error=mark+I(8).ln()/ls;finish=error+I(4).ln()/le
    overlap=I(0,max(Decimal(0),(1-I(error.lo)).hi));density=a*(-a*I(error.lo)).exp()
    root_lo=I('0.3');root_hi=I('0.9');A_root_lo=I('0.5');delay=I('0.3','0.4')
    gap_lo=8+A_root_lo+I(delay.lo)-root_hi-I(delay.hi)
    gap_hi=8+root_hi+I(delay.hi)-A_root_lo-I(delay.lo)
    L=I('2.5').ln()
    stable_return=root_hi+1+L/b1
    low_earliest_return=root_lo+1+L/b0
    stable_earliest_return=root_lo+1+L/b1
    slow_before_upper=I(b0.hi)*(gap_hi-1-root_lo)
    slow_through_error_upper=slow_before_upper+I(b1.hi)*I(finish.hi)
    reopen_after_protected=I(3)
    slow_at_return_lower=I(b0.lo)*(gap_lo-1-root_hi)+I(b1.lo)*(reopen_after_protected-I(mark.hi))
    gA=I('0.3')*eta.exp()*(3*dose).exp();gB=I('1.2')*eta.exp()*dose.exp()
    bounds=dict(epsilon=eps,a=a,kappa=k,C=C,Lm=lm,Ls=ls,Le=le,M=M,
      birth_b=b0,mark_dose=mark_dose,entry_b=b1,gain_dose=dose,
      aux_at_early=aux(tau.lo),aux_at_late=aux(tau.hi),aux_derivative=aux_derivative,
      mark_end=mark,error_start=error,aux_finish=finish,overlap=overlap,density=density,
      A_trained_gain=gA,B_trained_port1_gain=gB,
      min_input_gap=gap_lo,max_input_gap=gap_hi,stable_return_bound=stable_return,
      low_earliest_return=low_earliest_return,stable_earliest_return=stable_earliest_return,
      slow_before_protected_input_upper=slow_before_upper,
      slow_through_error_upper=slow_through_error_upper,slow_at_return_lower=slow_at_return_lower,
      protected_pulse_reopen_by=reopen_after_protected,slow_return_target=L)
    obligations=[]
    def relation(name,left,right,strict=True):
        left=I(left);right=I(right);bounds[name+'.left']=left;bounds[name+'.right']=right
        require(left.hi<right.lo if strict else left.hi<=right.lo,name)
        obligations.append(dict(name=name,relation='strict_lt' if strict else 'le',left=name+'.left',right=name+'.right'))
    lt=lambda name,left,right:relation(name,left,right,True)
    leq=lambda name,left,right:relation(name,left,right,False)
    lt('birth_aux_below_threshold',rm+eta,1)
    lt('aux_root_early',bounds['aux_at_early'],1);lt('aux_root_late',1,bounds['aux_at_late'])
    lt('aux_first_crossing_strict',0,aux_derivative)
    lt('aux_finish_after_raw_end',1,I(finish.lo));lt('aux_finish_before_next_input',I(finish.hi),gap_lo)
    lt('raw_pulses_do_not_overlap',1,gap_lo)
    for label,base,count in [('A','0.3',3),('B','1.2',1)]:
        for j in range(count):
            g=I(base)*eta.exp()*(j*dose).exp()
            coeff=k*(qex+g*a/(a-k));derivative=g*a*a/(a-k)-coeff*(a-k).exp()
            peak=r+qex*(-k).exp()+g*h(1)+g*(dose.exp()-1)*density*overlap
            carry=(peak-r)*(-k*(gap_lo-1)).exp()
            bounds.update({f'{label}_weak_gain_{j}':g,f'{label}_weak_peak_{j}':peak,f'{label}_weak_carry_{j}':carry})
            lt(f'{label}_weak_{j}_positive_coefficient',0,coeff)
            lt(f'{label}_weak_{j}_increasing_fixed_flow',0,derivative)
            lt(f'{label}_weak_{j}_never_fires',peak,1)
            lt(f'{label}_weak_{j}_charge_section_invariant',carry,I('0.03'))
        learned=gA if label=='A' else gB
        lt(label+'_gain_cap_not_reached',learned,I(C.lo))
        coeff=k*(qex+learned*a/(a-k));derivative=learned*a*a/(a-k)-coeff*(a-k).exp()
        ready=lambda t:r+qex*(-k*I(t)).exp()+learned*h(t)
        lt(label+'_strong_positive_coefficient',0,coeff)
        lt(label+'_strong_increasing_flow',0,derivative)
        lt(label+'_strong_early_below_threshold',ready(root_lo),1)
        lt(label+'_strong_late_above_threshold',1,ready(root_hi))
    lt('A_output_lower_latency_for_delivery_hulls',r+qex*(-k*A_root_lo).exp()+gA*h(A_root_lo),1)
    lt('mark_complete_before_first_main_fire',I(mark.hi),root_lo)
    lt('main_fire_before_error_start',root_hi,I(error.lo))
    lt('initial_error_entirely_protected',I(finish.hi),I(low_earliest_return.lo))
    lt('stable_error_entirely_protected',I(finish.hi),I(stable_earliest_return.lo))
    lt('next_input_is_after_fast',root_hi+1,gap_lo)
    lt('low_b_has_not_reopened_at_next_input',slow_before_upper,L)
    lt('whole_mark_and_error_of_protected_input_stay_protected',slow_through_error_upper,L)
    lt('protected_input_reopens_before_three_time_units',L,slow_at_return_lower)
    lt('protected_input_cycle_ends_before_reopening_deadline',I(finish.hi),reopen_after_protected)
    lt('protected_input_return_before_following_input',reopen_after_protected,gap_lo)
    lt('all_later_inputs_follow_stable_return',stable_return,gap_lo)
    lt('recovery_cap_not_reached',b1,I('1.1'))
    W=(3*I(C.hi)+3*I(M.hi)+1)*a+I('1.1')+I('4.5')*I(lm.hi)+I('2.4')*I(le.hi)
    bounds['work_bound']=W;lt('energy_reserve_gate_open',W,500)
    # Actual protocol calendar. A uses port 0; B is born at 160 and uses port 1.
    bounds['A_first_block_last_return']=120+stable_return
    bounds['A_second_block_last_emission']=280+root_hi
    bounds['A_second_block_last_return']=280+stable_return
    bounds['B_first_possible_arrival']=160+A_root_lo+I(delay.lo)
    bounds['B_last_possible_arrival']=280+root_hi+I(delay.hi)
    bounds['B_last_possible_emission']=bounds['B_last_possible_arrival']+root_hi
    bounds['B_last_return']=bounds['B_last_possible_arrival']+stable_return
    lt('A_quiescent_before_second_block',bounds['A_first_block_last_return'],I('159.9'))
    lt('A_first_block_emissions_precede_B_birth',120+root_hi,160)
    lt('first_B_input_strictly_after_birth',160,bounds['B_first_possible_arrival'])
    lt('all_A_teaching_emissions_inside_gate',bounds['A_second_block_last_emission'],310)
    lt('all_A_teaching_deliveries_before_gate_end',bounds['B_last_possible_arrival'],310)
    lt('B_teaching_phase_emissions_precede_reverse_gate',bounds['B_last_possible_emission'],320)
    lt('A_quiescent_at_prepared_cut',bounds['A_second_block_last_return'],I('319.9'))
    lt('B_quiescent_at_prepared_cut',bounds['B_last_return'],I('319.9'))
    # Closed inclusions into the pre-existing local theorem's section.
    leq('entry_b_contains_lower_endpoint',I('0.17999'),I(b1.lo))
    leq('entry_b_contains_upper_endpoint',I(b1.hi),I('0.18001'))
    leq('entry_rest_charge_above_section_lower',I('0.09999'),r)
    leq('entry_rest_charge_below_section_upper',r,I('0.10001'))
    return bounds,obligations


def rounded(value):
    scale=Decimal('1e-40');low=Context(prec=256,rounding=ROUND_FLOOR);high=Context(prec=256,rounding=ROUND_CEILING)
    return [str(low.quantize(value.lo,scale)),str(high.quantize(value.hi,scale))]


def contract(epsilon,dependency):
    return dict(status='CERTIFIED_PULSES_ONLY_ENTRY_AND_COMPOSITION',epsilon_relative=epsilon,
      scope='Original pulses-only prototype prefix through 459.9; no settings-copy variant or later fully open reciprocal phase',
      birth_family=dict(A_birth='0',B_birth='160',modes='main and all auxiliaries READY',
        q=['0.09999','0.10001'],m_each=['0.02499','0.02501'],
        log_gains='ln(0.3,1.2,0.3) + independent [-1e-5,1e-5]',b=['0.07999','0.08001'],E=['50','100'],
        initial_currents='none'),
      physical_family='30 original per-port parameters independently in the fixed relative box; all other kernel constants unchanged',
      protocol=dict(configuration='impulsions / pulses only',
        A_port0_sources='0,8,...,120 and 160,168,...,280',B_port2_sources='320,328,...,440',
        A_to_B='port 1, firing gate [160,310)',B_to_A='port 2, firing gate [320,470)',
        per_pulse_wire_delays=['0.3','0.4'],settings_copies='none',entry_cut='319.9',end='459.9'),
      entry_conclusion=dict(main_q='exactly 0.1',aux_modes='all READY',
        auxiliary_charges='within [0.02499,0.02501]; active trained auxiliaries exactly 0.025',
        feedback_log_gains='unchanged ln(0.3)+[-1e-5,1e-5] on port 2 of both cells',
        b=['0.17999','0.18001'],E=['50','100'],currents='none',
        A_port0_gain='initial gain * exp(1.8)',B_port1_gain='initial gain * exp(0.6)',
        full_protected_MARK_doses='exactly one in each cell, each adds 0.1 to b',
        prefix_emissions=dict(A_first_block=12,A_second_block=16,B_teaching_block=14)),
      composed_conclusion=dict(section_entry_assumption='discharged for the stated birth family and pulses-only protocol',
        feedback_phase=dependency['conclusion'],A_total_emissions_through_cut=38,B_total_emissions_through_cut=27,
        covered='A feedback gain grows by exp(1.8), isolated probe 0/8 before and 8/8 after, for every point in the stated box'),
      arithmetic='Outward Decimal 128 digits; independent integer replay; written induction, no complete Lean formalization')


def certify(epsilon,link_certificate,link_code,out):
    if not __debug__:raise Refusal('optimized execution is forbidden')
    link,identity=verify_dependency(epsilon,link_certificate,link_code)
    bounds,obligations=derive(epsilon)
    result=contract(epsilon,link)
    result.update(bounds={name:rounded(value) for name,value in bounds.items()},obligations=obligations,
      local_theorem=identity,source_sha256={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(HERE.glob('*.py'))})
    for ob in obligations:
        left=Decimal(result['bounds'][ob['left']][1]);right=Decimal(result['bounds'][ob['right']][0])
        require(left<right if ob['relation']=='strict_lt' else left<=right,'rounding loses '+ob['name'])
    out.parent.mkdir(parents=True,exist_ok=True);out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(file=str(out),epsilon=epsilon,status=result['status'],obligations=len(obligations),
      entry_b=result['bounds']['entry_b'],B_last_return=result['bounds']['B_last_return'])),flush=True)
    return result

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--epsilon',required=True);p.add_argument('--link-certificate',required=True,type=Path);p.add_argument('--link-code',required=True,type=Path);p.add_argument('--out',required=True,type=Path);a=p.parse_args()
    try:certify(a.epsilon,a.link_certificate,a.link_code,a.out)
    except Exception as exc:print('REFUSED:',str(exc),file=sys.stderr);sys.exit(1)
