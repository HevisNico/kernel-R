"""Independent integer-arithmetic replay of the published local certificate.

The analytic sufficient inequalities are restated here. Arithmetic, exp/ln and
rounding are independent of the Decimal certifier; this is not an independent
formalization of the handwritten hybrid-model argument.
"""
from pathlib import Path
from fractions import Fraction
import argparse,json,hashlib,sys
from integer_intervals import Q as I

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
    overlap=I(0,max(Fraction(0),(I(1)-I(error.lo)).hi))
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


def verify(path):
    if not __debug__:raise Refusal('optimized execution (-O) is forbidden')
    certificate=json.loads(path.read_text())
    require(certificate['status']=='CERTIFIED_LOCAL_PREPARED_SECTION','wrong certificate kind')
    require(isinstance(certificate['epsilon_relative'],str) and 0<Fraction(certificate['epsilon_relative'])<1,'invalid declared certificate width')
    require(certificate['scope']=='Two-cell B->A phase from an explicit prepared section, not reachability of that section from the complete earlier prototype','scope modified')
    require(certificate['parameters']=='All five original per-port parameters independently in their relative box, fixed in time; 30 physical parameters across two three-port cells','parameter family modified')
    here=Path(__file__).resolve().parent
    required={'certify.py','verify.py','decimal_intervals.py','integer_intervals.py','tests.py'}
    require(set(certificate['source_sha256'])==required,'incomplete source identity')
    for name,want in certificate['source_sha256'].items():
        require(hashlib.sha256((here/name).read_bytes()).hexdigest()==want,'source identity mismatch: '+name)
    require(certificate['conclusion']==dict(B_emissions=13,A_emissions=10,A_full_error_doses=3,
        A_final_gain='g_A_initial * exp(9/5)',A_recovery='unchanged from prepared section',
        isolated_probe_before='0/8',isolated_probe_after='8/8',probe_period='20',
        probe='standardized-rest independent copy, same physical parameters and learned gain/b, plasticity disabled'),'conclusion modified')
    expected_section=dict(main_mode='READY',aux_modes='all READY',q=['0.09999','0.10001'],
        m_each=['0.02499','0.02501'],active_port=2,
        active_log_gain='ln(3/10) + [-1e-5,1e-5]',b=['0.17999','0.18001'],E=['50','100'],
        other_gains='arbitrary positive values within their own caps',raw_currents='none')
    require(certificate['section']==expected_section,'initial section modified')
    require(certificate['protocol']==dict(B_source='16 canonical pulses at 0,8,...,120 on port 2',
        route='each B emission to A port 2 with delay independently in [0.3,0.4]',
        other_inputs='none; A->B route closed; no settings copies',measurement='139.9',
        interpretation='Local t=0 corresponds to prototype t=320; the prepared section is stable under silence from t=319.9'),'protocol modified')
    bounds,obligations=derive(certificate['epsilon_relative'])
    require(certificate['obligations']==obligations,'proof obligation missing, reordered or altered')
    require(set(certificate['bounds'])==set(bounds),'bound set mismatch')
    for name,q in bounds.items():
        low,high=map(Fraction,certificate['bounds'][name])
        require(low<=q.lo<=q.hi<=high,'integer enclosure is not contained in published bound: '+name)
    for obligation in obligations:
        l=certificate['bounds'][obligation['left']];r=certificate['bounds'][obligation['right']]
        require(Fraction(l[1])<Fraction(r[0]),'published strict inequality fails: '+obligation['name'])
    result=dict(status='VERIFIED_WITH_INDEPENDENT_INTEGER_ARITHMETIC',
        epsilon=certificate['epsilon_relative'],enclosures_checked=len(bounds),strict_obligations=len(obligations),
        certificate_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
        arithmetic='Python integer fixed point at 70 decimals, explicit Taylor/atanh tails; no Decimal or float',
        scope='Independent arithmetic replay of the stated sufficient inequalities, not a full proof-assistant check of the model semantics')
    print(json.dumps(result),flush=True)
    return result

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('certificate',type=Path);parser.add_argument('--out',type=Path)
    a=parser.parse_args()
    try:
        result=verify(a.certificate)
        if a.out:a.out.write_text(json.dumps(result,indent=2)+'\n')
    except Exception as exc:
        print('REFUSED:',str(exc),file=sys.stderr);sys.exit(1)
