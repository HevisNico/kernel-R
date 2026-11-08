"""N-independent local contracts for compositional R cadence learning."""
from pathlib import Path
from decimal import Decimal, Context, ROUND_FLOOR, ROUND_CEILING
import argparse, hashlib, json, sys
from decimal_intervals import I, configure
from dependency import arguments, replay
from algebra import identities

configure(128)
HERE=Path(__file__).resolve().parent

class Refusal(RuntimeError): pass

def require(condition,message):
    if not condition: raise Refusal(message)

def derive(epsilon):
    eps=I(epsilon)
    require(eps.lo==eps.hi and 0<eps.lo<1,'invalid epsilon')
    a,k,r,rm=I(4).ln(),I('0.5'),I('0.1'),I('0.025')
    eta=I('-0.00001','0.00001')
    factor=I((1-eps).lo,(1+eps).hi)
    lm=I('1.25').ln()/I('0.02')*factor
    ls=I(8).ln()/I('1.06')*factor
    le=a/I('0.15')*factor
    h=lambda t:a/(a-k)*((-k*I(t)).exp()-(-a*I(t)).exp())
    M=(1-rm)/h('0.02')*factor
    cap=4*factor
    tau=I('0.015','0.03')
    mark=tau+I('1.25').ln()/lm
    error=mark+I(8).ln()/ls
    finish=error+a/le
    J=I('0.15');period=I(4);settling=I(4,'4.1')
    slowgap=I('7.4','8.3')
    g=lambda count:I('0.3')*eta.exp()*(I('0.6')*count).exp()
    b0=I('0.07999','0.08001');b1=b0+I('0.1');b2=b1+I('0.1');b3=b2+I('0.1')
    L=I('2.5').ln()
    root_low=I('0.65','0.66');root_high=I('0.24','0.25')
    root_transient=I('0.20','0.25');root_leaf=I('0.4','0.66')
    bounds,obligations={},[]
    def save(name,value): bounds[name]=I(value);return bounds[name]
    def lt(name,left,right):
        left,right=save(name+'.left',left),save(name+'.right',right)
        require(left.hi<right.lo,name)
        obligations.append(dict(name=name,relation='strict_lt',left=name+'.left',right=name+'.right'))
    aux=lambda t:rm+eta*(-k*I(t)).exp()+M*h(t)
    ztime=I(0,tau.hi)
    auxprime=-k*eta*(-k*ztime).exp()+M*a/(a-k)*(-k*(-k*ztime).exp()+a*(-a*ztime).exp())
    lt('aux.birth_below_threshold',rm+eta,1)
    lt('aux.root_lower',aux(tau.lo),1);lt('aux.root_upper',1,aux(tau.hi))
    lt('aux.root_strict',0,auxprime)
    lt('aux.finish_after_raw',1,I(finish.lo))
    lt('aux.finish_before_fastest_next_input',I(finish.hi),period-2*J)
    W=(3*I(cap.hi)+3*I(M.hi)+1)*a+I('1.1')+I('4.5')*I(lm.hi)+I('2.4')*I(le.hi)
    lt('energy.reserve_invariant',W,500)
    lt('caps.final_gain',g(4),I(cap.lo));lt('caps.final_recovery',b3,I('1.1'))
    save('jitter_budget',J);save('prepared_recovery',b1);save('final_recovery',b3)
    save('prepared_gain',g(3));save('final_gain',g(4))
    save('aux.mark_end',mark);save('aux.ERROR_start',error);save('aux.finish',finish)
    deficit=I('0.1')*tau+(I('0.1')-I('0.4')*I('1.25').ln())/lm
    save('MARK_integral_deficit',deficit)
    density=a*(-a*I(error.lo)).exp()
    overlap=I(0,max(0,(1-I(error.lo)).hi))

    def root(name,gain,excess,bracket,b):
        fixed=lambda t:r+excess*(-k*I(t)).exp()+gain*h(t)
        coeff=k*(excess+gain*a/(a-k))
        lt(name+'.positive_coefficient',0,coeff)
        lt(name+'.increasing',0,gain*a*a/(a-k)-coeff*(a-k).exp())
        lt(name+'.lower_sign',fixed(bracket.lo),1)
        lt(name+'.upper_sign',1,fixed(bracket.hi))
        lt(name+'.MARK_precedes_fire',I(mark.hi),I(bracket.lo))
        lt(name+'.fire_precedes_ERROR',I(bracket.hi),I(error.lo))
        lt(name+'.ERROR_entirely_protected',I(finish.hi),I(bracket.lo)+1+L/b)
    root('relay.low_root',g(3),I(0),root_low,b1)
    lt('relay.low_root_at_b2.ERROR_entirely_protected',I(finish.hi),I(root_low.lo)+1+L/b2)
    root('relay.high_rest_root',g(4),I(0),root_high,b3)
    lt('slow_prefix.ready_before_every_input',I(root_low.hi)+1+L/b1,I(slowgap.lo)-2*J)
    lt('steady_tail.ready_before_every_input',I(root_high.hi)+1+L/b3,period-2*J)
    lt('h.increasing_through_raw_end',0,a*(-a).exp()-k*(-k).exp())

    def protected(name,b,gap,previous_root,which):
        duration=gap-1-previous_root
        lt(name+'.past_FAST',0,duration)
        lt(name+'.still_in_SLOW',b*duration,L)
        reopen=(L-b*duration+deficit)/(b+I('0.1'))
        save(name+'.return',reopen)
        lt(name+'.entire_MARK_protected',I(mark.hi),I(reopen.lo))
        lt(name+'.ready_before_following_input',I(reopen.hi),period-2*J)
        if which=='MARK_only':
            lt(name+'.entire_ERROR_protected',I(finish.hi),I(reopen.lo))
        else:
            lt(name+'.ready_before_ERROR',I(reopen.hi),I(error.lo))
        return reopen
    protected('relay.first_miss',b1,settling+I(-2*J.hi,2*J.hi),root_low,'MARK_only')
    returned=protected('relay.second_miss',b2,period+I(-2*J.hi,2*J.hi),root_low,'MARK_then_ERROR')
    lt('relay.second_miss.before_raw_end',I(returned.hi),1)
    v=I(returned.lo)
    tail=g(3)*a/(a-k)*((-k).exp()*(-(a-k)*v).exp()-(-a).exp())
    tail=tail+(g(4)-g(3))*density*overlap
    lt('relay.second_miss.no_refire_from_tail',r+I(tail.hi),1)
    carry=I(0,tail.hi)*(-k*(period-2*J-1)).exp()
    save('relay.transient_charge_excess',carry)
    root('relay.high_transient_root',g(4),carry,root_transient,b3)
    lt('relay.transient_return_before_next_input',I(root_transient.hi)+1+L/b3,period-2*J)
    # Output template: two new slow-prefix pulses, followed by a settling gap
    # and the same phase-jitter envelope. d' >= 4 uses q>=r comparison, proved
    # in the written induction; the upper bound uses these root brackets.
    new_slow_1=settling+period
    new_slow_2=2*period+root_transient-root_low
    lt('output.first_new_slow_lower',I(slowgap.lo),I(new_slow_1.lo))
    lt('output.first_new_slow_upper',I(new_slow_1.hi),I(slowgap.hi))
    lt('output.second_new_slow_lower',I(slowgap.lo),I(new_slow_2.lo))
    lt('output.second_new_slow_upper',I(new_slow_2.hi),I(slowgap.hi))
    lt('output.settling_upper',4+I(root_high.hi)-I(root_transient.lo),I(settling.hi))

    # Base case: the leaf sees an exact period-4 source on its untrained port.
    excess=I(0)
    for count in range(3):
        gain=g(count);coeff=k*(excess+gain*a/(a-k))
        lt('leaf.weak_'+str(count)+'.increasing',0,gain*a*a/(a-k)-coeff*(a-k).exp())
        peak=r+excess*(-k).exp()+gain*h(1)+gain*(I('0.6').exp()-1)*density*overlap
        lt('leaf.weak_'+str(count)+'.no_fire',peak,1)
        excess=I(0,(peak-r).hi)*(-k*3).exp()
    save('leaf.first_firing_excess',excess)
    root('leaf.first_root',g(3),excess,root_leaf,b1)
    protected('leaf.first_miss',b1,I(4),root_leaf,'MARK_only')
    # The second miss, residual tail and sustained response satisfy the relay
    # bounds already checked at a larger jitter envelope.
    initial_gap=8+root_low-root_leaf
    lt('leaf.first_output_gap_lower',I(slowgap.lo),I(initial_gap.lo))
    lt('leaf.first_output_gap_upper',I(initial_gap.hi),I(slowgap.hi))
    # Preparation is discharged by the authenticated earlier entry theorem:
    # direct period-8 sources are a subset of its [7.5,8.5] input family.
    lt('preparation.last_return_before_fast_start',120+I('0.9')+1+L/b1,I('159.9'))
    lt('horizon.cell_latency',I(root_low.hi),I('0.7'))
    lt('horizon.hop_budget',I(root_low.hi)+I('0.4'),I('1.1'))
    lt('horizon.last_return_budget',I(root_low.hi)+1+L/b1,8)
    # Frozen probes on independent copies: before 4/8, after 8/8 for relays.
    before_return=root_low+1+L/b1
    lt('probe.before.next_raw_entirely_protected',5,I(before_return.lo))
    lt('probe.before.ready_for_third',I(before_return.hi),8)
    after_return=root_high+1+L/b3
    lt('probe.after.ready_for_every_next',I(after_return.hi),4)
    weak_carry=g(0)*h(1)*(-k*3).exp()/(1-(-k*4).exp())
    lt('probe.leaf_before.flow_increases',0,g(0)*a*a/(a-k)-k*(weak_carry+g(0)*a/(a-k))*(a-k).exp())
    lt('probe.leaf_before.never_fires',r+weak_carry*(-k).exp()+g(0)*h(1),1)
    return bounds,obligations

def contract(epsilon):
    return dict(status='CERTIFIED_UNIFORM_N_CHAIN_COMPOSITION',epsilon_relative=epsilon,
        quantifier='Every finite integer N>=1, every K>=4*N+12, every independent fixed point of the 15*N physical parameter box, and all wire-error sequences within the stated budgets',
        scope='Directed chain with supplied preparation and input protocol; not arbitrary graphs, cycles, fixed 25-pulse scalability or unlimited per-hop jitter',
        physical_family='All C,Lm,Ls,Le,M parameters independently in the nominal relative box for each port of each cell; other R constants unchanged',
        birth_family=dict(time='0',modes='all READY',q=['0.09999','0.10001'],m_each=['0.02499','0.02501'],
            log_gains='ln(0.3,1.2,0.3) + independent [-1e-5,1e-5]',b=['0.07999','0.08001'],E=['50','100'],currents='none'),
        protocol=dict(preparation='Routes closed. Each relay: 16 direct port-2 pulses at 0,8,...,120. Leaf: same train on port 1. Wait until 160.',
            fast='K direct leaf port-0 pulses at 160+4*k, k=0,...,K-1. Each downstream emission drives its parent port 2. No other fast source.',
            routes='A finite directed leaf-to-root chain, enabled from 160, with no reverse edge or feedback cycle',
            copies='none',live_resets='none',wire='One canonical pulse per emission, without loss or waveform deformation. delay_i,k = d_i + error_i,k; sigma_i in [0,0.05], d_i fixed in [0.3+sigma_i,0.4-sigma_i], abs(error_i,k)<=sigma_i',
            jitter_sum='sum(sigma_i)<=0.15; fixed-link case sigma_i=0 supports any finite depth without tightening the physical boxes'),
        packet_contract=dict(name='P(m,L,J)',prefix='m>=1 ideal dates with consecutive gaps in [7.4,8.3]',
            tail='L>=1 ideal dates starting d in [4,4.1] after the final prefix date, then period 4',
            actual='Each actual date equals its ideal date plus an arbitrary phase error in [-J,J]; an existential template, no independent-noise assumption',
            local_assumption='Prepared relay at exact main rest, gain = own birth active gain * exp(1.8), b = birth b + 0.1, auxiliaries READY, no currents, E in [50,100]; J<=0.15, L>=5',
            local_guarantee='P(m,L,J) -> P(m+2,L-4,J); exactly two full MARK doses and one full ERROR dose; no raw-tail refiring',
            wire_rule='P(m,L,J) -> P(m,L,J+sigma_i)',
            leaf_base='K>=9 exact period-4 source -> P(3,K-8,0), with two full MARK doses and four full ERROR doses on its active port'),
        composition=dict(node_index='j=0 at leaf, j=N-1 at root',prefix_length='3+2*j',tail_length='K-8-4*j',
            node_outputs='K-5-2*j',root_outputs='K-2*N-3',root_tail='K-4*N-4 >= 8',
            total_fast_emissions='N*(K-N-4)',minimum_K='4*N+12',
            quiescent_by='160+4*(K-1)+(11/10)*(N-1)+8',
            scaling='Source length and time horizon are linear in N; total fast-block traffic is quadratic at the minimum K'),
        conclusion=dict(recovery='b_after = b_birth+0.3 = b_before_fast+0.2 in every cell',
            final_recovery=['0.37999','0.38001'],active_gain='Own birth active gain * exp(2.4) on leaf port 0 and every relay port 2',
            retained_probe='Eight canonical period-4 pulses on disconnected standardized-rest copies with learning disabled: leaf 0/8 -> 8/8, every relay 4/8 -> 8/8',
            cut='Cut any link during the fast phase: every ancestor above that cut remains at its prepared settings and its retained probe stays 4/8',
            end='All cells READY with main q exactly 0.1 and no active currents; no cell is removed'),
        arithmetic='N-independent local inequalities: outward Decimal generation and separate integer replay. Polynomial identities checked exactly. Universal composition uses the written packet induction, not finite-N enumeration or full Lean formalization')

def rounded(value):
    unit=Decimal('1e-40');down=Context(prec=256,rounding=ROUND_FLOOR);up=Context(prec=256,rounding=ROUND_CEILING)
    return [str(down.quantize(value.lo,unit)),str(up.quantize(value.hi,unit))]

def certify(epsilon,args,out):
    if not __debug__: raise Refusal('optimized execution is forbidden')
    dependency=replay(epsilon,args)
    bounds,obligations=derive(epsilon)
    document=contract(epsilon)
    document.update(preparation_theorem=dependency,symbolic_identities=identities(),
        bounds={name:rounded(value) for name,value in bounds.items()},obligations=obligations,
        source_sha256={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(HERE.glob('*.py'))})
    for ob in obligations:
        require(Decimal(document['bounds'][ob['left']][1])<Decimal(document['bounds'][ob['right']][0]),'rounding loses '+ob['name'])
    out.parent.mkdir(parents=True,exist_ok=True);out.write_text(json.dumps(document,indent=2)+'\n')
    print(json.dumps(dict(status=document['status'],epsilon=epsilon,local_obligations=len(obligations),
        enclosures=len(bounds),symbolic_identities=len(document['symbolic_identities']))),flush=True)
    return document

if __name__=='__main__':
    p=argparse.ArgumentParser();arguments(p);p.add_argument('--epsilon',required=True);p.add_argument('--out',type=Path,required=True);args=p.parse_args()
    try: certify(args.epsilon,args,args.out)
    except Exception as exc: print('REFUSED:',str(exc),file=sys.stderr);sys.exit(1)
