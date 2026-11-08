"""Integer replay of the cadence cascade, without importing the Decimal producer.

Root brackets are certificate witnesses: both endpoint signs and monotonicity
are rechecked, then used in the full pulse induction. No floating root solver.
"""
from pathlib import Path
from fractions import Fraction
import argparse, hashlib, json, sys
from integer_intervals import Q as I
from dependency import arguments, replay

HERE = Path(__file__).resolve().parent

class Refusal(RuntimeError):
    pass

def require(condition, message):
    if not condition:
        raise Refusal(message)

def derive(epsilon, root_hints):
    eps = I(epsilon)
    require(eps.lo == eps.hi and 0 < eps.lo < 1, 'invalid epsilon')
    a, k, r, rm = I(4).ln(), I('0.5'), I('0.1'), I('0.025')
    eta = I('-0.00001', '0.00001')
    factor = I((1-eps).lo, (1+eps).hi)
    lm = I('1.25').ln()/I('0.02')*factor
    ls = I(8).ln()/I('1.06')*factor
    le = a/I('0.15')*factor
    h = lambda t: a/(a-k)*((-k*I(t)).exp()-(-a*I(t)).exp())
    mult = (1-rm)/h('0.02')*factor
    cap = 4*factor
    tau = I('0.015', '0.03')
    mark = tau + I('1.25').ln()/lm
    error = mark + I(8).ln()/ls
    finish = error + a/le
    dose, mdose = I('0.6'), I('0.1')
    L = I('2.5').ln()
    bounds, obligations, trace = {}, [], []
    def save(name, value):
        bounds[name] = I(value)
        return bounds[name]
    def lt(name, left, right):
        left, right = save(name+'.left', left), save(name+'.right', right)
        require(left.hi < right.lo, name)
        obligations.append(dict(name=name, relation='strict_lt', left=name+'.left', right=name+'.right'))
    symbols = {}
    class Time:
        # Shared latency symbols cancel before interval evaluation. Wire jitter
        # has a fresh symbol for every pulse; none of it is cancelled accidentally.
        def __init__(self, constant=0, terms=None):
            self.constant, self.terms = I(constant), terms or {}
        def __add__(self, other):
            if not isinstance(other, Time): other = Time(other)
            terms = self.terms.copy()
            for name, coefficient in other.terms.items():
                terms[name] = terms.get(name, 0)+coefficient
                if not terms[name]: del terms[name]
            return Time(self.constant+other.constant, terms)
        __radd__ = __add__
        def __sub__(self, other):
            if not isinstance(other, Time): other = Time(other)
            return self+Time(-other.constant, {name:-c for name,c in other.terms.items()})
        def interval(self):
            result = self.constant
            for name, coefficient in sorted(self.terms.items()):
                result = result+coefficient*symbols[name]
            return result
    def symbol(name, value):
        if name in symbols:
            require(symbols[name].lo == value.lo and symbols[name].hi == value.hi, 'inconsistent shared latency')
        else: symbols[name] = value
        return Time(0, {name:1})
    def gain(base, count): return I(base)*eta.exp()*(count*dose).exp()
    # All first auxiliary cycles start within eta of rest. Later cycles reset
    # exactly to rm, so the same hull remains valid without a numerical reset.
    aux = lambda t: rm+eta*(-k*I(t)).exp()+mult*h(t)
    derivative = -k*eta*(-k*I(0,tau.hi)).exp()+mult*a/(a-k)*(-k*(-k*I(0,tau.hi)).exp()+a*(-a*I(0,tau.hi)).exp())
    lt('aux_initial_below_threshold', rm+eta, 1)
    lt('aux_root_early', aux(tau.lo), 1)
    lt('aux_root_late', 1, aux(tau.hi))
    lt('aux_root_strict', 0, derivative)
    lt('aux_cycle_after_raw_end', 1, I(finish.lo))
    W = (3*I(cap.hi)+3*I(mult.hi)+1)*a+I('1.1')+I('4.5')*I(lm.hi)+I('2.4')*I(le.hi)
    lt('reserve_invariant', W, 500)
    save('aux_mark_end', mark); save('aux_error_start', error); save('aux_finish', finish)
    save('gain_after_four_doses', gain('0.3',4))
    # For u after MARK ends: integral of b from input to u is
    # (b_pre + 0.1)*u - J. This integrates the actual exponential MARK.
    J = mdose*tau+(mdose-I('0.4')*I('1.25').ln())/lm
    save('mark_integral_deficit', J)

    class Cell:
        def __init__(self, name, base, count, b, birth, qex):
            self.name, self.base, self.count, self.b = name, base, count, b
            self.reference, self.qex = Time(birth), qex
            self.previous = self.fast = self.returned = None
            self.emissions, self.marks = [], 0
            self.last_case = None
        def pulse(self, arrival, label):
            prefix = self.name+'.'+label
            t = arrival.interval()
            if self.previous is not None:
                gap = (arrival-self.previous).interval()
                lt(prefix+'.aux_separation', I(finish.hi), gap)
            self.previous = arrival
            g = gain(self.base, self.count)
            lt(prefix+'.gain_below_cap', g, I(cap.lo))
            ready = self.returned is None or (arrival-self.returned).interval().lo > 0
            if ready:
                if self.returned is not None:
                    lt(prefix+'.ready_at_input', 0, (arrival-self.returned).interval())
                elapsed = (arrival-self.reference).interval()
                require(elapsed.lo >= 0, prefix+'.negative elapsed')
                qex = I(0) if self.qex.lo == self.qex.hi == 0 else self.qex*(-k*elapsed).exp()
                fixed = lambda u: r+qex*(-k*I(u)).exp()+g*h(u)
                coefficient = k*(qex+g*a/(a-k))
                lt(prefix+'.positive_derivative_coefficient', 0, coefficient)
                lt(prefix+'.fixed_flow_increases', 0, g*a*a/(a-k)-coefficient*(a-k).exp())
                jump = g*(dose.exp()-1)
                overlap = I(0, max(0, (1-I(error.lo)).hi))
                peak = fixed(1)+jump*a*(-a*I(error.lo)).exp()*overlap
                if peak.hi < 1:
                    lt(prefix+'.weak_no_firing', peak, 1)
                    lt(prefix+'.weak_end_above_rest', r, fixed(1))
                    self.count += 1
                    self.qex, self.reference = I(0, (peak-r).hi), arrival+1
                    self.returned = arrival+1
                    kind, emission = 'weak_full_ERROR', None
                else:
                    lt(prefix+'.strong_crosses_by_one', 1, fixed(1))
                    witness=root_hints[prefix+'.root_latency']
                    require(isinstance(witness,list) and len(witness)==2 and all(isinstance(v,str) for v in witness),'invalid root witness')
                    lo,hi=map(Fraction,witness)
                    require(0<lo<hi<1,'root bracket outside raw pulse')
                    root=I(lo,hi)
                    save(prefix+'.root_latency', root)
                    lt(prefix+'.root_lower', fixed(root.lo), 1)
                    lt(prefix+'.root_upper', 1, fixed(root.hi))
                    lt(prefix+'.MARK_before_fire', I(mark.hi), I(root.lo))
                    lt(prefix+'.fire_before_ERROR', I(root.hi), I(error.lo))
                    lt(prefix+'.ERROR_protected', I(finish.hi), I(root.lo)+1+L/self.b)
                    key = self.name+'.rest_gain_'+str(self.count)
                    if qex.lo != 0 or qex.hi != 0: key = prefix+'.root'
                    emission = arrival+symbol(key, root)
                    self.fast, self.returned = emission+1, emission+1+L/self.b
                    self.qex, self.reference = I(0), self.returned
                    self.emissions.append(emission)
                    kind = 'strong_firing'
            else:
                require(self.last_case == 'strong_firing', prefix+'.SLOW must have constant b since FAST end')
                lt(prefix+'.input_in_SLOW', self.fast.interval(), t)
                lt(prefix+'.input_before_return', t, self.returned.interval())
                duration = (arrival-self.fast).interval()
                newb = self.b+mdose
                reopen = (L-self.b*duration+J)/newb
                lt(prefix+'.whole_MARK_protected', I(mark.hi), I(reopen.lo))
                lt(prefix+'.b_below_cap', newb, I('1.1'))
                if finish.hi < reopen.lo:
                    lt(prefix+'.whole_ERROR_protected', I(finish.hi), I(reopen.lo))
                    kind = 'protected_MARK_only'
                else:
                    lt(prefix+'.return_before_ERROR', I(reopen.hi), I(error.lo))
                    self.count += 1
                    kind = 'protected_MARK_then_full_ERROR'
                # q=r at the physical SLOW return. Integrate only the raw tail
                # remaining afterwards; bound any ERROR/raw overlap separately.
                u = min(1, reopen.lo)
                tail = I(0) if reopen.lo >= 1 else g*a/(a-k)*((-k).exp()*(-(a-k)*I(u)).exp()-(-a).exp())
                overlap = I(0, max(0, (1-I(error.lo)).hi))
                extra = I(0) if kind == 'protected_MARK_only' else (gain(self.base,self.count)-g)*a*(-a*I(error.lo)).exp()*overlap
                tail_upper = max(0, (tail+extra).hi)
                lt(prefix+'.no_firing_from_raw_tail', r+tail_upper, 1)
                self.qex, self.reference = I(0,tail_upper), arrival+1
                self.b, self.marks = newb, self.marks+1
                self.returned = arrival+symbol(prefix+'.reopen', reopen)
                emission = None
                save(prefix+'.reopen', reopen)
            save(prefix+'.arrival', t); save(prefix+'.b_after', self.b)
            save(prefix+'.gain_after', gain(self.base,self.count))
            if emission is not None: save(prefix+'.emission', emission.interval())
            self.last_case = kind
            trace.append(dict(pulse=prefix,case=kind,gain_doses=self.count,protected_marks=self.marks))
            return emission

    # Previous composed theorem supplies these exact dose counts and b family.
    b1 = I('0.07999','0.08001')+mdose
    A = Cell('A','0.3',3,b1,'459.9',I(0))
    B = Cell('B','0.3',3,b1,'459.9',I(0))
    Cteach = Cell('Cteach','1.2',0,I('0.07999','0.08001'),480,eta)
    Bbefore = len(B.emissions)
    for n,source in enumerate(range(480,601,8)):
        fire = B.pulse(Time(source),'teach_'+str(n))
        require(fire is not None, 'B teaching emission missing')
        delivery = fire+symbol('teach_wire_'+str(n),I('0.3','0.4'))
        Cteach.pulse(delivery,'teach_'+str(n))
    require(Cteach.count==1 and Cteach.marks==1, 'C entry pattern changed')
    for cell in [B,Cteach]:
        lt(cell.name+'.quiescent_before_fast_cut', cell.returned.interval(), I('639.9'))
    lt('all_B_teaching_emissions_in_gate', B.emissions[-1].interval(), 630)
    C = Cell('C','0.3',0,Cteach.b,'639.9',I(0))
    fast_counts = {x.name:len(x.emissions) for x in [A,B,C]}
    for n,source in enumerate(range(640,737,4)):
        cfire = C.pulse(Time(source),'fast_'+str(n))
        if cfire is None: continue
        bfire = B.pulse(cfire+symbol('CB_wire_'+str(n),I('0.3','0.4')),'fast_'+str(n))
        if bfire is None: continue
        A.pulse(bfire+symbol('BA_wire_'+str(n),I('0.3','0.4')),'fast_'+str(n))
    for cell in [A,B,C]:
        lt(cell.name+'.quiescent_at_measurement', cell.returned.interval(), I('789.9'))
        lt(cell.name+'.last_emission_inside_fast_gate', cell.emissions[-1].interval(), 780)
        require(cell.marks == 2, cell.name+' MARK pattern changed')
        require(cell.count==4, cell.name+' gain pattern changed')
        save(cell.name+'.final_b', cell.b)
        save(cell.name+'.final_gain', gain(cell.base,cell.count))
        lt(cell.name+'.final_gain_below_cap', gain(cell.base,cell.count), I(cap.lo))
    # Retained probes run on independent standardized-rest copies with all
    # learning disabled; they never reset or otherwise intervene on live cells.
    for label,count,b,lo,hi in [('before',3,b1,'0.65','0.66'),('after',4,b1+2*mdose,'0.24','0.25')]:
        g = gain('0.3',count)
        fixed = lambda t: r+g*h(t)
        lt('probe.'+label+'.root_lower', fixed(lo), 1)
        lt('probe.'+label+'.root_upper', 1, fixed(hi))
        lt('probe.'+label+'.flow_increases', 0, g*a*a/(a-k)-k*g*a/(a-k)*(a-k).exp())
        returned = I(lo,hi)+1+L/b
        save('probe.'+label+'.return', returned)
        if label=='before':
            lt('probe.before.second_pulse_fully_protected', 5, I(returned.lo))
            lt('probe.before.return_before_third_pulse', I(returned.hi), 8)
        else:
            lt('probe.after.return_before_every_next_pulse', I(returned.hi), 4)
    weak_g = gain('0.3',0)
    weak_carry = weak_g*h(1)*(-k*3).exp()/(1-(-k*4).exp())
    lt('probe.C_before.positive_coefficient', 0, k*weak_g*a/(a-k))
    lt('probe.C_before.flow_increases', 0, weak_g*a*a/(a-k)-k*(weak_carry+weak_g*a/(a-k))*(a-k).exp())
    lt('probe.C_before.no_firing_even_in_infinite_train', r+weak_carry*(-k).exp()+weak_g*h(1), 1)
    summary = dict(teaching_emissions=dict(B=fast_counts['B']-Bbefore,C=len(Cteach.emissions)),
        fast_emissions={cell.name:len(cell.emissions)-fast_counts[cell.name] for cell in [A,B,C]},
        final_gain_doses={cell.name:cell.count for cell in [A,B,C]},
        added_fast_MARK_doses={cell.name:cell.marks for cell in [A,B,C]})
    require(summary['teaching_emissions']==dict(B=16,C=14), 'teaching counts changed')
    require(summary['fast_emissions']==dict(A=16,B=18,C=20), 'cascade counts changed')
    return bounds, obligations, trace, summary

def contract(epsilon):
    return dict(status='CERTIFIED_PULSES_ONLY_CADENCE_CASCADE',epsilon_relative=epsilon,
        scope='Original pulses-only READY birth-family prototype through 789.9; C-to-B-to-A cascade before open recurrence',
        physical_family='45 original per-port C,Lm,Ls,Le,M parameters independently in the fixed relative box; all other R constants unchanged',
        birth_family=dict(A_birth='0',B_birth='160',C_birth='480',
            modes='main and all auxiliaries READY',q=['0.09999','0.10001'],m_each=['0.02499','0.02501'],
            log_gains='ln(0.3,1.2,0.3) + independent [-1e-5,1e-5]',b=['0.07999','0.08001'],E=['50','100'],currents='none'),
        protocol=dict(configuration='impulsions / pulses only',prefix='Pinned birth-to-feedback theorem through 459.9',
            B_port2_sources='480,488,...,600',B_to_C='port 1, firing gate [480,630)',
            C_port0_sources='640,644,...,736',C_to_B='port 2, firing gate [640,780)',
            B_to_A='port 2, firing gate [640,780)',wire_delays=['0.3','0.4'],
            settings_copies='none',fast_before_cut='639.9',measurement='789.9',other_inputs='none besides the listed sources and routes in (459.9,789.9]'),
        conclusion=dict(teaching_emissions=dict(B=16,C=14),fast_emissions=dict(C=20,B=18,A=16),
            extra_full_MARK_doses=dict(A=2,B=2,C=2),recovery_identity='b_after = b_birth + 0.3 = b_before_fast + 0.2 in all three cells',
            final_recovery=['0.37999','0.38001'],gain_identity='active gain = own birth gain * exp(2.4): A port 2, B port 2, C port 0',
            final_modes='all READY, no raw or outgoing currents; main q exactly 0.1',
            live_state_resets='none',probe=dict(kind='independent standardized-rest copies; plasticity disabled; peers disconnected',
                pulses='eight canonical pulses at 0,4,...,28 on A/B port 2 and C port 0',
                before=dict(A='4/8',B='4/8',C='0/8'),after=dict(A='8/8',B='8/8',C='8/8')),
            ablations='Cut C->B during [640,780): neither parent receives input or changes b/g. Cut B->A: A receives no input or changes b/g. A retains 4/8 in either cut.'),
        arithmetic='Outward Decimal intervals at 128 digits; separate integer fixed-point replay of inequalities, pulse cases and contract; written hybrid induction, no full Lean formalization')

def verify(path,args):
    if not __debug__: raise Refusal('optimized execution is forbidden')
    document=json.loads(path.read_text())
    epsilon=document['epsilon_relative']
    require(isinstance(epsilon,str),'epsilon must be an exact string')
    identity=replay(epsilon,args)
    expected=contract(epsilon)
    require(set(document)==set(expected)|{'prefix_theorem','summary','pulse_trace','bounds','obligations','source_sha256'},'certificate field set changed')
    for key,value in expected.items(): require(document[key]==value,'statement changed: '+key)
    require(document['prefix_theorem']==identity,'prefix identity changed')
    required={'certify.py','verify.py','tests.py','dependency.py','decimal_intervals.py','integer_intervals.py'}
    require(set(document['source_sha256'])==required,'source set changed')
    for name,want in document['source_sha256'].items():
        require(hashlib.sha256((HERE/name).read_bytes()).hexdigest()==want,'source changed: '+name)
    bounds,obligations,trace,summary=derive(epsilon,document['bounds'])
    require(document['summary']==summary,'summary changed')
    require(document['pulse_trace']==trace,'pulse cases changed')
    require(document['obligations']==obligations,'obligation list changed')
    require(set(document['bounds'])==set(bounds),'enclosure set changed')
    for name,value in bounds.items():
        enclosure=document['bounds'][name]
        require(isinstance(enclosure,list) and len(enclosure)==2 and all(isinstance(v,str) for v in enclosure),'invalid enclosure')
        low,high=map(Fraction,enclosure)
        require(low<=value.lo<=value.hi<=high,'integer replay outside published bound: '+name)
    for ob in obligations:
        left=Fraction(document['bounds'][ob['left']][1]);right=Fraction(document['bounds'][ob['right']][0])
        require(left<right,'published inequality fails: '+ob['name'])
    result=dict(status='VERIFIED_CADENCE_CASCADE_WITH_INTEGER_ARITHMETIC',epsilon=epsilon,
        strict_obligations=len(obligations),enclosures=len(bounds),pulse_cases=len(trace),summary=summary,
        certificate_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),prefix_certificate_sha256=identity['certificate_sha256'],
        scope='Pulses-only birth-family prefix through 789.9; no settings copies or open recurrence',
        prefix_replayed=True)
    print(json.dumps(result),flush=True)
    return result

if __name__=='__main__':
    parser=argparse.ArgumentParser();arguments(parser)
    parser.add_argument('certificate',type=Path);parser.add_argument('--out',type=Path)
    args=parser.parse_args()
    try:
        result=verify(args.certificate,args)
        if args.out: args.out.write_text(json.dumps(result,indent=2)+'\n')
    except Exception as exc: print('REFUSED:',str(exc),file=sys.stderr);sys.exit(1)
