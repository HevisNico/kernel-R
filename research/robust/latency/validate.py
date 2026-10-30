"""End-to-end birth runs at the tighter noise-dependent periods."""
from pathlib import Path
from fractions import Fraction as F
import argparse,gzip,hashlib,json,math,sys,time
import numpy as np
from scipy.optimize import brentq
ROOT=Path(__file__).resolve().parents[1];HERE=Path(__file__).resolve().parent;sys.path.insert(0,str(ROOT))
from birth.simulator import History,initial_state,simulate,A,KAPPA
from birth.validate import audit_birth,sources as birth_sources
from validate import check,environment
from latency.chain import contract


def sources():
    d={'../birth/'+k:v for k,v in birth_sources().items()}
    for p in sorted(list(HERE.glob('*.py'))+list(HERE.glob('*.md'))+list((HERE/'certificates').glob('*.json'))):
        d[str(p.relative_to(HERE))]=hashlib.sha256(p.read_bytes()).hexdigest()
    return d


def run_chain(n,k,period,eps,nu,alpha,scenario,sigma,seed=73,**solver):
    arrivals=[160+float(period)*j for j in range(k)];nodes=[]
    for i in range(n):
        y=initial_state((-1,0,1)[(seed+i)%3])
        result=simulate([(8*j,0) for j in range(16)]+[(t,2) for t in arrivals],
                        History(eps,nu,alpha,scenario,seed,i),state=y,**solver)
        nodes.append(result)
        outputs=[t for t in result['outputs'] if t>=160]
        arrivals=[t+.35+float(sigma)*(1 if (j+3*(i+1)+seed)%2 else -1) for j,t in enumerate(outputs)]
    # audit_birth's noiseless packet check only applies to fixed wires.
    return dict(n=n,k=k,period=float(period),epsilon=eps,nu=nu,alpha=alpha,scenario=scenario,
                seed=seed,wire='fixed' if sigma==0 else 'budgeted',nodes=nodes)


def audit_latency(r,delta,sigma):
    accumulated_reference=0.;rows=[]
    h=lambda t:A/(A-KAPPA)*(math.exp(-KAPPA*t)-math.exp(-A*t))
    for i,node in enumerate(r['nodes']):
        inputs=[x['time'] for x in node['inputs'] if x['port']==2]
        outputs=[t for t in node['outputs'] if t>=160]
        g=math.exp(node['state'][6]);ref=brentq(lambda t:.1+g*h(t)-1,.5,.9,xtol=1e-14)
        latencies=[t-x for t,x in zip(outputs,inputs[3:])]
        regular=[x-ref for x in latencies[1:]];first_delay=max(0.,latencies[0]-ref)
        check(max(map(abs,regular))<=float(delta)+3e-8,'regular latency exceeds certified radius')
        check(first_delay<=float(delta)+3e-8,'first firing delay exceeds radius')
        advance=max(0.,ref-latencies[0]);accumulated_reference+=ref
        budget=float((i+1)*delta+i*sigma)
        phase=[]
        for j,t in enumerate(outputs):
            ideal=160+(j+3*(i+1))*r['period']+accumulated_reference+.35*i-(advance if j==0 else 0.)
            phase.append(t-ideal)
        check(max(map(abs,phase))<=budget+3e-8,'accumulated phase exceeds packet radius')
        incoming=float(i*(delta+sigma));mingap=min(b-a for a,b in zip(inputs,inputs[1:]))
        check(mingap>=r['period']-2*incoming-3e-8,'input gap exceeds phase-loss budget')
        rows.append(dict(cell=i,reference_latency=ref,regular_error_range=[min(regular),max(regular)],
                         max_absolute_regular_error=max(map(abs,regular)),first_delay=first_delay,
                         first_advance=advance,phase_radius=budget,max_phase_error=max(map(abs,phase)),minimum_input_gap=mingap))
    return rows


def run():
    out=HERE/'evidence';out.mkdir(exist_ok=True);start=time.monotonic()
    points=[(e,n,a) for e in ('0.003','0.1') for n,a in (('0','0'),('0.002','0'),('0','0.09'),('0.0015','0.05'))]
    cases=[(4,*p,'switching','0',None) for p in points]
    cases += [(8,'0.1','0.002','0','switching','.05',None),
              (16,'0.1','0.0015','0.05','oscillatory','0',None),
              (32,'0.1','0.002','0','oscillatory','0','8'),
              (32,'0.1','0.002','0','slow_positive','0','8')]
    reports=[];refinements=[]
    with gzip.open(out/'traces.jsonl.gz','wt') as trace:
        for index,(n,e,nu,alpha,h,sig,period) in enumerate(cases):
            k=3*n+8;p=HERE/f'certificates/eps{e}_nu{nu}_alpha{alpha}.json'
            c=contract(p,n,k,sig,period);t=F(c['period']);d=F(c['delta_each']);s=F(sig)
            birth=json.loads((ROOT/f'birth/certificates/eps{e}_nu{nu}_alpha{alpha}.json').read_text())
            result=run_chain(n,k,t,float(e),float(nu),float(alpha),h,s)
            summary,_=audit_birth(result,birth);latencies=audit_latency(result,d,s)
            key=dict(N=n,K=k,epsilon=e,nu=nu,alpha=alpha,scenario=h,sigma=sig,period=str(t),delta=str(d))
            reports.append(dict(**key,**summary,latencies=latencies))
            trace.write(json.dumps(dict(case=key,result=result))+'\n')
            print(json.dumps(dict(case=index+1,total=len(cases),**key,status='PASS')),flush=True)
            if n==4 and e=='0.1' and (nu,alpha) in (('0.002','0'),('0.0015','0.05')):
                opts=dict(rtol=1e-12,atol=1e-14,max_step=.08)
                tight=run_chain(n,k,t,float(e),float(nu),float(alpha),h,s,**opts)
                audit_birth(tight,birth,solver=opts);audit_latency(tight,d,s)
                dt=max(abs(x-y) for a,b in zip(result['nodes'],tight['nodes']) for x,y in zip(a['outputs'],b['outputs']))
                check(dt<1e-7,'latency campaign refinement failed');refinements.append(dict(**key,max_output_time_change=dt))
                trace.write(json.dumps(dict(case=key,refined=True,result=tight))+'\n')
    report=dict(status='PASS_NOISE_DEPENDENT_CHAIN_FROM_BIRTH',environment=environment(),source_sha256=sources(),
                trace_sha256=hashlib.sha256((out/'traces.jsonl.gz').read_bytes()).hexdigest(),cases=reports,refinement=refinements,
                elapsed_seconds=time.monotonic()-start,cells_tested=sum(x['N'] for x in reports),
                warmup_outputs=sum(12*x['N'] for x in reports),chain_outputs=sum(c['outputs'] for x in reports for c in x['continuation']['nodes']),
                scope='numerical evidence for recorded histories; universal statement is a written proof with interval replay')
    (out/'validation.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('source_sha256','cases','refinement')}))


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--verify-record',action='store_true');a=p.parse_args()
    if a.verify_record:
        r=json.loads((HERE/'evidence/validation.json').read_text());check(r['source_sha256']==sources(),'source mismatch')
        check(r['environment']==environment(),'runtime mismatch')
        check(r['trace_sha256']==hashlib.sha256((HERE/'evidence/traces.jsonl.gz').read_bytes()).hexdigest(),'trace mismatch')
        print('PASS: latency source/runtime/trace correspondence (not a rerun)')
    else:run()
