"""Numerical tests of constant-latency packet closure. No universal claim from sampling."""
from pathlib import Path
import argparse,gzip,hashlib,json,sys,time
from fractions import Fraction as F
import numpy as np
ROOT=Path(__file__).resolve().parents[1]; HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT))
from simulate_events import History,initial_state,simulate
from validate import audit,check,environment,source_manifest,interval
from periodic.certify_chain import contract


def sources():
    result={'../'+k:v for k,v in source_manifest().items()}
    result.update({str(p.relative_to(HERE)):hashlib.sha256(p.read_bytes()).hexdigest()
                   for p in sorted(list(HERE.glob('*.py'))+list(HERE.glob('*.md')))})
    return result


def simulate_chain(n,k,period,eps,scenario,seed,sigmas,**solver):
    arrivals=[float(period)*j for j in range(k)]; nodes=[]
    for i in range(n):
        node=simulate(arrivals,History(eps,0,0,scenario,seed,i),
                      state=initial_state((-1,0,1)[(seed+i)%3]),**solver)
        nodes.append(node)
        if i<n-1:
            # Same source-ordinal parity along the full path realizes aligned
            # +/- accumulated jitter, not accidental cancellation at each link.
            arrivals=[t+.35+float(sigmas[i])*(1 if (j+3*(i+1)+seed)%2 else -1)
                      for j,t in enumerate(node['outputs'])]
    return dict(n=n,k=k,period=float(period),epsilon=eps,nu=0.,alpha=0.,
                scenario=scenario,seed=seed,nodes=nodes)


def packet_audit(result,sigmas):
    summed_latency=0.; jitter=0.; reports=[]
    for i,node in enumerate(result['nodes']):
        latency=[t-x['time'] for t,x in zip(node['outputs'],node['inputs'][3:])]
        ell=float(np.median(latency[1:])); advance=ell-latency[0]
        check(advance>=-3e-8,'first output must advance rather than delay')
        check(node['inputs'][3]['q']>=.1-3e-8,'first emitting input has nonnegative residual')
        error=max(abs(t-ell) for t in latency[1:]); check(error<3e-8,'rest latency varies')
        summed_latency+=ell
        phase=[]
        for k,t in enumerate(node['outputs']):
            ideal=(k+3*(i+1))*result['period']+summed_latency+.35*i
            if k==0: ideal-=advance
            phase.append(t-ideal)
        check(max(map(abs,phase))<=jitter+3e-8,'packet phase envelope exceeded')
        gaps=[b-a for a,b in zip(node['outputs'],node['outputs'][1:])]
        check(min(gaps)>=result['period']-2*jitter-3e-8,'packet minimum gap')
        tail_error=max(abs(g-result['period']) for g in gaps[1:])
        if jitter==0: check(tail_error<3e-8,'fixed-wire periodic tail changed period')
        reports.append(dict(cell=i,rest_latency=ell,first_advance=advance,
                            max_rest_latency_change=error,jitter_budget=jitter,
                            max_phase_error=max(map(abs,phase)),minimum_output_gap=min(gaps),
                            fixed_wire_tail_gap_error=tail_error if jitter==0 else None))
        if i<len(sigmas): jitter+=float(sigmas[i])
    return reports


def run():
    start=time.monotonic(); out=HERE/'evidence';out.mkdir(exist_ok=True)
    cases=[(n,'0.1','oscillatory',F(15,2),[F(0)]*(n-1)) for n in (1,2,4,8,16,32)]
    cases += [(8,'0.1','switching',F(15,2),[F(0)]*7),
              (8,'0.1','switching',F(41,5),[F(1,20)]*7),
              (32,'0.1','oscillatory',F(8),[F(3,620)]*31),
              (16,'0.003','switching',F(15,2),[F(0)]*15)]
    reports=[]; refinements=[]
    with gzip.open(out/'traces.jsonl.gz','wt') as traces:
        for index,(n,eps,scenario,p,sigmas) in enumerate(cases):
            k=3*n+8; path=ROOT/f'results/eps{eps}/nu0_alpha0.json'
            expected=contract(path,n,k,str(p),list(map(str,sigmas)))
            cert=json.loads(path.read_text()); result=simulate_chain(n,k,p,float(eps),scenario,41,sigmas)
            summary=audit(result,cert,expected); packets=packet_audit(result,sigmas)
            key=dict(N=n,K=k,epsilon=eps,period=str(p),scenario=scenario,seed=41,sigma_each=list(map(str,sigmas)))
            reports.append(dict(**key,**summary,packets=packets))
            traces.write(json.dumps(dict(case=key,result=result))+'\n')
            print(json.dumps(dict(case=index+1,total=len(cases),N=n,period=str(p),jitter=str(sum(sigmas,F(0))),status='PASS')),flush=True)
            if n==8:
                options=dict(rtol=1e-12,atol=1e-14,max_step=.08)
                tight=simulate_chain(n,k,p,float(eps),scenario,41,sigmas,**options)
                audit(tight,cert,expected,solver=options); packet_audit(tight,sigmas)
                dt=max(abs(x-y) for a,b in zip(result['nodes'],tight['nodes']) for x,y in zip(a['outputs'],b['outputs']))
                check(dt<1e-7,'periodic-chain tolerance refinement failed')
                refinements.append(dict(**key,max_output_time_change=dt))
                traces.write(json.dumps(dict(case=key,refined=True,result=tight))+'\n')
    report=dict(status='PASS_NUMERICAL_PERIODIC_PACKET_VALIDATION',environment=environment(),
                source_sha256=sources(),trace_sha256=hashlib.sha256((out/'traces.jsonl.gz').read_bytes()).hexdigest(),
                acceptance_tolerance=3e-8,elapsed_seconds=time.monotonic()-start,cases=reports,refinement=refinements,
                cells_tested=sum(len(x['nodes']) for x in reports),
                outputs_tested=sum(c['outputs'] for x in reports for c in x['nodes']),
                scope='zero noise and identical waveforms; written proof for arbitrary N, simulations only for recorded histories')
    (out/'validation.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('source_sha256','cases','refinement')}))


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--verify-record',action='store_true');a=p.parse_args()
    if a.verify_record:
        r=json.loads((HERE/'evidence/validation.json').read_text())
        check(r['source_sha256']==sources(),'source mismatch')
        check(r['environment']==environment(),'runtime mismatch')
        check(r['trace_sha256']==hashlib.sha256((HERE/'evidence/traces.jsonl.gz').read_bytes()).hexdigest(),'trace mismatch')
        print('PASS: periodic record source, runtime and trace hashes match (not a rerun)')
    else: run()
