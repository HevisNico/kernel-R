"""Reproducible hybrid validation; numerical tests do not replace the theorem."""
import argparse, gzip, hashlib, json, math, platform, sys, time
from pathlib import Path
from fractions import Fraction
import numpy as np
import scipy
from chain import contract, schedule
from simulate_events import History, SCENARIOS, initial_state, run_chain, simulate
from verify import verify
HERE=Path(__file__).resolve().parent
TOL=3e-8


def check(condition,message):
    if not condition: raise AssertionError(message)


def interval(x,lo,hi,message,tol=TOL):
    check(lo-tol<=x<=hi+tol,f'{message}: {x} not in [{lo},{hi}] within tolerance {tol}')


def audit(result,cert,expected,probes=True,solver=None):
    solver={} if solver is None else solver
    b=cert['bounds']; dose_lo,dose_hi=map(float,b['gain_log_dose'])
    finish_hi=float(b['aux_finish'][1]); reopen=float(b['main_reopen_bound'][1])
    summaries=[]; max_identity=0.; max_dose_outside=0.
    for i,node in enumerate(result['nodes']):
        inputs=node['inputs']; outs=node['outputs']; initial=node['initial']; final=node['state']
        prefix=f'cell {i}: '
        check(len(inputs)==result['k']-3*i,prefix+'input count')
        check(len(outs)==expected['nodes'][i]['emissions'],prefix+'output count')
        check(node['main']==0 and node['aux']==[0,0,0] and not node['raw'],prefix+'terminal modes')
        for x in inputs:
            check(x['main']==0 and x['aux']==[0,0,0],prefix+'input before recovery')
            interval(x['q']-.1,-1e-5-2*result['nu'],.03,prefix+'input section')
            for m in x['m']: interval(m-.025,-1e-5-2*result['nu'],1e-5+2*result['nu'],prefix+'aux rest')
        gaps=[y['time']-x['time'] for x,y in zip(inputs,inputs[1:])]
        check(min(gaps)>=7.5-TOL,prefix+'input gap')
        latencies=[t-x['time'] for t,x in zip(outs,inputs[3:])]
        for latency in latencies: interval(latency,.5,.9,prefix+'firing latency')
        for k,t in enumerate(outs):
            ideal=result['period']*(k+3*(i+1))
            interval(t,ideal+.8*i+.5,ideal+1.3*i+.9,prefix+'source/output correspondence')
        errors=[x for x in node['errors'] if x['port']==2]
        check(len(errors)==len(inputs),prefix+'aux cycle count')
        doses=[x['dose'] for x in errors]
        for j,(e,inp) in enumerate(zip(errors,inputs)):
            check(e['end']-inp['time']<=finish_hi+TOL,prefix+'aux finish bound')
            if j<3:
                interval(e['dose'],dose_lo,dose_hi,prefix+'full dose')
                residual=abs(e['dose']-e['physical_dose'])
                check(residual<=TOL,prefix+'continuous dose identity')
                max_identity=max(max_identity,residual)
                max_dose_outside=max(max_dose_outside,dose_lo-e['dose'],e['dose']-dose_hi)
            else: interval(e['dose'],0,0,prefix+'protected ERROR dose')
        check(errors[2]['end']<outs[0],prefix+'learning before first emission')
        for e,t in zip(errors[3:],outs):
            check(t<e['start'],prefix+'ERROR before fire')
        interval(final[6]-initial[6],sum(doses),sum(doses),prefix+'gain accounting')
        interval(final[7],initial[7],initial[7],prefix+'unchanged recovery')
        for idx in range(4): interval(node['extrema_min'][idx],0,1,prefix+'minimum charge')
        for idx in range(4): interval(node['extrema_max'][idx],0,1,prefix+'maximum charge')
        interval(node['extrema_min'][8],50,100,prefix+'sampled reserve minimum')
        interval(node['extrema_max'][8],50,100,prefix+'sampled reserve maximum')
        check(math.exp(node['extrema_max'][6])<4*(1-result['epsilon']),prefix+'active gain touches cap')
        returns=[x['time'] for x in node['transitions'] if x['coordinate']=='q' and x['new']==0]
        check(len(returns)==len(outs),prefix+'main cycle count')
        for t,x in zip(returns,inputs[3:]): check(t-x['time']<=reopen+TOL,prefix+'main reopen bound')
        ready=max([x['time'] for x in node['transitions']]+[outs[-1]+1,inputs[-1]['time']+1])
        check(ready<=float(Fraction(expected['all_ready_by']))+TOL,prefix+'chain terminal calendar')
        probe_counts=None
        if probes:
            probe_counts=[]
            for gains,expected_count in ((initial[4:7],0),(final[4:7],8)):
                st=initial_state(0,gain=gains,recovery=final[7])
                h=History(result['epsilon'],result['nu'],result['alpha'],result['scenario'],result['seed'],i)
                p=simulate([20*j for j in range(8)],h,state=st,plastic=False,**solver)
                check(len(p['outputs'])==expected_count,prefix+'retained probe count')
                check(p['state'][4:8]==p['initial'][4:8],prefix+'plasticity disabled')
                check(p['main']==0 and p['aux']==[0,0,0],prefix+'probe recovery')
                for j,t in enumerate(p['outputs']): interval(t-20*j,.5,.9,prefix+'probe latency')
                probe_counts.append(len(p['outputs']))
        summaries.append(dict(cell=i,inputs=len(inputs),outputs=len(outs),minimum_input_gap=min(gaps),
                              latency_range=[min(latencies),max(latencies)],doses=doses[:3],
                              max_later_dose=max(map(abs,doses[3:]),default=0.),probe_counts=probe_counts,
                              reserve_sample_range=[node['extrema_min'][8],node['extrema_max'][8]],
                              ready_by=ready,nfev=node['nfev']))
    check(sum(x['outputs'] for x in summaries)==expected['total_emissions'],'total traffic')
    return dict(nodes=summaries,max_dose_identity_residual=max_identity,
                max_distance_outside_certified_dose=max(0.,max_dose_outside))


def certificate_path(eps,nu,alpha):
    return HERE/f'results/eps{eps}/nu{nu}_alpha{alpha}.json'


def source_manifest():
    files=list(HERE.glob('*.py'))+list(HERE.glob('*.md'))+list(HERE.glob('requirements*.txt'))
    files+=list((HERE/'results').glob('*/*.json'))
    return {str(p.relative_to(HERE)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(files)}


def environment():
    return dict(python=platform.python_version(),numpy=np.__version__,scipy=scipy.__version__)


def run(quick=False):
    start=time.monotonic(); out=HERE/'evidence'; out.mkdir(exist_ok=True)
    points=[(e,n,a) for e in ('0.003','0.1') for n,a in (('0','0'),('0.002','0'),('0','0.09'),('0.0015','0.05'))]
    for p in points: verify(certificate_path(*p),emit=False)
    cases=[(2,16,*p,h,7) for p in points for h in SCENARIOS]
    cases += [(n,3*n+8,'0.1',nu,alpha,h,23) for n in (1,3,4,8,16)
              for nu,alpha in (('0.002','0'),('0.0015','0.05')) for h in ('slow_positive','switching')]
    cases += [(32,104,'0.1','0.0015','0.05','oscillatory',101)]
    if quick: cases=[cases[5],cases[-1]]; cases[-1]=(4,20,'0.1','0.0015','0.05','switching',101)
    reports=[]; refinement=[]
    with gzip.open(out/'traces.jsonl.gz','wt') as traces:
        for ordinal,(n,k,eps,nu,alpha,scenario,seed) in enumerate(cases):
            path=certificate_path(eps,nu,alpha); cert=json.loads(path.read_text()); p=schedule(n,k)
            expected=contract(path,n,k,str(p))
            result=run_chain(n,k,p,float(eps),float(nu),float(alpha),scenario,seed)
            summary=audit(result,cert,expected)
            key=dict(N=n,K=k,epsilon=eps,nu=nu,alpha=alpha,scenario=scenario,seed=seed,period=str(p))
            reports.append(dict(**key,**summary))
            traces.write(json.dumps(dict(case=key,result=result))+'\n')
            print(json.dumps(dict(case=ordinal+1,total=len(cases),**key,status='PASS')),flush=True)
            # Refine every local point with oscillatory histories, plus a discontinuous chain.
            if (n==2 and scenario=='oscillatory') or (n==4 and scenario=='switching') or quick:
                opts=dict(rtol=1e-12,atol=1e-14,max_step=.08)
                tight=run_chain(n,k,p,float(eps),float(nu),float(alpha),scenario,seed,**opts)
                audit(tight,cert,expected,solver=opts)
                time_error=max(abs(x-y) for a,b in zip(result['nodes'],tight['nodes']) for x,y in zip(a['outputs'],b['outputs']))
                dose_error=max(abs(x['dose']-y['dose']) for a,b in zip(result['nodes'],tight['nodes']) for x,y in zip(a['errors'],b['errors']))
                check(time_error<1e-7 and dose_error<1e-8,'tolerance refinement failed')
                refinement.append(dict(**key,max_output_time_change=time_error,max_dose_change=dose_error))
                traces.write(json.dumps(dict(case=key,refined=True,result=tight))+'\n')
    report=dict(status='PASS_NUMERICAL_VALIDATION_NOT_A_FORMAL_PROOF',quick=quick,
                environment=environment(),source_sha256=source_manifest(),
                numerical_acceptance_tolerance=TOL,solver=dict(method='DOP853',rtol=1e-9,atol=1e-11,max_step=.25),
                trace_sha256=hashlib.sha256((out/'traces.jsonl.gz').read_bytes()).hexdigest(),
                elapsed_seconds=time.monotonic()-start,cases=reports,refinement=refinement,
                certificate_points=8,inequalities_per_point=36,
                cells_tested=sum(len(r['nodes']) for r in reports),
                outputs_tested=sum(c['outputs'] for r in reports for c in r['nodes']))
    (out/'validation.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('cases','refinement','source_sha256')}))


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--quick',action='store_true');parser.add_argument('--verify-record',action='store_true')
    args=parser.parse_args()
    if args.verify_record:
        r=json.loads((HERE/'evidence/validation.json').read_text())
        check(r['source_sha256']==source_manifest(),'source manifest mismatch')
        check(r['environment']==environment(),'runtime versions differ')
        check(r['trace_sha256']==hashlib.sha256((HERE/'evidence/traces.jsonl.gz').read_bytes()).hexdigest(),'trace mismatch')
        print('PASS: record source, runtime and trace hashes match (not a rerun)')
    else: run(args.quick)
