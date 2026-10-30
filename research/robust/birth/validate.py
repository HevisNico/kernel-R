"""End-to-end numerical validation from birth, without state resets at preparation."""
from pathlib import Path
import argparse,copy,gzip,hashlib,json,sys,time
from fractions import Fraction as F
ROOT=Path(__file__).resolve().parents[1];HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT))
from birth.simulator import run_chain,SCENARIOS
from birth.verify import verify
from validate import audit,check,interval,environment,source_manifest
from periodic.validate import packet_audit


def path(e,n,a):return HERE/f'certificates/eps{e}_nu{n}_alpha{a}.json'


def sources():
    d={'../'+k:v for k,v in source_manifest().items()}
    for p in sorted(list(HERE.glob('*.py'))+list(HERE.glob('*.md'))+list((HERE/'certificates').glob('*.json'))):
        d[str(p.relative_to(HERE))]=hashlib.sha256(p.read_bytes()).hexdigest()
    d['../periodic/validate.py']=hashlib.sha256((ROOT/'periodic/validate.py').read_bytes()).hexdigest()
    return d


def audit_birth(result,cert,probes=True,solver=None):
    b=cert['bounds'];rows=[];chain=copy.deepcopy(result)
    def bound(x,name,reason):interval(x,*map(float,b[name]),reason)
    for i,node in enumerate(result['nodes']):
        prefix=f'birth cell {i}: ';entry=node['snapshots']['159.9'];s=entry['state'];y=node['initial']
        check(entry['main']==0 and entry['aux']==[0,0,0] and not any(entry['raw']),prefix+'entry modes')
        bound(s[0],'entry_q',prefix+'entry q')
        for m in s[1:4]:bound(m,'entry_m',prefix+'entry m')
        bound(s[7],'entry_recovery',prefix+'entry recovery')
        interval(s[8],50,100,prefix+'entry reserve')
        check(s[6]==y[6] and s[5]==y[5],prefix+'unused birth memories changed')
        warm=[x for x in node['inputs'] if x['port']==0];wo=[x for x in node['outputs'] if x<160]
        check(len(warm)==16 and len(wo)==12,prefix+'warmup counts')
        check([x['main'] for x in warm]==[0,0,0,0,2]+[0]*11,prefix+'warmup gate word')
        for t,j in zip(wo,[3]+list(range(5,16))):interval(t-8*j,.5,.9,prefix+'warmup firing latency')
        errors=[x for x in node['errors'] if x['port']==0]
        marks=[x for x in node['marks'] if x['port']==0]
        check(len(errors)==16 and len(marks)==16,prefix+'warmup auxiliary cycles')
        for j,e in enumerate(errors):
            if j<3:
                bound(e['dose'],'local.gain_log_dose',prefix+'warmup ERROR')
                interval(e['dose'],e['physical_dose'],e['physical_dose'],prefix+'ERROR identity')
            else:interval(e['dose'],0,0,prefix+'extra ERROR dose')
        for j,m in enumerate(marks):
            if j==4:
                bound(m['dose'],'protected_MARK_dose',prefix+'protected MARK')
                interval(m['dose'],m['physical_dose'],m['physical_dose'],prefix+'MARK identity')
            else:interval(m['dose'],0,0,prefix+'extra MARK dose')
        interval(s[7]-y[7],marks[4]['dose'],marks[4]['dose'],prefix+'recovery accounting')
        interval(s[4]-y[4],sum(e['dose'] for e in errors[:3]),sum(e['dose'] for e in errors[:3]),prefix+'gain accounting')
        interval(node['state'][4],s[4],s[4],prefix+'warmup gain changed in chain')
        check(node['state'][5]==y[5],prefix+'unused port1 changed')
        rows.append(dict(cell=i,entry_q=s[0],entry_m=s[1:4],entry_b=s[7],birth_b=y[7],
                         protected_MARK_dose=marks[4]['dose'],warmup_ERROR_doses=[e['dose'] for e in errors[:3]],
                         warmup_outputs=len(wo)))
        # A view for auditing only: the simulator above ran one continuous history.
        c=chain['nodes'][i];c['initial']=s;c['raw']=any(c['raw'])
        c['inputs']=[dict(x,time=x['time']-160) for x in c['inputs'] if x['port']==2]
        c['outputs']=[t-160 for t in c['outputs'] if t>=160]
        c['errors']=[dict(x,start=x['start']-160,end=x['end']-160) for x in c['errors'] if x['port']==2]
        c['transitions']=[dict(x,time=x['time']-160) for x in c['transitions'] if x['time']>=160]
    local={'bounds':{k[6:]:v for k,v in b.items() if k.startswith('local.')}}
    n,k=result['n'],result['k']
    expected=dict(nodes=[dict(emissions=k-3*(i+1)) for i in range(n)],total_emissions=n*k-3*n*(n+1)//2,
                  all_ready_by=str(F(str(result['period']))*(k-1)+F(13*(n-1),10)+F(b['local.main_reopen_bound'][1])))
    summary=audit(chain,local,expected,probes=probes,solver=solver)
    if result['nu']==result['alpha']==0 and result['wire']=='fixed':
        summary['packets']=packet_audit(chain,[F(0)]*(n-1))
    return dict(entry=rows,continuation=summary),chain


def run():
    start=time.monotonic();out=HERE/'evidence';out.mkdir(exist_ok=True)
    points=[(e,n,a) for e in ('0.003','0.1') for n,a in (('0','0'),('0.002','0'),('0','0.09'),('0.0015','0.05'))]
    cases=[(2,16,*p,h,'alternating') for p in points for h in SCENARIOS]
    cases += [(n,3*n+8,'0.1','0.0015','0.05',('switching' if n==8 else 'oscillatory'),'alternating') for n in (4,8,16,32)]
    cases += [(n,3*n+8,'0.1','0','0','oscillatory','fixed') for n in (4,16,32)]
    reports=[];refinements=[]
    with gzip.open(out/'traces.jsonl.gz','wt') as trace:
        for idx,(n,k,eps,nu,alpha,scenario,wire) in enumerate(cases):
            cp=path(eps,nu,alpha);verify(cp,emit=False);cert=json.loads(cp.read_text())
            period=F(15,2) if wire=='fixed' else max(F(8),F(15,2)+F(n-1,2))
            r=run_chain(n,k,period,float(eps),float(nu),float(alpha),scenario,47,wire)
            summary,view=audit_birth(r,cert)
            key=dict(N=n,K=k,epsilon=eps,nu=nu,alpha=alpha,scenario=scenario,wire=wire,period=str(period),seed=47)
            reports.append(dict(**key,**summary));trace.write(json.dumps(dict(case=key,result=r))+'\n')
            print(json.dumps(dict(case=idx+1,total=len(cases),**key,status='PASS')),flush=True)
            if n==2 and scenario=='oscillatory':
                options=dict(rtol=1e-12,atol=1e-14,max_step=.08)
                tight=run_chain(n,k,period,float(eps),float(nu),float(alpha),scenario,47,wire,**options)
                audit_birth(tight,cert,solver=options)
                dt=max(abs(x-y) for a,b in zip(r['nodes'],tight['nodes']) for x,y in zip(a['outputs'],b['outputs']))
                db=max(abs(a['snapshots']['159.9']['state'][7]-b['snapshots']['159.9']['state'][7]) for a,b in zip(r['nodes'],tight['nodes']))
                check(dt<1e-7 and db<1e-8,'birth tolerance refinement failed')
                refinements.append(dict(**key,max_output_time_change=dt,max_entry_b_change=db))
                trace.write(json.dumps(dict(case=key,refined=True,result=tight))+'\n')
    report=dict(status='PASS_BIRTH_TO_CHAIN_NUMERICAL_VALIDATION',environment=environment(),source_sha256=sources(),
                trace_sha256=hashlib.sha256((out/'traces.jsonl.gz').read_bytes()).hexdigest(),cases=reports,refinement=refinements,
                elapsed_seconds=time.monotonic()-start,cells_tested=sum(x['N'] for x in reports),
                warmup_outputs=sum(12*x['N'] for x in reports),
                chain_outputs=sum(c['outputs'] for x in reports for c in x['continuation']['nodes']),
                numerical_tolerance=3e-8,scope='specified READY birth family, external parallel warm-up, no reset; numerical evidence, not Lean')
    (out/'validation.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('source_sha256','cases','refinement')}))


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--verify-record',action='store_true');a=p.parse_args()
    if a.verify_record:
        r=json.loads((HERE/'evidence/validation.json').read_text());check(r['source_sha256']==sources(),'source mismatch')
        check(r['environment']==environment(),'runtime mismatch')
        check(r['trace_sha256']==hashlib.sha256((HERE/'evidence/traces.jsonl.gz').read_bytes()).hexdigest(),'trace mismatch')
        print('PASS: birth record source/runtime/trace correspondence (not a rerun)')
    else:run()
