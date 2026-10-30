"""Causal contrasts, native dynamics, equal budgets and independent numerical checks."""
from pathlib import Path
import argparse,json,math,hashlib
import numpy as np
from run import PolicyBank,Device,NOMINAL,cell_sim,learner,diagnose,assay,read_policy,ACTIONS,LIBRARY,SLOT,FEEDBACK_OFFSET,HERE,ROOT
from ode_reference import simulate_ode


def validate(out):
    checks=[]
    def check(label,passed,**details):
        row=dict(test=label,passed=bool(passed),**details);checks.append(row);print(json.dumps(row),flush=True)
    plan=json.loads((out/'plan.json').read_text());training=json.loads((out/'training.json').read_text())
    policies=json.loads((out/'policies.json').read_text());evaluation=json.loads((out/'evaluation.json').read_text());report=json.loads((out/'summary.json').read_text())
    check('run source matches locked plan',hashlib.sha256((HERE/'run.py').read_bytes()).hexdigest()==plan['source_sha256'])
    check('feedback occurs after diagnostic, lesson and full student probe',FEEDBACK_OFFSET>30.+180.+80. and SLOT>FEEDBACK_OFFSET+24.)
    if (out/'pilot_plan.json').exists():
        check('confirmation test seed differs from the recorded pilot',plan['seeds']['test']!=json.loads((out/'pilot_plan.json').read_text())['seeds']['test'])
    check('complete policy factorial',len(policies)==plan['replicates']*4 and len({(p['replicate'],p['arm']) for p in policies})==len(policies))
    trainseeds={t['seed'] for r in training for t in r['trials']};testseeds={e['seed'] for e in evaluation}
    check('training and test learners disjoint',not trainseeds.intersection(testseeds))
    check('exactly the declared number of fresh test learners',len(evaluation)==2*plan['test_per_family'] and len(testseeds)==len(evaluation))
    check('complete fixed-curriculum evaluation matrix',all(set(e['curricula'])==set(LIBRARY) for e in evaluation))
    check('every curriculum has ten canonical pulses in a common deadline',all(len(t)==10 and t[-1]<=144 and all(b-a>1.38 for a,b in zip(t,t[1:])) for t in LIBRARY.values()))
    check('context comes from recorded observable response',all(t['context']==int(bool(t['diagnostic'])) for r in training for t in r['trials']) and all(e['context']==int(bool(e['diagnostic'])) for e in evaluation))
    check('both contexts occur in train and test',all({t['context'] for t in r['trials']}=={0,1} for r in training) and {e['context'] for e in evaluation}=={0,1})
    for rep in range(plan['replicates']):
        trials=training[rep]['trials'];byarm={p['arm']:p for p in policies if p['replicate']==rep}
        for arm,p in byarm.items():
            r=p['record'];cells=[c for s in r['samples'] for c in s['cells'][:2]]
            check(f'{rep}/{arm}: physical bounds and reserve',all(0<min(c['gains'])<=max(c['gains'])<=4+1e-7 and 0<c['b']<=1.1+1e-7 and 50<c['E']<=100+1e-7 for c in cells))
            check(f'{rep}/{arm}: live memory preserved without copies',all(c['alive'] for c in cells) and not r['copies'])
            check(f'{rep}/{arm}: two feedback-circuit pulses per trial',len(r['arrivals'])==2*len(trials))
            valid=True
            for k,t in enumerate(trials):
                arrivals=[a for a in r['arrivals'] if k*SLOT<=a['time']<(k+1)*SLOT]
                action=1-t['action'] if arm=='wrong_credit' else t['action']
                good=t['success'] and arm!='uninformative'
                expected=sorted([(k*SLOT+FEEDBACK_OFFSET+.35,action,'student_outcome'),(k*SLOT+FEEDBACK_OFFSET+(3.5 if good else 0),2,'outcome_guard')])
                got=sorted((a['time'],a['port'],a['source']) for a in arrivals)
                valid &= got==expected and all(a['node']==t['context'] for a in arrivals)
            check(f'{rep}/{arm}: feedback follows measured outcome and declared encoder',valid)
            monotone=all(all(a<=b+1e-7 for a,b in zip(x['gains']+[x['b']],y['gains']+[y['b']])) for i in range(2) for x,y in zip([s['cells'][i] for s in r['samples']],[s['cells'][i] for s in r['samples']][1:]))
            check(f'{rep}/{arm}: monotone native memory',monotone)
        actual=byarm['actual_credit']['record'];wrong=byarm['wrong_credit']['record']
        a=[(x['time'],x['node'],2 if x['port']==2 else 1-x['port']) for x in actual['arrivals']]
        b=[(x['time'],x['node'],x['port']) for x in wrong['arrivals']]
        check(f'{rep}: wrong-credit pulses have identical counts, times and contexts',a==b)
        sym_error=max(abs(x-y) for s,t in zip(actual['samples'],wrong['samples']) for c,d in zip(s['cells'][:2],t['cells'][:2]) for x,y in zip(c['gains'][:2],d['gains'][1::-1]))
        recovery_error=max(abs(c['b']-d['b']) for s,t in zip(actual['samples'],wrong['samples']) for c,d in zip(s['cells'][:2],t['cells'][:2]))
        check(f'{rep}: wrong credit swaps memory without global recovery advantage',sym_error<1e-6 and recovery_error<1e-6,max_gain_symmetry_error=sym_error,max_recovery_difference=recovery_error)
        for arm in ['frozen','uninformative']:
            gains=[c['gains'][:2] for c in byarm[arm]['record']['samples'][-1]['cells'][:2]]
            check(f'{rep}/{arm}: no action memory acquired',np.max(np.abs(np.array(gains)-.3))<1e-7)
        check(f'{rep}: inherited R settings retain the same policy',report['inherited'][rep]['readout']==byarm['actual_credit']['decisions'][-1]['readout'])
    # Independent event-driven implementation of each persistent policy cell.
    for arm in ['actual_credit','wrong_credit']:
        record=next(p['record'] for p in policies if p['replicate']==0 and p['arm']==arm)
        for node in [0,1]:
            arrivals=[[a['time'] for a in record['arrivals'] if a['node']==node and a['port']==j] for j in range(3)]
            d=Device(np.broadcast_to(NOMINAL,(3,5)).tolist(),.1,[.025]*3,np.log([.3,.3,4.]).tolist(),.08,[0]*3)
            independent=cell_sim(arrivals,d,record['samples'][-1]['time'])
            final=record['samples'][-1]['cells'][node]
            recorded=[o['time'] for o in record['outputs'] if o['node']==node]
            same=len(recorded)==len(independent['outputs'])
            error=max((abs(a-b) for a,b in zip(recorded,independent['outputs'])),default=0.) if same else 1e9
            pe=max([abs(a-b) for a,b in zip(final['gains'],independent['final_gain'])]+[abs(final['b']-independent['final_b'])])
            check(f'independent persistent R replay {arm}/{node}',same and error<2e-6 and pe<2e-6,max_event_error=error,max_parameter_error=pe)
    tight=PolicyBank(training[0]['trials'],'actual_credit',rtol=2e-11,atol=2e-13,max_step=.06).execute()
    reference=next(p['record'] for p in policies if p['replicate']==0 and p['arm']=='actual_credit')
    same=len(tight['outputs'])==len(reference['outputs'])
    err=max((abs(a['time']-b['time']) for a,b in zip(tight['outputs'],reference['outputs'])),default=0.) if same else 1e9
    check('tighter direct-ODE solver preserves policy firings',same and err<2e-6,max_event_error=err)
    check('tighter solver preserves decoded curriculum choices',[read_policy(c)['action'] for c in tight['samples'][-1]['cells'][:2]]==[x['action'] for x in next(p['decisions'][-1]['readout'] for p in policies if p['replicate']==0 and p['arm']=='actual_credit')])
    # Independent direct ODE for representative learner lessons from both families.
    for family in [0,1]:
        d,_=learner('test',0,family,0);ctx,prepared,_=diagnose(d)
        for name in ACTIONS:
            direct=simulate_ode([[],LIBRARY[name],[]],prepared,180.)
            event=cell_sim([[],LIBRARY[name],[]],prepared,180.)
            same=len(direct['outputs'])==len(event['outputs'])
            err=max((abs(a-b) for a,b in zip(direct['outputs'],event['outputs'])),default=0.) if same else 1e9
            pe=max([abs(a-b) for a,b in zip(direct['final_gain'],event['final_gain'])]+[abs(direct['final_b']-event['final_b'])])
            check(f'independent learner ODE family {family}, {name}',same and err<2e-6 and pe<2e-6,max_event_error=err,max_parameter_error=pe)
    check('frozen learners do not acquire the tested skill',report['frozen_student_successful']==0)
    # Retained choices must live in action gains rather than general recovery speed.
    for p in policies:
        if p['arm']!='actual_credit':continue
        states=p['record']['samples'][-1]['cells'][:2]
        reset=[read_policy(dict(gains=[.3,.3,4.],b=c['b']))['action'] for c in states]
        swapped=[read_policy(dict(gains=[c['gains'][1],c['gains'][0],4.],b=c['b']))['action'] for c in states]
        learned=[d['action'] for d in p['decisions'][-1]['readout']]
        check(f"{p['replicate']}: action gains carry the acquired policy",reset==[0,0] and swapped==[1-x for x in learned])
    result=dict(checks=len(checks),passed=sum(c['passed'] for c in checks),results=checks,
                scope='Numerical and structural checks of this added architecture, not a formal certificate or hardware result')
    (out/'validation.json').write_text(json.dumps(result,indent=2)+'\n')
    if not all(c['passed'] for c in checks):raise RuntimeError('validation failure')
    return result

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--out',type=Path,default=ROOT/'audit_runs'/'pedagogy');validate(p.parse_args().out)
