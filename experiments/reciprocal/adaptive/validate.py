"""Independent dynamics, causal online replay, paired controls and state continuity."""
from pathlib import Path
import argparse,json,hashlib,math
import numpy as np
import model as m
from ode_reference import simulate_ode


def online_episode(initial,choices):
    # Deliberately does not compute future blocks or an evaluation probe before STOP.
    device=initial;observations=[]
    for k in range(1,m.MAX_BLOCKS+1):
        device,row=m.block(device)
        context=row['context'];action=choices[context]
        observations.append(dict(block=k,context=context,action=action))
        if action==1 or k==m.MAX_BLOCKS:
            return dict(blocks=k,student_pulses=3*k,retained=m.probe(device),observations=observations)
    raise AssertionError('unreachable')


def validate(out):
    plan=json.loads((out/'plan.json').read_text());training=json.loads((out/'training.json').read_text())
    policies=json.loads((out/'policies.json').read_text());evaluations=json.loads((out/'evaluation.json').read_text());summary=json.loads((out/'summary.json').read_text())
    checks=[];online_records=[]
    def check(name,passed,**details):
        row=dict(test=name,passed=bool(passed),**details);checks.append(row);print(json.dumps(row),flush=True)
    check('locked source hashes match',all(hashlib.sha256((m.HERE/name).read_bytes()).hexdigest()==h for name,h in plan['source_sha256'].items()))
    check('feedback follows the full counterfactual pupil episode',m.FEEDBACK_OFFSET>m.MAX_BLOCKS*m.BLOCK_TIME+80. and m.TRAIN_SLOT>m.FEEDBACK_OFFSET+24.)
    check('each observation precedes its next action',30.+20.+2*20.==m.BLOCK_TIME)
    check('complete teacher factorial',len(policies)==4*plan['replicates'] and len({(p['replicate'],p['arm']) for p in policies})==len(policies))
    trainseeds={t['metadata']['seed'] for rep in training for t in rep['trajectories']}
    testseeds=[{s['metadata']['seed'] for s in e['students']} for e in evaluations]
    check('training and two test lots have disjoint learner seeds',not trainseeds.intersection(set.union(*testseeds)) and not testseeds[0].intersection(testseeds[1]))
    check('interpolation gain band is excluded from training',all(not t['metadata']['interpolation'] for rep in training for t in rep['trajectories']))
    check('fresh tests contain the excluded initial gain band',all(any(s['metadata']['interpolation'] for s in e['students']) for e in evaluations))
    # A conservative analytic bound keeps the untracked learner reserve gate open.
    C,Lm,Ls,Le,M=[float(x*1.1) for x in m.NOMINAL];A=math.log(4)
    work_bound=max(3*C*A,A,1.1)+3*max(M*A,Lm,Ls,Le)+2.4*Le+1.5*Lm
    reserve_lower=100-work_bound/10
    check('conservative workload bound keeps learner reserve positive',reserve_lower>50,
          maximum_instantaneous_work_bound=work_bound,reserve_lower_bound=reserve_lower,
          assumptions='q and auxiliary charges <=1, ERROR charge <=0.1, parameters in declared +/-10% box, initial E=100')
    allpaths=[t['path'] for rep in training for t in rep['trajectories']]+[s['path'] for e in evaluations for s in e['students']]
    check('actual charges and learned parameters are carried between blocks',all(a['after']==b['before'] for path in allpaths for a,b in zip(path,path[1:])))
    freeze_error=max(abs(a-b) for path in allpaths for r in path for stage in ['after_assessment','after'] for a,b in zip(r['after_teaching']['gains']+[r['after_teaching']['b']],r[stage]['gains']+[r[stage]['b']]))
    check('assessment and readout quiet stages do not change learned settings',freeze_error<1e-12,max_roundtrip_difference=freeze_error)
    check('observations are derived only from assessment outputs',all(r['context']==(0 if not r['assessment'] else 1 if r['assessment'][0]>.5 else 2) for path in allpaths for r in path))
    check('student-pulse counts include every assessment',all(r['student_pulses']==3*r['block'] for path in allpaths for r in path))
    for rep,train in enumerate(training):
        valid=all(c['winner']==m.rollout_preference(train['trajectories'][c['student']]['path'][c['block']-1],train['trajectories'][c['student']]['path'][-1]) for c in train['comparisons'])
        check(f'{rep}: preferences follow measured paired rollout outcomes',valid)
        first=[]
        for context in range(3):
            pool=[dict(student=t['student'],block=r['block']) for t in train['trajectories'] for r in t['path'][:-1] if r['context']==context]
            chosen=[dict(student=c['student'],block=c['block']) for c in train['comparisons'] if c['context']==context]
            first.append(chosen==pool[:plan['comparisons_per_context']])
        check(f'{rep}: comparison sampling does not filter on preference winner',all(first))
        check(f'{rep}: both actions receive one outcome per comparison',all(sorted(t['action'] for t in train['trials'] if t['comparison']==i)==[0,1] for i in range(len(train['comparisons']))))
        byarm={p['arm']:p for p in policies if p['replicate']==rep}
        for arm,p in byarm.items():
            r=p['record'];cells=[c for s in r['samples'] for c in s['cells']]
            bounded=all(c['alive'] and 0<min(c['gains'])<=max(c['gains'])<=4+1e-7 and 0<c['b']<=1.1+1e-7 and 50<c['E']<=100+1e-7 for c in cells)
            check(f'{rep}/{arm}: bounded live native memory and reserve',bounded and not r['copies'])
            check(f'{rep}/{arm}: exact pulse budget',len(r['arrivals'])==2*len(train['trials']))
            valid=True
            for k,t in enumerate(train['trials']):
                actual=[a for a in r['arrivals'] if k*m.TRAIN_SLOT<=a['time']<(k+1)*m.TRAIN_SLOT]
                port=1-t['action'] if arm=='wrong_credit' else t['action'];good=t['preferred'] and arm!='uninformative'
                f=k*m.TRAIN_SLOT+m.FEEDBACK_OFFSET
                expected=sorted([(f+.35,port,'paired_outcome'),(f+(3.5 if good else 0.),2,'outcome_guard')])
                valid &= sorted((a['time'],a['port'],a['source']) for a in actual)==expected and all(a['node']==t['context'] for a in actual)
            check(f'{rep}/{arm}: outcome encoder respects declared timing and credit',valid)
            check(f'{rep}/{arm}: decoded choices come from native R readout',m.read_bank(r)==p['readout'] and [x['action'] for x in p['readout']]==p['choices'])
        a=byarm['actual_credit']['record'];b=byarm['wrong_credit']['record']
        swapped=[(x['time'],x['node'],2 if x['port']==2 else 1-x['port']) for x in a['arrivals']]
        raw=[(x['time'],x['node'],x['port']) for x in b['arrivals']]
        error=max(abs(c['b']-d['b']) for s,t in zip(a['samples'],b['samples']) for c,d in zip(s['cells'],t['cells']))
        check(f'{rep}: wrong credit preserves pulse counts, times, contexts and recovery',swapped==raw and error<2e-6,max_recovery_error=error)
        for arm in ['frozen','uninformative']:
            gains=np.array([c['gains'][:2] for c in byarm[arm]['record']['samples'][-1]['cells']])
            check(f'{rep}/{arm}: no action gains acquired',np.max(np.abs(gains-.3))<1e-7)
    # Confirm every primary result in actual causal execution, without future probes.
    for evaluation,lot_summary in zip(evaluations,summary['lots']):
        lot=evaluation['lot'];students=evaluation['students']
        choices=next(p['choices'] for p in policies if p['replicate']==0 and p['arm']=='actual_credit')
        valid=True
        for s in students:
            initial,_=m.make_learner(s['metadata']['seed'])
            online=online_episode(initial,choices);cached=m.select(s['path'],choices)
            valid &= online['blocks']==cached['blocks'] and online['retained']['success']==cached['retained']['success'] and online['retained']['correct']==cached['retained']['correct']
            online_records.append(dict(lot=lot,student=s['student'],**online))
        check(f'{lot}: every primary learner confirmed online without future data',valid,learners=len(students))
        for p in policies:
            records=[m.select(s['path'],p['choices']) for s in students]
            recorded=next(r for r in lot_summary['policies'] if r['replicate']==p['replicate'] and r['arm']==p['arm'])
            check(f'{lot}/{p["replicate"]}/{p["arm"]}: summary reproduces selected outcomes',recorded['successful']==sum(r['retained']['success'] for r in records) and recorded['total_student_pulses']==sum(r['student_pulses'] for r in records))
        check(f'{lot}: replay has the exact adaptive student pulse budget',all(r['total_student_pulses']==next(p['total_student_pulses'] for p in lot_summary['policies'] if p['arm']=='actual_credit' and p['replicate']==r['replicate']) for r in lot_summary['replay']))
        check(f'{lot}: replay donors are a permutation without self-pairs',sorted(map(int,lot_summary['donors'].keys()))==list(range(len(students))) and sorted(lot_summary['donors'].values())==list(range(len(students))) and all(int(k)!=v for k,v in lot_summary['donors'].items()))
        check(f'{lot}: fixed controls exhaust all supplied open-loop stopping times',sorted(r['blocks'] for r in lot_summary['fixed'])==[1,2,3,4])
        check(f'{lot}: inheritance preserves all acquired choices',all(r['choices']==next(p['choices'] for p in policies if p['replicate']==r['replicate'] and p['arm']=='actual_credit') for r in lot_summary['inheritance']))
        check(f'{lot}: frozen learners have no tested acquisition',lot_summary['frozen_student_successful']==0)
        # Alter final grading information: the stopping action must remain identical.
        invariance=True
        for s in students:
            original=m.select(s['path'],choices)
            poisoned=[{**r,'retained':dict(success=False,correct=-999)} for r in s['path']]
            changed=m.select(poisoned,choices)
            invariance &= original['blocks']==changed['blocks'] and original['actions']==changed['actions']
        check(f'{lot}: actions cannot depend on final evaluation labels',invariance)
    # Independent single-cell implementation replays persistent teacher memory.
    for node in range(3):
        record=next(p['record'] for p in policies if p['replicate']==0 and p['arm']=='actual_credit')
        arrivals=[[a['time'] for a in record['arrivals'] if a['node']==node and a['port']==j] for j in range(3)]
        d=m.Device(np.broadcast_to(m.NOMINAL,(3,5)).tolist(),.1,[.025]*3,np.log([.3,.3,4.]).tolist(),.08,[0]*3)
        independent=m.cell_sim(arrivals,d,record['samples'][-1]['time'])
        final=record['samples'][-1]['cells'][node];expected=[o['time'] for o in record['outputs'] if o['node']==node]
        same=len(expected)==len(independent['outputs'])
        err=max((abs(a-b) for a,b in zip(expected,independent['outputs'])),default=0.) if same else 1e9
        pe=max([abs(a-b) for a,b in zip(final['gains'],independent['final_gain'])]+[abs(final['b']-independent['final_b'])])
        check(f'independent persistent teacher replay {node}',same and err<2e-6 and pe<2e-6,max_event_error=err,max_parameter_error=pe)
    tight=m.MemoryBank(training[0]['trials'],'actual_credit',rtol=2e-11,atol=2e-13,max_step=.06).execute()
    reference=next(p for p in policies if p['replicate']==0 and p['arm']=='actual_credit')
    check('tighter teacher integration preserves learned decisions',[r['action'] for r in m.read_bank(tight)]==reference['choices'])
    same=len(tight['outputs'])==len(reference['record']['outputs'])
    err=max((abs(a['time']-b['time']) for a,b in zip(tight['outputs'],reference['record']['outputs'])),default=0.) if same else 1e9
    check('tighter teacher integration preserves firing trace',same and err<2e-6,max_event_error=err)
    # Independent direct ODE carries all learner charges through piecewise plasticity.
    def independent_carry(d,r):
        assert r['final_main_mode']==0 and r['final_aux_modes']==[0,0,0]
        return m.Device(d.params,r['final_q'],r['final_m'],np.log(r['final_gain']).tolist(),r['final_b'],[0]*3)
    for index in [0,1,2,3,4,5]:
        s=evaluations[0]['students'][index];d,_=m.make_learner(s['metadata']['seed']);error=0.;same=True
        for row in s['path']:
            r=simulate_ode([[],[0.,4.],[]],d,30.);d=independent_carry(d,r)
            q=simulate_ode([[],[0.],[]],d,20.,mode='fixed');d=independent_carry(d,q)
            quiet=simulate_ode([[],[],[]],d,40.,mode='fixed');d=independent_carry(d,quiet)
            same &= len(q['outputs'])==len(row['assessment'])
            error=max(error,max((abs(a-b) for a,b in zip(q['outputs'],row['assessment'])),default=0.),
              max(abs(a-b) for a,b in zip(np.exp(d.initial_z),row['after']['gains'])),abs(d.initial_b-row['after']['b']))
        check(f'independent continuous learner ODE {index}',same and error<2e-6,max_event_or_parameter_error=error)
    (out/'online_validation.json').write_text(json.dumps(online_records,indent=2)+'\n')
    result=dict(checks=len(checks),passed=sum(c['passed'] for c in checks),results=checks,
       scope='Numerical, causal and structural checks of a supplied adaptive-stopping architecture; not a formal certificate, invented curriculum or chip result')
    (out/'validation.json').write_text(json.dumps(result,indent=2)+'\n')
    if not all(c['passed'] for c in checks):raise RuntimeError('validation failure')
    return result

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--out',type=Path,required=True);validate(p.parse_args().out)
