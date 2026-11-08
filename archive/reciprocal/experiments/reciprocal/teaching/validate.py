"""Validate the teaching experiment without treating repeated students as independent."""
from pathlib import Path
import argparse,json,math
import numpy as np
import run as study
from ode_reference import simulate_ode
from engine import Device,NOMINAL


def validate(out):
    checks=[]
    def check(label,passed,**values):
        row=dict(test=label,passed=bool(passed),**study.network.plain(values));checks.append(row);print(json.dumps(row),flush=True)
    plan=json.loads((out/'plan.json').read_text())
    classrooms=json.loads((out/'classrooms.json').read_text())
    teachers=json.loads((out/'teachers.json').read_text())
    rows=[json.loads(s) for s in (out/'evaluation.jsonl').read_text().splitlines()]
    check('complete factorial evaluation',len(rows)==len(teachers)*len(study.CUES)*len(study.BUDGETS)*len(study.TRANSFER_MODES)*len(plan['student_ids']))
    check('no duplicate evaluations',len(rows)==len({(r['teacher'],r['gap'],r['budget'],r['mode'],r['student']) for r in rows}))
    check('budget respected',all(r['pulses_delivered']==(0 if r['mode']=='reglages' else r['budget']) for r in rows))
    check('learned parameters bounded',all(0<r['learned_b']<=1.1+1e-8 and all(0<g<=p[0]+1e-8 for g,p in zip(r['learned_gains'],study.learner(r['student']).params)) for r in rows))
    for context in study.TRAINING_CONTEXTS:
        byarm={c['arm']:c['record'] for c in classrooms if c['context']['id']==context['id']}
        actual=[a['time'] for a in byarm['retour_reel']['arrivals'] if a['node']==0 and a['source']=='B']
        replay=[a['time'] for a in byarm['retour_inverse']['arrivals'] if a['node']==0 and a['source']=='retour_rejoue']
        expected=sorted(127-t for t in actual)
        check('replay count and exact reversal context '+str(context['id']),len(actual)==len(replay) and len(expected)==len(replay) and max((abs(a-b) for a,b in zip(expected,replay)),default=0)<1e-8,count=len(actual))
        check('same external exercises context '+str(context['id']),all([a['time'] for a in r['arrivals'] if a['node']==0 and a['source']=='exercice']==study.CLOCK for r in byarm.values()))
        check('no settings copied in training context '+str(context['id']),all(not r['copies'] for r in byarm.values()))
        check('energy reserve positive context '+str(context['id']),all(r['min_observed_energy']>50 for r in byarm.values()))
    for arm in ['retour_reel','retour_inverse']:
        c=next(c for c in classrooms if c['context']['id']==0 and c['arm']==arm)
        actual=next(c for c in classrooms if c['context']['id']==0 and c['arm']=='retour_reel')
        replay=sorted(127-a['time'] for a in actual['record']['arrivals'] if a['node']==0 and a['source']=='B')
        tight=study.Classroom(study.fresh_teacher(),c['context'],arm,replay,rtol=2e-11,atol=2e-13,max_step=.06).execute()
        errors=[];counts=True
        for i in range(2):
            a=[o['time'] for o in c['record']['outputs'] if o['node']==i];b=[o['time'] for o in tight['outputs'] if o['node']==i]
            counts &= len(a)==len(b)
            if len(a)==len(b):errors += [abs(x-y) for x,y in zip(a,b)]
        check('classroom convergence '+arm,counts and max(errors,default=0)<2e-6,max_date_difference=max(errors,default=0))
    c=next(c for c in classrooms if c['context']['id']==3 and c['arm']=='retour_reel')
    for i in [0,1]:
        arrivals=[[a['time'] for a in c['record']['arrivals'] if a['node']==i and a['port']==j] for j in range(3)]
        teacher=study.fresh_teacher();z=np.log(teacher['gains']) if i==0 else np.log([.3,c['context']['gain'],.3]);b=teacher['b'] if i==0 else c['context']['b']
        dev=Device(np.broadcast_to(NOMINAL,(3,5)).tolist(),.1,[.025]*3,z.tolist(),b,[0]*3)
        independent=simulate_ode(arrivals,dev,160.)
        recorded=[o['time'] for o in c['record']['outputs'] if o['node']==i]
        counts=len(recorded)==len(independent['outputs'])
        error=max((abs(a-b) for a,b in zip(recorded,independent['outputs'])),default=0.) if counts else float('inf')
        check('independent classroom replay '+str(i),counts and error<2e-6,max_date_difference=error)
    # Any held-out improvement attributable to b alone is not evidence of selecting a teaching policy.
    matched=[]
    for teacher in teachers:
        if teacher['arm']!='retour_reel':continue
        own=teacher['state'];counter=dict(gains=own['gains'].copy(),b=own['b'])
        # The practiced port and recovery suffice for the open-loop outgoing lesson.
        counter['gains'][1:]=[1.2,.3]
        for gap in study.CUES:
            a=study.lesson(own,gap);b=study.lesson(counter,gap)
            matched.append(len(a)==len(b) and max((abs(x-y) for x,y in zip(a,b)),default=0)<1e-9)
    check('feedback-port saturation not needed in frozen outgoing lesson',all(matched))
    for teacherkey in ['sans_retour_0','retour_reel_0']:
        teacher=next(t['state'] for t in teachers if t['key']==teacherkey)
        emissions=study.lesson(teacher,3.)
        for mode in ['impulsions','les_deux']:
            student=study.learner(23)
            if mode=='les_deux':
                student.initial_z[1]=max(student.initial_z[1],min(math.log(student.params[1][0]),math.log(teacher['gains'][0])))
                student.initial_b=max(student.initial_b,teacher['b'])
            pulses=emissions[:10];arrivals=[[],[p-pulses[0]+study.DELAY for p in pulses],[]]
            direct=simulate_ode(arrivals,student,arrivals[1][-1]+30)
            stored=next(r for r in rows if r['teacher']==teacherkey and r['gap']==3 and r['budget']==10 and r['mode']==mode and r['student']==23)
            error=max([abs(a-b) for a,b in zip(direct['final_gain'],stored['learned_gains'])]+[abs(direct['final_b']-stored['learned_b'])])
            check('independent learner lesson '+teacherkey+' '+mode,error<2e-6,max_parameter_difference=error)
    report=dict(checks=len(checks),passed=sum(c['passed'] for c in checks),results=checks)
    (out/'validation.json').write_text(json.dumps(study.network.plain(report),indent=2)+'\n')
    if not all(c['passed'] for c in checks):raise RuntimeError('validation failed')
    return report
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--out',type=Path,default=study.DEFAULT_OUT);validate(p.parse_args().out)
