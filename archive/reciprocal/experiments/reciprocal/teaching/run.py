"""Does native R become a more effective teacher after student feedback?

The teacher has no reward optimizer, copy selector or learned policy added here.
True feedback is compared with no feedback and time-reversed, count-matched replay.
Teaching quality is measured on fresh learners with an equal emitted-pulse budget.
"""
from pathlib import Path
import sys,json,math,hashlib,time,argparse
import numpy as np
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent))
import simulate as network
from engine import Device,NOMINAL,simulate as cell_sim
from analyse import probe

ROOT=HERE.parents[2]
DEFAULT_OUT=ROOT/'audit_runs'/'teaching'
CLOCK=[float(t) for t in range(0,125,4)]
TRAINING_CONTEXTS=[dict(id=i,gain=g,b=b) for i,(g,b) in enumerate([(g,b) for g in [.3,.8,1.2] for b in [.06,.12]])]
BUDGETS=[6,10]
CUES=[3.,4.]
TRANSFER_MODES=['impulsions','reglages','les_deux']
ARMS=['sans_retour','retour_reel','retour_inverse']
DELAY=.35


def fresh_teacher():
    # State of A after its own lesson, before meeting a student; no inheritance into A.
    path=network.ROOT/'audit_runs'/'reciprocal'/'impulsions.json'
    if path.exists():
        r=json.loads(path.read_text());sample=min(r['samples'],key=lambda s:abs(s['time']-159.9))
        return sample['cells'][0]
    # Reconstruct the same physical preparation if only this teaching package is present.
    dev=Device(np.broadcast_to(NOMINAL,(3,5)).tolist(),.1,[.025]*3,np.log([.3,1.2,.3]).tolist(),.08,[0]*3)
    r=cell_sim([list(range(0,121,8)),[],[]],dev,160.)
    return dict(gains=r['final_gain'],b=r['final_b'])


class Classroom(network.Network):
    def __init__(self,teacher,context,arm,replay=(),**kwargs):
        super().__init__('impulsions',**kwargs)
        self.arm=arm;self.queue=[];self.samples=[];self.copies=[];self.outputs=[];self.arrivals=[]
        self.alive=np.array([True,True,False]);self.y[0,4:7]=np.log(teacher['gains']);self.y[0,7]=teacher['b']
        self.y[1,5]=math.log(context['gain']);self.y[1,7]=context['b']
        for when in CLOCK:
            self.add(when,'on',(0,0,'exercice'));self.add(when+1,'off',(0,0,'exercice'))
        if arm=='retour_inverse':
            for when in replay:
                self.add(when,'on',(0,2,'retour_rejoue'));self.add(when+1,'off',(0,2,'retour_rejoue'))
        for when in [0.,32.,64.,96.,128.,159.9,160.]:self.add(when,'sample',())
    def pulse_routes(self,source,when):
        if when>=128:return []
        if source==0:return [dict(source=0,target=1,port=1)]
        if source==1 and self.arm=='retour_reel':return [dict(source=1,target=0,port=2)]
        return []
    def execute(self):
        previous=network.END;network.END=160.
        try:return self.run()
        finally:network.END=previous


def learner(index):
    rng=np.random.default_rng(2026110100+index)
    params=(NOMINAL*rng.uniform(.9,1.1,(3,5))).tolist()
    return Device(params,.1,[.025]*3,np.log([.3,1.2,.3]).tolist(),.08,[0]*3)


def lesson(teacher,gap):
    # Fixed readout: evaluate acquired teacher state without further adaptation.
    dev=Device(np.broadcast_to(NOMINAL,(3,5)).tolist(),.1,[.025]*3,np.log(teacher['gains']).tolist(),teacher['b'],[0]*3)
    cues=[k*gap for k in range(48)]
    r=cell_sim([cues,[],[]],dev,cues[-1]+20,mode='fixed')
    return r['outputs']


def teach(teacher,emissions,index,budget,mode,gap):
    student=learner(index)
    if mode in ['reglages','les_deux']:
        # Declared semantic mapping: teacher's practiced port 0 -> student's lesson port 1.
        student.initial_z[1]=max(student.initial_z[1],min(math.log(student.params[1][0]),math.log(teacher['gains'][0])))
        student.initial_b=max(student.initial_b,teacher['b'])
    pulses=emissions[:budget] if mode in ['impulsions','les_deux'] else []
    enough=len(pulses)==budget if mode!='reglages' else True
    # Canonical pulses are delivered without altering their spacing.
    if pulses:
        arrivals=[[],[p-pulses[0]+DELAY for p in pulses],[]]
        end=arrivals[1][-1]+30.
    else:arrivals=[[],[],[]];end=30.
    learned=cell_sim(arrivals,student,end)
    state=dict(gains=learned['final_gain'],b=learned['final_b'])
    # Same student's physical parameters in the independent post-lesson probe.
    qdev=Device(student.params,.1,[.025]*3,np.log(state['gains']).tolist(),state['b'],[0]*3)
    tests=[k*gap for k in range(8)];r=cell_sim([[],tests,[]],qdev,tests[-1]+20.,mode='fixed')
    counts=[sum(t<=x<t+gap for x in r['outputs']) for t in tests]
    return dict(student=index,budget=budget,mode=mode,gap=gap,teacher_enough_pulses=enough,
                pulses_delivered=len(pulses),lesson_duration=pulses[-1]-pulses[0] if pulses else 0.,
                responses=counts,correct=sum(c==1 for c in counts),success=enough and all(c==1 for c in counts),
                learned_gains=state['gains'],learned_b=state['b'])


def score(rows):
    return dict(n=len(rows),successful=sum(r['success'] for r in rows),
                mean_correct=float(np.mean([r['correct'] for r in rows])),
                mean_lesson_duration=float(np.mean([r['lesson_duration'] for r in rows])),
                mean_delivered_pulses=float(np.mean([r['pulses_delivered'] for r in rows])))


def run(out,students=24):
    out.mkdir(parents=True,exist_ok=True)
    if (out/'plan.json').exists():raise RuntimeError('fresh output directory required')
    teacher=fresh_teacher()
    plan=dict(question='Does native feedback improve transferable teaching efficacy beyond additional stimulation?',
              training_contexts=TRAINING_CONTEXTS,arms=ARMS,clock=CLOCK,training_end=128.,readout=160.,
              initial_teacher=teacher,student_ids=list(range(students)),student_parameters='independent uniform +/-10% original five per-port parameters; nominal READY initial state',
              held_out_cue_gaps=CUES,budgets=BUDGETS,transfer_modes=TRANSFER_MODES,
              native_rule='q/m/z/b/E R unchanged; teacher receives student firings, no learner score or reward',
              replay='t -> 127-t of the true-feedback arrival times; same count and pulse shape, reversed temporal gaps',
              transfer='externally specified copy: teacher g0 to student g1, b inherited by max; no choice policy is learned',
              evaluation='Teacher and learner plasticity frozen during readout/probes; fresh learners, paired across states and arms',
              primary='8/8 isolated target-gap responses after a budget of 10 emitted teaching pulses, gap=3, impulses only',
              exploratory='No hypothesis of teaching intent; native teacher competence and pedagogical policy are distinct claims',
              source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    (out/'plan.json').write_text(json.dumps(network.plain(plan),ensure_ascii=False,indent=2)+'\n')
    classrooms=[];states=[dict(key='initial',context=None,arm='initial',state=teacher)]
    started=time.perf_counter()
    for context in TRAINING_CONTEXTS:
        actual=Classroom(teacher,context,'retour_reel').execute()
        actual_times=[a['time'] for a in actual['arrivals'] if a['node']==0 and a['source']=='B' and 0<=a['time']<=127.]
        replay=sorted(127.-t for t in actual_times)
        if len(replay)>1 and min(np.diff(replay))<1:raise RuntimeError('replay raw-pulse overlap')
        for arm in ARMS:
            r=actual if arm=='retour_reel' else Classroom(teacher,context,arm,replay).execute()
            end=r['samples'][-1]['cells'][0]
            states.append(dict(key=f"{arm}_{context['id']}",context=context['id'],arm=arm,state=end))
            classrooms.append(dict(context=context,arm=arm,record=r))
        print('classroom',context['id'],'done',round(time.perf_counter()-started,1),'s',flush=True)
    (out/'classrooms.json').write_text(json.dumps(network.plain(classrooms),separators=(',',':'))+'\n')
    (out/'teachers.json').write_text(json.dumps(network.plain(states),ensure_ascii=False,indent=2)+'\n')
    rows=[];summaries=[]
    with (out/'evaluation.jsonl').open('w') as log:
        for state in states:
            for gap in CUES:
                emissions=lesson(state['state'],gap)
                for budget in BUDGETS:
                    for mode in TRANSFER_MODES:
                        group=[]
                        for index in range(students):
                            r=teach(state['state'],emissions,index,budget,mode,gap)
                            r.update(teacher=state['key'],arm=state['arm'],context=state['context'])
                            r=network.plain(r);rows.append(r);group.append(r);log.write(json.dumps(r)+'\n')
                        s=score(group);s.update(teacher=state['key'],arm=state['arm'],context=state['context'],gap=gap,budget=budget,mode=mode);summaries.append(s)
                log.flush()
            print('evaluated',state['key'],round(time.perf_counter()-started,1),'s',flush=True)
    # Pooled summaries use the paired contexts, not independent extra teachers.
    pooled=[]
    for arm in ['initial']+ARMS:
        for gap in CUES:
            for budget in BUDGETS:
                for mode in TRANSFER_MODES:
                    group=[r for r in rows if r['arm']==arm and r['gap']==gap and r['budget']==budget and r['mode']==mode]
                    pooled.append(dict(arm=arm,gap=gap,budget=budget,mode=mode,**score(group)))
    report=dict(summaries=summaries,pooled=pooled,classroom_runs=len(classrooms),evaluation_runs=len(rows),
                teacher_states=len(states),elapsed_seconds=time.perf_counter()-started)
    (out/'summary.json').write_text(json.dumps(network.plain(report),ensure_ascii=False,indent=2)+'\n')
    print('DONE',json.dumps({k:report[k] for k in ['classroom_runs','evaluation_runs','elapsed_seconds']}),flush=True)
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--out',type=Path,default=DEFAULT_OUT);p.add_argument('--students',type=int,default=24)
    a=p.parse_args();run(a.out,a.students)
