"""Continuous-state learner episodes and native-R memory for adaptive stopping.

Local R laws are unchanged. Assessments freeze plasticity; block timing,
observation bins, rollout preferences, the encoder and decoder are supplied.
"""
from pathlib import Path
import sys,math
import numpy as np
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent))
from engine import Device,NOMINAL,simulate as cell_sim
import simulate as net

MAX_BLOCKS=4;BLOCK_TIME=90.;FEEDBACK_OFFSET=500.;TRAIN_SLOT=540.
LATENCY=(.22,.5);CONTEXTS=['missing','late','not_late'];ACTIONS=['continue','stop']


def carry(device,result):
    s=result['final_state']
    assert s['main_mode']==0 and s['aux_modes']==[0,0,0] and not any(s['raw_active'])
    return Device(device.params,s['q'],s['aux_charge'],np.log(s['gain']).tolist(),s['b'],s['aux_modes'])


def make_learner(seed,training=False,index=0):
    rng=np.random.default_rng(seed)
    gain=rng.uniform(.15,.45) if training and index%2==0 else rng.uniform(1.2,1.5) if training else rng.uniform(.15,1.5)
    b=rng.uniform(.18,.4)
    pars=(NOMINAL*rng.uniform(.9,1.1,(3,5))).tolist()
    dev=Device(pars,.1,[.025]*3,np.log([.3,gain,.3]).tolist(),b,[0]*3)
    return dev,dict(initial_gain=gain,initial_b=b,seed=seed,interpolation=.45<gain<1.2)


def snapshot(d):
    return dict(q=d.initial_q,m=list(d.initial_m),gains=np.exp(d.initial_z).tolist(),b=d.initial_b,
                aux_modes=list(d.initial_aux))


def probe(device):
    cues=[k*8. for k in range(8)]
    r=cell_sim([[],cues,[]],device,80.,mode='fixed')
    windows=[[t-cue for t in r['outputs'] if cue<=t<cue+8.] for cue in cues]
    correct=sum(len(w)==1 and LATENCY[0]<=w[0]<=LATENCY[1] for w in windows)
    return dict(success=correct==8,correct=correct,latencies=windows,outputs=r['outputs'])


def block(device,plastic=True):
    # One physical state passes through every stage; no reset to the resting state.
    taught=cell_sim([[],[0.,4.],[]],device,30.,mode='a22' if plastic else 'fixed')
    after_teaching=carry(device,taught)
    assessed=cell_sim([[],[0.],[]],after_teaching,20.,mode='fixed')
    after_assessment=carry(after_teaching,assessed)
    # A declared 40-time-unit readout budget separates this observation from the
    # next action. The student evolves in quiescence throughout that budget.
    quiet=cell_sim([[],[],[]],after_assessment,40.,mode='fixed')
    final=carry(after_assessment,quiet)
    response=assessed['outputs']
    context=0 if not response else 1 if response[0]>LATENCY[1] else 2
    record=dict(context=context,assessment=response,teaching_outputs=taught['outputs'],
       before=snapshot(device),after_teaching=snapshot(after_teaching),
       after_assessment=snapshot(after_assessment),after=snapshot(final))
    return final,record


def full_path(initial,plastic=True):
    device=initial;rows=[]
    for k in range(1,MAX_BLOCKS+1):
        device,r=block(device,plastic=plastic)
        r.update(block=k,decision_time=k*BLOCK_TIME,student_pulses=3*k,
                 retained=probe(device))
        rows.append(r)
    return rows


def select(rows,choices,initial_only=False):
    # This decoder only consumes observations already available at this decision.
    for k,row in enumerate(rows):
        context=rows[0]['context'] if initial_only else row['context']
        action=choices[context]
        if action==1 or k==MAX_BLOCKS-1:
            return dict(blocks=k+1,student_pulses=3*(k+1),retained=row['retained'],
                        contexts=[r['context'] for r in rows[:k+1]],
                        actions=[choices[rows[0]['context'] if initial_only else r['context']] for r in rows[:k+1]],
                        stop_reason='policy' if action==1 else 'budget')
    raise AssertionError('unreachable')


def rollout_preference(current,terminal):
    # A task-provided comparison of measured outcomes, not a context -> action label.
    # STOP is cheaper if already successful. Otherwise CONTINUE is credited only
    # if its fixed continue-to-budget training rollout succeeds. Both fail: abstain.
    if current['retained']['success']:return 1
    if terminal['retained']['success']:return 0
    return None


class MemoryBank(net.Network):
    def __init__(self,trials,arm,**kwargs):
        super().__init__('impulsions',**kwargs)
        self.configuration=arm;self.cfg=dict(pulses=False,settings=False,reverse=False,plastic=arm!='frozen')
        self.queue=[];self.samples=[];self.copies=[];self.outputs=[];self.arrivals=[]
        self.alive=np.ones(3,dtype=bool);self.y[:,4:7]=np.log([.3,.3,4.]);self.y[:,7]=.08
        self.end=TRAIN_SLOT*len(trials)+24.
        self.add(0.,'sample',())
        for k,tr in enumerate(trials):
            t=k*TRAIN_SLOT;feedback=t+FEEDBACK_OFFSET
            port=1-tr['action'] if arm=='wrong_credit' else tr['action']
            good=tr['preferred'] and arm!='uninformative'
            guard=feedback+(3.5 if good else 0.)
            self.add(feedback+.35,'on',(tr['context'],port,'paired_outcome'))
            self.add(feedback+1.35,'off',(tr['context'],port,'paired_outcome'))
            self.add(guard,'on',(tr['context'],2,'outcome_guard'))
            self.add(guard+1.,'off',(tr['context'],2,'outcome_guard'))
            self.add(t+TRAIN_SLOT-1.,'sample',())
        self.add(self.end,'sample',())
    def pulse_routes(self,source,when):return []
    def execute(self):
        old=net.END;net.END=self.end
        try:return self.run()
        finally:net.END=old


def read_cell(state):
    latencies=[]
    for action in range(2):
        d=Device(np.broadcast_to(NOMINAL,(3,5)).tolist(),.1,[.025]*3,
                 np.log(state['gains']).tolist(),state['b'],[0]*3)
        arrivals=[[],[],[]];arrivals[action]=[0.]
        result=cell_sim(arrivals,d,20.,mode='fixed')
        latencies.append(result['outputs'][0] if result['outputs'] else None)
    firing=[(t,a) for a,t in enumerate(latencies) if t is not None]
    if not firing:action=0
    else:
        earliest=min(t for t,_ in firing)
        action=min(a for t,a in firing if t<=earliest+1e-7)
    return dict(action=action,name=ACTIONS[action],latencies=latencies,fallback=not bool(firing))


def read_bank(record,sample=-1):
    return [read_cell(c) for c in record['samples'][sample]['cells']]
