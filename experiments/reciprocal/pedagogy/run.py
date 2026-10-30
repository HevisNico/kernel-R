"""Learn a conditional curriculum using native R plasticity in an added architecture.

The kernel is unchanged. Behavioral context sensing, a binary outcome-to-pulse
encoder, fixed exploration, a readout decoder and a curriculum library are external.
No optimizer updates the teacher: its persistent q/m/z/b/E trajectory does so.
"""
from pathlib import Path
import argparse,sys,json,math,time,hashlib,itertools
import numpy as np
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent))
import simulate as net
from engine import Device,NOMINAL,simulate as cell_sim

ROOT=HERE.parents[2]
LIBRARY={f'gap_{x}':[float(k*x) for k in range(10)] for x in [1.4,1.6,2,3,4,6,8,12,16]}
LIBRARY.update(slow_fast=[0.,12.,24.,36.,38.,40.,42.,44.,46.,48.],
               fast_slow=[0.,2.,4.,6.,8.,10.,22.,34.,46.,58.],
               pairs=[0.,1.4,16.,17.4,32.,33.4,48.,49.4,64.,65.4],
               bursts=[0.,1.4,2.8,25.,26.4,27.8,50.,51.4,52.8,54.2])
ACTIONS=['gap_4','gap_8']
LATENCY=(.22,.5);TARGET=8.;LESSON_END=180.;SLOT=360.;FEEDBACK_OFFSET=320.
ARMS=['actual_credit','wrong_credit','frozen','uninformative']
SEEDS=dict(development=419000,training=517000,test=717000)


def learner(split,rep,family,index):
    seed=SEEDS[split]+10000*rep+1000*family+index
    rng=np.random.default_rng(seed)
    gain=rng.uniform(.285,.315) if family==0 else rng.uniform(1.33,1.47)
    b=rng.uniform(.23,.27)
    params=(NOMINAL*rng.uniform(.9,1.1,(3,5))).tolist()
    return Device(params,.1,[.025]*3,np.log([.3,gain,.3]).tolist(),b,[0]*3),seed


def carry(device,result):
    """Carry physical state through quiet stage boundaries, without resetting it."""
    s=result['final_state']
    assert s['main_mode']==0 and s['aux_modes']==[0,0,0] and not any(s['raw_active'])
    return Device(device.params,s['q'],s['aux_charge'],np.log(s['gain']).tolist(),s['b'],s['aux_modes'])


def diagnose(device):
    # Observable response to a two-port cue, not access to the hidden family/parameters.
    r=cell_sim([[0.],[0.],[]],device,30.,mode='fixed')
    context=int(bool(r['outputs']))
    return context,carry(device,r),r['outputs']


def assay(device,lesson,plastic=True):
    r=cell_sim([[],lesson,[]],device,LESSON_END,mode='a22' if plastic else 'fixed')
    acquired=carry(device,r)
    cues=[k*TARGET for k in range(8)]
    p=cell_sim([[],cues,[]],acquired,cues[-1]+24.,mode='fixed')
    windows=[[t-cue for t in p['outputs'] if cue<=t<cue+TARGET] for cue in cues]
    correct=sum(len(w)==1 and LATENCY[0]<=w[0]<=LATENCY[1] for w in windows)
    return dict(success=correct==8,correct=correct,latencies=windows,
                acquired_gains=r['final_gain'],acquired_b=r['final_b'],lesson_outputs=r['outputs'])


class PolicyBank(net.Network):
    def __init__(self,trials,arm,**kwargs):
        super().__init__('impulsions',**kwargs)
        self.configuration=arm;self.cfg=dict(pulses=False,settings=False,reverse=False,plastic=arm!='frozen')
        self.queue=[];self.samples=[];self.copies=[];self.outputs=[];self.arrivals=[]
        self.alive=np.array([True,True,False])
        # One live R cell per observable context; two curriculum ports and a guard port.
        self.y[:,4:7]=np.log([.3,.3,4.]);self.y[:,7]=.08
        self.trials=trials;self.end=SLOT*len(trials)+24.
        self.add(0.,'sample',())
        for k,tr in enumerate(trials):
            t=k*SLOT;ctx=tr['context'];action=tr['action']
            credited=1-action if arm=='wrong_credit' else action
            good=tr['success'] and arm!='uninformative'
            # Same two canonical pulses for every trial. Timing encodes the outcome.
            # An early guard fires R before feedback's ERROR phase, suppressing gain
            # learning. A late guard lets a successful feedback pulse acquire gain.
            feedback=t+FEEDBACK_OFFSET
            guard=feedback+(3.5 if good else 0.)
            self.add(feedback+.35,'on',(ctx,credited,'student_outcome'))
            self.add(feedback+1.35,'off',(ctx,credited,'student_outcome'))
            self.add(guard,'on',(ctx,2,'outcome_guard'))
            self.add(guard+1,'off',(ctx,2,'outcome_guard'))
            self.add(t+SLOT-1.,'sample',())
        self.add(self.end,'sample',())
    def pulse_routes(self,source,when):return []
    def execute(self):
        old=net.END;net.END=self.end
        try:return self.run()
        finally:net.END=old


def read_policy(state):
    """Fixed decoder of actual native firing responses; it never edits memory."""
    latencies=[]
    for action in range(2):
        d=Device(np.broadcast_to(NOMINAL,(3,5)).tolist(),.1,[.025]*3,
                 np.log(state['gains']).tolist(),state['b'],[0]*3)
        arrivals=[[],[],[]];arrivals[action]=[0.]
        r=cell_sim(arrivals,d,20.,mode='fixed')
        latencies.append(r['outputs'][0] if r['outputs'] else None)
    firing=[(latency,action) for action,latency in enumerate(latencies) if latency is not None]
    choice=min(firing)[1] if firing else 0
    return dict(action=choice,curriculum=ACTIONS[choice],latencies=latencies,
                fallback=not bool(firing))


def write(out,name,value):
    (out/name).write_text(json.dumps(net.plain(value),ensure_ascii=False,indent=2)+'\n')


def run(out,replicates=4,training_per_family=6,test_per_family=64):
    out.mkdir(parents=True,exist_ok=True)
    if (out/'plan.json').exists():raise RuntimeError('fresh output directory required')
    started=time.perf_counter()
    plan=dict(question='Can native R plasticity store a conditional curriculum choice that improves fresh learners?',
      claim_scope='Curriculum-selection learning in an added R-based architecture, not spontaneous pedagogy in an isolated R cell',
      kernel='q/m/z/b/E unchanged; no optimizer, direct weight update, live-state reset or cell removal',
      additions=['behavioral diagnostic cue with plasticity temporarily disabled',
       'one R policy cell per binary diagnostic context; two lesson ports and a guard port',
       'binary post-lesson timing success encoded by early/late guard pulses',
       'fixed exploration of both curricula; first-response decoder with fixed action-0 tie/fallback',
       'fixed curriculum templates and optional external parameter inheritance'],
      task=dict(target_period=TARGET,latency_window=LATENCY,probe_prompts=8,
       diagnostic_pulses=2,teaching_pulses=10,probe_plasticity=False,lesson_end=LESSON_END,
       diagnostic_end=30.,probe_duration=80.,feedback_offset=FEEDBACK_OFFSET,episode_slot=SLOT),
      learner_initials=dict(gain_family_0=[.285,.315],gain_family_1=[1.33,1.47],b=[.23,.27],
       physical_parameters='independent uniform +/-10% of the original five per-port parameters',
       scope='Extra initial states, outside A22 certified initial family'),
      curriculum_library=LIBRARY,learned_actions=ACTIONS,arms=ARMS,seeds=SEEDS,
      replicates=replicates,training_per_family=training_per_family,test_per_family=test_per_family,
      fixed_baseline='fast_slow, selected from all 13 curricula on disjoint development data',
      primary='final actual-credit policy versus development-selected best fixed curriculum on fresh held-out learners',
      controls=['wrong action credit with identical pulse count and timing per live cell',
        'frozen R plasticity','uninformative negative outcome timing','random choice expected score',
        'best fixed curriculum in hindsight across 13 templates, explicitly a test-set oracle',
        'saturated equal policy gains','context-swap decoder','learner plasticity disabled',
        'inherited policy on fresh R cells'],
      provenance='Benchmark and two curricula designed on development data. An initial 128-learner pilot used precomputed outcomes. This confirmation uses fresh test seed 717000 and feedback only after the complete pupil episode; no lesson or threshold was retuned after the pilot',
      source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    write(out,'plan.json',plan)
    development=ROOT/'audit_runs'/'pedagogy_development'
    for filename in ['grid.json','precision.json','curricula.json']:
        if (development/filename).exists():(out/('development_'+filename)).write_bytes((development/filename).read_bytes())
    pilot=ROOT/'audit_runs'/'pedagogy_pilot'
    for filename in ['plan.json','summary.json']:
        if (pilot/filename).exists():(out/('pilot_'+filename)).write_bytes((pilot/filename).read_bytes())
    training=[];policies=[]
    for rep in range(replicates):
        trials=[]
        for family,index in itertools.product(range(2),range(training_per_family)):
            d,seed=learner('training',rep,family,index);ctx,prepared,diagnostic=diagnose(d)
            for action,name in enumerate(ACTIONS):
                result=assay(prepared,LIBRARY[name])
                trials.append(dict(context=ctx,action=action,family=family,index=index,seed=seed,
                                   diagnostic=diagnostic,**result))
        rng=np.random.default_rng(817000+rep);rng.shuffle(trials)
        training.append(dict(replicate=rep,trials=trials))
        for arm in ARMS:
            r=PolicyBank(trials,arm).execute()
            decisions=[dict(time=s['time'],readout=[read_policy(c) for c in s['cells'][:2]]) for s in r['samples']]
            policies.append(dict(replicate=rep,arm=arm,record=r,decisions=decisions))
            print('policy',rep,arm,[x['action'] for x in decisions[-1]['readout']],round(time.perf_counter()-started,1),'s',flush=True)
    write(out,'training.json',training);write(out,'policies.json',policies)
    evaluation=[]
    # Test learners and their outcomes never update teacher policy states.
    for family,index in itertools.product(range(2),range(test_per_family)):
        d,seed=learner('test',0,family,index);ctx,prepared,diagnostic=diagnose(d)
        results={name:assay(prepared,times) for name,times in LIBRARY.items()}
        frozen=assay(prepared,LIBRARY[ACTIONS[0]],plastic=False)
        evaluation.append(dict(family=family,index=index,seed=seed,context=ctx,
                               diagnostic=diagnostic,curricula=results,frozen_student=frozen))
    write(out,'evaluation.json',evaluation)
    summaries=[]
    for policy in policies:
        for stage in ['before','after']:
            decision=policy['decisions'][0 if stage=='before' else -1]['readout']
            selected=[e['curricula'][decision[e['context']]['curriculum']] for e in evaluation]
            summaries.append(dict(replicate=policy['replicate'],arm=policy['arm'],stage=stage,
              successful=sum(r['success'] for r in selected),n=len(selected),
              mean_correct=float(np.mean([r['correct'] for r in selected])),
              actions=[r['action'] for r in decision]))
    fixed={name:sum(e['curricula'][name]['success'] for e in evaluation) for name in LIBRARY}
    curves=[];inherited=[]
    for p in policies:
        if p['arm']!='actual_credit':continue
        for s in p['decisions']:
            curves.append(dict(replicate=p['replicate'],time=s['time'],
              successful=sum(e['curricula'][s['readout'][e['context']]['curriculum']]['success'] for e in evaluation),n=len(evaluation)))
        cells=p['record']['samples'][-1]['cells'][:2]
        children=[dict(gains=[max(.3,c['gains'][0]),max(.3,c['gains'][1]),4.],b=max(.08,c['b'])) for c in cells]
        decisions=[read_policy(c) for c in children]
        inherited.append(dict(replicate=p['replicate'],parent_state=cells,child_state=children,readout=decisions,
          successful=sum(e['curricula'][decisions[e['context']]['curriculum']]['success'] for e in evaluation)))
    actual=[p for p in policies if p['arm']=='actual_credit']
    swapped=[sum(e['curricula'][p['decisions'][-1]['readout'][1-e['context']]['curriculum']]['success'] for e in evaluation) for p in actual]
    saturated=read_policy(dict(gains=[4.,4.,4.],b=1.1))
    primary=[]
    for p in actual:
        decisions=p['decisions'][-1]['readout']
        a=np.array([e['curricula'][decisions[e['context']]['curriculum']]['success'] for e in evaluation],dtype=float)
        b=np.array([e['curricula']['fast_slow']['success'] for e in evaluation],dtype=float)
        differences=a-b
        rng=np.random.default_rng(917000+p['replicate'])
        # Resample the fresh learner, not the repeated teacher/student pair.
        means=np.mean(differences[rng.integers(0,len(a),(5000,len(a)))],axis=1)
        primary.append(dict(replicate=p['replicate'],difference=float(np.mean(differences)),
          descriptive_bootstrap_95_interval=np.quantile(means,[.025,.975]).tolist(),
          scope='Conditional on these trained policies and this designed benchmark; training-population uncertainty not estimated'))
    report=dict(teacher_summaries=summaries,fixed_curricula=fixed,test_learners=len(evaluation),
      best_fixed_development_selected='fast_slow',best_fixed_hindsight=max(fixed,key=fixed.get),
      random_two_actions_expected_successes=sum(sum(e['curricula'][a]['success'] for a in ACTIONS)/2 for e in evaluation),
      context_swapped_successes=swapped,inherited=inherited,
      saturated_policy=dict(readout=saturated,successful=fixed[saturated['curriculum']]),
      frozen_student_successful=sum(e['frozen_student']['success'] for e in evaluation),
      primary=primary,learning_curve=curves,
      evaluation_pairing='The same held-out learners are reused across all policies, arms and curriculum alternatives; no pooling as independent students',
      elapsed_seconds=time.perf_counter()-started)
    write(out,'summary.json',report)
    print('DONE',json.dumps(dict(test_learners=len(evaluation),fixed=fixed,primary=primary)),flush=True)
    return report

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--out',type=Path,default=ROOT/'audit_runs'/'pedagogy');p.add_argument('--replicates',type=int,default=4);p.add_argument('--training-per-family',type=int,default=6);p.add_argument('--test-per-family',type=int,default=64)
    a=p.parse_args();run(a.out,a.replicates,a.training_per_family,a.test_per_family)
