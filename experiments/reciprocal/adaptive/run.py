"""Locked evaluation of a learned within-lesson stopping policy."""
from pathlib import Path
from datetime import datetime, timezone
import argparse,json,hashlib,time,itertools
import numpy as np
import model as m
import provenance

ROOT=Path(__file__).resolve().parents[3]
ARMS=['actual_credit','wrong_credit','frozen','uninformative']
SEEDS=dict(training=1032000,test=1332000,confirmation=1432000)


def write(out,name,value):
    (out/name).write_text(json.dumps(m.net.plain(value),indent=2)+'\n')


def score(records):
    return dict(n=len(records),successful=sum(r['retained']['success'] for r in records),
      mean_correct=float(np.mean([r['retained']['correct'] for r in records])),
      mean_student_pulses=float(np.mean([r['student_pulses'] for r in records])),
      total_student_pulses=sum(r['student_pulses'] for r in records))


def run(out,replicates=3,training_students=64,comparisons_per_context=8,test_students=160):
    out.mkdir(parents=True,exist_ok=True)
    if (out/'plan.json').exists():raise RuntimeError('fresh output directory required')
    started=time.perf_counter()
    plan=dict(question='Can native-R memory learn a policy that adapts lesson stopping to intermediate learner feedback?',
      supported_scope='Within-lesson stopping adaptation using supplied blocks, assessment and paired-rollout preference training; no curriculum invention',
      kernel='q/m/z/b/E unchanged; teacher memory continuous; no direct learned-weight updates',
      architecture=['one R memory cell per externally binned observation: missing, late, not_late',
       'two supplied actions: continue with another two-pulse block, or stop',
       'blocks contain teaching at 0 and 4, quiet to 30, one plasticity-disabled assessment at 30, quiet to 50, and readout budget to 90',
       'actual q and auxiliary charges carried across stages; no learner reset',
       'native R gains store preferences; fixed first-response decoder with 1e-7 tie tolerance',
       'canonical feedback plus early/late guard encodes a preferred action'],
      training='For each observed training prefix, compare STOP now with CONTINUE under a fixed continue-to-four-block rollout. Reward STOP if it already passes; otherwise reward CONTINUE only if its rollout passes; abstain if both fail. Preferences are supplied by paired numerical outcome experiments, not discovered autonomously by an isolated cell.',
      feedback_causality=dict(maximum_learner_episode=440.,feedback_offset=m.FEEDBACK_OFFSET,trial_slot=m.TRAIN_SLOT),
      task=dict(target_period=8.,latency_window=m.LATENCY,probe_prompts=8,maximum_blocks=m.MAX_BLOCKS,
       teaching_pulses_per_block=2,assessment_pulses_per_block=1,student_budget=12,block_time=m.BLOCK_TIME,
       learner_deadline=360.,final_probe_plasticity=False),
      learner_distribution=dict(training_gain_bands=[[.15,.45],[1.2,1.5]],test_gain=[.15,1.5],
       b=[.18,.4],physical_parameters='original five per-port parameters independently uniform +/-10%; original certified initial family not assumed',
       interpolation='Test initial gains strictly between .45 and 1.2 are excluded from training'),
      seeds=SEEDS,replicates=replicates,training_students=training_students,
      comparisons_per_context=comparisons_per_context,test_students_per_lot=test_students,
      primary='Fresh-test success of the learned closed-loop policy versus the development-selected fixed block count; student pulse usage and matched replay are required companion outcomes',
      fixed_baseline=3,baseline_scope='All four possible fixed stopping times under the same supplied block protocol, not all possible pulse waveforms or schedules',
      controls=['all four fixed block counts','same adaptive lesson-length multiset replayed onto other learners',
       'initial observation only','time-aligned other-learner observations','wrong action credit with exact pulse timing/count match',
       'frozen teacher plasticity','uninformative outcomes','frozen learner plasticity',
       'fresh bank inheriting learned settings'],
      design_provenance='The supplied stopping task, block protocol and rollout preference were designed previously. This is a computational reproduction using the original training/test seeds, not a new independent confirmation sample or a preregistered experiment. Historical development recordings are not imported.',
      execution_started_utc=datetime.now(timezone.utc).isoformat(),
      **provenance.capture())
    write(out,'plan.json',plan)
    training=[];policies=[]
    for rep in range(replicates):
        trajectories=[];pool=[]
        for i in range(training_students):
            dev,metadata=m.make_learner(SEEDS['training']+rep*10000+i,training=True,index=i)
            rows=m.full_path(dev)
            trajectories.append(dict(student=i,metadata=metadata,path=rows))
            for row in rows[:-1]:
                pool.append(dict(student=i,block=row['block'],context=row['context'],
                  winner=m.rollout_preference(row,rows[-1]),current_success=row['retained']['success'],
                  rollout_success=rows[-1]['retained']['success']))
        comparisons=[]
        for context in range(3):
            subset=[r for r in pool if r['context']==context][:comparisons_per_context]
            if len(subset)<comparisons_per_context:raise RuntimeError(f'insufficient natural context {context} examples: {len(subset)}')
            comparisons.extend(subset)
        trials=[]
        for comparison,c in enumerate(comparisons):
            for action in range(2):trials.append(dict(comparison=comparison,context=c['context'],action=action,preferred=c['winner']==action))
        np.random.default_rng(1532000+rep).shuffle(trials)
        training.append(dict(replicate=rep,trajectories=trajectories,comparisons=comparisons,trials=trials))
        for arm in ARMS:
            record=m.MemoryBank(trials,arm).execute()
            decoded=m.read_bank(record)
            policies.append(dict(replicate=rep,arm=arm,record=record,readout=decoded,choices=[r['action'] for r in decoded]))
            print('policy',rep,arm,[r['name'] for r in decoded],round(time.perf_counter()-started,1),flush=True)
    write(out,'training.json',training);write(out,'policies.json',policies)
    evaluations=[];summaries=[]
    for lot in ['test','confirmation']:
        students=[]
        for i in range(test_students):
            dev,metadata=m.make_learner(SEEDS[lot]+i)
            rows=m.full_path(dev)
            frozen=m.full_path(dev,plastic=False)
            students.append(dict(student=i,metadata=metadata,path=rows,frozen_student=frozen[-1]['retained']))
        # A cyclic random order maps every donor lesson onto a different learner.
        order=np.random.default_rng(SEEDS[lot]+5000).permutation(test_students).tolist()
        donors={order[k]:order[(k+1)%test_students] for k in range(test_students)}
        lot_summary=dict(lot=lot,policies=[],fixed=[],replay=[],initial_only=[],other_feedback=[],inheritance=[])
        for count in range(1,m.MAX_BLOCKS+1):
            records=[dict(retained=s['path'][count-1]['retained'],student_pulses=3*count) for s in students]
            lot_summary['fixed'].append(dict(blocks=count,**score(records)))
        for p in policies:
            records=[m.select(s['path'],p['choices']) for s in students]
            row=dict(replicate=p['replicate'],arm=p['arm'],choices=p['choices'],**score(records))
            lot_summary['policies'].append(row)
            if p['arm']!='actual_credit':continue
            replay=[dict(retained=s['path'][records[donors[s['student']]]['blocks']-1]['retained'],student_pulses=records[donors[s['student']]]['student_pulses']) for s in students]
            initial=[m.select(s['path'],p['choices'],initial_only=True) for s in students]
            other=[]
            for s in students:
                donor=students[donors[s['student']]]
                for k in range(m.MAX_BLOCKS):
                    if p['choices'][donor['path'][k]['context']]==1 or k==m.MAX_BLOCKS-1:
                        other.append(dict(retained=s['path'][k]['retained'],student_pulses=3*(k+1)));break
            states=p['record']['samples'][-1]['cells']
            children=[dict(gains=[max(.3,c['gains'][0]),max(.3,c['gains'][1]),4.],b=max(.08,c['b'])) for c in states]
            inherited=[m.read_cell(c)['action'] for c in children]
            lot_summary['replay'].append(dict(replicate=p['replicate'],**score(replay)))
            lot_summary['initial_only'].append(dict(replicate=p['replicate'],**score(initial)))
            lot_summary['other_feedback'].append(dict(replicate=p['replicate'],**score(other)))
            lot_summary['inheritance'].append(dict(replicate=p['replicate'],choices=inherited,**score([m.select(s['path'],inherited) for s in students])))
            subsets={name:[i for i,s in enumerate(students) if s['metadata']['interpolation']==flag] for name,flag in [('unseen_initial_gain_band',True),('endpoint_bands',False)]}
            row['subgroups']={name:score([records[i] for i in indices]) for name,indices in subsets.items() if indices}
            # Descriptive, paired uncertainty conditional on the trained policy.
            a=np.array([r['retained']['success'] for r in records],dtype=float)
            b=np.array([s['path'][2]['retained']['success'] for s in students],dtype=float)
            rng=np.random.default_rng(SEEDS[lot]+7000+p['replicate'])
            means=np.mean((a-b)[rng.integers(0,len(a),(4000,len(a)))],axis=1)
            row['paired_success_difference']=float(np.mean(a-b));row['descriptive_bootstrap_95_interval']=np.quantile(means,[.025,.975]).tolist()
        lot_summary['frozen_student_successful']=sum(s['frozen_student']['success'] for s in students)
        lot_summary['donors']=donors
        lot_summary['best_fixed_hindsight']=max(lot_summary['fixed'],key=lambda x:(x['successful'],-x['mean_student_pulses']))['blocks']
        evaluations.append(dict(lot=lot,students=students));summaries.append(lot_summary)
        print('lot',lot,'done',round(time.perf_counter()-started,1),flush=True)
    write(out,'evaluation.json',evaluations)
    report=dict(lots=summaries,elapsed_seconds=time.perf_counter()-started,
      inference='Held-out policy memory frozen; online actions use only intermediate assessment pulses and hard budget, not hidden parameters, training preferences or final probe outcomes',
      pairing='Same fresh learners reused across controls and training replicates within each lot; the two test lots are disjoint',
      invention='No invention claim: pulse shape, two-pulse block and four-block budget are supplied. The learned policy adapts the stopping time.')
    write(out,'summary.json',report)
    for lot in summaries:print('RESULT',lot['lot'],json.dumps(dict(actual=[r for r in lot['policies'] if r['arm']=='actual_credit'],fixed=lot['fixed'],replay=lot['replay'])),flush=True)
    return report

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--out',type=Path,default=ROOT/'audit_runs'/'adaptive');p.add_argument('--replicates',type=int,default=3);p.add_argument('--training-students',type=int,default=64);p.add_argument('--comparisons-per-context',type=int,default=8);p.add_argument('--test-students',type=int,default=160)
    a=p.parse_args();run(a.out,a.replicates,a.training_students,a.comparisons_per_context,a.test_students)
