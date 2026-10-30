"""Run every primary pupil with a continuously retained native R teacher readout.

This is execution verification of the same test pupils, not another independent
sample. The actual trained memory bank is retained, then plasticity is frozen.
"""
from pathlib import Path
import argparse,json,hashlib
import numpy as np
import model as m


def advance(bank,target):
    if target<bank.t-1e-9:raise RuntimeError('teacher time cannot move backwards')
    while bank.t<target-1e-9:
        bank.process_external()
        boundary=min(target,bank.queue[0][0] if bank.queue else target)
        bank.advance(boundary)
    bank.process_external()


def query(bank,context,origin):
    latencies=[];events=[]
    for action in range(2):
        start=origin+action*20.;advance(bank,start)
        before=len(bank.outputs)
        bank.add(start,'on',(context,action,'native_policy_query'))
        bank.add(start+1.,'off',(context,action,'native_policy_query'))
        advance(bank,start+20.)
        outputs=[x['time']-start for x in bank.outputs[before:] if x['node']==context]
        latencies.append(outputs[0] if outputs else None)
        events.append(dict(action=action,absolute_start=start,relative_outputs=outputs))
    firing=[(latency,action) for action,latency in enumerate(latencies) if latency is not None]
    if not firing:choice=0
    else:
        earliest=min(t for t,_ in firing);choice=min(a for t,a in firing if t<=earliest+1e-7)
    return choice,events


def validate_live(out):
    training=json.loads((out/'training.json').read_text())
    policies=json.loads((out/'policies.json').read_text())
    evaluation=json.loads((out/'evaluation.json').read_text())
    # Execute training once more and retain this exact full q/m/z/b/E object.
    bank=m.MemoryBank(training[0]['trials'],'actual_credit');trained=bank.execute()
    reference=next(p for p in policies if p['replicate']==0 and p['arm']=='actual_credit')
    assert [x['action'] for x in m.read_bank(trained)]==reference['choices']
    training_end=bank.t;learned=bank.y[:,4:8].copy()
    bank.cfg['plastic']=False
    records=[];checks=[]
    for lot in evaluation:
        correct=0;pulses=0;equal=True;query_count=0
        for s in lot['students']:
            initial,_=m.make_learner(s['metadata']['seed']);device=initial;origin=bank.t;steps=[]
            for k in range(1,m.MAX_BLOCKS+1):
                device,observation=m.block(device)
                # Student teaching + assessment completes before either query.
                decision_start=origin+(k-1)*m.BLOCK_TIME+50.
                action,events=query(bank,observation['context'],decision_start)
                query_count+=2
                steps.append(dict(block=k,context=observation['context'],action=action,queries=events))
                if action==1 or k==m.MAX_BLOCKS:
                    # Evaluation outcome is computed only after the real STOP.
                    retained=m.probe(device);advance(bank,origin+k*m.BLOCK_TIME+80.)
                    break
            expected=m.select(s['path'],reference['choices'])
            equal &= k==expected['blocks'] and retained['success']==expected['retained']['success']
            correct+=retained['success'];pulses+=3*k
            records.append(dict(lot=lot['lot'],student=s['student'],origin=origin,blocks=k,
                                retained=retained,steps=steps))
        checks.append(dict(lot=lot['lot'],passed=bool(equal),learners=len(lot['students']),successful=correct,
                           student_pulses=pulses,native_teacher_query_pulses=query_count))
        print(json.dumps(checks[-1]),flush=True)
    memory_error=float(np.max(np.abs(bank.y[:,4:8]-learned)))
    result=dict(passed=all(c['passed'] for c in checks) and memory_error<1e-12,
      lots=checks,training_end_time=training_end,evaluation_end_time=bank.t,
      source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      teacher_memory_change_during_evaluation=memory_error,
      min_observed_teacher_reserve=bank.min_energy,
      retained_teacher='Same full q/m/z/b/E instance from training through all 320 evaluation pupils; no cell reset or settings copy',
      policy_weights='Frozen during evaluation; q/m/E and modes continue dynamically',
      accounting='Student pulses include teaching and assessments. Native teacher readout uses two additional query pulses per block; no joule or physical circuit cost is estimated.',
      records=records)
    (out/'live_validation.json').write_text(json.dumps(m.net.plain(result),indent=2)+'\n')
    if not result['passed']:raise RuntimeError('live readout mismatch')
    return result

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--out',type=Path,required=True);validate_live(p.parse_args().out)
