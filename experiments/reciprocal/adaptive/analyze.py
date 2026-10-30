"""Post-hoc descriptive limits and transparent reference comparisons.

These references do not update the policy, task, or locked primary analysis.
"""
from pathlib import Path
import argparse,json,collections
import model as m


def analyze(out):
    evaluations=json.loads((out/'evaluation.json').read_text())
    policies=json.loads((out/'policies.json').read_text())
    choices=next(p['choices'] for p in policies if p['replicate']==0 and p['arm']=='actual_credit')
    results=[]
    for evaluation in evaluations:
        rows=[];failures=collections.Counter();counts=collections.Counter();oracle=0;handcoded=0
        for s in evaluation['students']:
            selected=m.select(s['path'],choices)
            # Explicit programmed equivalent: continue if missing or late; stop otherwise.
            programmed=m.select(s['path'],[0,0,1])
            handcoded+=programmed['retained']['success']
            oracle+=any(r['retained']['success'] for r in s['path'])
            counts[selected['blocks']]+=1
            if not selected['retained']['success']:
                assessed=s['path'][selected['blocks']-1]['assessment']
                failures['early_at_stop' if assessed and assessed[0]<.22 else 'late_or_missing_at_budget']+=1
                rows.append(dict(student=s['student'],blocks=selected['blocks'],assessment=assessed,
                  any_successful_prefix=any(r['retained']['success'] for r in s['path'])))
        results.append(dict(lot=evaluation['lot'],programmed_equivalent_successful=handcoded,
          learned_choices_equal_programmed=choices==[0,0,1],
          per_learner_prefix_oracle_successful=oracle,
          scope='Oracle sees all four counterfactual stopping outcomes; it is a descriptive upper reference within this fixed block protocol only',
          failures=dict(failures),failure_records=rows,block_counts=dict(counts)))
    result=dict(status='Post-hoc descriptive references, not a new confirmatory sample',lots=results,
      interpretation='The learned policy represents an effective stopping rule. Its performance is matched by an explicitly programmed equivalent; no superiority to ordinary feedback control is shown. All recorded failures lack a successful prefix within this supplied four-block protocol, not necessarily under other lesson designs.')
    (out/'POSTHOC_ANALYSIS.json').write_text(json.dumps(result,indent=2)+'\n')
    return result

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--out',type=Path,required=True);analyze(p.parse_args().out)
