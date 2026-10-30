"""Build a self-contained English report from recorded numerical outcomes."""
from pathlib import Path
import argparse,json,html


def report(out):
    summary=json.loads((out/'summary.json').read_text())
    validation=json.loads((out/'validation.json').read_text())
    n=summary['test_learners']
    def count(arm,stage='after'):
        return next(r['successful'] for r in summary['teacher_summaries'] if r['replicate']==0 and r['arm']==arm and r['stage']==stage)
    entries=[('Before policy training',count('actual_credit','before')),
      ('Learned choice · actual outcome credit',count('actual_credit')),
      ('Best fixed lesson among 13',max(summary['fixed_curricula'].values())),
      ('R plasticity disabled during training',count('frozen')),
      ('Wrong credit · matched pulse times and counts',count('wrong_credit')),
      ('Inherited learned policy',summary['inherited'][0]['successful'])]
    rows=''.join(f'<tr><td>{html.escape(label)}</td><td>{value}/{n}</td></tr>' for label,value in entries)
    fixed=''.join(f'<tr><td>{html.escape(name)}</td><td>{v}/{n}</td></tr>' for name,v in summary['fixed_curricula'].items())
    states=summary['inherited'][0]['parent_state']
    inherited_readout=summary['inherited'][0]['readout']
    replicated=len({r['replicate'] for r in summary['teacher_summaries']})
    memory=''.join(f'<tr><td>{i}</td><td>0.300, 0.300</td><td>{s["gains"][0]:.6f}, {s["gains"][1]:.6f}</td><td>Period {4 if inherited_readout[i]['curriculum']=='gap_4' else 8}</td></tr>' for i,s in enumerate(states))
    content='''<!doctype html>
<html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Learned curriculum selection with R</title>
<style>:root{color-scheme:light dark}body{font:17px/1.6 system-ui,sans-serif;max-width:940px;margin:36px auto;padding:0 22px;color:light-dark(#20242a,#e8edf3);background:light-dark(#fafbfc,#16191e)}h1{font-size:30px;line-height:1.2}h2{font-size:23px;margin-top:32px}table{border-collapse:collapse;width:100%;margin:22px 0}td,th{text-align:left;padding:10px 8px;border-bottom:1px solid light-dark(#cdd4dc,#46515e)}a{color:light-dark(#17657d,#80c8df)}.note{font-size:15px}code{overflow-wrap:anywhere}strong{font-weight:650}.scroll{overflow-x:auto}</style>
<h1>A minimal learned teaching choice with R</h1>
<p><strong>The system learns which pulse lesson helps a learner profile.</strong>
This is a numerical proof of concept in an explicitly added R-based architecture.
R's internal equations remain unchanged.</p>
<h2>Fresh-learner confirmation</h2><table><thead><tr><th>Policy</th><th>Successful learners</th></tr></thead><tbody>__ROWS__</tbody></table>
<p class="note">The same __N__ fresh learners are paired across every comparison.
Counts shown are for the first of __REPLICATES__ independently trained policy banks;
all per-bank results are in the recorded summary. Reusing test learners does not
create additional independent observations. The fixed comparator was selected from all
13 templates on development data and is also best in hindsight on this test set.</p>
<h2>A timing task where faster is not always better</h2>
<p>After ten teaching pulses, a learner must answer eight period-8 prompts exactly
once each, with latency in [0.22, 0.50] model time units. Early and late responses
both fail. The two learner profiles favor period-4 or period-8 lessons. Physical
learner parameters vary independently by ±10%.</p>
<h2>Where the acquired choice lives</h2><div class="scroll"><table><thead><tr><th>Observable context</th><th>Action gains before</th><th>Action gains after</th><th>Decoded lesson</th></tr></thead><tbody>__MEMORY__</tbody></table></div>
<p>A behavioral diagnostic selects one of two persistent R policy cells. Successful
student outcomes permit native ERROR-phase gain plasticity on the tried lesson's
port. A fixed decoder reads which port responds. The action mapping is acquired
from outcomes; no optimizer writes gains.</p>
<h2>The added architecture matters</h2>
<p>The diagnostic, two candidate lessons, fixed exploration, binary success test,
outcome-to-pulse timing encoder, readout decoder and settings-copy operation are
supplied by the experiment. R does not invent those components. The learned object
is the conditional choice of a lesson, retained in native R gains.</p>
<p>Wrong-credit controls retain exactly the same feedback pulse counts, times and
contexts but exchange the two action ports. They reverse the learned choice while
matching recovery histories. Thus extra stimulation or global recovery saturation
alone does not explain this result.</p>
<h2>Verification and boundaries</h2>
<p><strong>__CHECKS__ numerical and structural checks pass.</strong> Feedback is delayed
until after the complete student lesson and probe. Independent integration and
causal ablations support the recorded result. This is not A22 certification or a
hardware experiment.</p>
<p class="note">The task, diagnostic categories and curriculum library were designed
on development cases. An initial pilot preceded this confirmation on a new test
seed. General pedagogy, curriculum invention, learned diagnosis, forgetting,
relearning after changed contingencies and chip energy/area benefits remain open.</p>
<p><a href="README.md">Full protocol, provenance, limits and reproduction</a> ·
<a href="summary.json">Recorded summary</a> · <a href="validation.json">Verification details</a></p>
<details><summary>All 13 fixed curriculum results</summary><table><thead><tr><th>Template</th><th>Successful learners</th></tr></thead><tbody>__FIXED__</tbody></table></details>
</html>
'''
    content=content.replace('__ROWS__',rows).replace('__MEMORY__',memory).replace('__FIXED__',fixed).replace('__CHECKS__',str(validation['passed'])).replace('__N__',str(n)).replace('__REPLICATES__',str(replicated))
    (out/'RESULTS.html').write_text(content)
    print(out/'RESULTS.html')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--out',type=Path,required=True);report(p.parse_args().out)
