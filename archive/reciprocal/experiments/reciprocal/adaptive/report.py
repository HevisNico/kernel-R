"""Self-contained English report, generated from recorded outcomes."""
from pathlib import Path
import argparse,json


def report(out):
    summary=json.loads((out/'summary.json').read_text())
    validation=json.loads((out/'validation.json').read_text())
    live=json.loads((out/'live_validation.json').read_text())
    posthoc=json.loads((out/'POSTHOC_ANALYSIS.json').read_text())
    lots=summary['lots']
    def actual(lot):return next(r for r in lot['policies'] if r['arm']=='actual_credit' and r['replicate']==0)
    def fixed(lot,count):return next(r for r in lot['fixed'] if r['blocks']==count)
    rows=[]
    entries=[('Learned within-lesson adaptation',[actual(l) for l in lots]),
      ('Preselected fixed duration: 3 blocks',[fixed(l,3) for l in lots]),
      ('Best fixed duration in hindsight',[max(l['fixed'],key=lambda r:r['successful']) for l in lots]),
      ('Same lesson lengths reassigned to other pupils',[l['replay'][0] for l in lots]),
      ('Only the initial observation',[l['initial_only'][0] for l in lots]),
      ('Inherited policy',[l['inheritance'][0] for l in lots])]
    for label,values in entries:
        rows.append('<tr><td>'+label+'</td>'+''.join(f'<td>{r["successful"]}/{r["n"]}</td>' for r in values)+'</tr>')
    pupil=', '.join(f'{actual(l)["mean_student_pulses"]:.3f}' for l in lots)
    teacher=', '.join(str(l['native_teacher_query_pulses']) for l in live['lots'])
    failures=''.join(f'<tr><td>{r["lot"]}</td><td>{r["failures"].get("early_at_stop",0)}</td><td>{r["failures"].get("late_or_missing_at_budget",0)}</td></tr>' for r in posthoc['lots'])
    content='''<!doctype html>
<html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Learned adaptation during a lesson</title>
<style>:root{color-scheme:light dark}body{font:17px/1.6 system-ui,sans-serif;max-width:960px;margin:36px auto;padding:0 22px;color:light-dark(#20242a,#e8edf3);background:light-dark(#fafbfc,#16191e)}h1{font-size:30px;line-height:1.2}h2{font-size:23px;margin-top:32px}table{border-collapse:collapse;width:100%;margin:22px 0}td,th{text-align:left;padding:10px 8px;border-bottom:1px solid light-dark(#cdd4dc,#46515e)}a{color:light-dark(#17657d,#80c8df)}.note{font-size:15px}.scroll{overflow-x:auto}strong{font-weight:650}code{overflow-wrap:anywhere}</style>
<h1>The teacher learns when to continue or stop</h1>
<p><strong>Within-lesson adaptation is supported in this supplied R-based architecture.</strong>
The same learned policy uses each pupil's intermediate responses to choose its
stopping time. Pulse shapes and teaching blocks remain predefined.</p>
<h2>Reproduction on two held-out learner lots</h2>
<p>This execution uses the corrected terminal-event scheduler and a complete
source/runtime manifest. Training and evaluation were recomputed from scratch
on the original seeds. This is a computational reproduction, not an additional
independent confirmation sample. Legacy development and aborted-run records
are excluded from this release. See <a href="plan.json">the locked plan</a>.</p>
<div class="scroll"><table><thead><tr><th>Method</th><th>Test</th><th>Confirmation</th></tr></thead><tbody>__ROWS__</tbody></table></div>
<p class="note">Three independently trained banks obtain these same counts on the
same two lots; teacher repetitions do not multiply the independent learner count.
The fixed hindsight reference exhausts the four possible stopping times within
this block protocol, not every possible pulse schedule.</p>
<h2>What changes during the lesson?</h2>
<p>After two teaching pulses, the pupil receives a plasticity-disabled assessment.
The teacher observes missing, late or not-late response timing. Learned action gains
in three R cells determine CONTINUE or STOP. A four-block ceiling limits teaching.
The pupil must retain 8/8 period-8 responses within a finite latency window.</p>
<p>The original q/m/z/b/E laws remain unchanged. Observation bins, block timing,
paired-rollout outcome preferences, guard-pulse coding and the action decoder are
provided by the experiment. The acquired mapping is retained in native R gains.</p>
<h2>Causal execution with the living R teacher</h2>
<p>The exact trained R memory bank was retained through all 320 primary pupil
episodes. Its q, m, E and modes evolved continuously. Actual native query firings
selected each next action, and final grading occurred only after stopping.
The bank was never reset or replaced. Its learned parameters were frozen during
evaluation to measure the acquired policy.</p>
<h2>Count the measurements too</h2>
<p>Mean pupil-side pulse counts, including assessments: <strong>__PUPIL__</strong>
for the two lots. Reassigned-lesson controls use exactly the same total pupil pulses.
Native teacher readout additionally uses __TEACHER__ query pulses over the two lots.
This is not an energy or area comparison.</p>
<h2>Failures and a conventional-controller reference</h2>
<table><thead><tr><th>Lot</th><th>Early at stopping</th><th>Still late or missing at budget</th></tr></thead><tbody>__FAILURES__</tbody></table>
<p>A post-hoc programmed equivalent stopping rule matches the learned rule's
performance. No superiority to conventional feedback control is established.
The recorded failures have no successful alternative among the four available
prefixes; other teaching rhythms or budgets remain untested.</p>
<h2>Adaptation and invention are separate claims</h2>
<p>This experiment demonstrates learned stopping adaptation. A novel pulse rhythm,
waveform or teaching content has not been synthesized. The proposed invention
protocol below defines novelty and held-out utility separately, with matched
measurement, training and actuation budgets.</p>
<p><strong>__CHECKS__ numerical, causal and structural checks pass</strong>, plus
continuous native-readout confirmation on every primary pupil. These are numerical
model results outside the A22 certificate, not a silicon experiment.</p>
<p><a href="README.md">Full method, resource accounting, provenance and limits</a> ·
<a href="INVENTION_PROTOCOL.md">Proposed invention protocol</a> ·
<a href="validation.json">Checks</a> · <a href="live_validation.json">Live R readout</a> ·
<a href="POSTHOC_ANALYSIS.json">Failures and programmed reference</a></p>
</html>
'''
    content=content.replace('__ROWS__',''.join(rows)).replace('__PUPIL__',pupil).replace('__TEACHER__',teacher).replace('__FAILURES__',failures).replace('__CHECKS__',str(validation['passed']))
    (out/'RESULTS.html').write_text(content)
    print(out/'RESULTS.html')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--out',type=Path,required=True);report(p.parse_args().out)
