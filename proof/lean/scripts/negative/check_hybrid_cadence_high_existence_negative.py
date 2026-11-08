#!/usr/bin/env python3
"""Paired genuine high-gain cadence FIRE and unfinished protected completion."""
from pathlib import Path
import subprocess
import tempfile

from scripts.lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[2]
PREFIX = '''import KernelR.HybridCadenceHighCompletion
open KernelR.Hybrid
noncomputable section
'''


def pair(label, template, good, bad):
    assert '@v@' in template
    assert good != bad
    return label, template.replace('@v@', good), template.replace('@v@', bad)


def cases():
    fire = '''example {θ : Fin 1 → Parameters} {s : Snapshot 1} {p : Port}
    (f : CadenceHighFire θ (fun _ _ => []) s 0 p) '''
    complete = fire + '(c : CadenceHighCompletion f) '
    factory = '''example {θ ε} (hb : PhysicalBox θ ε) (s : Snapshot 1) (p : Port)
    (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (hs : CadenceReadyCoordinates s 0 (8/25)) (hq : 1/10≤s.x 0 .q)
    (hg : 16/5≤Real.exp (s.x 0 (.z p)) ∧ Real.exp (s.x 0 (.z p))≤7/2)
    (hB : 37999/100000≤s.x 0 .b ∧ s.x 0 .b≤38001/100000)
    (hr : s.raw 0 p=some s.time) (ho : ∀ q,q≠p→s.raw 0 q=none)
    (hp : ∀ d∈s.pending,s.time+4≤d.due) :
    ∃ f : CadenceHighFire θ (fun _ _ => []) s 0 p,
      ∃ c : CadenceHighCompletion f,
      (f.execution.emissionTimes 0).length=@v@ ∧
      c.final.time=s.time+4 ∧ c.final.x 0 .q=1/10 ∧
      c.final.pending=s.pending ∧ c.execution.ledger.emissions=[] := by
  obtain ⟨f⟩ := cadence_high_fire_exists hb s p hf hv hs hq hg hr ho hp
  obtain ⟨c⟩ := f.high_completion_exists hb hs hB ho hp
  exact ⟨f,c,f.emission_count,c.date,c.charge,
    c.pending.trans (by simpa only [List.append_nil] using f.pending),c.emissions⟩
'''
    return [
        pair('actual high factory constructs a complete response without a reaching execution', factory, '1', '0'),
        pair('own four-dose gain supplies a physical high amplitude lower bound',
             '''example {z : ℝ}
    (hz : Real.log (3/10)+12/5-1/100000≤z ∧ z≤Real.log (3/10)+12/5+1/100000) :
    @v@≤Real.exp z := by exact (cadence_four_dose_gain_bounds hz).1
''', '16/5', '7/2'),
        pair('high carried root lies strictly after sixteen hundredths', fire +
             ': s.time+@v@<f.final.time := by exact f.window.1\n', '4/25', '3/10'),
        pair('high carried root lies strictly before twenty-six hundredths', fire +
             ': f.final.time<s.time+@v@ := by exact f.window.2\n', '13/50', '4/25'),
        pair('high root retains its real source charge', fire +
             ': readyPulse @v@ (Real.exp (s.x 0 (.z p))) s.time (s.time+f.latency)=1 := by exact f.response_root\n',
             '(s.x 0 .q)', '(1/10)'),
        pair('actual high FIRE enters FAST without a READY replacement', fire +
             ': f.final.main 0=.@v@ := by exact f.main_fast\n', 'fast', 'ready'),
        pair('sensor is still SILENT at the actual high FIRE', fire +
             ': f.final.aux 0 p=.@v@ := by exact f.aux_silent\n', 'silent', 'error'),
        pair('actual high FIRE contributes exactly one emitted occurrence', fire +
             ': (f.execution.emissionTimes 0).length=@v@ := by exact f.emission_count\n', '1', '2'),
        pair('high pre-FIRE path remains neutral for global weaving', fire +
             ': f.portBeforeExecution.ledger.emissions=@v@ := by exact f.portBefore_emissions\n',
             '[]', '[(0,f.final.time)]'),
        pair('high FIRE keeps its actual source RAW origin', fire +
             ': f.final.raw 0 p=@v@ := by exact f.raw_active\n', 'some s.time', 'none'),
        pair('high FIRE preserves every own acquired gain', fire +
             '(q : Port) : f.final.x 0 (.z q)=s.x 0 (.z q)@v@ := by exact f.gain_preserved 0 q\n', '', '+3/5'),
        pair('high FIRE preserves the own acquired recovery', fire +
             ': f.final.x 0 .b=s.x 0 .b@v@ := by exact f.recovery_preserved 0\n', '', '+1/10'),
        pair('high completion really reaches the fourth-period endpoint', complete +
             ': c.final.time=s.time+@v@ := by exact c.date\n', '4', '8'),
        pair('protected completion has no extra emitted occurrence', complete +
             ': c.execution.ledger.emissions=@v@ := by exact c.emissions\n', '[]', '[(0,c.final.time)]'),
        pair('protected completion consumes no future source before the next constructor', complete +
             ': c.execution.deliveries=@v@ := by exact c.deliveries\n', '[]', '[⟨0,p,c.final.time⟩]'),
        pair('protected completion retains the exact future source queue', complete +
             ': c.final.pending=@v@ := by exact c.pending\n', 'f.final.pending', '[]'),
        pair('real SLOW reopen leaves exact resting charge', complete +
             ': c.final.x 0 .q=@v@ := by exact c.charge\n', '1/10', '1/4'),
        pair('real completion returns the main mode to READY', complete +
             ': c.final.main 0=.@v@ := by exact (c.ready 0).ready\n', 'ready', 'slow'),
        pair('real completion returns all auxiliary ports to READY', complete +
             '(q : Port) : c.final.aux 0 q=.@v@ := by exact (c.auxiliary_rest q).1\n', 'ready', 'error'),
        pair('source RAW is actually expired by the next source boundary', complete +
             '(q : Port) : c.final.raw 0 q=@v@ := by exact c.raw_none 0 q\n', 'none', 'some s.time'),
        pair('ERROR under FAST or SLOW does not add a fictitious gain dose', complete +
             '(q : Port) : c.final.x 0 (.z q)=f.final.x 0 (.z q)@v@ := by exact c.gains 0 q\n', '', '+3/5'),
        pair('high protected continuation retains its own recovery', complete +
             ': c.final.x 0 .b=f.final.x 0 .b@v@ := by exact c.recovery 0\n', '', '+1/10'),
        pair('actual reopen happens before the variable-gap margin', complete +
             ': c.returned.returnState.time<s.time+@v@ := by exact c.return_deadline\n', '19/5', '3'),
        pair('energy is the endpoint of the same actual return path', complete +
             ': c.final.x 0 .energy=@v@ := by rw [c.returned_final]\n',
             'c.returned.final.x 0 .energy', 'f.final.x 0 .energy'),
        pair('the actual reopen prefix ends in READY before quiet waiting', complete +
             ': c.returned.returnState.main 0=.@v@ := by exact (c.return_ready 0).ready\n', 'ready', 'slow'),
        pair('the actual reopen prefix has its exact physical rest charge', complete +
             ': c.returned.returnState.x 0 .q=@v@ := by exact c.return_charge\n', '1/10', '1/4'),
        pair('the actual reopen prefix has already expired every RAW current', complete +
             '(q : Port) : c.returned.returnState.raw 0 q=@v@ := by exact c.return_raw_none 0 q\n', 'none', 'some s.time'),
        pair('the actual reopen prefix retains the complete future queue', complete +
             ': c.returned.returnState.pending=@v@ := by exact c.return_pending\n', 'f.final.pending', '[]'),
        pair('the actual reopen prefix preserves own acquired gains', complete +
             '(q : Port) : c.returned.returnState.x 0 (.z q)=f.final.x 0 (.z q)@v@ := by exact c.return_gains 0 q\n', '', '+3/5'),
        pair('the actual reopen prefix preserves own acquired recovery', complete +
             ': c.returned.returnState.x 0 .b=f.final.x 0 .b@v@ := by exact c.return_recovery 0\n', '', '+1/10'),
        pair('the actual protected prefix adds no extra output before its quiet tail', complete +
             ': c.returnExecution.ledger.emissions=@v@ := by exact c.return_emissions\n', '[]', '[(0,c.returned.returnState.time)]'),
        pair('the actual protected prefix consumes no future source', complete +
             ': c.returnExecution.deliveries=@v@ := by exact c.return_deliveries\n', '[]', '[⟨0,p,c.returned.returnState.time⟩]'),
    ]


def main():
    controls = cases()
    with tempfile.TemporaryDirectory(prefix='hybrid-cadence-high-existence-', dir=ROOT) as tmp:
        path = Path(tmp) / 'Check.lean'
        command = lean_check_command(tmp)

        def check(source, expected, name):
            path.write_text(PREFIX + source)
            result = subprocess.run([*command, str(path)], cwd=ROOT, text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=180)
            if (result.returncode == 0) != expected:
                raise SystemExit(f'{name}: unexpected result:\n{result.stdout}')
            if not expected and 'error:' not in result.stdout:
                raise SystemExit(f'{name}: failed without a Lean diagnostic:\n{result.stdout}')

        check('\n'.join(good for _, good, _ in controls), True, 'valid high-cadence controls')
        print(f'All {len(controls)} positive high-cadence contracts accepted.', flush=True)
        for name, _, bad in controls:
            check(bad, False, name)
            print(f'{name}: valid conclusion accepted; altered claim rejected.', flush=True)
        print(f'{len(controls)} paired high-cadence existence controls passed.', flush=True)


if __name__ == '__main__':
    main()
