#!/usr/bin/env python3
"""Paired proof contracts for the autonomous C continuation after real C660.

These controls concern the actual isolated C path; they do not advance A/B.
"""
from pathlib import Path
import subprocess
import tempfile

from lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[1]
PREFIX = '''import KernelR.HybridBirthCadenceLocalCTail
open KernelR.Hybrid
noncomputable section
'''


def pair(label, template, good, bad):
    assert '@v@' in template and good != bad
    return label, template.replace('@v@', good), template.replace('@v@', bad)


def cases():
    high = '''example {θ s n later} (h : LocalCadenceHighTrain θ s n later) '''
    high18 = '''example {θ s} (h : LocalCadenceHighTrain θ s 17 []) '''
    tail = '''example {θ s} (t : LocalCadenceTail θ s) '''
    birth = '''example {θ born freshB freshC newbornB newbornC forward backward delay cascadeForward cascadeBackward}
    {c : ConstructedCadenceFirstMarkReturn θ born freshB freshC newbornB newbornC
      forward backward delay cascadeForward cascadeBackward}
    (t : LocalCadenceTail (fun _ : Fin 1 => freshC) c.localCSource) '''
    return [
        pair('high train includes the active source in its eighteen FIREs', high18+
             ': (h.execution.emissionTimes 0).length=@v@ := by exact h.emission_count\n', '18', '17'),
        pair('generic high train counts active plus queued sources', high+
             ': (h.execution.emissionTimes 0).length=@v@ := by exact h.emission_count\n', 'n+1', 'n'),
        pair('first high latency remains the actual carried-charge latency', high+
             ''': h.execution.emissionTimes 0=(@v@) ::
      (sourceTrain (0 : Fin 1) 0 (s.time+4) 4 n).map
        (fun d => d.due+highRestLatency (Real.exp (s.x 0 (.z 0)))) := by exact h.calendar
''', 'h.first.final.time', 's.time+highRestLatency (Real.exp (s.x 0 (.z 0)))'),
        pair('first high latency is bounded rather than reset to the rest root', high+
             ': h.first.latency @v@ highRestLatency (Real.exp (s.x 0 (.z 0))) := by exact h.first_latency_le_rest\n', '≤', '='),
        pair('seventeen later high roots use the same own gain memory', high18+
             ''': h.execution.emissionTimes 0=h.first.final.time ::
      (sourceTrain (0 : Fin 1) 0 (s.time+4) 4 17).map
        (fun d => d.due+@v@) := by exact h.calendar
''', 'highRestLatency (Real.exp (s.x 0 (.z 0)))', 'h.first.latency'),
        pair('active high source is not delivered a second time', high+
             ': h.execution.deliveries=sourceTrain 0 0 (s.time+4) 4 (@v@) := by exact h.deliveries\n', 'n', 'n+1'),
        pair('last high response completes at740', tail+
             ': t.high.final.time=@v@ := by exact t.high_date\n', '740', '736'),
        pair('C660 tail adds nineteen FIREs including its second strong response', tail+
             ': (t.execution.emissionTimes 0).length=@v@ := by exact t.emission_count\n', '19', '20'),
        pair('tail consumes all nineteen actual future C source tokens', tail+
             ': t.execution.deliveries=sourceTrain 0 0 664 4 @v@ := by exact t.deliveries\n', '19', '18'),
        pair('tail exhausts the pending queue', tail+
             ': t.final.pending=@v@ := by exact t.pending\n', '[]', 's.pending'),
        pair('final main mode is genuinely READY', tail+
             ': t.final.main 0=@v@ := by exact (t.ready 0).ready\n', '.ready', '.slow'),
        pair('final quiet charge is the rest value', tail+
             ': t.final.x 0 .q=@v@ := by exact t.charge\n', '1/10', '1/4'),
        pair('final RAW is absent after all actual expiries', tail+
             ': t.final.raw 0 0=@v@ := by exact t.raw_none 0 0\n', 'none', 'some t.final.time'),
        pair('quiet tail reaches the exact789point9 endpoint', tail+
             ': t.final.time=@v@ := by exact t.date\n', '7899/10', '740'),
        pair('only the mixed ERROR adds one own gain dose after660', tail+
             ': t.final.x 0 (.z 0)=s.x 0 (.z 0)+@v@ := by exact t.gain_target\n', '3/5', '9/5'),
        pair('other port memories retain their own source660 values', tail+
             '(q : Port) (hq : q≠0) : t.final.x 0 (.z q)=s.x 0 (.z q)@v@ := by exact t.gain_other q hq\n', '', '+3/5'),
        pair('mixed MARK adds one recovery dose after660', tail+
             ': t.final.x 0 .b=s.x 0 .b+@v@ := by exact t.recovery_gain\n', '1/10', '1/5'),
        pair('complete horizon includes the real quiet endpoint', tail+
             ': CompleteThrough t.execution (@v@) := by exact t.complete\n', '7899/10', '740'),
        pair('second strong SLOW energy is the actual continued flow energy', tail+
             ''': t.second.slow.final.x 0 .energy=@v@ := by exact t.second.slow.energy_clock
''', 'protectedMainValues θ t.second.fast.final 0 0 .slow .ready none (s.time+4) 0 .energy', '100'),
        pair('high train preserves the mixed response own gain', tail+
             ': t.high.final.x 0 (.z 0)=t.source668.final.x 0 (.z 0)@v@ := by exact t.high.gains 0 0\n', '', '+3/5'),
        pair('quiet extension adds no invented delivery', tail+
             ': t.wait.deliveries=@v@ := by exact t.wait_deliveries\n', '[]', '[⟨0,0,740⟩]'),
        pair('birth wrapper starts from the actual C660 section', birth+
             ': c.localCSource.time=@v@ := by exact c.local_c_source_date\n', '660', '664'),
        pair('C own gain remains tied to its newborn after four doses', birth+
             ': t.final.x 0 (.z 0)=@v@+12/5 := by exact t.c_gain_own\n', 'newbornC.x (.z 0)', 'newbornB.x (.z 0)'),
        pair('C own recovery retains all three actual MARK doses', birth+
             ': t.final.x 0 .b=newbornC.x .b+@v@ := by exact t.c_recovery_own\n', '3/10', '1/5'),
        factory_case(),
    ]


def factory_case():
    template = '''example {θ born freshB freshC ε}
    (hborn : @BirthState 1 born)
    (hb : @PhysicalBox 3 (extendParameters (extendParameters θ freshB) freshC) ε)
    (ha : ∀ q, born.aux 0 q=.ready)
    (hqueue : born.pending=sourceTrain 0 0 0 8 16++sourceTrain 0 0 160 8 16)
    (newbornB newbornC : Newborn) (forward backward delay cascadeForward cascadeBackward : ℝ→ℝ)
    (hforward : ∀ t, (3/10:ℝ)≤forward t ∧ forward t≤2/5)
    (hback : ∀ t, (3/10:ℝ)≤backward t ∧ backward t≤2/5)
    (hdelay : ∀ t, (3/10:ℝ)≤delay t ∧ delay t≤2/5)
    (hcf : ∀ t, (3/10:ℝ)≤cascadeForward t ∧ cascadeForward t≤2/5)
    (hcb : ∀ t, (3/10:ℝ)≤cascadeBackward t ∧ cascadeBackward t≤2/5) :
    ∃ c : ConstructedCadenceFirstMarkReturn θ born freshB freshC newbornB newbornC
      forward backward delay cascadeForward cascadeBackward,
    ∃ t : LocalCadenceTail (fun _ : Fin 1 => freshC) c.localCSource,
      t.final.time=7899/10 ∧ t.final.pending=[] ∧
      t.final.x 0 (.z 0)=newbornC.x (.z 0)+12/5 ∧
      t.final.x 0 .b=newbornC.x .b+3/10 ∧
      (c.wave.cadence.teaching.staged.after.emissionTimes 2).length+
        (c.execution.emissionTimes 2).length+(t.execution.emissionTimes 0).length=@v@ ∧
      PhysicalInvariant (fun _ : Fin 1 => freshC) t.final := by
  obtain ⟨c⟩ := birth_protocol_cadence_first_mark_return_exists hborn hb ha hqueue
    newbornB newbornC forward backward delay cascadeForward cascadeBackward
    hforward hback hdelay hcf hcb
  obtain ⟨t⟩ := c.local_c_tail_exists hb
  exact ⟨c,t,t.date,t.pending,t.c_gain_own,t.c_recovery_own,t.cumulative_c_emission_count,t.physical⟩
'''
    return pair('original-birth factory reaches local C34 without a supplied execution', template, '34', '33')


def main():
    controls = cases()
    assert len(controls) == 25
    with tempfile.TemporaryDirectory(prefix='hybrid-local-cadence-tail-', dir=ROOT) as tmp:
        path = Path(tmp)/'Check.lean'
        command = lean_check_command(tmp)

        def check(source, expected, name):
            path.write_text(PREFIX+source)
            result = subprocess.run([*command, str(path)], cwd=ROOT, text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=180)
            if (result.returncode == 0) != expected:
                raise SystemExit(f'{name}: unexpected result:\n{result.stdout}')
            if not expected and not any(marker in result.stdout for marker in ('error:', 'error(')):
                raise SystemExit(f'{name}: failed without a Lean diagnostic:\n{result.stdout}')

        check('\n'.join(good for _,good,_ in controls), True, 'valid local C cadence tail controls')
        print(f'All {len(controls)} positive local C tail contracts accepted.', flush=True)
        for name,_,bad in controls:
            check(bad, False, name)
            print(f'{name}: physical conclusion accepted; altered claim rejected.', flush=True)
        print(f'{len(controls)} paired local C cadence tail controls passed.', flush=True)


if __name__ == '__main__':
    main()
