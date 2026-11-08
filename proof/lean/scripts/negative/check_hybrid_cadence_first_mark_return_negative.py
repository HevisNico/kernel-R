#!/usr/bin/env python3
"""Paired actual global656/C660 and original-birth MARK-return contracts."""
from pathlib import Path
import subprocess
import tempfile

from scripts.lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[2]
PREFIX = '''import KernelR.HybridBirthCadenceFirstMarkReturn
open KernelR.Hybrid
noncomputable section
'''


def pair(label, template, good, bad):
    assert '@v@' in template
    assert good != bad
    return label, template.replace('@v@', good), template.replace('@v@', bad)


def cases():
    source = '''example {θ born freshB freshC newbornB newbornC forward backward delay}
    {c : ConstructedCTeaching θ born freshB freshC newbornB newbornC forward backward delay}
    {cascadeForward cascadeBackward} {w : ConstructedCadenceWarmup c cascadeForward cascadeBackward}
    {r : FirstCadenceWire w} {relay : FirstCadenceRelayWire r} {a : FirstCadenceAFire relay}
    (g : FirstCadenceMarkSource a) '''
    mark = '''example {θ born freshB freshC newbornB newbornC forward backward delay}
    {c : ConstructedCTeaching θ born freshB freshC newbornB newbornC forward backward delay}
    {cascadeForward cascadeBackward} {w : ConstructedCadenceWarmup c cascadeForward cascadeBackward}
    {r : FirstCadenceWire w} {relay : FirstCadenceRelayWire r} {a : FirstCadenceAFire relay}
    {g : FirstCadenceMarkSource a} (m : FirstCadenceMarkReturn g) '''
    born = '''example {θ born freshB freshC newbornB newbornC forward backward delay cascadeForward cascadeBackward}
    (c : ConstructedCadenceFirstMarkReturn θ born freshB freshC newbornB newbornC
      forward backward delay cascadeForward cascadeBackward) '''
    factory = '''example {θ born freshB freshC ε} (hborn : @BirthState 1 born)
    (hb : @PhysicalBox 3 (extendParameters (extendParameters θ freshB) freshC) ε)
    (ha : ∀ q, born.aux 0 q = .ready)
    (hqueue : born.pending = sourceTrain 0 0 0 8 16 ++ sourceTrain 0 0 160 8 16)
    (newbornB newbornC : Newborn) (forward backward delay cascadeForward cascadeBackward : ℝ → ℝ)
    (hforward : ∀ t, (3/10:ℝ) ≤ forward t ∧ forward t ≤ 2/5)
    (hback : ∀ t, (3/10:ℝ) ≤ backward t ∧ backward t ≤ 2/5)
    (hdelay : ∀ t, (3/10:ℝ) ≤ delay t ∧ delay t ≤ 2/5)
    (hcascadeForward : ∀ t, (3/10:ℝ) ≤ cascadeForward t ∧ cascadeForward t ≤ 2/5)
    (hcascadeBackward : ∀ t, (3/10:ℝ) ≤ cascadeBackward t ∧ cascadeBackward t ≤ 2/5) :
    ∃ c : ConstructedCadenceFirstMarkReturn θ born freshB freshC newbornB newbornC
      forward backward delay cascadeForward cascadeBackward,
      c.final.time = @v@ ∧ c.final.pending.length = 19 ∧
      c.final.x 2 (.z 0) = newbornC.x (.z 0) + 9/5 ∧
      c.final.x 2 .b = newbornC.x .b + 1/5 ∧ CompleteThrough c.execution 660 := by
  obtain ⟨c⟩ := birth_protocol_cadence_first_mark_return_exists hborn hb ha hqueue newbornB newbornC
    forward backward delay cascadeForward cascadeBackward hforward hback hdelay
    hcascadeForward hcascadeBackward
  exact ⟨c,c.date,c.pending_length,c.c_gain_own,c.c_recovery_own,c.complete⟩
'''
    return [
        pair('actual source656 leaves exactly twenty later C sources', source +
             ': g.final.pending = sourceTrain 2 0 660 4 @v@ := by exact g.pending\n', '20', '21'),
        pair('the global source656 token is actually consumed', source +
             ': g.execution.deliveries = [⟨2,0,@v@⟩] := by exact g.deliveries\n', '656', '660'),
        pair('C source656 retains the genuine SLOW carry lower bound', source +
             ': @v@ ≤ g.final.x 2 .q := by exact g.c_charge.1\n', '37/250', '1/4'),
        pair('C source656 RAW is fresh rather than inherited from652', source +
             ': g.final.raw 2 0 = some (@v@) := by rw [← g.date]; exact g.c_raw_active\n', '656', '652'),
        pair('C source656 energy is the actual retained SLOW endpoint', source +
             ': g.final.x 2 .energy = @v@ := by exact congrFun g.c_values .energy\n',
             'relay.cSpan.final.x 0 .energy', '100'),
        pair('A and B source656 energies are their actual retained cuts', source +
             ''': (g.final.x 0 .energy,g.final.x 1 .energy) = @v@ := by
  exact Prod.ext (congrFun g.a_values .energy) (congrFun g.b_values .energy)
''', '(g.aCut.state.x 0 .energy,g.bCut.state.x 0 .energy)', '(100,100)'),
        pair('the actual C660 source leaves exactly nineteen later sources', mark +
             ': m.final.pending = sourceTrain 2 0 664 4 @v@ := by exact m.pending\n', '19', '20'),
        pair('the first global MARK return produces no extra FIRE', mark +
             ': m.execution.ledger.emissions = @v@ := by exact m.emissions\n', '[]', '[(2,660)]'),
        pair('the source660 arrival is real and has its own current date', mark +
             ': m.execution.deliveries = [⟨2,0,@v@⟩] := by exact m.deliveries\n', '660', '656'),
        pair('C physically returns to the exact main rest charge at660', mark +
             ': m.final.x 2 .q = @v@ := by exact m.c_charge\n', '1/10', '1/4'),
        pair('C is really READY after its protected MARK return', mark +
             ': m.final.main 2 = .@v@ := by exact m.c_ready.ready\n', 'ready', 'slow'),
        pair('C RAW660 starts at the actual source660 arrival', mark +
             ': m.final.raw 2 0 = some (@v@) := by rw [← m.date]; exact m.c_raw_active\n', '660', '656'),
        pair('C energy at660 comes from the actual local MARK and quiet paths', mark +
             ': m.final.x 2 .energy = @v@ := by exact congrFun m.c_values .energy\n',
             'm.localSource.final.x 0 .energy', '100'),
        pair('A and B energies at660 preserve their real unfinished or returned paths', mark +
             ''': (m.final.x 0 .energy,m.final.x 1 .energy) = @v@ := by
  exact Prod.ext (congrFun m.a_values .energy) (congrFun m.b_values .energy)
''', '(m.aCut.state.x 0 .energy,m.bCut.state.x 0 .energy)', '(100,100)'),
        pair('the real C656 MARK dose is one tenth', mark +
             ': m.execution.ledger.mark 2 0 = @v@ := by exact m.c_mark\n', '1/10', '0'),
        pair('the protected C656 response adds no ERROR dose of three fifths', mark +
             ': m.execution.ledger.error 2 0 = @v@ := by exact m.error_zero 2 0\n', '0', '3/5'),
        pair('C recovery retains its own newborn memory rather than inheriting A memory', mark +
             ': m.final.x 2 .b = @v@ := by exact m.c_recovery_own\n',
             'newbornC.x .b + 1/5', 'born.x 0 .b + 1/5'),
        pair('C initial-port gain retains its own newborn coordinate', mark +
             ': m.final.x 2 (.z 0) = @v@ := by exact m.c_gain_target\n',
             'newbornC.x (.z 0) + 9/5', 'born.x 0 (.z 0) + 9/5'),
        pair('A gain is carried from A own current state rather than C state', mark +
             '(q : Port) : m.final.x 0 (.z q) = g.final.x @v@ (.z q) := by exact m.gains 0 q\n', '0', '2'),
        pair('only C receives the new MARK recovery increment', mark +
             '(i : Fin 3) (hi : i ≠ 2) : m.final.x i .b = g.final.x i .b@v@ := by exact m.recovery_other i hi\n', '', '+1/10'),
        pair('original birth constructs the complete actual C660 state without a reaching trace',
             factory, '660', '664'),
        pair('the original birth still has exactly cumulative A39 at660', born +
             ''': (c.wave.cadence.teaching.reverse.staged.before.emissionTimes 0 ++
      c.wave.cadence.teaching.reverse.staged.after.emissionTimes 0).length +
      (c.wave.cadence.teaching.staged.before.emissionTimes 0).length +
      (c.wave.cadence.teaching.staged.after.emissionTimes 0).length +
      (c.execution.emissionTimes 0).length = @v@ := by exact c.a_emission_count
''', '39', '40'),
        pair('the original birth still has exactly cumulative B44 at660', born +
             ''': (c.wave.cadence.teaching.reverse.staged.after.emissionTimes 1).length +
      (c.wave.cadence.teaching.staged.before.emissionTimes 1).length +
      (c.wave.cadence.teaching.staged.after.emissionTimes 1).length +
      (c.execution.emissionTimes 1).length = @v@ := by exact c.b_emission_count
''', '44', '45'),
        pair('the original birth still has exactly cumulative C15 at660', born +
             ''': (c.wave.cadence.teaching.staged.after.emissionTimes 2).length +
      (c.execution.emissionTimes 2).length = @v@ := by exact c.c_emission_count
''', '15', '16'),
    ]


def main():
    controls = cases()
    assert len(controls) == 24
    with tempfile.TemporaryDirectory(prefix='hybrid-cadence-first-mark-return-', dir=ROOT) as tmp:
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

        check('\n'.join(good for _, good, _ in controls), True, 'valid actual global656/C660 contracts')
        print('All24 positive actual global656/C660 contracts accepted.', flush=True)
        for name, _, bad in controls:
            check(bad, False, name)
            print(f'{name}: physical conclusion accepted; altered claim rejected.', flush=True)
        print(f'{len(controls)} paired actual global656/C660 controls passed.', flush=True)


if __name__ == '__main__':
    main()
