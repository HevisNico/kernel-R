#!/usr/bin/env python3
"""Paired contracts for constructed reverse source, weak and learned epochs."""
from pathlib import Path
import subprocess
import tempfile

from scripts.lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[2]
PREFIX = ('import KernelR.HybridReverseWeakStep\n'
          'import KernelR.HybridReverseCoupledLearnedTrain\n'
          'import KernelR.HybridReverseLatencyGeometry\n'
          'import KernelR.HybridReverseTeachingCompletion\n'
          'import KernelR.HybridBirthReverseTeaching\n'
          'open KernelR.Hybrid\n')


def cases():
    cycle = '''example {θ fresh forward backward source}
    (c : ReverseCoupledLearnedCycle θ fresh forward backward source) '''
    train = '''example {θ fresh forward backward source count later}
    (t : ReverseCoupledLearnedTrain θ fresh forward backward source count later) '''
    wire = '''example {θA θB forward backward source cycle}
    (r : ReverseSourceWire θA θB forward backward source cycle) '''
    weak = '''example {θA θB forward backward source cycle}
    {r : ReverseSourceWire θA θB forward backward source cycle} {later}
    (s : ReverseWeakStep r later) '''

    def pair(label, template, good, bad):
        assert '@v@' in template
        assert good != bad
        return label, template.replace('@v@', good), template.replace('@v@', bad)

    entry = '''example {θ forward backward start}
    {w : FeedbackWeakEntry θ (reciprocalEntryRouter forward backward) start}
    {f : FeedbackFirstFire w} {r : FirstReverseWiredArrival f}
    {p : FirstReverseInterleavedPair r} (e : ReverseEntryCompletion p) '''
    teaching = '''example {θ forward backward start}
    {w : FeedbackWeakEntry θ (reciprocalEntryRouter forward backward) start}
    {f : FeedbackFirstFire w} {r : FirstReverseWiredArrival f}
    {p : FirstReverseInterleavedPair r} (t : ReverseTeachingCompletion p) '''

    controls = [
        pair('learned reverse cycle completes at source plus eight', cycle +
             ': c.final.time=source.time+@v@ := by exact c.date\n', '8', '7'),
        pair('actual learned reverse cycle retains both ordered real FIREs', cycle +
             ': c.execution.ledger.emissions=@v@ := by exact c.emissions\n',
             '[(1,c.fireB),(0,c.fireA)]', '[(0,c.fireA)]'),
        pair('reverse wire is timed from its actual issuing B FIRE', cycle +
             ': c.wireTime=c.fireB+backward @v@ := by exact c.wire_date\n',
             'c.fireB', 'source.time'),
        pair('learned cycle does not consume the pending next source', cycle +
             ': c.final.pending=@v@ := by exact c.pending\n', 'source.pending', '[]'),
        pair('learned reverse response preserves each own acquired gain', cycle +
             '(i : Fin 2) (q : Port) : c.final.x i (.z q)=source.x i (.z q)@v@ := by exact c.gains i q\n',
             '', '+3/5'),
        pair('train active source plus n queued sources produces n plus one A outputs', train +
             ': (t.execution.emissionTimes 0).length=@v@ := by exact t.a_emission_count\n',
             'count+1', 'count'),
        pair('train keeps every real B output including the active source', train +
             ': (t.execution.emissionTimes 1).length=@v@ := by exact t.b_emission_count\n',
             'count+1', 'count+2'),
        pair('train horizon counts the already active input', train +
             ': t.final.time=source.time+8*((count:ℝ)+@v@) := by exact t.date\n', '1', '0'),
        pair('train B receiving calendar contains only actual next external sources', train +
             ': t.execution.cellDeliveries 1=sourceTrain 1 2 (source.time+8) 8 @v@ := by exact t.b_deliveries\n',
             'count', 'count+1'),
        pair('train derives one actual reverse wire for each emitting source', train +
             ': (t.execution.cellDeliveries 0).length=@v@ := by exact t.a_wire_count\n',
             'count+1', 'count'),
        pair('train wire provenance refers to the issuing B emission stream', train +
             ': ∀ time∈t.wireTimes, ∃ F∈t.execution.emissionTimes @v@, time=F+backward F := by exact t.wire_provenance\n',
             '1', '0'),
        pair('learned train introduces no protected MARK dose', train +
             '(i : Fin 2) (q : Port) : t.execution.ledger.mark i q=@v@ := by exact t.mark_zero i q\n',
             '0', '1/10'),
        pair('weak handoff reaches the real next eight-gap source date', weak +
             ': s.final.time=source.time+@v@ := by exact s.date\n', '8', '16'),
        pair('weak handoff consumes the actual next B source occurrence', weak +
             ': s.execution.deliveries=[⟨@v@,2,source.time+8⟩] := by exact s.deliveries\n', '1', '0'),
        pair('weak handoff retains the exact remaining global queue', weak +
             ': s.final.pending=@v@ := by exact s.pending\n', 'later', 'source.pending'),
        pair('actual receiving weak pulse learns one ERROR dose', weak +
             ': s.execution.ledger.error 0 2=@v@ := by exact s.a_error_dose\n', '3/5', '0'),
        pair('weak handoff retains carried charge rather than imposing exact rest', weak +
             ': 1/10 @v@ s.final.x 0 .q := by exact s.a_charge_lower\n', '≤', '='),
        pair('weak receiver energy is preserved from its real maximal cut', weak +
             ': s.final.x 0 .energy=@v@ := by exact congrFun s.a_values .energy\n',
             's.receiver.cut.state.x 0 .energy', '100'),
        pair('the new B RAW origin is the actual next source clock', weak +
             ': s.final.raw 1 2=some (@v@) := by exact s.raw_active\n',
             'source.time+8', 'r.final.time'),
        pair('weak receiver and sender return do not invent any FIRE', weak +
             ': s.execution.ledger.emissions=@v@ := by exact s.emissions\n',
             '[]', '[(0,source.time+8)]'),
        pair('guarded receiver transport retains the real B source FIRE', wire +
             ': r.execution.ledger.emissions=@v@ := by exact r.emissions\n',
             '[(1,cycle.fire.final.time)]', '[]'),
        pair('next reverse receipt samples delay at its own actual FIRE', wire +
             ': r.final.time=cycle.fire.final.time+backward @v@ := by exact r.date\n',
             'cycle.fire.final.time', 'source.time'),
        pair('next wire receipt retains actual sender energy at its FAST cut', wire +
             ': r.final.x 1 .energy=@v@ := by exact congrFun r.b_values .energy\n',
             'r.cutH.state.x 0 .energy', '100'),
        pair('first residual firing lower bound retains fresh wire jitter',
             '''example {first second d1 d2 : ℝ} (hf : first+8≤second)
    (h1 : 3/10≤d1 ∧ d1≤2/5) (h2 : 3/10≤d2 ∧ d2≤2/5) :
    first+d1+@v@≤second+d2 := by exact received_gap_of_firing_lower hf h1 h2
''', '79/10', '81/10'),
        pair('actual352 to376 path has its first real A return output', entry +
             ': (e.execution.emissionTimes 0).length=@v@ := by exact e.a_emission_count\n', '1', '2'),
        pair('actual352 to376 path retains three actual B source outputs', entry +
             ': (e.execution.emissionTimes 1).length=@v@ := by exact e.b_emission_count\n', '3', '2'),
        pair('two further weak A inputs contribute ERROR1.2 after352', entry +
             ''': e.execution.ledger.error 0 2=@v@ := by
  have h := e.execution.gain_balance 0 2
  rw [e.a_gain_target] at h
  linarith
''', '6/5', '9/5'),
        pair('actual376 entry preserves the own learned B gains', entry +
             '(q : Port) : e.final.x 1 (.z q)=p.final.x 1 (.z q)@v@ := by exact e.b_gains q\n',
             '', '+3/5'),
        pair('complete reciprocal suffix reaches the quiet459.9 endpoint', teaching +
             ': t.final.time=@v@ := by exact t.date\n', '4599/10', '448'),
        pair('the actual352 to459.9 suffix constructs ten A outputs', teaching +
             ': (t.execution.emissionTimes 0).length=@v@ := by exact t.a_emission_count\n', '10', '9'),
        pair('the actual352 to459.9 suffix constructs twelve B outputs', teaching +
             ': (t.execution.emissionTimes 1).length=@v@ := by exact t.b_emission_count\n', '12', '13'),
        pair('terminal queue retains all sixteen later B birth sources', teaching +
             ': t.final.pending=sourceTrain 1 2 480 8 @v@ := by exact t.pending\n', '16', '15'),
        pair('both terminal main modes are genuinely prepared', teaching +
             '(i : Fin 2) : t.final.main i=.@v@ := by exact (t.prepared i).ready\n', 'ready', 'slow'),
        pair('terminal main charges are exact own reopen roots', teaching +
             '(i : Fin 2) : t.final.x i .q=@v@ := by exact t.charge i\n', '1/10', '1/4'),
        pair('all RAW currents have physically expired at459.9', teaching +
             '(i : Fin 2) (q : Port) : t.final.raw i q=@v@ := by exact t.raw_none i q\n',
             'none', 'some t.final.time'),
    ]
    return controls + final_factory_cases()


def final_factory_cases():
    born = '''example {θ born fresh newborn forward backward}
    (t : ConstructedReverseTeaching θ born fresh newborn forward backward) '''
    factory = '''example {θ born fresh ε}
    (hborn : @BirthState 1 born) (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (ha : ∀ q, born.aux 0 q=.ready)
    (hqueue : born.pending=sourceTrain 0 0 0 8 16++sourceTrain 0 0 160 8 16)
    (newborn : Newborn) (forward backward : ℝ → ℝ)
    (hd : ∀ time, (3/10:ℝ)≤forward time ∧ forward time≤2/5)
    (hback : ∀ time, (3/10:ℝ)≤backward time ∧ backward time≤2/5) :
    ∃ t : ConstructedReverseTeaching θ born fresh newborn forward backward,
      t.final.time=@v@ ∧ t.final.pending.length=16 := by
  obtain ⟨t⟩ := birth_protocol_reverse_teaching_exists hborn hb ha hqueue newborn forward backward hd hback
  exact ⟨t,t.date,t.pending_length⟩
'''

    def pair(label, template, good, bad):
        assert '@v@' in template
        assert good != bad
        return label, template.replace('@v@', good), template.replace('@v@', bad)

    return [
        pair('original birth constructs the full459.9 epoch without a reaching trace',
             factory, '4599/10', '448'),
        pair('complete original-birth trace has cumulative A38', born +
             ': (t.staged.before.emissionTimes 0++t.staged.after.emissionTimes 0).length=@v@ := by exact t.a_emission_count\n',
             '38', '37'),
        pair('complete original-birth trace has cumulative B27', born +
             ': (t.staged.after.emissionTimes 1).length=@v@ := by exact t.b_emission_count\n',
             '27', '28'),
        pair('A reciprocal learning remains tied to its own original birth', born +
             ': t.final.x 0 (.z 2)=@v@+9/5 := by exact t.a_gain_target\n',
             'born.x 0 (.z 2)', 'newborn.x (.z 2)'),
        pair('B reciprocal learning remains tied to its independent own newborn', born +
             ': t.final.x 1 (.z 2)=@v@+9/5 := by exact t.b_gain_target\n',
             'newborn.x (.z 2)', 'born.x 0 (.z 2)'),
    ]


def main():
    controls = cases()
    with tempfile.TemporaryDirectory(prefix='hybrid-reverse-epoch-negative-', dir=ROOT) as tmp:
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

        check('\n'.join(good for _, good, _ in controls), True, 'valid reverse-epoch controls')
        for name, _, bad in controls:
            check(bad, False, name)
            print(f'{name}: physical conclusion accepted; altered claim rejected.', flush=True)


if __name__ == '__main__':
    main()
