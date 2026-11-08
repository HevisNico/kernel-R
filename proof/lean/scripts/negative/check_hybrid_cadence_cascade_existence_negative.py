#!/usr/bin/env python3
"""Paired actual three-cell cascade existence, wiring and birth contracts."""
from pathlib import Path
import subprocess
import tempfile

from scripts.lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[2]
PREFIX = '''import KernelR.HybridBirthCadenceProtocol
open KernelR.Hybrid
noncomputable section
'''


def pair(label, template, good, bad):
    assert '@v@' in template and good != bad
    return label, template.replace('@v@', good), template.replace('@v@', bad)


def cases():
    core = '''example {θ born freshB freshC newbornB newbornC forward backward delay cascadeForward cascadeBackward}
    {c : ConstructedCadenceFirstMarkReturn θ born freshB freshC newbornB newbornC forward backward delay
      cascadeForward cascadeBackward} (g : ConstructedCadenceCascade c) '''
    birth = '''example {θ born freshB freshC newbornB newbornC forward backward delay cascadeForward cascadeBackward}
    (g : ConstructedBirthCadence θ born freshB freshC newbornB newbornC forward backward delay
      cascadeForward cascadeBackward) '''
    back = core + '''(backDelay : ℝ → ℝ)
    (hd : ∀ time, (3/10:ℝ)≤backDelay time ∧ backDelay time≤2/5) '''
    factory = '''example {θ born freshB freshC newbornB newbornC forward backward delay cascadeForward cascadeBackward ε}
    (c : ConstructedCadenceFirstMarkReturn θ born freshB freshC newbornB newbornC forward backward delay
      cascadeForward cascadeBackward)
    (hb : @PhysicalBox 3 (extendParameters (extendParameters θ freshB) freshC) ε)
    (hborn : BirthState born)
    (hf : ∀ t, (3/10:ℝ)≤cascadeForward t ∧ cascadeForward t≤2/5)
    (hbk : ∀ t, (3/10:ℝ)≤cascadeBackward t ∧ cascadeBackward t≤2/5) :
    ∃ g : ConstructedCadenceCascade c, g.final.time=@v@ ∧ g.final.pending=[] ∧
      (g.execution.emissionTimes 0).length=16 := by
  obtain ⟨g⟩ := constructed_cadence_cascade_exists c hb hborn hf hbk
  exact ⟨g,g.date,g.pending,g.a_emission_count⟩
'''
    born_factory = '''example {θ born freshB freshC ε}
    (hborn : @BirthState 1 born)
    (hb : @PhysicalBox 3 (extendParameters (extendParameters θ freshB) freshC) ε)
    (ha : ∀ q, born.aux 0 q=.ready)
    (hq : born.pending=sourceTrain 0 0 0 8 16++sourceTrain 0 0 160 8 16)
    (newbornB newbornC : Newborn) (forward backward delay cascadeForward cascadeBackward : ℝ → ℝ)
    (hf : ∀ t, (3/10:ℝ)≤forward t ∧ forward t≤2/5)
    (hbw : ∀ t, (3/10:ℝ)≤backward t ∧ backward t≤2/5)
    (hd : ∀ t, (3/10:ℝ)≤delay t ∧ delay t≤2/5)
    (hcf : ∀ t, (3/10:ℝ)≤cascadeForward t ∧ cascadeForward t≤2/5)
    (hcb : ∀ t, (3/10:ℝ)≤cascadeBackward t ∧ cascadeBackward t≤2/5) :
    ∃ g : ConstructedBirthCadence θ born freshB freshC newbornB newbornC forward backward delay
      cascadeForward cascadeBackward, g.final.time=@v@ ∧ g.final.pending=[] ∧
      (∀ i q, g.final.raw i q=none) := by
  obtain ⟨g⟩ := birth_protocol_cadence_cascade_exists hborn hb ha hq newbornB newbornC
    forward backward delay cascadeForward cascadeBackward hf hbw hd hcf hcb
  exact ⟨g,g.date,g.pending,g.raw_none⟩
'''
    proto = birth.replace('ConstructedBirthCadence θ', 'ConstructedBirthCadenceProtocol θ')
    proto_factory = born_factory.replace('ConstructedBirthCadence θ', 'ConstructedBirthCadenceProtocol θ').replace(
        'birth_protocol_cadence_cascade_exists', 'birth_protocol_complete_cadence_exists').replace(
        '(∀ i q, g.final.raw i q=none)', 'CompleteThrough g.staged.after (7899/10)').replace(
        'g.pending,g.raw_none', 'g.pending,g.complete')
    return [
        pair('core factory constructs the complete cadence without a reaching premise', factory, '7899/10', '660'),
        pair('original-birth factory constructs both later independent births and cadence', born_factory, '7899/10', '6399/10'),
        pair('actual global terminal date is789point9', core+
             ': g.final.time=@v@ := by exact g.date\n', '7899/10', '740'),
        pair('all actual external and wire tokens are consumed', core+
             ': g.final.pending=@v@ := by exact g.pending\n', '[]', 'sourceTrain 2 0 736 4 1'),
        pair('all three physical endpoints are READY', core+
             '(i : Fin 3) : g.final.main i=@v@ := by exact (g.ready i).ready\n', '.ready', '.slow'),
        pair('all three endpoint charges are proved exact rest', core+
             '(i : Fin 3) : g.final.x i .q=@v@ := by exact g.charge i\n', '1/10', '1'),
        pair('no endpoint RAW survives the actual completion', core+
             '(i : Fin 3) (q : Port) : g.final.raw i q=@v@ := by exact g.raw_none i q\n', 'none', 'some g.final.time'),
        pair('complete-through applies to the real global789point9 execution', core+
             ': CompleteThrough g.execution (@v@) := by exact g.complete\n', '7899/10', '660'),
        pair('physical validity uses the three cells own parameter families', core+
             ': PhysicalInvariant (extendParameters (extendParameters θ @v@) freshC) g.final := by exact g.physical\n', 'freshB', 'freshC'),
        pair('constructed cadence has sixteen actual A outputs', core+
             ': (g.execution.emissionTimes 0).length=@v@ := by exact g.a_emission_count\n', '16', '18'),
        pair('constructed cadence has eighteen actual B outputs', core+
             ': (g.execution.emissionTimes 1).length=@v@ := by exact g.b_emission_count\n', '18', '20'),
        pair('constructed cadence has twenty actual C outputs', core+
             ': (g.execution.emissionTimes 2).length=@v@ := by exact g.c_emission_count\n', '20', '19'),
        pair('A target gain retains its own original birth memory', core+
             ': g.final.x 0 (.z 2)=@v@+12/5 := by exact g.a_gain_target\n', 'born.x 0 (.z 2)', 'newbornB.x (.z 2)'),
        pair('B target gain retains its independent newborn memory', core+
             ': g.final.x 1 (.z 2)=@v@+12/5 := by exact g.b_gain_target\n', 'newbornB.x (.z 2)', 'born.x 0 (.z 2)'),
        pair('C target gain retains its own independent newborn memory', core+
             ': g.final.x 2 (.z 0)=@v@+12/5 := by exact g.c_gain_target\n', 'newbornC.x (.z 0)', 'newbornB.x (.z 0)'),
        pair('A recovery includes three real MARK doses', core+
             ': g.final.x 0 .b=born.x 0 .b+@v@ := by exact g.a_recovery\n', '3/10', '1/5'),
        pair('B recovery starts from its own independent newborn', core+
             ': g.final.x 1 .b=@v@+3/10 := by exact g.b_recovery\n', 'newbornB.x .b', 'born.x 0 .b'),
        pair('C recovery starts from its own independent newborn', core+
             ': g.final.x 2 .b=@v@+3/10 := by exact g.c_recovery\n', 'newbornC.x .b', 'newbornB.x .b'),
        pair('A other-port memories retain their actual teaching values', core+
             '(q : Port) (hq : q≠2) : g.final.x 0 (.z q)=c.wave.cadence.teaching.final.x @v@ (.z q) := by exact g.a_gain_other q hq\n', '0', '1'),
        pair('B other-port memories retain their actual teaching values', core+
             '(q : Port) (hq : q≠2) : g.final.x 1 (.z q)=c.wave.cadence.teaching.final.x @v@ (.z q) := by exact g.b_gain_other q hq\n', '1', '0'),
        pair('C other-port memories retain their actual teaching values', core+
             '(q : Port) (hq : q≠0) : g.final.x 2 (.z q)=c.wave.cadence.teaching.final.x @v@ (.z q) := by exact g.c_gain_other q hq\n', '2', '1'),
        pair('A final work is the retained local physical endpoint', core+
             ': g.final.x 0 .energy=@v@ := by rw [g.final_state]; rfl\n', 'g.aRun.final.x 0 .energy', '100'),
        pair('B final work is retained from the real BC weave', core+
             ': g.final.x 1 .energy=@v@ := by rw [g.final_state]; rfl\n', 'g.bc.final.x 0 .energy', '100'),
        pair('C final work is retained from the real BC weave', core+
             ': g.final.x 2 .energy=@v@ := by rw [g.final_state]; rfl\n', 'g.bc.final.x 1 .energy', '100'),
        pair('shared initial BC queue contains only the twenty-five external C sources', core+
             ': g.bc.source.pending=sourceTrain 1 0 640 4 @v@ := by exact g.bc.source_pending\n', '25', '45'),
        pair('initial B energy is the actual teaching-boundary value', core+
             ': g.bc.source.x 0 .energy=@v@ := by exact congrFun (g.bc.source_x 0) .energy\n', 'c.wave.cadence.teaching.final.x 1 .energy', '100'),
        pair('initial C energy is the actual teaching-boundary value', core+
             ': g.bc.source.x 1 .energy=@v@ := by exact congrFun (g.bc.source_x 1) .energy\n', 'c.wave.cadence.teaching.final.x 2 .energy', '100'),
        pair('twenty B inputs are issued by actual C FIREs in the shared execution', core+
             ''': g.bc.execution.issuedTo 0=List.ofFn (fun i : Fin @v@ =>
    (⟨0,2,g.bc.bPacket.actual i.val⟩ : Delivery 2)) := by exact g.bc.issued_b_tokens
''', '20', '21'),
        pair('eighteen actual B outputs supply exactly eighteen A analysis tokens', back+
             ''': g.bc.returnTokens backDelay=List.ofFn (fun i : Fin @v@ =>
    (⟨0,2,(g.bc.receivedBPacket backDelay hd).actual i.val⟩ : Delivery 1)) := by
  exact g.bc.return_tokens_received_calendar backDelay hd
''', '18', '19'),
        pair('return delay is sampled at each actual B FIRE', back+
             '''(i : Fin 18) : (g.bc.receivedBPacket backDelay hd).actual i.val=
    g.bc.outputPacket.actual i.val+backDelay (@v@) := by exact g.bc.received_b_actual backDelay hd i.val
''', 'g.bc.outputPacket.actual i.val', '640+4*(i.val:ℝ)'),
        pair('A analysis queue is derived from the actual remaining BC FIRE ledger', core+
             ': g.aSource.pending=@v@ := by exact g.a_head_queue\n',
             'g.bc.execution.headInputQueue (cadenceAContacts cascadeBackward)', '[]'),
        pair('global A output calendar is the actual constructed local response ledger', core+
             ': g.execution.emissionTimes 0=@v@ := by exact g.a_emission_times\n', 'g.aRun.execution.emissionTimes 0', '[]'),
        pair('global B output calendar is preserved by the outer causal weave', core+
             ': g.execution.emissionTimes 1=@v@ := by exact g.b_emission_times\n', 'g.bc.execution.emissionTimes 0', '[]'),
        pair('global C output calendar is preserved through both causal weaves', core+
             ': g.execution.emissionTimes 2=@v@ := by exact g.c_emission_times\n', 'g.bc.execution.emissionTimes 1', '[]'),
        pair('two physical delay errors produce the proved point1 A jitter budget', back+
             ': KernelR.Chain.Packet 5 13 (@v@) := g.bc.receivedBPacket backDelay hd\n', '1/10', '1/20'),
        pair('original-birth cumulative A count is fifty-four', birth+
             ''': (g.entry.wave.cadence.teaching.reverse.staged.before.emissionTimes 0++
    g.entry.wave.cadence.teaching.reverse.staged.after.emissionTimes 0).length+
    (g.entry.wave.cadence.teaching.staged.before.emissionTimes 0).length+
    (g.entry.wave.cadence.teaching.staged.after.emissionTimes 0).length+
    (g.execution.emissionTimes 0).length=@v@ := by exact g.a_emission_count
''', '54', '39'),
        pair('original-birth cumulative B count is sixty-one', birth+
             ''': (g.entry.wave.cadence.teaching.reverse.staged.after.emissionTimes 1).length+
    (g.entry.wave.cadence.teaching.staged.before.emissionTimes 1).length+
    (g.entry.wave.cadence.teaching.staged.after.emissionTimes 1).length+
    (g.execution.emissionTimes 1).length=@v@ := by exact g.b_emission_count
''', '61', '44'),
        pair('original-birth cumulative C count is thirty-four', birth+
             ''': (g.entry.wave.cadence.teaching.staged.after.emissionTimes 2).length+
    (g.execution.emissionTimes 2).length=@v@ := by exact g.c_emission_count
''', '34', '15'),
        pair('public birth wrapper preserves the independently born C gain', birth+
             ': g.final.x 2 (.z 0)=@v@+12/5 := by exact g.c_gain_own\n', 'newbornC.x (.z 0)', 'born.x 0 (.z 0)'),
        pair('public birth wrapper certifies the actual completed789point9 execution', birth+
             ': CompleteThrough g.execution (@v@) := by exact g.complete\n', '7899/10', '6399/10'),
        pair('public fixed-router protocol factory constructs the complete physical history',
             proto_factory, '7899/10', '6399/10'),
        pair('actual staged protocol cumulatively contains fifty-four A FIREs', proto+
             ''': (g.cadence.entry.wave.cadence.teaching.reverse.staged.before.emissionTimes 0++
    g.cadence.entry.wave.cadence.teaching.reverse.staged.after.emissionTimes 0).length+
    (g.staged.before.emissionTimes 0).length+(g.staged.after.emissionTimes 0).length=@v@ := by
  exact g.a_emission_count
''', '54', '53'),
        pair('actual staged protocol cumulatively contains sixty-one B FIREs', proto+
             ''': (g.cadence.entry.wave.cadence.teaching.reverse.staged.after.emissionTimes 1).length+
    (g.staged.before.emissionTimes 1).length+(g.staged.after.emissionTimes 1).length=@v@ := by
  exact g.b_emission_count
''', '61', '60'),
        pair('actual staged protocol contains thirty-four C FIREs after its real birth', proto+
             ': (g.staged.after.emissionTimes 2).length=@v@ := by exact g.c_emission_count\n', '34', '33'),
        pair('fixed-router concatenation keeps both physical ledgers', proto+
             ''': g.staged.after.ledger=g.cadence.entry.wave.cadence.teaching.staged.after.ledger.add @v@ := by
  exact g.after_ledger
''', 'g.cadence.execution.ledger', 'Ledger.zero'),
        pair('fixed-router concatenation preserves actual receiving order', proto+
             ''': g.staged.after.deliveries=g.cadence.entry.wave.cadence.teaching.staged.after.deliveries++@v@ := by
  exact g.after_deliveries
''', 'g.cadence.execution.deliveries', '[]'),
        pair('one fixed gated router governs the whole three-cell post-birth execution', proto+
             ''': Execution (extendParameters (extendParameters θ freshB) freshC)
    (@v@) g.staged.afterBirth g.final := g.staged.after
''', 'teachingCadenceRouter delay cascadeForward cascadeBackward',
             'cadenceRouter cascadeForward cascadeBackward'),
        pair('between-births execution retains the actual reverse suffix and teaching prefix', proto+
             ''': HEq g.betweenBirths (@v@) := by exact HEq.rfl
''', 'g.cadence.entry.wave.cadence.teaching.reverse.staged.after.append g.staged.before', 'g.staged.before'),
    ]


def main():
    controls = cases()
    assert len(controls) == 48
    with tempfile.TemporaryDirectory(prefix='hybrid-cadence-cascade-', dir=ROOT) as tmp:
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

        check('\n'.join(good for _, good, _ in controls), True, 'valid cadence-cascade controls')
        print(f'All {len(controls)} positive cadence-cascade contracts accepted.', flush=True)
        for name, _, bad in controls:
            check(bad, False, name)
            print(f'{name}: physical conclusion accepted; altered claim rejected.', flush=True)
        print(f'{len(controls)} paired cadence-cascade controls passed.', flush=True)


if __name__ == '__main__':
    main()
