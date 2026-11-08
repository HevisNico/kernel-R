#!/usr/bin/env python3
"""Paired physical contracts for C's constructed birth and teaching epoch.

The valid contracts are checked together before each altered conclusion is
rejected in isolation. A rejected snippet must produce a Lean diagnostic.
"""
from pathlib import Path
import subprocess
import tempfile

from scripts.lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[2]
PREFIX = '''import KernelR.HybridBirthCTeaching
import KernelR.HybridCLearnedEpoch
import KernelR.HybridGuardedPortSourceWire
open KernelR.Hybrid
'''


def pair(label, template, good, bad):
    assert '@v@' in template
    assert good != bad
    return label, template.replace('@v@', good), template.replace('@v@', bad)


def cases():
    birth = '''example {θ born freshB newbornB forward backward}
    {t : ConstructedReverseTeaching θ born freshB newbornB forward backward}
    {freshC newbornC delay} (c : ConstructedCBirth t freshC newbornC delay) '''
    weak = '''example {θ s p C} (w : ReadyWeakCut θ s p C) '''
    guarded = '''example {θS θR route source pS cycle pR delay}
    (r : @GuardedPortSourceWire θS θR route source pS cycle pR delay) '''
    first = '''example {θS θR route source pS cycle pR delay}
    {r : @PortSourceWire θS θR route source pS cycle pR delay} {later}
    (p : PortFirstLearnedCut r later) '''
    slow = '''example {θS θR route source pS cycle pR delay}
    {r : @PortSourceWire θS θR route source pS cycle pR delay} {later}
    {p : PortFirstLearnedCut r later} (w : PortSlowWire p) '''
    protected = '''example {θS θR route source pS cycle pR delay}
    {r : @PortSourceWire θS θR route source pS cycle pR delay} {later}
    {p : PortFirstLearnedCut r later} {w : PortSlowWire p} {laterNext}
    (t : PortProtectedReturn w laterNext) '''
    prepared = '''example {θ born freshB newbornB forward backward}
    {t : ConstructedReverseTeaching θ born freshB newbornB forward backward}
    {freshC newbornC delay} {c : ConstructedCBirth t freshC newbornC delay}
    {w : CWeakEntry c} {p : CFirstLearnedBoundary w} (x : CPreparedPair p) '''
    cycle = '''example {θS θR route source pS pR delay}
    (c : PortCoupledLearnedCycle θS θR route source pS pR delay) '''
    train = '''example {θS θR route source pS pR delay count later}
    (t : PortCoupledLearnedTrain θS θR route source pS pR delay count later) '''
    epoch = '''example {θB θC delay source} (e : CLearnedEpoch θB θC delay source) '''
    teaching = '''example {θ born freshB newbornB forward backward}
    {t : ConstructedReverseTeaching θ born freshB newbornB forward backward}
    {freshC newbornC delay} {c : ConstructedCBirth t freshC newbornC delay}
    {w : CWeakEntry c} {p : CFirstLearnedBoundary w} {x : CPreparedPair p}
    (e : CTeachingPair x) '''
    return [
        pair('actual C birth retains forty-one pending sources before B480', birth +
             ': c.afterBirth.pending.length=@v@ := by exact c.after_pending_length\n', '41', '40'),
        pair('actual B480 arrival consumes exactly one of those sources', birth +
             ': c.final.pending.length=@v@ := by exact c.pending_length\n', '40', '41'),
        pair('C own birth recovery remains the low newborn band', birth +
             ': @v@/25-1/100000≤c.final.x 2 .b ∧ c.final.x 2 .b≤@v@/25+1/100000 := by exact c.c_recovery\n', '2', '9/2'),
        pair('C is ready but its own low recovery is not prepared', birth +
             ': ¬ @v@ c.final 2 := by exact c.c_not_prepared\n', 'PreparedSection', 'ReadyCoordinates'),
        pair('birth preserves every original cell gain', birth +
             '(i : Fin 2) (q : Port) : c.final.x i.castSucc (.z q)=@v@ := by exact c.old_gains i q\n',
             't.final.x i (.z q)', 'newbornC.x (.z q)'),
        pair('birth uses C own independent energy and coordinates', birth +
             ': c.final.x 2=@v@ := by exact c.c_coordinates\n', 'newbornC.x', 'newbornB.x'),
        pair('B480 is an actual queued external delivery without a FIRE', birth +
             ': c.staged.after.deliveries=[⟨@v@,2,480⟩] := by exact c.after_deliveries\n', '1', '2'),
        pair('quiet head reconstruction retains the exact actual A energy', birth +
             ': (c.activePair.prependQuiet c.quietA).x @v@ .energy=c.final.x 0 .energy := by rw [c.active_pair_reconstruct]\n',
             '0', '1'),
        pair('quiet head mapping retains the whole actual global queue', birth +
             ': c.final.pending=c.activePair.pending.map @v@ := by exact c.active_pair_queue_map\n',
             'Delivery.succ', '(fun d => (⟨0,d.port,d.due⟩ : Delivery 3))'),
        pair('weak cut learns one full real ERROR dose', weak +
             ': w.cut.cut.ledger.error 0 p=@v@ := by exact w.cut_error_dose\n', '3/5', '0'),
        pair('weak cut keeps its own newborn recovery', weak +
             ': w.cut.state.x 0 .b=s.x 0 .b@v@ := by exact w.cut_recovery\n', '', '+1/10'),
        pair('weak cut retains carried charge with the newborn lower band', weak +
             ': 1/10-1/100000 @v@ w.cut.state.x 0 .q := by exact w.cut_charge_lower\n', '≤', '='),
        pair('weak cut never invents an output', weak +
             ': w.cut.cut.ledger.emissions=@v@ := by exact w.cut_emissions\n', '[]', '[(0,C)]'),
        pair('weak continuation matches actual charge without resetting to rest', weak +
             '(T : ℝ) : (quietAt w.cut.state T).x 0 .q=@v@ := by exact w.quiet_after_cut_charge_identity T\n',
             'relax (1/2) (1/10) (w.weak.final.x 0 .q) w.weak.final.time T', '1/10'),
        pair('guarded wire samples the delay at its actual issuing FIRE', guarded +
             ': r.final.time=cycle.fire.final.time+delay @v@ := by exact r.date\n', 'cycle.fire.final.time', 'source.time'),
        pair('guarded wire retains the actual sender FIRE', guarded +
             ': r.execution.ledger.emissions=@v@ := by exact r.emissions\n', '[(0,cycle.fire.final.time)]', '[]'),
        pair('guarded wire carries actual sender FAST-cut energy', guarded +
             ': r.final.x 0 .energy=@v@ := by exact congrFun r.sender_values .energy\n', 'r.cutH.state.x 0 .energy', '100'),
        pair('guarded wire needs ready only at actual receipt for conversion', guarded +
             '''(h : ReadyCoordinates (quietAt (portSourceReceiver source) r.final.time) 0) :
    (r.to_portSourceWire h).final=@v@ := by rfl
''', 'r.final', 'source'),
        pair('first learned receiver output is a real right-cell FIRE', first +
             ': p.execution.ledger.emissions=[(@v@,p.fire.final.time)] := by exact p.emissions\n', '1', '0'),
        pair('first learned receiver remains genuinely SLOW at next source', first +
             ': p.final.main 1=.@v@ := by exact p.receiver_main\n', 'slow', 'ready'),
        pair('first learned cut carries the low-SLOW span energy', first +
             ': p.final.x 1 .energy=@v@ := by exact congrFun p.receiver_values .energy\n', 'p.lowSpan.final.x 0 .energy', '100'),
        pair('first learned cut preserves its own recovery', first +
             ': p.final.x 1 .b=r.final.x 1 .b@v@ := by exact p.recovery 1\n', '', '+1/10'),
        pair('next wire lower spacing includes fresh delay jitter', slow +
             ': r.final.time+@v@≤w.final.time := by exact w.receiving_gap.1\n', '79/10', '81/10'),
        pair('next wire upper spacing includes fresh delay jitter', slow +
             ': w.final.time≤r.final.time+@v@ := by exact w.receiving_gap.2\n', '81/10', '79/10'),
        pair('third receiving input meets the actual protected SLOW charge', slow +
             ': @v@<w.final.x 1 .q ∧ w.final.x 1 .q<4/25 := by exact w.receiver_charge\n', '7/50', '4/25'),
        pair('third input remains a real fresh right-port token', slow +
             ': w.final.raw 1 pR=some @v@ := by exact w.raw_active\n', 'w.final.time', 'p.final.time'),
        pair('protected return contributes MARK one tenth', protected +
             ': t.execution.ledger.mark 1 pR=@v@ := by exact t.mark_dose\n', '1/10', '0'),
        pair('protected return introduces no ERROR', protected +
             '(i : Fin 2) (q : Port) : t.execution.ledger.error i q=@v@ := by exact t.error_zero i q\n', '0', '3/5'),
        pair('protected return preserves every acquired own gain', protected +
             '(i : Fin 2) (q : Port) : t.final.x i (.z q)=w.final.x i (.z q)@v@ := by exact t.gains i q\n', '', '+3/5'),
        pair('protected return raises only receiver own recovery by one tenth', protected +
             ': t.final.x 1 .b=w.final.x 1 .b+@v@ := by exact t.receiver_recovery\n', '1/10', '3/5'),
        pair('C prepared boundary consumes actual B504 and retains Q37', prepared +
             ': x.final.pending.length=@v@ := by exact x.pending_length\n', '37', '38'),
        pair('C own protected recovery remains tied to its newborn', prepared +
             ': x.final.x 1 .b=@v@+1/10 := by exact x.c_recovery\n', 'newbornC.x .b', 'newbornB.x .b'),
        pair('learned cycle retains both real ordered cell FIREs', cycle +
             ': c.execution.ledger.emissions=@v@ := by exact c.emissions\n',
             '[(0,c.senderCycle.fire.final.time),(1,c.receiverCycle.fire.final.time)]',
             '[(0,c.senderCycle.fire.final.time)]'),
        pair('learned cycle completes at the actual eight-gap boundary', cycle +
             ': c.final.time=source.time+@v@ := by exact c.date\n', '8', '7'),
        pair('train counts the active source in sender outputs', train +
             ': (t.execution.emissionTimes 0).length=count+@v@ := by exact t.a_emission_count\n', '1', '0'),
        pair('train counts every genuine receiver response', train +
             ': (t.execution.emissionTimes 1).length=count+@v@ := by exact t.b_emission_count\n', '1', '2'),
        pair('train retains the exact later queued sources', train +
             ': t.final.pending=@v@ := by exact t.pending\n', 'later', '[]'),
        pair('train wire provenance comes from real sender FIREs', train +
             ': ∀ H∈t.wireTimes, ∃ F∈t.execution.emissionTimes @v@, H=F+delay F := by exact t.wire_provenance\n', '0', '1'),
        pair('learned epoch constructs thirteen actual B outputs', epoch +
             ': (e.execution.emissionTimes 0).length=@v@ := by exact e.b_emission_count\n', '13', '12'),
        pair('learned epoch constructs thirteen actual C outputs', epoch +
             ': (e.execution.emissionTimes 1).length=@v@ := by exact e.c_emission_count\n', '13', '14'),
        pair('learned epoch reaches quiet639.9 by a physical wait', epoch +
             ': e.final.time=@v@ := by exact e.date\n', '6399/10', '608'),
        pair('learned epoch retains all twenty-five own later C sources', epoch +
             ': e.final.pending=sourceTrain @v@ 0 640 4 25 := by exact e.pending\n', '1', '0'),
        pair('learned epoch preserves learned memories through the wait', epoch +
             '(i : Fin 2) (q : Port) : e.final.x i (.z q)=source.x i (.z q)@v@ := by exact e.gains i q\n', '', '+3/5'),
        pair('whole C teaching suffix constructs sixteen actual B outputs', teaching +
             ': (e.execution.emissionTimes 0).length=@v@ := by exact e.b_emission_count\n', '16', '15'),
        pair('whole C teaching suffix constructs fourteen actual C outputs', teaching +
             ': (e.execution.emissionTimes 1).length=@v@ := by exact e.c_emission_count\n', '14', '13'),
    ] + final_factory_cases()


def final_factory_cases():
    born = '''example {θ born freshB freshC newbornB newbornC forward backward delay}
    (t : ConstructedCTeaching θ born freshB freshC newbornB newbornC forward backward delay) '''
    factory = '''example {θ born freshB freshC ε}
    (hborn : @BirthState 1 born)
    (hb : @PhysicalBox 3 (extendParameters (extendParameters θ freshB) freshC) ε)
    (ha : ∀ q, born.aux 0 q=.ready)
    (hqueue : born.pending=sourceTrain 0 0 0 8 16++sourceTrain 0 0 160 8 16)
    (newbornB newbornC : Newborn) (forward backward delay : ℝ → ℝ)
    (hd : ∀ time, (3/10:ℝ)≤forward time ∧ forward time≤2/5)
    (hback : ∀ time, (3/10:ℝ)≤backward time ∧ backward time≤2/5)
    (hdelay : ∀ time, (3/10:ℝ)≤delay time ∧ delay time≤2/5) :
    ∃ t : ConstructedCTeaching θ born freshB freshC newbornB newbornC forward backward delay,
      t.final.time=@v@ ∧ t.final.pending.length=25 ∧
      t.final.x 2 (.z 1)=newbornC.x (.z 1)+3/5 ∧
      t.final.x 2 .b=newbornC.x .b+1/10 ∧
      t.lifted.ledger.emissions=t.teaching.execution.ledger.emissions.map (fun ev => (ev.1.succ,ev.2)) ∧
      PhysicalInvariant (extendParameters (extendParameters θ freshB) freshC) t.final := by
  obtain ⟨t⟩ := birth_protocol_c_teaching_exists hborn hb ha hqueue newbornB newbornC
    forward backward delay hd hback hdelay
  exact ⟨t,t.date,t.pending_length,t.c_gain_target,t.c_recovery,t.lifted_emissions,t.physical⟩
'''
    return [
        pair('original birth constructs physical639.9 with Q25 and mapped real outputs without reaching',
             factory, '6399/10', '608'),
        pair('whole original-birth trace retains cumulative A38', born +
             ''': (t.reverse.staged.before.emissionTimes 0++t.reverse.staged.after.emissionTimes 0).length+
    (t.staged.before.emissionTimes 0).length+(t.staged.after.emissionTimes 0).length=@v@ := by exact t.a_emission_count
''', '38', '39'),
        pair('whole original-birth trace constructs cumulative B43', born +
             ''': (t.reverse.staged.after.emissionTimes 1).length+(t.staged.before.emissionTimes 1).length+
    (t.staged.after.emissionTimes 1).length=@v@ := by exact t.b_emission_count
''', '43', '42'),
        pair('whole original-birth trace constructs fourteen real C outputs', born +
             ': (t.staged.after.emissionTimes 2).length=@v@ := by exact t.c_emission_count\n', '14', '15'),
        pair('C learned gain remains tied to its own independent newborn', born +
             ': t.final.x 2 (.z 1)=@v@+3/5 := by exact t.c_gain_target\n',
             'newbornC.x (.z 1)', 'newbornB.x (.z 1)'),
    ]


def main():
    controls = cases()
    with tempfile.TemporaryDirectory(prefix='hybrid-c-teaching-negative-', dir=ROOT) as tmp:
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

        check('\n'.join(good for _, good, _ in controls), True, 'valid C teaching controls')
        for name, _, bad in controls:
            check(bad, False, name)
            print(f'{name}: physical conclusion accepted; altered claim rejected.', flush=True)
        print(f'{len(controls)} paired C teaching controls passed.', flush=True)


if __name__ == '__main__':
    main()
