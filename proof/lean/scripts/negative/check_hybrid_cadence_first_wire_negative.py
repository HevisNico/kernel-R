#!/usr/bin/env python3
"""Paired actual-global cadence warmup, wire and local-bridge contracts."""
from pathlib import Path
import subprocess
import tempfile

from scripts.lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[2]
CORE_PREFIX = '''import KernelR.HybridBirthCadenceFirstWire
import KernelR.HybridNeutralFutureFrame
open KernelR.Hybrid
noncomputable section
'''
BRIDGE_PREFIX = '''import KernelR.HybridBirthLearnedRest
open KernelR.Hybrid
noncomputable section
'''
PREFIX = '''import KernelR.HybridBirthCadenceFirstWire
import KernelR.HybridNeutralFutureFrame
import KernelR.HybridBirthLearnedRest
open KernelR.Hybrid
noncomputable section
'''


def pair(label, template, good, bad):
    assert '@v@' in template
    assert good != bad
    return label, template.replace('@v@', good), template.replace('@v@', bad)


def cases():
    warm = '''example {θ born freshB freshC newbornB newbornC forward backward delay}
    {c : ConstructedCTeaching θ born freshB freshC newbornB newbornC forward backward delay}
    {cascadeForward cascadeBackward} (w : ConstructedCadenceWarmup c cascadeForward cascadeBackward) '''
    wire = '''example {θ born freshB freshC newbornB newbornC forward backward delay}
    {c : ConstructedCTeaching θ born freshB freshC newbornB newbornC forward backward delay}
    {cascadeForward cascadeBackward} {w : ConstructedCadenceWarmup c cascadeForward cascadeBackward}
    (r : FirstCadenceWire w) '''
    frame = '''example {n θ route s u} (e : @Execution n θ route s u)
    (he : e.ledger.emissions=[]) (future : List (Delivery n))
    (hf : ∀ d∈future, u.time≤d.due) '''
    return [
        pair('global warmup produces no output from any of the three real cells', warm +
             ': w.execution.ledger.emissions=@v@ := by exact w.emissions\n', '[]', '[(2,652)]'),
        pair('global warmup consumes exactly the four actual C external sources', warm +
             ': w.execution.deliveries=@v@ := by exact w.deliveries\n',
             '[⟨2,0,640⟩,⟨2,0,644⟩,⟨2,0,648⟩,⟨2,0,652⟩]',
             '[⟨2,0,640⟩,⟨2,0,644⟩,⟨2,0,648⟩]'),
        pair('global warmup retains twenty-one later C sources in exact order', warm +
             ': w.final.pending=sourceTrain 2 0 656 4 @v@ := by exact w.pending\n', '21', '22'),
        pair('fresh C RAW originates at the actual current source652', warm +
             ': w.final.raw 2 0=some (@v@) := by rw [←w.date]; exact w.raw_active\n', '652', '648'),
        pair('global warmup ERROR learning adds1.8 to C own entry gain', warm +
             ': w.final.x 2 (.z 0)=c.final.x 2 (.z 0)+@v@ := by exact w.c_gain_target\n', '9/5', '6/5'),
        pair('global warmup preserves every own recovery memory', warm +
             '(i : Fin 3) : w.final.x i .b=c.final.x i .b@v@ := by exact w.recovery i\n', '', '+1/10'),
        pair('actual quiet A and B retain their exact main rest roots', warm +
             ': w.final.x 0 .q=@v@ ∧ w.final.x 1 .q=@v@ := by exact ⟨w.a_charge,w.b_charge⟩\n', '1/10', '1/4'),
        pair('C carried main charge has its actual stage-three upper cap', warm +
             ': w.final.x 2 .q≤@v@ := by exact w.c_coordinates.charge.2\n', '3/10', '1/10'),
        pair('C carried charge is bounded below without an artificial reset', warm +
             ': 1/10 @v@ w.final.x 2 .q := by exact w.c_charge_lower\n', '≤', '='),
        pair('global warmup C energy is the actual local physical endpoint', warm +
             ': w.final.x 2 .energy=@v@ := by rw [w.final_state]; rfl\n',
             'w.localWarmup.final.x 0 .energy', '100'),
        pair('future frame preserves the complete actual physical ledger', frame +
             ''': ∃ lifted : Execution θ route (appendPending s future) (appendPending u future),
    lifted.ledger=@v@ := by
  obtain ⟨lifted,hL,hD⟩ := e.appendFuture_neutral he future hf
  exact ⟨lifted,hL⟩
''', 'e.ledger', 'Ledger.zero'),
        pair('future frame retains every real delivery occurrence', frame +
             ''': ∃ lifted : Execution θ route (appendPending s future) (appendPending u future),
    lifted.deliveries=@v@ := by
  obtain ⟨lifted,hL,hD⟩ := e.appendFuture_neutral he future hf
  exact ⟨lifted,hD⟩
''', 'e.deliveries', '[]'),
        pair('already issued token framing appends after the old queue', frame +
             ': (appendPending s future).pending=@v@ := by rfl\n', 's.pending++future', 'future++s.pending'),
        pair('already issued token framing does not replace physical coordinates', frame +
             ': (appendPending s future).x=@v@ := by rfl\n', 's.x', 'u.x'),
        pair('first cadence wire is issued by the real global C FIRE', wire +
             ': r.execution.ledger.emissions=[(@v@,r.fire.final.time)] := by exact r.emissions\n', '2', '1'),
        pair('first cadence wire is really consumed by B port2', wire +
             ': r.execution.deliveries=[⟨@v@,2,r.final.time⟩] := by exact r.deliveries\n', '1', '0'),
        pair('first consumed wire leaves only the exact twenty-one later C sources', wire +
             ': r.final.pending=sourceTrain 2 0 656 4 @v@ := by exact r.pending\n', '21', '20'),
        pair('first wire delay is sampled at its actual issuing C threshold', wire +
             ': r.final.time=r.fire.final.time+cascadeForward @v@ := by exact r.date\n',
             'r.fire.final.time', 'w.final.time'),
        pair('actual first cadence receipt lower bound retains fresh jitter', wire +
             ': @v@<r.final.time := by exact r.window.1\n', '6527/10', '6533/10'),
        pair('actual first cadence receipt upper bound retains fresh jitter', wire +
             ': r.final.time<@v@ := by exact r.window.2\n', '6533/10', '6527/10'),
        pair('B receiver remains truly prepared after the actual wire delivery', wire +
             ': r.final.main 1=.@v@ := by exact r.b_prepared.ready\n', 'ready', 'slow'),
        pair('B receiver charge is its own exact rest root', wire +
             ': r.final.x 1 .q=@v@ := by exact r.b_charge\n', '1/10', '1/4'),
        pair('B port2 RAW is fresh at the actual receiving clock', wire +
             ': r.final.raw 1 2=some (@v@) := by exact r.b_raw_active\n',
             'r.final.time', 'r.fire.final.time'),
        pair('actual global wire preserves every own acquired gain', wire +
             '(i : Fin 3) (q : Port) : r.final.x i (.z q)=w.final.x i (.z q)@v@ := by exact r.gains i q\n', '', '+3/5'),
        pair('actual global wire preserves every own recovery memory', wire +
             '(i : Fin 3) : r.final.x i .b=w.final.x i .b@v@ := by exact r.recovery i\n', '', '+1/10'),
        pair('C FAST energy is retained from the actual cut rather than replaced', wire +
             ': r.final.x 2 .energy=@v@ := by exact congrFun r.c_values .energy\n',
             'r.cutH.state.x 0 .energy', '100'),
        pair('C RAW history is exactly its actual FAST prefix history', wire +
             '(q : Port) : r.final.raw 2 q=@v@ := by exact r.c_raw q\n',
             'r.cutH.state.raw 0 q', 'none'),
        pair('A energy follows its own actual quiet solution through the wire', wire +
             ': r.final.x 0 .energy=@v@ := by exact congrFun r.a_values .energy\n',
             '(quietAt w.start.quietA r.final.time).x 0 .energy', '100'),
        pair('global completion is certified at the real receipt clock', wire +
             ': CompleteThrough r.execution @v@ := by exact r.complete\n',
             'r.final.time', 'r.fire.final.time'),
    ] + bridge_cases() + final_factory_cases()


def bridge_cases():
    bridge = '''example {θ born freshB freshC newbornB newbornC forward backward delay}
    (c : ConstructedCTeaching θ born freshB freshC newbornB newbornC forward backward delay) '''
    boxed = bridge + '''{ε} (hb : @PhysicalBox 3 (extendParameters (extendParameters θ freshB) freshC) ε) '''
    return [
        pair('analysis projection preserves every actual energy coordinate', bridge +
             '(i : Fin 3) : (c.final.learnedProjection i).x 0 .energy=@v@ := by rfl\n',
             'c.final.x i .energy', '100'),
        pair('isolated A learned projection has exact rest charge and no RAW', bridge +
             '''(hborn : BirthState born) (q : Port) :
    (c.final.learnedProjection 0).x 0 .q=@v@ ∧ (c.final.learnedProjection 0).raw 0 q=none := by
  exact ⟨(c.a_learned_rest hborn).charge 0,(c.a_learned_rest hborn).raw 0 q⟩
''', '1/10', '1/4'),
        pair('isolated B learned domain uses the sharp1.9 gain ceiling', bridge +
             ': Real.exp ((c.final.learnedProjection 1).x 0 (.z 2))≤@v@ := by exact (c.b_learned_rest.gain 0).2\n',
             '19/10', '9/5'),
        pair('isolated A pulse contract has the actual7.5 duration', boxed +
             '(hborn : BirthState born) : (c.a_pulse_contract hb hborn).duration=@v@ := by rfl\n',
             '15/2', '4'),
        pair('isolated B pulse contract has the actual7.5 duration', boxed +
             ': (c.b_pulse_contract hb).duration=@v@ := by rfl\n', '15/2', '4'),
        pair('one-cell pulse contract explicitly has empty routing', boxed +
             '''(hborn : BirthState born) :
    PulseContract θ (fun _ _ => @v@) (fun _ => 2) (c.final.learnedProjection 0) 0 2 :=
  c.a_pulse_contract hb hborn
''', '[]', '[⟨0,2,0⟩]'),
    ]


def final_factory_cases():
    born = '''example {θ born freshB freshC newbornB newbornC forward backward delay cascadeForward cascadeBackward}
    (c : ConstructedCadenceFirstWire θ born freshB freshC newbornB newbornC forward backward delay
      cascadeForward cascadeBackward) '''
    factory = '''example {θ born freshB freshC ε} (hborn : @BirthState 1 born)
    (hb : @PhysicalBox 3 (extendParameters (extendParameters θ freshB) freshC) ε)
    (ha : ∀ q, born.aux 0 q=.ready)
    (hqueue : born.pending=sourceTrain 0 0 0 8 16++sourceTrain 0 0 160 8 16)
    (newbornB newbornC : Newborn) (forward backward delay cascadeForward cascadeBackward : ℝ → ℝ)
    (hforward : ∀ t, (3/10:ℝ)≤forward t ∧ forward t≤2/5)
    (hback : ∀ t, (3/10:ℝ)≤backward t ∧ backward t≤2/5)
    (hdelay : ∀ t, (3/10:ℝ)≤delay t ∧ delay t≤2/5)
    (hcascade : ∀ t, (3/10:ℝ)≤cascadeForward t ∧ cascadeForward t≤2/5) :
    ∃ c : ConstructedCadenceFirstWire θ born freshB freshC newbornB newbornC forward backward delay
      cascadeForward cascadeBackward,
      6527/10<c.final.time ∧ c.final.time<@v@ ∧
      c.final.x 2 (.z 0)=newbornC.x (.z 0)+9/5 ∧
      c.final.raw 1 2=some c.final.time ∧ CompleteThrough c.execution c.final.time := by
  obtain ⟨c⟩ := birth_protocol_cadence_first_wire_exists hborn hb ha hqueue newbornB newbornC
    forward backward delay cascadeForward cascadeBackward hforward hback hdelay hcascade
  exact ⟨c,c.window.1,c.window.2,c.c_gain_own,c.raw_receiver,c.complete⟩
'''
    return [
        pair('original birth constructs the first real cadence receipt without a reaching trace',
             factory, '6533/10', '6527/10'),
        pair('original birth keeps cumulative A38 through the first cadence wire', born +
             ''': (c.teaching.reverse.staged.before.emissionTimes 0++c.teaching.reverse.staged.after.emissionTimes 0).length+
    (c.teaching.staged.before.emissionTimes 0).length+(c.teaching.staged.after.emissionTimes 0).length+
    (c.execution.emissionTimes 0).length=@v@ := by exact c.a_emission_count
''', '38', '39'),
        pair('original birth keeps cumulative B43 through the first cadence wire', born +
             ''': (c.teaching.reverse.staged.after.emissionTimes 1).length+
    (c.teaching.staged.before.emissionTimes 1).length+(c.teaching.staged.after.emissionTimes 1).length+
    (c.execution.emissionTimes 1).length=@v@ := by exact c.b_emission_count
''', '43', '44'),
        pair('original birth constructs cumulative C15 including the genuine new FIRE', born +
             ''': (c.teaching.staged.after.emissionTimes 2).length+(c.execution.emissionTimes 2).length=@v@ := by
  exact c.c_emission_count
''', '15', '14'),
        pair('original-birth receipt retains exactly twenty-one pending real C sources', born +
             ': c.final.pending.length=@v@ := by exact c.pending_length\n', '21', '22'),
    ]


def main():
    controls=cases()
    with tempfile.TemporaryDirectory(prefix='hybrid-cadence-first-wire-', dir=ROOT) as tmp:
        path=Path(tmp)/'Check.lean'
        command=lean_check_command(tmp)

        def check(source, expected, name, prefix=PREFIX):
            path.write_text(prefix+source)
            result=subprocess.run([*command,str(path)],cwd=ROOT,text=True,
                                  stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=180)
            if (result.returncode==0)!=expected:
                raise SystemExit(f'{name}: unexpected result:\n{result.stdout}')
            if not expected and 'error:' not in result.stdout:
                raise SystemExit(f'{name}: failed without a Lean diagnostic:\n{result.stdout}')

        check('\n'.join(good for _,good,_ in controls),True,'valid first-cadence-wire controls')
        print('All40 positive first-cadence-wire contracts accepted.',flush=True)
        bridge_labels={name for name,_,_ in bridge_cases()}
        for name,_,bad in controls:
            check(bad,False,name,BRIDGE_PREFIX if name in bridge_labels else CORE_PREFIX)
            print(f'{name}: physical conclusion accepted; altered claim rejected.',flush=True)
        print(f'{len(controls)} paired first-cadence-wire controls passed.',flush=True)


if __name__=='__main__':
    main()
