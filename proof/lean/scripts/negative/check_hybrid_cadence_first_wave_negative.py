#!/usr/bin/env python3
"""Future paired contracts for the actual first cadence relay wave."""
from pathlib import Path
import subprocess
import tempfile

from scripts.lean_check import lean_check_command

ROOT=Path(__file__).resolve().parents[2]
PREFIX='''import KernelR.HybridBirthCadenceFirstWave
import KernelR.HybridCadenceStrongSlowSpan
import KernelR.HybridCadenceMarkOnlyExistence
import KernelR.HybridNeutralHeadExecutionProduct
open KernelR.Hybrid
noncomputable section
'''


def pair(label, template, good, bad):
    assert '@v@' in template
    assert good!=bad
    return label,template.replace('@v@',good),template.replace('@v@',bad)


def cases():
    relay='''example {θ born freshB freshC newbornB newbornC forward backward delay}
    {c : ConstructedCTeaching θ born freshB freshC newbornB newbornC forward backward delay}
    {cascadeForward cascadeBackward} {w : ConstructedCadenceWarmup c cascadeForward cascadeBackward}
    {r : FirstCadenceWire w} (t : FirstCadenceRelayWire r) '''
    span='''example {θ : Fin 1 → Parameters} {s : Snapshot 1} {p : Port}
    {fire : FirstLearnedFire θ (fun _ _ => []) s 0 p}
    {fast : PortFastCompletion θ (fun _ _ => []) fire.final p}
    (v : CadenceStrongSlowSpan fast) '''
    mark='''example {θ route s p} (c : CadenceMarkOnlyResponse θ route s p) '''
    next_source='''example {θ route s p} {c : CadenceMarkOnlyResponse θ route s p} {later}
    (a : CadenceMarkOnlyNextSource c later) '''
    neutral='''example {n θ θA route routeA s u a b}
    (tail : @Execution n θ route s u) (head : @Execution 1 θA routeA a b)
    (hstart : s.time=a.time) (hfinish : u.time=b.time)
    (heTail : tail.ledger.emissions=[]) (heHead : head.ledger.emissions=[])
    (hdHead : head.deliveries=[]) (hPending : a.pending=[]) (global : Router (n+1)) '''
    return [
        pair('relay wire is issued by the actual B cell FIRE',relay+
             ': t.execution.ledger.emissions=[(@v@,t.senderCycle.fire.final.time)] := by exact t.emissions\n','1','0'),
        pair('relay wire is actually delivered to A port2',relay+
             ': t.execution.deliveries=[⟨@v@,2,t.final.time⟩] := by exact t.deliveries\n','0','1'),
        pair('relay delay is sampled at the actual B issuing threshold',relay+
             ': t.final.time=t.senderCycle.fire.final.time+cascadeBackward @v@ := by exact t.date\n',
             't.senderCycle.fire.final.time','r.final.time'),
        pair('actual relay receipt retains its complete jitter window',relay+
             ': 6534/10<t.final.time ∧ t.final.time<@v@ := by exact t.window\n','6544/10','6534/10'),
        pair('relay receipt retains the exact twenty-one later C source occurrences',relay+
             ': t.final.pending=sourceTrain 2 0 656 4 @v@ := by exact t.pending\n','21','20'),
        pair('A receiver RAW is fresh at the actual relay receipt clock',relay+
             ': t.final.raw 0 2=some (@v@) := by exact t.a_raw_active\n',
             't.final.time','t.senderCycle.fire.final.time'),
        pair('A receiver retains its own exact rest charge at receipt',relay+
             ': t.final.x 0 .q=@v@ := by exact t.a_charge\n','1/10','1/4'),
        pair('B energy is carried from its actual retained FAST cut',relay+
             ': t.final.x 1 .energy=@v@ := by exact congrFun t.b_values .energy\n',
             't.bCutA.state.x 0 .energy','100'),
        pair('C energy is carried from its actual unfinished retained path',relay+
             ': t.final.x 2 .energy=@v@ := by exact congrFun t.c_values .energy\n',
             't.cCutA.state.x 0 .energy','100'),
        pair('B RAW is exactly its actual retained cut history',relay+
             '(q : Port) : t.final.raw 1 q=@v@ := by exact t.b_raw q\n',
             't.bCutA.state.raw 0 q','none'),
        pair('C RAW is exactly its actual retained cut history',relay+
             '(q : Port) : t.final.raw 2 q=@v@ := by exact t.c_raw q\n',
             't.cCutA.state.raw 0 q','some t.final.time'),
        pair('global relay preserves all three own acquired gain families',relay+
             '(i : Fin 3) (q : Port) : t.final.x i (.z q)=r.final.x i (.z q)@v@ := by exact t.gains i q\n','','+3/5'),
        pair('global relay preserves all three own recovery memories',relay+
             '(i : Fin 3) : t.final.x i .b=r.final.x i .b@v@ := by exact t.recovery i\n','','+1/10'),
        pair('the actual C SLOW continuation reaches the pending source656 date',span+
             '(ht : s.time=652) : v.final.time=@v@ := by rw [v.date,ht]; norm_num\n','656','655'),
        pair('the carried C continuation remains genuinely SLOW',span+
             ': v.final.main 0=.@v@ := by exact v.main_slow\n','slow','ready'),
        pair('actual C charge remains strictly above point15 without reset',span+
             '''(hB : 17999/100000≤s.x 0 .b ∧ s.x 0 .b≤18001/100000)
    (hlat : 2/5<fire.latency ∧ fire.latency<9/10) : @v@<v.final.x 0 .q := by
  rw [v.charge_clock]
  exact (cadence_strong_slow_charge_bounds hB hlat (by linarith [hlat.2]) le_rfl).1
''','3/20','1/4'),
        pair('C SLOW endpoint energy is the actual protected flow energy',span+
             ': v.final.x 0 .energy=@v@ := by exact v.energy_clock\n',
             'protectedMainValues θ fast.final 0 p .slow .ready none (s.time+4) 0 .energy','100'),
        pair('C SLOW continuation retains the actual unfinished source queue',span+
             ': v.final.pending=@v@ := by exact v.pending\n','fast.final.pending','[]'),
        pair('neutral head weaving creates no output from retained non-ready paths',neutral+
             ''': ∃ e : Execution (prependParameters θA θ) global (s.prependQuiet a) (u.prependQuiet b),
    e.ledger.emissions=@v@ := by
  obtain ⟨e,he,hd⟩ := tail.prepend_neutral head hstart hfinish heTail heHead hdHead hPending global
  exact ⟨e,he⟩
''','[]','[(0,u.time)]'),
        pair('neutral head weaving maps the exact actual tail delivery occurrences',neutral+
             ''': ∃ e : Execution (prependParameters θA θ) global (s.prependQuiet a) (u.prependQuiet b),
    e.deliveries=@v@ := by
  obtain ⟨e,he,hd⟩ := tail.prepend_neutral head hstart hfinish heTail heHead hdHead hPending global
  exact ⟨e,hd⟩
''','tail.deliveries.map Delivery.succ','[]'),
        pair('neutral product keeps the actual possibly non-ready head energy',neutral+
             ': (u.prependQuiet b).x 0 .energy=@v@ := by rfl\n','b.x 0 .energy','100'),
        pair('MARK-only response constructs a full real point1 MARK dose',mark+
             ': c.execution.ledger.mark 0 p=@v@ := by exact c.mark_dose\n','1/10','0'),
        pair('MARK-only response suppresses ERROR while the main remains SLOW',mark+
             '(q : Port) : c.execution.ledger.error 0 q=@v@ := by exact c.error_zero q\n','0','3/5'),
        pair('MARK-only response creates no output',mark+
             ': c.execution.ledger.emissions=@v@ := by exact c.emissions\n','[]','[(0,s.time)]'),
        pair('MARK-only learning raises the cell own recovery by point1',mark+
             ': c.final.x 0 .b=s.x 0 .b+@v@ := by exact c.recovery_gain\n','1/10','0'),
        pair('MARK-only response preserves every own acquired gain',mark+
             '(j : Fin 1) (q : Port) : c.final.x j (.z q)=s.x j (.z q)@v@ := by exact c.gains j q\n','','+3/5'),
        pair('MARK-only actual return occurs before source plus3point8',mark+
             ': c.returnState.time<s.time+@v@ := by exact c.returnDeadline\n','19/5','1'),
        pair('MARK-only response waits physically to the next period-four boundary',mark+
             ': c.final.time=s.time+@v@ := by exact c.date\n','4','3'),
        pair('next MARK-only handoff consumes a genuine source and creates fresh RAW',next_source+
             ': a.final.raw 0 p=some (@v@) := by exact a.raw_active\n','a.final.time','s.time'),
        pair('next MARK-only handoff keeps the exact real queue tail',next_source+
             ': a.final.pending=@v@ := by exact a.pending\n','later','[]'),
    ]+first_a_cases()+final_factory_cases()


def first_a_cases():
    first_a='''example {θ born freshB freshC newbornB newbornC forward backward delay}
    {c : ConstructedCTeaching θ born freshB freshC newbornB newbornC forward backward delay}
    {cascadeForward cascadeBackward} {w : ConstructedCadenceWarmup c cascadeForward cascadeBackward}
    {r : FirstCadenceWire w} {relay : FirstCadenceRelayWire r} (a : FirstCadenceAFire relay) '''
    return [
        pair('first A cadence threshold is a genuine global A FIRE',first_a+
             ': a.execution.ledger.emissions=[(@v@,a.localCycle.fire.final.time)] := by exact a.emissions\n','0','1'),
        pair('first A cadence FIRE enters FAST at the actual threshold charge',first_a+
             ': a.final.main 0=.fast ∧ a.final.x 0 .q=@v@ := by exact ⟨a.a_main_fast,a.a_charge⟩\n','1','1/4'),
        pair('first A FIRE carries B energy from its actual retained continuation cut',first_a+
             ': a.final.x 1 .energy=@v@ := by exact congrFun a.b_values .energy\n','a.bCut.state.x 0 .energy','100'),
        pair('first A FIRE carries C energy from its actual retained continuation cut',first_a+
             ': a.final.x 2 .energy=@v@ := by exact congrFun a.c_values .energy\n','a.cCut.state.x 0 .energy','100'),
        pair('first A FIRE preserves all three own acquired gain families',first_a+
             '(i : Fin 3) (q : Port) : a.final.x i (.z q)=relay.final.x i (.z q)@v@ := by exact a.gains i q\n','','+3/5'),
        pair('first A FIRE preserves all three own recovery memories',first_a+
             '(i : Fin 3) : a.final.x i .b=relay.final.x i .b@v@ := by exact a.recovery i\n','','+1/10'),
        pair('first A FIRE introduces no synthetic source delivery',first_a+
             ': a.execution.deliveries=@v@ := by exact a.deliveries\n','[]','[⟨0,2,a.final.time⟩]'),
        pair('actual first A firing lies inside the constructed wave window',first_a+
             ': 6538/10<a.final.time ∧ a.final.time<@v@ := by exact a.window\n','6551/10','6538/10'),
    ]


def final_factory_cases():
    born='''example {θ born freshB freshC newbornB newbornC forward backward delay cascadeForward cascadeBackward}
    (c : ConstructedCadenceFirstWave θ born freshB freshC newbornB newbornC forward backward delay
      cascadeForward cascadeBackward) '''
    factory='''example {θ born freshB freshC ε} (hborn : @BirthState 1 born)
    (hb : @PhysicalBox 3 (extendParameters (extendParameters θ freshB) freshC) ε)
    (ha : ∀ q, born.aux 0 q=.ready)
    (hqueue : born.pending=sourceTrain 0 0 0 8 16++sourceTrain 0 0 160 8 16)
    (newbornB newbornC : Newborn) (forward backward delay cascadeForward cascadeBackward : ℝ → ℝ)
    (hforward : ∀ t, (3/10:ℝ)≤forward t ∧ forward t≤2/5)
    (hback : ∀ t, (3/10:ℝ)≤backward t ∧ backward t≤2/5)
    (hdelay : ∀ t, (3/10:ℝ)≤delay t ∧ delay t≤2/5)
    (hcascadeForward : ∀ t, (3/10:ℝ)≤cascadeForward t ∧ cascadeForward t≤2/5)
    (hcascadeBackward : ∀ t, (3/10:ℝ)≤cascadeBackward t ∧ cascadeBackward t≤2/5) :
    ∃ c : ConstructedCadenceFirstWave θ born freshB freshC newbornB newbornC forward backward delay
      cascadeForward cascadeBackward,
      6538/10<c.final.time ∧ c.final.time<@v@ ∧ c.final.pending.length=21 ∧
      c.final.x 2 (.z 0)=newbornC.x (.z 0)+9/5 ∧ CompleteThrough c.execution c.final.time := by
  obtain ⟨c⟩ := birth_protocol_cadence_first_wave_exists hborn hb ha hqueue newbornB newbornC
    forward backward delay cascadeForward cascadeBackward hforward hback hdelay hcascadeForward hcascadeBackward
  exact ⟨c,c.window.1,c.window.2,c.pending_length,c.c_gain_own,c.complete⟩
'''
    return [
        pair('original birth constructs the complete actual first wave without a reaching trace',
             factory,'6551/10','6538/10'),
        pair('original birth counts genuine cumulative A39 after its actual cadence FIRE',born+
             ''': (c.cadence.teaching.reverse.staged.before.emissionTimes 0++
    c.cadence.teaching.reverse.staged.after.emissionTimes 0).length+
    (c.cadence.teaching.staged.before.emissionTimes 0).length+
    (c.cadence.teaching.staged.after.emissionTimes 0).length+(c.execution.emissionTimes 0).length=@v@ := by
  exact c.a_emission_count
''','39','38'),
        pair('original birth counts genuine cumulative B44 after the relay FIRE',born+
             ''': (c.cadence.teaching.reverse.staged.after.emissionTimes 1).length+
    (c.cadence.teaching.staged.before.emissionTimes 1).length+
    (c.cadence.teaching.staged.after.emissionTimes 1).length+(c.execution.emissionTimes 1).length=@v@ := by
  exact c.b_emission_count
''','44','43'),
        pair('original birth retains cumulative C15 through the actual full wave',born+
             ''': (c.cadence.teaching.staged.after.emissionTimes 2).length+(c.execution.emissionTimes 2).length=@v@ := by
  exact c.c_emission_count
''','15','16'),
        pair('full actual wave retains all twenty-one queued later C sources',born+
             ': c.final.pending.length=@v@ := by exact c.pending_length\n','21','20'),
    ]


def main():
    controls=cases()
    with tempfile.TemporaryDirectory(prefix='hybrid-cadence-first-wave-',dir=ROOT) as tmp:
        path=Path(tmp)/'Check.lean'
        command=lean_check_command(tmp)

        def check(source,expected,name):
            path.write_text(PREFIX+source)
            result=subprocess.run([*command,str(path)],cwd=ROOT,text=True,
                                  stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=180)
            if (result.returncode==0)!=expected:
                raise SystemExit(f'{name}: unexpected result:\n{result.stdout}')
            if not expected and 'error:' not in result.stdout:
                raise SystemExit(f'{name}: failed without a Lean diagnostic:\n{result.stdout}')

        check('\n'.join(good for _,good,_ in controls),True,'valid first-cadence-wave controls')
        for name,_,bad in controls:
            check(bad,False,name)
            print(f'{name}: physical conclusion accepted; altered claim rejected.',flush=True)
        print(f'{len(controls)} paired first-cadence-wave controls passed.',flush=True)


if __name__=='__main__':
    main()
