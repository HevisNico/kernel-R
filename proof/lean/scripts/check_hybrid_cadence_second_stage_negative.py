#!/usr/bin/env python3
"""Future paired contracts for the second strong and mixed cadence inputs."""
from pathlib import Path
import subprocess
import tempfile

from lean_check import lean_check_command

ROOT=Path(__file__).resolve().parents[1]
PREFIX='''import KernelR.HybridCadenceSecondStrongResponse
import KernelR.HybridCadenceMixedNextSource
import KernelR.HybridCadenceMarkOnlyExistence
open KernelR.Hybrid
noncomputable section
'''


def pair(label,template,good,bad):
    assert '@v@' in template
    assert good!=bad
    return label,template.replace('@v@',good),template.replace('@v@',bad)


def cases():
    slow='''example {θ : Fin 1 → Parameters} {s : Snapshot 1} {p : Port}
    {fire : FirstLearnedFire θ (fun _ _ => []) s 0 p}
    {fast : PortFastCompletion θ (fun _ _ => []) fire.final p}
    (v : CadenceSecondStrongSlowSpan fast) '''
    strong='''example {θ s p later} (c : CadenceSecondStrongResponse θ s p later) '''
    prefix='''example {θ route s p} (m : CadenceMixedPrefix θ route s p) '''
    reopen='''example {θ route s p} {m : CadenceMixedPrefix θ route s p} (r : CadenceMixedReopen m) '''
    error='''example {θ route input p origin P} (e : ReadySilentErrorStart θ route input p origin P) '''
    mixed='''example {θ s p} (m : CadenceMixedResponse θ s p) '''
    next_source='''example {θ s p} {m : CadenceMixedResponse θ s p} {later}
    (entry : CadenceMixedNextSource m later) '''
    chain='''example {θ s p later660 later664}
    (mark : CadenceMarkOnlyResponse θ (fun _ _ => []) s p)
    (source660 : CadenceMarkOnlyNextSource mark later660)
    (strong : CadenceSecondStrongResponse θ source660.final p later664)
    (mixed : CadenceMixedResponse θ strong.final p) '''
    return factory_cases()+[
        pair('second SLOW path carries a real mixed-input charge band',slow+
             ': @v@≤v.final.x 0 .q ∧ v.final.x 0 .q≤7/50 := by exact v.charge\n','61/500','1/4'),
        pair('second SLOW clock uses its own carried recovery and actual latency',slow+
             ': v.final.x 0 .q=(1/4:ℝ)*Real.exp (-s.x 0 .b*((s.time+4)-(s.time+@v@+1))) := by exact v.charge_clock\n',
             'fire.latency','0'),
        pair('second SLOW energy is the genuine continued protected flow energy',slow+
             ': v.final.x 0 .energy=@v@ := by exact v.energy_clock\n',
             'protectedMainValues θ fast.final 0 p .slow .ready none (s.time+4) 0 .energy','100'),
        pair('second strong response produces exactly its own one real FIRE',strong+
             ': c.execution.ledger.emissions=@v@ := by exact c.emissions\n','[(0,c.fire.final.time)]','[]'),
        pair('second strong handoff consumes the actual source664 occurrence',strong+
             '(ht : s.time=660) : c.execution.deliveries=[⟨0,p,@v@⟩] := by rw [c.deliveries,ht]; norm_num\n','664','660'),
        pair('second strong handoff retains the exact later source queue',strong+
             ': c.final.pending=@v@ := by exact c.pending\n','later','s.pending'),
        pair('source664 RAW origin is fresh at its actual delivery clock',strong+
             ': c.final.raw 0 p=some (@v@) := by exact c.raw_active\n','c.final.time','s.time'),
        pair('mixed protected MARK raises only the own recovery memory',prefix+
             ': m.final.x 0 .b=s.x 0 .b+@v@ := by exact m.recovery_gain\n','1/10','0'),
        pair('mixed ERROR threshold follows the protected reopening window',prefix+
             ': s.time+@v@<m.final.time+Real.log 8/(θ 0).ls p := by exact m.error_lower\n','99/100','123/100'),
        pair('mixed reopen preserves the old source RAW origin',reopen+
             ': r.final.raw 0 p=some (@v@) := by exact r.raw_active\n','s.time','r.final.time'),
        pair('mixed reopen retains the actual SILENT sensor clock instead of restarting it',reopen+
             ': r.final.x 0 (.m p)=(4/5:ℝ)*Real.exp (-(θ 0).ls p*(r.final.time-@v@)) := by exact r.sensor_clock\n',
             'm.final.time','r.final.time'),
        pair('ERROR before RAW expiry retains that old origin',error+
             '(h : e.final.time<origin+1) : e.final.raw 0 p=@v@ := by rw [e.raw_option,ite_eq_left h]\n',
             'some origin','none'),
        pair('ERROR exactly at RAW expiry consumes the expiry first',error+
             '(h : e.final.time=origin+1) : e.final.raw 0 p=@v@ := by rw [e.raw_option,ite_eq_right (by linarith)]\n',
             'none','some origin'),
        pair('ERROR after RAW expiry carries no synthetic renewed current',error+
             '(h : origin+1<e.final.time) : e.final.raw 0 p=@v@ := by rw [e.raw_option,ite_eq_right (by linarith)]\n',
             'none','some e.final.time'),
        pair('mixed response constructs the full real ERROR dose',mixed+
             ': m.execution.ledger.error 0 p=@v@ := by exact m.pulse.error_dose\n','3/5','0'),
        pair('mixed response constructs its protected MARK dose as well',mixed+
             ': m.execution.ledger.mark 0 p=@v@ := by exact m.pulse.mark_case.mark_dose\n','1/10','0'),
        pair('mixed response produces no extra FIRE',mixed+
             ': m.execution.ledger.emissions=@v@ := by exact m.emissions\n','[]','[(0,s.time)]'),
        pair('mixed endpoint carries the bounded point32 charge without resetting to it',mixed+
             ': m.final.x 0 .q @v@ 8/25 := by exact m.coordinates.charge.2\n','≤','='),
        pair('mixed own recovery reaches the genuine point38 band',mixed+
             ': @v@/100000≤m.final.x 0 .b ∧ m.final.x 0 .b≤38001/100000 := by exact m.recovery_band\n',
             '37999','38001'),
        pair('mixed handoff delivers the real source668 exactly once',next_source+
             '(ht : s.time=664) : entry.execution.deliveries=[⟨0,p,@v@⟩] := by rw [entry.deliveries,ht]; norm_num\n','668','664'),
        pair('mixed source handoff retains the actual residual energy',next_source+
             ': entry.final.x 0 .energy=@v@ := by exact congrFun (congrFun entry.values 0) .energy\n',
             'm.final.x 0 .energy','100'),
        pair('two actual MARK inputs retain own point18 to point28 to point38 recovery',chain+
             ''': mixed.final.x 0 .b=s.x 0 .b+@v@ := by
  rw [mixed.recovery_gain,strong.recovery,source660.recovery_gain]
  ring
''','1/5','1/10'),
        pair('mixed ERROR advances the own three-dose memory to four doses',chain+
             '''(own : ℝ) (hown : s.x 0 (.z p)=own+9/5) : mixed.final.x 0 (.z p)=own+@v@ := by
  rw [mixed.gain_target,strong.gains,source660.gains,hown]
  ring
''','12/5','9/5'),
    ]


def factory_cases():
    strong_factory='''example {θ ε} (hb : PhysicalBox θ ε) (s : Snapshot 1) (p : Port)
    (hf : PhysicalInvariant θ s) (hv : RawValid s) (ht : s.time=660)
    (hs : CadenceReadyCoordinates s 0 (3/10)) (hq : s.x 0 .q=1/10)
    (hz : Real.log (3/10)+9/5-1/100000≤s.x 0 (.z p) ∧ s.x 0 (.z p)≤Real.log (3/10)+9/5+1/100000)
    (hB : 27999/100000≤s.x 0 .b ∧ s.x 0 .b≤28001/100000)
    (hr : s.raw 0 p=some s.time) (ho : ∀ q, q≠p → s.raw 0 q=none)
    (hqueue : s.pending=sourceTrain 0 p 664 4 19) :
    ∃ c : CadenceSecondStrongResponse θ s p (sourceTrain 0 p 668 4 18),
      c.final.time=664 ∧ c.final.pending.length=@v@ ∧ c.final.raw 0 p=some (664:ℝ) := by
  have hhead : s.pending=⟨0,p,s.time+4⟩::sourceTrain 0 p 668 4 18 := by
    rw [hqueue,ht,sourceTrain_succ]; norm_num
  have hfuture : ∀ d∈sourceTrain (0:Fin 1) p 668 4 18, s.time+4<d.due := by
    intro d hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    rw [ht]
    dsimp
    nlinarith [Nat.cast_nonneg (α:=ℝ) k.val]
  obtain ⟨c⟩ := cadence_second_strong_response_exists hb s p hf hv hs hq hz hB hr ho _ hhead hfuture
  have hd : c.final.time=664 := by rw [c.date,ht]; norm_num
  refine ⟨c,hd,?_,?_⟩
  · rw [c.pending]; simp only [sourceTrain,List.length_ofFn]
  · rw [c.raw_active,hd]
'''
    mixed_factory='''example {θ ε} (hb : PhysicalBox θ ε) (s : Snapshot 1) (p : Port)
    (hf : PhysicalInvariant θ s) (hv : RawValid s) (ht : s.time=664) (hm : s.main 0=.slow)
    (hq : 61/500≤s.x 0 .q ∧ s.x 0 .q≤7/50)
    (hB : 27999/100000≤s.x 0 .b ∧ s.x 0 .b≤28001/100000)
    (ha : ∀ q, s.aux 0 q=.ready ∧ RestBand (s.x 0 (.m q)))
    (hz : Real.log (3/10)+9/5-1/100000≤s.x 0 (.z p) ∧ s.x 0 (.z p)≤Real.log (3/10)+9/5+1/100000)
    (hr : s.raw 0 p=some s.time) (ho : ∀ q, q≠p → s.raw 0 q=none)
    (hqueue : s.pending=sourceTrain 0 p 668 4 18) :
    ∃ m : CadenceMixedResponse θ s p,
    ∃ entry : CadenceMixedNextSource m (sourceTrain 0 p 672 4 17),
      entry.final.time=@v@ ∧ entry.final.pending.length=17 ∧ entry.final.raw 0 p=some (668:ℝ) := by
  have hp : ∀ d∈s.pending, s.time+4≤d.due := by
    intro d hd
    rw [hqueue] at hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    rw [ht]
    dsimp
    nlinarith [Nat.cast_nonneg (α:=ℝ) k.val]
  obtain ⟨m⟩ := cadence_mixed_response_exists hb s p hf hv hm hq hB ha hz hr ho hp
  have hhead : s.pending=⟨0,p,s.time+4⟩::sourceTrain 0 p 672 4 17 := by
    rw [hqueue,ht,sourceTrain_succ]; norm_num
  have hfuture : ∀ d∈sourceTrain (0:Fin 1) p 672 4 17, s.time+4<d.due := by
    intro d hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    rw [ht]
    dsimp
    nlinarith [Nat.cast_nonneg (α:=ℝ) k.val]
  obtain ⟨entry⟩ := cadence_mixed_next_source_exists m hb hf hv _ hhead hfuture
  have hd : entry.final.time=668 := by rw [entry.date,ht]; norm_num
  refine ⟨m,entry,hd,?_,?_⟩
  · rw [entry.pending]; simp only [sourceTrain,List.length_ofFn]
  · rw [entry.raw_active,hd]
'''
    return [
        pair('second strong factory constructs source664 with tail18 without a reaching trace',
             strong_factory,'18','19'),
        pair('mixed factory constructs source668 with tail17 without a reaching trace',
             mixed_factory,'668','664'),
    ]


def main():
    controls=cases()
    with tempfile.TemporaryDirectory(prefix='hybrid-cadence-second-stage-',dir=ROOT) as tmp:
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

        check('\n'.join(good for _,good,_ in controls),True,'valid second-cadence-stage controls')
        print(f'All{len(controls)} positive second-stage contracts accepted.',flush=True)
        for name,_,bad in controls:
            check(bad,False,name)
            print(f'{name}: physical conclusion accepted; altered claim rejected.',flush=True)
        print(f'{len(controls)} paired second-cadence-stage controls passed.',flush=True)


if __name__=='__main__':
    main()
