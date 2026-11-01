import KernelR.HybridBirthCadenceFirstMarkReturn
import KernelR.HybridLocalCadenceTail

/-! Instantiate the autonomous local C continuation with the actual C660
coordinates reached from the original births. The surrounding network is
not advanced by this one-cell theorem. -/
namespace KernelR.Hybrid

namespace ConstructedCadenceFirstMarkReturn
variable {θ born freshB freshC newbornB newbornC forward backward delay cascadeForward cascadeBackward}
  (c : ConstructedCadenceFirstMarkReturn θ born freshB freshC newbornB newbornC
    forward backward delay cascadeForward cascadeBackward)

noncomputable abbrev localCSource : Snapshot 1 := c.mark.localSource.final

theorem local_c_source_date : c.localCSource.time = 660 := by
  change c.mark.localSource.final.time = 660
  rw [c.mark.localSource.date]
  change c.source.final.time + 4 = 660
  rw [c.source.date]
  norm_num

theorem local_c_source_gain : c.localCSource.x 0 (.z 0) = newbornC.x (.z 0) + 9 / 5 :=
  (congrFun c.mark.c_values (.z 0)).symm.trans c.c_gain_own

theorem local_c_source_recovery : c.localCSource.x 0 .b = newbornC.x .b + 1 / 5 :=
  (congrFun c.mark.c_values .b).symm.trans c.c_recovery_own

theorem local_c_tail_exists {ε}
    (hb : @PhysicalBox 3 (extendParameters (extendParameters θ freshB) freshC) ε) :
    Nonempty (LocalCadenceTail (fun _ : Fin 1 => freshC) c.localCSource) := by
  have hs : CadenceReadyCoordinates c.localCSource 0 (3 / 10) := by
    have h := c.mark.localSource.ready 0
    exact ⟨h.ready,⟨h.charge.1,by linarith [h.charge.2]⟩,h.auxiliary⟩
  have hz : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ c.localCSource.x 0 (.z 0) ∧
      c.localCSource.x 0 (.z 0) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000 := by
    rw [c.local_c_source_gain]
    have h := newbornC.gain 0
    simp only [nominalGain,show (0 : Port) ≠ 1 by decide,ite_false] at h
    constructor <;> linarith [h.1,h.2]
  have hB : 27999 / 100000 ≤ c.localCSource.x 0 .b ∧
      c.localCSource.x 0 .b ≤ 28001 / 100000 := by
    rw [c.local_c_source_recovery]
    constructor <;> linarith [newbornC.recovery.1,newbornC.recovery.2]
  exact local_cadence_tail_exists hb.extend_new c.localCSource c.mark.localSource.physical
    c.mark.localSource.raw_valid c.local_c_source_date hs c.mark.localSource.charge hz hB
    c.mark.localSource.raw_active c.mark.localSource.raw_other c.mark.localSource.pending

end ConstructedCadenceFirstMarkReturn

namespace LocalCadenceTail
variable {θ born freshB freshC newbornB newbornC forward backward delay cascadeForward cascadeBackward}
  {c : ConstructedCadenceFirstMarkReturn θ born freshB freshC newbornB newbornC
    forward backward delay cascadeForward cascadeBackward}
  (tail : LocalCadenceTail (fun _ : Fin 1 => freshC) c.localCSource)

theorem c_gain_own : tail.final.x 0 (.z 0) = newbornC.x (.z 0) + 12 / 5 := by
  rw [tail.gain_target,c.local_c_source_gain]
  ring

theorem c_recovery_own : tail.final.x 0 .b = newbornC.x .b + 3 / 10 := by
  rw [tail.recovery_gain,c.local_c_source_recovery]
  ring

theorem cumulative_c_emission_count :
    (c.wave.cadence.teaching.staged.after.emissionTimes 2).length +
      (c.execution.emissionTimes 2).length + (tail.execution.emissionTimes 0).length = 34 := by
  rw [c.c_emission_count,tail.emission_count]

end LocalCadenceTail
end KernelR.Hybrid
