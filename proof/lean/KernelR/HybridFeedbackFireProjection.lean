import KernelR.HybridFeedbackFirstFire

/-! Project the actual first reciprocal FIRE into the two local states used
by its continuation. Neither projection injects a local queue or resets the
sender's charge, sensor clock, RAW origin or acquired memories. -/
namespace KernelR.Hybrid

namespace FeedbackFirstFire
variable {θ forward backward start}
  {w : FeedbackWeakEntry θ (reciprocalEntryRouter forward backward) start} (f : FeedbackFirstFire w)

noncomputable def localA : Snapshot 1 := f.final.cellProjection 0 []
noncomputable def localB : Snapshot 1 := f.final.cellProjection 1 []

def parametersA (_f : FeedbackFirstFire w) : Fin 1 → Parameters := fun _ => θ 0
def parametersB (_f : FeedbackFirstFire w) : Fin 1 → Parameters := fun _ => θ 1

noncomputable def silentStart : ℝ := f.firing.firstSilent.final.time
noncomputable def errorStart : ℝ := f.firing.firstSilent.errorDate
noncomputable def readyTime : ℝ :=
  w.final.time + f.firing.firstMark.latency + auxCycleDuration (θ 1) 2
noncomputable def reverseToken : Delivery 2 := ⟨0,2,f.final.time + backward f.final.time⟩

theorem parameters_product : extendParameters f.parametersA (f.parametersB 0) = θ := by
  funext i
  fin_cases i <;> rfl

theorem localA_box {ε} (hb : PhysicalBox θ ε) : PhysicalBox f.parametersA ε :=
  ⟨hb.1,fun _ p => hb.2 0 p⟩

theorem localB_box {ε} (hb : PhysicalBox θ ε) : PhysicalBox f.parametersB ε :=
  ⟨hb.1,fun _ p => hb.2 1 p⟩

theorem localA_physical : PhysicalInvariant f.parametersA f.localA :=
  ⟨fun _ => f.firing.physical.region 0,fun _ p => f.firing.physical.gain_cap 0 p,
    fun _ => f.firing.physical.recovery_cap 0,fun _ => f.firing.physical.reserve 0⟩

theorem localB_physical : PhysicalInvariant f.parametersB f.localB :=
  ⟨fun _ => f.firing.physical.region 1,fun _ p => f.firing.physical.gain_cap 1 p,
    fun _ => f.firing.physical.recovery_cap 1,fun _ => f.firing.physical.reserve 1⟩

theorem localA_raw_valid : RawValid f.localA :=
  fun _ p origin h => f.firing.raw_valid 0 p origin h

theorem localB_raw_valid : RawValid f.localB :=
  fun _ p origin h => f.firing.raw_valid 1 p origin h

theorem localA_prepared (j : Fin 1) : PreparedSection f.localA j :=
  ⟨f.a_prepared.ready,f.a_prepared.charge,f.a_prepared.recovery,f.a_prepared.auxiliary⟩

theorem localA_ready (j : Fin 1) : ReadyCoordinates f.localA j :=
  (f.localA_prepared j).ready_coordinates

theorem localA_charge (j : Fin 1) : f.localA.x j .q = 1 / 10 := f.a_charge

theorem localA_raw_none (j : Fin 1) (p : Port) : f.localA.raw j p = none := f.a_raw_none p

theorem localA_pending : f.localA.pending = [] := rfl

theorem localB_pending : f.localB.pending = [] := rfl

/-- The only pending wire is the token issued by the actual global FIRE. -/
theorem product_pending : f.localA.product f.localB (w.final.pending ++ [f.reverseToken]) = f.final := by
  change (f.final.cellProjection 0 []).product (f.final.cellProjection 1 [])
    (w.final.pending ++ [⟨0,2,f.final.time + backward f.final.time⟩]) = f.final
  rw [← f.pending]
  exact f.final.cellProjection_product [] []

theorem localA_clock : f.localA.time = f.final.time := rfl

theorem localB_clock : f.localB.time = f.final.time := rfl

theorem localB_fast (j : Fin 1) : f.localB.main j = .fast := f.firing.main_fast

theorem localB_charge (j : Fin 1) : f.localB.x j .q = 1 := f.firing.charge

theorem localB_silent (j : Fin 1) : f.localB.aux j 2 = .silent := f.firing.aux_silent

theorem localB_sensor_above (j : Fin 1) : 1 / 10 < f.localB.x j (.m 2) := f.firing.sensor_above

theorem localB_aux_other (j : Fin 1) (p : Port) (hp : p ≠ 2) :
    f.localB.aux j p = .ready := f.firing.aux_other 1 p (Or.inr hp)

theorem localB_other_rest (j : Fin 1) (p : Port) (hp : p ≠ 2) :
    RestBand (f.localB.x j (.m p)) := by
  exact (f.execution.aux_no_input_rest_band 1 p ((w.prepared 1).auxiliary p).1
    ((w.prepared 1).auxiliary p).2 (w.raw_other 1 p (Or.inr hp))
    (by simp [NoArrivalAt,f.deliveries])).1.2

theorem localB_other_below (j : Fin 1) (p : Port) (hp : p ≠ 2) :
    f.localB.x j (.m p) < 1 := by
  linarith [(f.localB_other_rest j p hp).2]

theorem localB_raw_active (j : Fin 1) : f.localB.raw j 2 = some w.final.time := f.firing.raw_active

theorem localB_raw344 (j : Fin 1) : f.localB.raw j 2 = some 344 := by
  rw [f.localB_raw_active,w.date]

theorem localB_raw_other (j : Fin 1) (p : Port) (hp : p ≠ 2) :
    f.localB.raw j p = none := f.firing.raw_other 1 p (Or.inr hp)

/-- The SILENT exponential is the one already in the constructed global
FIRE snapshot, with its actual SILENT-entry clock. -/
theorem localB_sensor_clock (j : Fin 1) :
    f.localB.x j (.m 2) = (4 / 5 : ℝ) *
      Real.exp (-(θ 1).ls 2 * (f.localB.time - f.silentStart)) := by
  change f.firing.firstSilent.final.x 1 (.m 2) *
    Real.exp (-protectedReadyRate (θ 1) 2 .silent *
      (w.final.time + f.firing.latency - f.firing.firstSilent.final.time)) = _
  rw [f.firing.firstSilent.sensor_charge]
  rfl

theorem localB_main_clock (j : Fin 1) :
    f.localB.x j .q = Real.exp (-a * (f.localB.time - f.final.time)) := by
  rw [f.localB_clock,sub_self,mul_zero,Real.exp_zero]
  exact f.localB_charge j

theorem silentStart_before_fire : f.silentStart < f.final.time := f.firing.flow.positive

theorem silentStart_window {ε} (hb : PhysicalBox θ ε) :
    (344 : ℝ) ≤ f.silentStart ∧ f.silentStart < 344 + 1 / 20 := by
  have hupper := f.firing.firstSilent.deadline
  have hstart : w.final.time ≤ f.silentStart := by
    change w.final.time ≤ w.final.time + f.firing.firstMark.latency +
      Real.log (5 / 4) / (θ 1).lm 2
    linarith [f.firing.firstMark.early,(hb.aux_durations_positive 1 2).1]
  rw [w.date] at hstart hupper
  exact ⟨hstart,hupper⟩

theorem localA_gains (j : Fin 1) (p : Port) : f.localA.x j (.z p) = start.x 0 (.z p) := by
  change f.final.x 0 (.z p) = _
  rw [f.gains,w.gain_other 0 p (Or.inl (by decide))]

theorem localB_gains (j : Fin 1) (p : Port) : f.localB.x j (.z p) = w.final.x 1 (.z p) := f.gains 1 p

theorem localB_gain_target (j : Fin 1) : f.localB.x j (.z 2) = start.x 1 (.z 2) + 9 / 5 := by
  rw [f.localB_gains,w.gain_target]

theorem localB_gain_other (j : Fin 1) (p : Port) (hp : p ≠ 2) :
    f.localB.x j (.z p) = start.x 1 (.z p) := by
  rw [f.localB_gains,w.gain_other 1 p (Or.inr hp)]

theorem localA_recovery (j : Fin 1) : f.localA.x j .b = start.x 0 .b := by
  change f.final.x 0 .b = _
  rw [f.recovery,w.recovery]

theorem localB_recovery (j : Fin 1) : f.localB.x j .b = start.x 1 .b := by
  change f.final.x 1 .b = _
  rw [f.recovery,w.recovery]

theorem localB_recovery_prepared (j : Fin 1) :
    17999 / 100000 ≤ f.localB.x j .b ∧ f.localB.x j .b ≤ 18001 / 100000 := by
  change 17999 / 100000 ≤ f.final.x 1 .b ∧ f.final.x 1 .b ≤ 18001 / 100000
  rw [f.recovery]
  exact (w.prepared 1).recovery

/-- The sharper lower clock follows from the real carried charge and a
current gain bound, rather than a reset to exact rest. -/
theorem fire_after_four_tenths (hg : Real.exp (w.final.x 1 (.z 2)) ≤ 2) :
    344 + (2 / 5 : ℝ) < f.final.time := by
  have h := readyPulse_root_after_four_tenths (w.prepared 1).charge.2 hg
    (by linarith [f.firing.early]) f.firing.response_root
  rw [f.date]
  rwa [w.date] at h

/-- The real sensor floors are measured from the constructed SILENT entry. -/
theorem errorStart_eq : f.errorStart = f.silentStart + Real.log 8 / (θ 1).ls 2 := rfl

theorem readyTime_eq : f.readyTime = f.errorStart + Real.log 4 / (θ 1).le 2 := by
  change w.final.time + f.firing.firstMark.latency + auxCycleDuration (θ 1) 2 =
    (w.final.time + f.firing.firstMark.latency + Real.log (5 / 4) / (θ 1).lm 2 +
      Real.log 8 / (θ 1).ls 2) + Real.log 4 / (θ 1).le 2
  dsimp [auxCycleDuration]
  ring

theorem errorStart_window {ε} (hb : PhysicalBox θ ε) :
    344 + (99 / 100 : ℝ) < f.errorStart ∧ f.errorStart < 344 + 123 / 100 := by
  have h := f.firing.firstSilent.errorDate_bounds hb
  rwa [w.date] at h

theorem readyTime_window {ε} (hb : PhysicalBox θ ε) :
    344 + (1 : ℝ) < f.readyTime ∧ f.readyTime < 344 + 419 / 300 := by
  have h := hb.first_cycle_schedule 1 2 ⟨f.firing.firstMark.early,f.firing.firstMark.deadline⟩
  change 344 + (1 : ℝ) < w.final.time + f.firing.firstMark.latency + auxCycleDuration (θ 1) 2 ∧
    w.final.time + f.firing.firstMark.latency + auxCycleDuration (θ 1) 2 < 344 + 419 / 300
  rw [w.date]
  constructor <;> linarith [h.2.2.2.2.1,h.2.2.2.2.2]

theorem errorStart_after_fire {ε} (hb : PhysicalBox θ ε) :
    f.final.time < f.errorStart := by
  linarith [(f.errorStart_window hb).1,f.window.2]

theorem readyTime_before_fast_end {ε} (hb : PhysicalBox θ ε)
    (hg : Real.exp (w.final.x 1 (.z 2)) ≤ 2) :
    f.readyTime < f.final.time + 1 := by
  linarith [(f.readyTime_window hb).2,f.fire_after_four_tenths hg]

end FeedbackFirstFire
end KernelR.Hybrid
