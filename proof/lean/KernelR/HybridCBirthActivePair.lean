import KernelR.HybridConstructedCBirth
import KernelR.HybridQuietHeadExecutionProduct

/-! Extract the actual B/C state after C's birth, with its exact queue.
Prepending the original quiet A reconstructs the whole three-cell state. -/
namespace KernelR.Hybrid

noncomputable def cBirthPairPending : List (Delivery 2) :=
  sourceTrain 0 2 488 8 15 ++ sourceTrain 1 0 640 4 25

abbrev cBirthPairParameters (freshB freshC : Parameters) : Fin 2 → Parameters :=
  extendParameters (fun _ : Fin 1 => freshB) freshC

def cBirthPairContact (delay : ℝ → ℝ) : Contact 2 := ⟨0,1,1,480,630,delay⟩

noncomputable def cBirthPairRouter (delay : ℝ → ℝ) : Router 2 :=
  (cBirthPairContact delay).route

theorem cBirthPairRouter_prepend (delay : ℝ → ℝ) (i : Fin 2) (time : ℝ) :
    cTeachingRouter delay i.succ time = (cBirthPairRouter delay i time).map Delivery.succ := by
  classical
  fin_cases i <;>
    simp [cTeachingRouter,cTeachingContact,cBirthPairRouter,cBirthPairContact,Contact.route,
      Contact.token]
  split_ifs <;> rfl

theorem cBirthPairRouter_fire (delay : ℝ → ℝ) {source fire : ℝ}
    (hsource : 480 ≤ source ∧ source ≤ 600)
    (hfire : source + 2 / 5 < fire ∧ fire < source + 7 / 10) :
    cBirthPairRouter delay 0 fire = [⟨1,1,fire + delay fire⟩] := by
  have hwindow : (480 : ℝ) ≤ fire ∧ fire < 630 := by constructor <;> linarith
  simp [cBirthPairRouter,cBirthPairContact,Contact.route,Contact.token,hwindow]

theorem cBirthPairParameters_prepend (θ : Fin 1 → Parameters) (freshB freshC : Parameters) :
    prependParameters θ (cBirthPairParameters freshB freshC) =
      extendParameters (extendParameters θ freshB) freshC := by
  funext i
  fin_cases i <;> rfl

theorem cBirthPairParameters_at_succ (θ : Fin 1 → Parameters) (freshB freshC : Parameters)
    (i : Fin 2) : cBirthPairParameters freshB freshC i =
      extendParameters (extendParameters θ freshB) freshC i.succ := by
  fin_cases i <;> rfl

theorem cBirthPairParameters_physical_box {θ freshB freshC ε}
    (hb : @PhysicalBox 3 (extendParameters (extendParameters θ freshB) freshC) ε) :
    PhysicalBox (cBirthPairParameters freshB freshC) ε := by
  refine ⟨hb.1,?_⟩
  intro i q
  rw [cBirthPairParameters_at_succ θ freshB freshC i]
  exact hb.2 i.succ q

namespace ConstructedCBirth
variable {θ born freshB newbornB forward backward}
  {t : ConstructedReverseTeaching θ born freshB newbornB forward backward}
  {freshC newbornC delay} (c : ConstructedCBirth t freshC newbornC delay)

noncomputable def quietA : Snapshot 1 := c.final.quietHead

noncomputable def activePair : Snapshot 2 := c.final.activeTail cBirthPairPending

theorem active_pair_pending : c.activePair.pending =
    sourceTrain 0 2 488 8 15 ++ sourceTrain 1 0 640 4 25 := rfl

theorem active_pair_pending_length : c.activePair.pending.length = 40 := by
  rw [c.active_pair_pending]
  simp [sourceTrain]

theorem active_pair_queue_map : c.final.pending = c.activePair.pending.map Delivery.succ := by
  rw [c.pending,c.active_pair_pending]
  simp [constructedCBirthSources,sourceTrain,Delivery.succ]

theorem active_pair_reconstruct : c.activePair.prependQuiet c.quietA = c.final :=
  c.final.prependQuiet_reconstruct cBirthPairPending c.active_pair_queue_map

theorem active_pair_date : c.activePair.time = 480 := c.date

theorem quiet_a_date : c.quietA.time = 480 := c.date

theorem quiet_a_prepared (i : Fin 1) : PreparedSection c.quietA i :=
  ⟨(c.old_prepared 0).ready,(c.old_prepared 0).charge,
    (c.old_prepared 0).recovery,(c.old_prepared 0).auxiliary⟩

theorem quiet_a_ready (i : Fin 1) : ReadyCoordinates c.quietA i :=
  (c.quiet_a_prepared i).ready_coordinates

theorem quiet_a_charge (i : Fin 1) : c.quietA.x i .q = 1 / 10 := c.old_charge 0

theorem quiet_a_raw_none (i : Fin 1) (q : Port) : c.quietA.raw i q = none :=
  c.raw_other 0 q (Or.inl (by decide))

theorem quiet_a_pending : c.quietA.pending = [] := rfl

theorem active_pair_physical : PhysicalInvariant (cBirthPairParameters freshB freshC) c.activePair := by
  refine ⟨fun i => c.physical.region i.succ,?_,
    fun i => c.physical.recovery_cap i.succ,fun i => c.physical.reserve i.succ⟩
  intro i q
  rw [cBirthPairParameters_at_succ θ freshB freshC i]
  exact c.physical.gain_cap i.succ q

theorem active_pair_raw_valid : RawValid c.activePair :=
  fun i q origin h => c.raw_valid i.succ q origin h

theorem active_pair_b_prepared : PreparedSection c.activePair 0 :=
  ⟨(c.old_prepared 1).ready,(c.old_prepared 1).charge,
    (c.old_prepared 1).recovery,(c.old_prepared 1).auxiliary⟩

theorem active_pair_b_charge : c.activePair.x 0 .q = 1 / 10 := c.old_charge 1

theorem active_pair_raw_active : c.activePair.raw 0 2 = some (480 : ℝ) := c.raw_active

theorem active_pair_raw_other (i : Fin 2) (q : Port) (h : i ≠ 0 ∨ q ≠ 2) :
    c.activePair.raw i q = none := by
  apply c.raw_other i.succ q
  rcases h with hi | hq
  · left
    intro he
    apply hi
    apply Fin.ext
    have hv := congrArg (fun j : Fin 3 => j.val) he
    change i.val + 1 = 1 at hv
    omega
  · exact Or.inr hq

theorem active_pair_b_gain_own : c.activePair.x 0 (.z 2) = newbornB.x (.z 2) + 9 / 5 :=
  (c.old_gains 1 2).trans t.b_gain_target

theorem active_pair_b_gain_bounds : 9 / 5 ≤ Real.exp (c.activePair.x 0 (.z 2)) ∧
    Real.exp (c.activePair.x 0 (.z 2)) ≤ 2 := by
  have hz : Real.log (3 / 10) - 1 / 100000 ≤ newbornB.x (.z 2) ∧
      newbornB.x (.z 2) ≤ Real.log (3 / 10) + 1 / 100000 := by
    simpa only [nominalGain,show (2 : Port) ≠ 1 by decide,ite_false] using newbornB.gain (2 : Port)
  rw [c.active_pair_b_gain_own]
  exact learned_gain_bounds (by linarith [hz.1]) (by linarith [hz.2])

theorem active_pair_c_coordinates : c.activePair.x 1 = newbornC.x := c.c_coordinates

theorem active_pair_c_ready : ReadyCoordinates c.activePair 1 :=
  ⟨(c.ready 2).ready,(c.ready 2).charge,(c.ready 2).auxiliary⟩

theorem active_pair_c_not_prepared : ¬ PreparedSection c.activePair 1 := by
  intro h
  exact c.c_not_prepared ⟨h.ready,h.charge,h.recovery,h.auxiliary⟩

theorem active_pair_c_raw_none (q : Port) : c.activePair.raw 1 q = none :=
  c.raw_other 2 q (Or.inl (by decide))

theorem active_pair_c_gain (q : Port) :
    Real.log (nominalGain q) - 1 / 100000 ≤ c.activePair.x 1 (.z q) ∧
      c.activePair.x 1 (.z q) ≤ Real.log (nominalGain q) + 1 / 100000 := by
  rw [c.active_pair_c_coordinates]
  exact newbornC.gain q

theorem active_pair_c_charge : 1 / 10 - 1 / 100000 ≤ c.activePair.x 1 .q ∧
    c.activePair.x 1 .q ≤ 1 / 10 + 1 / 100000 := c.c_charge

theorem active_pair_c_recovery : 2 / 25 - 1 / 100000 ≤ c.activePair.x 1 .b ∧
    c.activePair.x 1 .b ≤ 2 / 25 + 1 / 100000 := c.c_recovery

theorem active_pair_pending_future : PendingFuture c.activePair := by
  intro d hd
  have hm : d.succ ∈ c.final.pending := by
    rw [c.active_pair_queue_map]
    exact List.mem_map.mpr ⟨d,hd,rfl⟩
  exact c.pending_future d.succ hm

end ConstructedCBirth
end KernelR.Hybrid
