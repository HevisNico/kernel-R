import KernelR.HybridBirthCTeaching
import KernelR.HybridCadenceStrongPulse
import KernelR.LearnedSingleCell

/-! Learned-domain membership of one-cell coordinate projections of the
constructed639.9 state. These projections use an empty analysis queue; they
are not physical operations on the global state, whose25 C tokens remain.
The resulting PulseContracts concern isolated one-cell future source queues
with empty routing. No network continuation or every-N refinement is claimed. -/
namespace KernelR.Hybrid

/-- Coordinate projection for an isolated one-cell domain. The empty analysis
queue is not a mutation or transition of the original network snapshot. -/
noncomputable def Snapshot.learnedProjection {n} (s : Snapshot n) (i : Fin n) : Snapshot 1 where
  time := s.time
  x := fun _ => s.x i
  main := fun _ => s.main i
  aux := fun _ => s.aux i
  raw := fun _ => s.raw i
  pending := []

/-- A physical prepared cell at exact charge rest belongs to the one-cell
learned domain when its chosen port has the required gain. -/
theorem prepared_projection_learned_rest {n Θ s}
    (hf : @PhysicalInvariant n Θ s) (i : Fin n) (p : Port)
    (hs : PreparedSection s i) (hq : s.x i .q = 1 / 10)
    (hr : ∀ q, s.raw i q = none)
    (hg : 9 / 5 ≤ Real.exp (s.x i (.z p)) ∧ Real.exp (s.x i (.z p)) ≤ 19 / 10)
    (θ : Fin 1 → Parameters) (hθ : θ 0 = Θ i) :
    LearnedRest θ (fun _ => p) (s.learnedProjection i) where
  main := fun _ => hs.ready
  aux := fun _ q => (hs.auxiliary q).1
  raw := fun _ q => hr q
  pending := rfl
  charge := fun _ => hq
  sensor := by
    intro j q
    apply abs_le.mpr
    change -(1 / 100000 : ℝ) ≤ s.x i (.m q) - 1 / 40 ∧
      s.x i (.m q) - 1 / 40 ≤ 1 / 100000
    have h := (hs.auxiliary q).2
    constructor <;> linarith [h.1,h.2]
  reserve := fun _ => hf.reserve i
  gain := fun _ => hg
  cap := by
    intro j q
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    change s.x i (.z q) ≤ Real.log ((θ 0).cap q)
    rw [hθ]
    exact hf.gain_cap i q
  recovery := by
    intro j
    change (17 / 100 : ℝ) ≤ s.x i .b ∧ s.x i .b ≤ 1 / 5
    constructor <;> linarith [hs.recovery.1,hs.recovery.2]

namespace ConstructedCTeaching
variable {θ born freshB freshC newbornB newbornC forward backward delay}
  (c : ConstructedCTeaching θ born freshB freshC newbornB newbornC forward backward delay)

/-- Aport2's own acquired memory reaches the imported learned one-cell domain.
The projected empty queue does not alter c.final or its pending C sources. -/
theorem a_learned_rest (hborn : BirthState born) :
    LearnedRest θ (fun _ => 2) (c.final.learnedProjection 0) := by
  apply prepared_projection_learned_rest c.physical 0 2 (c.prepared 0)
    (c.charge 0) (c.raw_none 0) _ θ rfl
  apply cadence_three_dose_gain_bounds
  rw [c.a_gain_target]
  have hg := ((hborn.2.2 0).2.2.2.2 2).1
  simp only [nominalGain,show (2 : Port) ≠ 1 by decide,ite_false] at hg
  constructor <;> linarith [hg.1,hg.2]

/-- Bport2 is measured from B's independent newborn, not A's coordinates. -/
theorem b_learned_rest :
    LearnedRest (fun _ : Fin 1 => freshB) (fun _ => 2) (c.final.learnedProjection 1) := by
  apply prepared_projection_learned_rest c.physical 1 2 (c.prepared 1)
    (c.charge 1) (c.raw_none 1) _ (fun _ : Fin 1 => freshB) rfl
  apply cadence_three_dose_gain_bounds
  rw [c.b_gain_target]
  have hg := newbornB.gain 2
  simp only [nominalGain,show (2 : Port) ≠ 1 by decide,ite_false] at hg
  constructor <;> linarith [hg.1,hg.2]

/-- Actual isolated one-cell pulse law from A's projected learned state. -/
noncomputable def a_pulse_contract {ε}
    (hb : @PhysicalBox 3 (extendParameters (extendParameters θ freshB) freshC) ε)
    (hborn : BirthState born) :
    PulseContract θ (fun _ _ => []) (fun _ => 2) (c.final.learnedProjection 0) 0 2 :=
  learnedPulseContract hb.extend_old.extend_old (c.a_learned_rest hborn)

/-- Actual isolated one-cell pulse law from B's projected learned state. -/
noncomputable def b_pulse_contract {ε}
    (hb : @PhysicalBox 3 (extendParameters (extendParameters θ freshB) freshC) ε) :
    PulseContract (fun _ : Fin 1 => freshB) (fun _ _ => []) (fun _ => 2)
      (c.final.learnedProjection 1) 0 2 :=
  learnedPulseContract hb.extend_old.extend_new c.b_learned_rest

/-- Finite complete prefixes under newly supplied isolated A future sources. -/
theorem a_complete_at_every_horizon {ε}
    (hb : @PhysicalBox 3 (extendParameters (extendParameters θ freshB) freshC) ε)
    (hborn : BirthState born) (schedule : FutureSchedule (15 / 2))
    (hfirst : c.final.time ≤ schedule.time 0) (T : ℝ) (hT : c.final.time ≤ T) :
    ∃ (k : ℕ) (last : Snapshot 1)
      (run : Execution θ (fun _ _ => [])
        (withFuture (c.final.learnedProjection 0) (sourceQueue 0 2 schedule.time k)) last),
      CompleteThrough run T ∧ ∀ j, schedule.time j ≤ T → j < k := by
  exact learned_complete_at_every_horizon hb.extend_old.extend_old (c.a_learned_rest hborn)
    schedule (c.final.learnedProjection 0)
    ⟨c.a_learned_rest hborn,fun _ => ⟨rfl,fun _ => rfl⟩⟩ hfirst T hT

/-- Finite complete prefixes under newly supplied isolated B future sources. -/
theorem b_complete_at_every_horizon {ε}
    (hb : @PhysicalBox 3 (extendParameters (extendParameters θ freshB) freshC) ε)
    (schedule : FutureSchedule (15 / 2))
    (hfirst : c.final.time ≤ schedule.time 0) (T : ℝ) (hT : c.final.time ≤ T) :
    ∃ (k : ℕ) (last : Snapshot 1)
      (run : Execution (fun _ : Fin 1 => freshB) (fun _ _ => [])
        (withFuture (c.final.learnedProjection 1) (sourceQueue 0 2 schedule.time k)) last),
      CompleteThrough run T ∧ ∀ j, schedule.time j ≤ T → j < k := by
  exact learned_complete_at_every_horizon hb.extend_old.extend_new c.b_learned_rest
    schedule (c.final.learnedProjection 1)
    ⟨c.b_learned_rest,fun _ => ⟨rfl,fun _ => rfl⟩⟩ hfirst T hT

end ConstructedCTeaching
end KernelR.Hybrid
