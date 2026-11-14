import NativeMultiTokenTarget
import KernelR.HybridFirstLearnedFireExistence

/-! The guarded certificates and scalar READY margins of the frozen target. -/
namespace NetworkStability.NativeMultiToken

open KernelR.Hybrid PhaseAdmission Set
open AutonomousFeedback (mass)
open AutonomousFeedback.Schedule.PortMemory (Address address_encode_injective)

private theorem valid_of_check {p : Parameters N} (accepted : p.check = true) : p.Valid :=
  of_decide_eq_true accepted

private theorem exp_dose_bounds :
    (1822 / 1000 : ℝ) ≤ Real.exp (3 / 5) ∧ Real.exp (3 / 5) ≤ 1823 / 1000 := by
  have h := Real.exp_bound (x := (3 / 5 : ℝ)) (n := 9) (by norm_num) (by decide)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  obtain ⟨lo, hi⟩ := abs_le.mp h
  constructor <;> linarith

private theorem exp_two_doses_bounds :
    (3320 / 1000 : ℝ) ≤ Real.exp (6 / 5) ∧ Real.exp (6 / 5) ≤ 3321 / 1000 := by
  have h := Real.exp_bound (x := (3 / 5 : ℝ)) (n := 9) (by norm_num) (by decide)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  obtain ⟨lo, hi⟩ := abs_le.mp h
  have bounds : (182211 / 100000 : ℝ) ≤ Real.exp (3 / 5) ∧
      Real.exp (3 / 5) ≤ 182212 / 100000 := by
    constructor <;> linarith
  rw [show (6 / 5 : ℝ) = 3 / 5 + 3 / 5 by norm_num, Real.exp_add]
  constructor <;> nlinarith [mul_nonneg (Real.exp_pos (3 / 5 : ℝ)).le
    (sub_nonneg.mpr bounds.1), mul_nonneg (Real.exp_pos (3 / 5 : ℝ)).le
    (sub_nonneg.mpr bounds.2)]

private theorem gain_windows {p : Parameters N} (accepted : p.check = true) (i : Fin N) :
    let A := (p.amplitude i : ℝ)
    (0 ≤ A ∧ A ≤ 7 / 6) ∧
    (0 ≤ A * Real.exp (3 / 5) ∧ A * Real.exp (3 / 5) ≤ 7 / 6) ∧
    (9 / 5 ≤ launchAmplitude p i ∧ launchAmplitude p i ≤ 2) := by
  obtain ⟨lo, hi⟩ := (valid_of_check accepted).2.1 i
  change 9 / 5 ≤ (3320 / 1000 : ℚ) * p.amplitude i at lo
  change (3321 / 1000 : ℚ) * p.amplitude i ≤ 2 at hi
  have loR : (9 / 5 : ℝ) ≤ (3320 / 1000) * (p.amplitude i : ℝ) := by simpa using (Rat.cast_le (K := ℝ)).mpr lo
  have hiR : (3321 / 1000 : ℝ) * (p.amplitude i : ℝ) ≤ 2 := by simpa using (Rat.cast_le (K := ℝ)).mpr hi
  have pos : 0 ≤ (p.amplitude i : ℝ) := by linarith
  have doseUpper := mul_le_mul_of_nonneg_left exp_dose_bounds.2 pos
  have twoLower := mul_le_mul_of_nonneg_left exp_two_doses_bounds.1 pos
  have twoUpper := mul_le_mul_of_nonneg_left exp_two_doses_bounds.2 pos
  dsimp [launchAmplitude]
  exact ⟨⟨pos, by linarith⟩, ⟨mul_nonneg pos (Real.exp_pos _).le, by linarith⟩,
    ⟨by linarith, by linarith⟩⟩

private theorem ready_bound {charge gain t : ℝ}
    (chargeLo : 1 / 10 ≤ charge) (chargeHi : charge ≤ 7 / 50)
    (gainLo : 0 ≤ gain) (gainHi : gain ≤ 7 / 6) (ht : 0 ≤ t) :
    1 / 10 ≤ readyPulse charge gain 0 t ∧ readyPulse charge gain 0 t ≤ 133 / 150 := by
  have carryLo := mul_nonneg (sub_nonneg.mpr chargeLo) (Real.exp_pos (-(1 / 2 : ℝ) * t)).le
  have carryHi := decay_upper (show charge - 1 / 10 ≤ 1 / 25 by linarith)
    (by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num) ht
  have driveLo := mul_nonneg gainLo (response_nonnegative ht)
  have driveHi := mul_le_mul gainHi (response_uniform_upper ht) (response_nonnegative ht)
    (by norm_num : (0 : ℝ) ≤ 7 / 6)
  simp only [readyPulse, sub_zero]
  constructor <;> linarith

private theorem inter_wave_decay {gap : ℝ} (hgap : 8 ≤ gap) :
    Real.exp (-(gap - 1) / 2) ≤ 1 / 20 := by
  have repeated : Real.exp (3 : ℝ) = Real.exp (3 / 5 : ℝ) ^ 5 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have high : (20 : ℝ) ≤ Real.exp 3 := by
    rw [repeated]
    calc
      (20 : ℝ) ≤ (1822 / 1000) ^ (5 : ℕ) := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) exp_dose_bounds.1 _
  calc
    _ ≤ Real.exp (-3 : ℝ) := Real.exp_le_exp.mpr (by linarith)
    _ = (Real.exp (3 : ℝ))⁻¹ := Real.exp_neg _
    _ ≤ 1 / 20 := by
      rw [inv_le_comm₀ (Real.exp_pos _) (by norm_num : (0 : ℝ) < 1 / 20)]
      norm_num
      exact high

private theorem afterSilent_mem {charge gain gap : ℝ}
    (qLo : 1 / 10 ≤ charge) (qHi : charge ≤ 7 / 50)
    (gLo : 0 ≤ gain) (gHi : gain ≤ 7 / 6) (gapLo : 8 ≤ gap) :
    1 / 10 ≤ afterSilent charge gain gap ∧ afterSilent charge gain gap ≤ 7 / 50 := by
  obtain ⟨lo, hi⟩ := ready_bound qLo qHi gLo gHi (t := 1) (by norm_num)
  have low := mul_nonneg (sub_nonneg.mpr lo) (Real.exp_pos (-(gap - 1) / 2)).le
  have high := mul_le_mul (show readyPulse charge gain 0 1 - 1 / 10 ≤ 59 / 75 by linarith)
    (inter_wave_decay gapLo) (Real.exp_pos _).le (by norm_num : (0 : ℝ) ≤ 59 / 75)
  unfold afterSilent
  constructor <;> linarith

private theorem gap_windows {p : Parameters N} (accepted : p.check = true) :
    (8 : ℝ) ≤ p.gap1 ∧ (8 : ℝ) ≤ p.gap2 := by
  obtain ⟨first, second⟩ := (valid_of_check accepted).2.2.1
  exact ⟨by exact_mod_cast first, by exact_mod_cast second⟩

private theorem second_charge_mem {p : Parameters N} (accepted : p.check = true) (i : Fin N) :
    1 / 10 ≤ afterSilent (1 / 10) (p.amplitude i) p.gap1 ∧
    afterSilent (1 / 10) (p.amplitude i) p.gap1 ≤ 7 / 50 := by
  have gain := (gain_windows accepted i).1
  exact afterSilent_mem (by norm_num) (by norm_num) gain.1 gain.2 (gap_windows accepted).1

/-- Both scalar training waves stay at least 17/150 below FIRE. The second
uses the actual carried READY charge in the frozen scalar compiler. -/
theorem training_silence {p : Parameters N} (accepted : p.check = true) (i : Fin N) :
    (∀ t : ℝ, 0 ≤ t → readyPulse (1 / 10) (p.amplitude i) 0 t ≤ 133 / 150) ∧
    (∀ t : ℝ, 0 ≤ t →
      readyPulse (afterSilent (1 / 10) (p.amplitude i) p.gap1)
        ((p.amplitude i : ℝ) * Real.exp (3 / 5)) 0 t ≤ 133 / 150) := by
  obtain ⟨first, second, _⟩ := gain_windows accepted i
  obtain ⟨lo, hi⟩ := second_charge_mem accepted i
  exact ⟨fun _ ht => (ready_bound (by norm_num) (by norm_num) first.1 first.2 ht).2,
    fun _ ht => (ready_bound lo hi second.1 second.2 ht).2⟩

/-- The infimum in the frozen calendar is the first scalar crossing. -/
theorem scalar_latency {p : Parameters N} (accepted : p.check = true) (i : Fin N) :
    3 / 10 < latency p i ∧ latency p i < 9 / 10 ∧
    readyPulse (launchCharge p i) (launchAmplitude p i) 0 (latency p i) = 1 ∧
    ∀ t, 0 ≤ t → t < latency p i →
      readyPulse (launchCharge p i) (launchAmplitude p i) 0 t < 1 := by
  obtain ⟨lo, hi⟩ := second_charge_mem accepted i
  obtain ⟨_, second, gain⟩ := gain_windows accepted i
  have charge : 1 / 10 ≤ launchCharge p i ∧ launchCharge p i ≤ 7 / 50 :=
    afterSilent_mem lo hi second.1 second.2 (gap_windows accepted).2
  obtain ⟨f, early, late, root, prior⟩ := readyPulse_first_learned_crossing (start := 0)
    (initial := launchCharge p i) ⟨by linarith [charge.1], charge.2⟩ gain
  simp only [zero_add] at root prior
  let roots := {t : ℝ | 3 / 10 < t ∧ t < 9 / 10 ∧
    readyPulse (launchCharge p i) (launchAmplitude p i) 0 t = 1}
  have mem : f ∈ roots := ⟨early, late, root⟩
  have least : ∀ t ∈ roots, f ≤ t := by
    intro t ht
    by_contra! before
    have h : 3 / 10 < t ∧ t < 9 / 10 ∧
        readyPulse (launchCharge p i) (launchAmplitude p i) 0 t = 1 := ht
    exact (ne_of_lt (prior t ⟨by linarith [h.1], before⟩)) h.2.2
  have exactClock : latency p i = f :=
    le_antisymm (csInf_le ⟨f, least⟩ mem) (le_csInf ⟨f, mem⟩ least)
  rw [exactClock]
  exact ⟨early, late, root, fun t pos before => prior t ⟨pos, before⟩⟩

private theorem delay_lower {p : Parameters N} (accepted : p.check = true) (i : Fin N) :
    (8 / 5 : ℝ) < p.delay i := by
  have delay := (valid_of_check accepted).2.2.2.2.1 i
  have bound : (8 / 5 : ℚ) < p.delay i := by linarith
  simpa using (Rat.cast_lt (K := ℝ)).mpr bound

private def credit (p : Parameters N) (coordinate : Fin (3 * N)) (probe : Probe N) : Nat :=
  let i := probe.input.1
  let gain := (Address.mk i .port0).encode
  let recovery := (Address.mk i .recovery).encode
  let childRecovery := (Address.mk (p.successor i) .recovery).encode
  match probe.input.2 with
  | .first | .second => if coordinate = gain then 1 else 0
  | .launch => if coordinate = gain ∨ coordinate = childRecovery then 1 else 0
  | .receipt => if coordinate = recovery then 1 else 0

private theorem credit_pays (p : Parameters N) (probe : Probe N) (fire : Bool)
    (coordinate : Fin (3 * N)) :
    mass (credit p coordinate) (MarkFeedback.emitted (calendar p).model probe fire) +
      MarkFeedback.footprint (calendar p).model probe fire coordinate ≤ credit p coordinate probe := by
  obtain ⟨date, i, stage⟩ := probe
  have firstPort : (Stage.first == Stage.receipt) = false := rfl
  have secondPort : (Stage.second == Stage.receipt) = false := rfl
  have launchPort : (Stage.launch == Stage.receipt) = false := rfl
  have receiptPort : (Stage.receipt == Stage.receipt) = true := rfl
  cases stage <;> cases fire <;>
    simp [firstPort, secondPort, launchPort, receiptPort, credit, MarkFeedback.emitted, MarkFeedback.footprint, MarkFeedback.gain,
      MarkFeedback.recovery, Calendar.model, calendar, inputCell, mass] <;>
    split_ifs <;> omega

private theorem mass_at_most_one {α : Type*} {xs : List α} (unique : xs.Nodup)
    (choose : α → Prop) [DecidablePred choose]
    (single : ∀ i j, choose i → choose j → i = j) :
    (xs.map (fun i => if choose i then 1 else 0)).sum ≤ 1 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨absent, tail⟩ := List.nodup_cons.mp unique
    by_cases selected : choose x
    · have zero : xs.map (fun i => if choose i then 1 else 0) = xs.map (fun _ => 0) := by
        apply List.map_congr_left
        intro i member
        have rejected : ¬ choose i := fun h => absent (single i x h selected ▸ member)
        simp [rejected]
      simp [selected, zero]
    · simpa [selected] using ih tail

private theorem same_gain_cell {i j : Fin N} {coordinate : Fin (3 * N)}
    (left : coordinate = (Address.mk i .port0).encode)
    (right : coordinate = (Address.mk j .port0).encode) : i = j :=
  congrArg Address.cell (address_encode_injective _ _ (left.symm.trans right))

private theorem gain_ne_recovery (i j : Fin N) :
    (Address.mk i .port0).encode ≠ (Address.mk j .recovery).encode := by
  intro eq
  have different := congrArg Address.coordinate (address_encode_injective _ _ eq)
  cases different

private theorem credit_seed {p : Parameters N} (injective : Function.Injective p.successor)
    (coordinate : Fin (3 * N)) : mass (credit p coordinate) (seed p) ≤ Q := by
  have train : ((List.finRange N).map
      (fun i => if coordinate = (Address.mk i .port0).encode then 1 else 0)).sum ≤ 1 :=
    mass_at_most_one (List.nodup_finRange N) _ fun _ _ => same_gain_cell
  have launch : ((List.finRange N).map (fun i =>
      if coordinate = (Address.mk i .port0).encode ∨
        coordinate = (Address.mk (p.successor i) .recovery).encode then 1 else 0)).sum ≤ 1 := by
    apply mass_at_most_one (List.nodup_finRange N)
    intro i j left right
    rcases left with g | r <;> rcases right with g' | r'
    · exact same_gain_cell g g'
    · exact (gain_ne_recovery i _ (g.symm.trans r')).elim
    · exact (gain_ne_recovery j _ (g'.symm.trans r)).elim
    · exact injective (congrArg Address.cell (address_encode_injective _ _ (r.symm.trans r')))
  simpa [seed, mass, credit, List.map_map, Function.comp_def, List.sum_append] using
    Nat.add_le_add train (Nat.add_le_add train launch)

/-- A reserve covering both branches for all keys, including hypothetical FIREs. -/
theorem guarded_reserve {p : Parameters N} (accepted : p.check = true) :
    Nonempty (MarkFeedback.Reserve Q (calendar p).model (seed p)) :=
  ⟨⟨credit p, credit_pays p, credit_seed (valid_of_check accepted).2.2.2.1.1⟩⟩

/-- Each launch pays for one child plus one step; all other keys cost one step. -/
theorem guarded_rank (p : Parameters N) :
    ∃ rank : MarkFeedback.Rank W eta₀ (calendar p).model (seed p),
      rank.weight = occurrenceRank := by
  refine ⟨⟨occurrenceRank, by decide, ?_, ?_⟩, rfl⟩
  · rintro ⟨date, i, stage⟩
    cases stage <;> simp [Calendar.model, calendar, occurrenceRank, mass]
  · have sumConst (xs : List (Fin N)) (weight : Nat) :
        (xs.map (fun _ => weight)).sum = xs.length * weight := by
      induction xs with
      | nil => simp
      | cons _ _ _ => simp [Nat.add_mul, Nat.add_comm]
    have ones := sumConst (List.finRange N) 1
    have twos := sumConst (List.finRange N) 2
    simp only [seed, mass, List.map_append, List.map_map, List.sum_append, Function.comp_def,
      occurrenceRank, show Stage.first ≠ .launch by decide, show Stage.second ≠ .launch by decide,
      ite_false, ite_true, ones, twos, List.length_finRange]
    change N * 1 + N * 1 + N * 2 ≤ 4 * N
    omega

/-- The relative calendar route is causal at arbitrary dates. -/
theorem guarded_causal {p : Parameters N} (accepted : p.check = true) : Causal (calendar p) := by
  rintro ⟨date, i, stage⟩ child member
  cases stage <;> simp [calendar] at member
  subst child
  change date ≤ date + latency p i + (p.delay i : ℝ)
  linarith [(scalar_latency accepted i).1, delay_lower accepted i]

private def scheduled (p : Parameters N) (probe : Probe N) : Prop :=
  match probe.input.2 with
  | .first => probe.due = firstDate
  | .second => probe.due = secondDate p
  | .launch => probe.due = launchDate p
  | .receipt => ∃ parent, probe.input.1 = p.successor parent ∧
      probe.due = launchDate p + latency p parent + p.delay parent

private theorem seed_scheduled (p : Parameters N) (probe : Probe N) (member : probe ∈ seed p) :
    scheduled p probe := by
  simp only [seed, List.mem_append, List.mem_map] at member
  rcases member with (⟨i, _, rfl⟩ | ⟨i, _, rfl⟩) | ⟨i, _, rfl⟩ <;> rfl

private theorem child_scheduled {p : Parameters N} {probe child : Probe N}
    (parent : scheduled p probe) (member : child ∈ (calendar p).route probe) :
    scheduled p child := by
  obtain ⟨date, i, stage⟩ := probe
  cases stage <;> simp [calendar] at member
  subst child
  exact ⟨i, rfl, by rw [show date = launchDate p from parent]⟩

private theorem reachable_scheduled {p : Parameters N} {state : State N}
    (reach : DatedPath (calendar p) d (MarkFeedback.initial N (seed p)) state) :
    ∀ probe ∈ state.pending, scheduled p probe := by
  induction reach with
  | refl => exact seed_scheduled p
  | @tail previous _ _ step ih =>
    obtain ⟨probe, rest, available, _, rfl⟩ := step
    intro child member
    rcases List.mem_append.mp member with kept | new
    · exact ih child (available.mem_iff.mpr (List.mem_cons_of_mem _ kept))
    · have parent := ih probe (available.mem_iff.mpr (by simp))
      cases read : MarkFeedback.read (calendar p).model d previous probe 0
      · simp [MarkFeedback.emitted, read] at new
      · have routed : child ∈ (calendar p).model.route probe := by
          simpa [MarkFeedback.emitted, read] using new
        exact child_scheduled parent routed

private theorem scheduled_same_cell_date {p : Parameters N} (accepted : p.check = true)
    {a b : Probe N} (ha : scheduled p a) (hb : scheduled p b)
    (cell : a.input.1 = b.input.1) (date : a.due = b.due) : a = b := by
  obtain ⟨first, i, left⟩ := a
  obtain ⟨second, j, right⟩ := b
  change i = j at cell
  change first = second at date
  subst j
  subst second
  obtain ⟨gap1, gap2⟩ := gap_windows accepted
  have receipt_late (parent : Fin N) :
      launchDate p < launchDate p + latency p parent + p.delay parent := by
    linarith [(scalar_latency accepted parent).1, delay_lower accepted parent]
  cases left <;> cases right <;> simp only [scheduled] at ha hb
  all_goals try rfl
  all_goals first
    | obtain ⟨k, _, hd⟩ := ha
      have late := receipt_late k
      simp only [launchDate, secondDate] at late hd hb
      linarith
    | obtain ⟨k, _, hd⟩ := hb
      have late := receipt_late k
      simp only [launchDate, secondDate] at late hd ha
      linarith
    | simp only [launchDate, secondDate] at ha hb
      linarith

/-- An earliest-date tie can only involve distinct cells. -/
theorem guarded_ties {p : Parameters N} (accepted : p.check = true) :
    TieAdmissible (calendar p) d (MarkFeedback.initial N (seed p)) := by
  intro state reach a b ha hb different sameCell
  have reachable := reachable_scheduled reach
  have date := le_antisymm (ha.2 b hb.1) (hb.2 a ha.1)
  exact False.elim (different (scheduled_same_cell_date accepted
    (reachable a ha.1) (reachable b hb.1) sameCell date))

/-- All guarded conjuncts of the frozen refinement target. -/
theorem guarded_conjuncts {p : Parameters N} (accepted : p.check = true) :
    let C := calendar p
    let start := MarkFeedback.initial N (seed p)
    Nonempty (MarkFeedback.Reserve Q C.model (seed p)) ∧
    (∃ rank : MarkFeedback.Rank W eta₀ C.model (seed p), rank.weight = occurrenceRank) ∧
    Causal C ∧ TieAdmissible C d start :=
  ⟨guarded_reserve accepted, guarded_rank p, guarded_causal accepted, guarded_ties accepted⟩

end NetworkStability.NativeMultiToken
