import Thresholds.ThresholdProbe
import Training.StopLearningLatency

/-! Training of one port that stops at the first FIRE, as a native execution
at nominal thresholds.

A pulse on a port whose gain is at most `7/6` leaves the cell silent and
writes the full dose `3/5`. A pulse on a port whose gain lies in
`[9/5, 11/5]` makes the cell fire and writes nothing. The start gain is not
fixed: the number of silent pulses before the first FIRE depends on it, and
the gain reached does not depend on how many pulses follow. -/

namespace RecursiveLearning.Native
open KernelR.Hybrid Set

private theorem raw_valid_at_rest {s : Snapshot 1} (raw : ∀ p, s.raw 0 p = none) : RawValid s := by
  intro i p t h
  rw [Subsingleton.elim i 0, raw p] at h
  contradiction

private theorem no_deliveries_if_pending_kept {θ s u} (e : @Execution 1 θ (fun _ _ => []) s u)
    (queue : u.pending = s.pending) : e.deliveries = [] := by
  have balance := e.token_balance
  have emptyRoute :
      e.ledger.emissions.flatMap (fun (_ : Fin 1 × ℝ) => ([] : List (Delivery 1))) = [] := by simp
  change (u.pending : Multiset (Delivery 1)) + (e.deliveries : Multiset (Delivery 1)) =
    (s.pending : Multiset (Delivery 1)) +
      ((e.ledger.emissions.flatMap (fun _ => []) : List (Delivery 1)) : Multiset (Delivery 1)) at balance
  simp only [emptyRoute, queue, Multiset.coe_nil, add_zero] at balance
  have cancelled : (e.deliveries : Multiset (Delivery 1)) = 0 :=
    add_left_cancel (balance.trans (add_zero _).symm)
  exact (Multiset.coe_eq_coe.mp cancelled : e.deliveries.Perm []).eq_nil

/-- A training pulse that leaves the cell silent. The pulsed port gains the
full dose and the cell is READY again before the next pulse. -/
structure SilentSlot (θ : Fin 1 → Parameters) (start : Snapshot 1) (p : Port) (due : ℝ)
    (later : List (Delivery 1)) where
  final : Snapshot 1
  execution : Execution θ (fun _ _ => []) start final
  transverse : execution.ContactsTransversal
  ready : ReadyCoordinates final 0
  rawNone : ∀ q, final.raw 0 q = none
  pending : final.pending = later
  date : final.time ≤ due + 23
  gain : ∀ q, final.x 0 (.z q) = start.x 0 (.z q) + (if q = p then 3 / 5 else 0)
  recovery : final.x 0 .b = 2 / 25
  deliveries : execution.deliveries = [⟨0, p, due⟩]
  silent : execution.emissionTimes 0 = []

/-- A training pulse that makes the cell fire. No gain changes, the
recovery rate is unchanged, and the cell is READY again before the next
pulse. -/
structure FiringSlot (θ : Fin 1 → Parameters) (start : Snapshot 1) (p : Port) (due : ℝ)
    (later : List (Delivery 1)) where
  final : Snapshot 1
  execution : Execution θ (fun _ _ => []) start final
  transverse : execution.ContactsTransversal
  ready : ReadyCoordinates final 0
  rawNone : ∀ q, final.raw 0 q = none
  pending : final.pending = later
  date : final.time ≤ due + 23
  gain : ∀ q, final.x 0 (.z q) = start.x 0 (.z q)
  recovery : final.x 0 .b = 2 / 25
  deliveries : execution.deliveries = [⟨0, p, due⟩]
  fireTime : ℝ
  fired : execution.emissionTimes 0 = [fireTime]
  window : due < fireTime ∧ fireTime < due + 1

theorem silent_slot_exists {θ ε start p due later}
    (box : @PhysicalBox 1 θ ε) (physical : PhysicalInvariant θ start)
    (ready : ReadyCoordinates start 0) (rawNone : ∀ q, start.raw 0 q = none)
    (before : start.time < due) (queue : start.pending = ⟨0, p, due⟩ :: later)
    (spacing : ∀ d ∈ later, due + 24 ≤ d.due)
    (weak : Real.exp (start.x 0 (.z p)) ≤ 7 / 6) (recovery : start.x 0 .b = 2 / 25) :
    Nonempty (SilentSlot θ start p due later) := by
  have small : start.x 0 (.z p) ≤ Real.log (6 / 5) + 1 / 1000 := by
    have h := Real.log_le_log (Real.exp_pos _) (weak.trans (by norm_num : (7 / 6 : ℝ) ≤ 6 / 5))
    rw [Real.log_exp] at h
    linarith
  obtain ⟨dose⟩ := port_dose_exists (route := fun _ _ => []) box physical
    (raw_valid_at_rest rawNone) ready rawNone before queue
    (fun d hd => by linarith [spacing d hd]) weak small
  refine ⟨⟨dose.final, dose.execution, dose.transversal, dose.ready, dose.rawNone,
    dose.pending, ?_, dose.gain, dose.recovery.trans recovery, dose.deliveries, ?_⟩⟩
  · rw [dose.complete.1]
    linarith
  · simp [Execution.emissionTimes, dose.emissions]

theorem firing_slot_exists {θ ε start p due later}
    (box : @PhysicalBox 1 θ ε) (physical : PhysicalInvariant θ start)
    (ready : ReadyCoordinates start 0) (rawNone : ∀ q, start.raw 0 q = none)
    (before : start.time < due) (queue : start.pending = ⟨0, p, due⟩ :: later)
    (spacing : ∀ d ∈ later, due + 24 ≤ d.due)
    (strong : 9 / 5 ≤ Real.exp (start.x 0 (.z p)) ∧ Real.exp (start.x 0 (.z p)) ≤ 11 / 5)
    (recovery : start.x 0 .b = 2 / 25) :
    Nonempty (FiringSlot θ start p due later) := by
  let token : Delivery 1 := ⟨0, p, due⟩
  have localReady (i : Fin 1) : ReadyCoordinates start i := by
    rw [Subsingleton.elim i 0]; exact ready
  have localRaw (i : Fin 1) (q : Port) : start.raw i q = none := by
    rw [Subsingleton.elim i 0]
    exact rawNone q
  obtain ⟨arrival⟩ := quiet_source_arrival_exists (route := fun _ _ => []) box start token later
    physical (raw_valid_at_rest rawNone) localReady localRaw before queue
    (fun d hd => by change due ≤ d.due; linarith [spacing d hd])
  have date : arrival.final.time = due := arrival.date
  have gainAtRead : 9 / 5 ≤ Real.exp (arrival.final.x 0 (.z p)) ∧
      Real.exp (arrival.final.x 0 (.z p)) ≤ 11 / 5 := by
    rw [arrival.gain_preserved]
    exact strong
  have late : ∀ d ∈ arrival.final.pending, arrival.final.time + 31 / 4 ≤ d.due := by
    rw [arrival.pending, date]
    intro d h
    linarith [spacing d h]
  obtain ⟨fire⟩ := first_mid_learned_fire_exists arrival.final box arrival.physical arrival.raw_valid
    0 p arrival.ready gainAtRead arrival.raw_active arrival.raw_other late
  obtain ⟨fast⟩ := fire.mid_learned_fast_end_exists box (arrival.ready 0) gainAtRead.2
    (fun q ne => arrival.raw_other 0 q (Or.inr ne)) late
  let empty := fast.final.requeue []
  have b : empty.x 0 .b = 2 / 25 := by
    change fast.final.x 0 .b = _
    rw [fast.recovery, fire.recovery_preserved, arrival.recovery_preserved, recovery]
  have dispatch : LearnerDispatchState empty :=
    ⟨fast.raw_none, fun q => ⟨fast.auxiliary 0 q, fast.rest q⟩,
      Or.inr ⟨fast.main_slow, by rw [show empty.x 0 .q = 1 / 4 from fast.charge]; norm_num,
        fast.charge.le, b⟩⟩
  have wait : empty.time + 19 < due + 23 := by
    change fast.final.time + 19 < _
    rw [fast.date, fire.date, date]
    linarith [fire.deadline]
  obtain ⟨tail⟩ := learner_wait_exists (θ := θ) (T := due + 23) dispatch rfl wait
  have tailFuture (d : Delivery 1) (hd : d ∈ later) : tail.final.time ≤ d.due := by
    rw [tail.complete.1]
    linarith [spacing d hd]
  have startQueue : fast.final.pending = later := by
    rw [fast.pending, fire.pending, arrival.pending, List.append_nil]
  have startEq : withFuture empty later = fast.final := by
    have eta (s : Snapshot 1) : s.requeue s.pending = s := by cases s; rfl
    change fast.final.requeue (later ++ []) = fast.final
    rw [List.append_nil]
    exact (congrArg fast.final.requeue startQueue.symm).trans (eta fast.final)
  let framed := tail.execution.withFuture later tailFuture
  have framedSilent : framed.ledger.emissions = [] := by
    rw [Execution.withFuture_ledger, tail.silent]
  have framedPending : (withFuture tail.final later).pending = later := by
    simp [withFuture, tail.empty]
  have framedDeliveries : framed.deliveries = [] := no_deliveries_if_pending_kept framed
    (framedPending.trans (by simp [empty, withFuture, Snapshot.requeue]))
  obtain ⟨ending, endingPositive, endingSilent, endingDeliveries⟩ :
      ∃ ending : Execution θ (fun _ _ => []) fast.final (withFuture tail.final later),
        ending.ContactsTransversal ∧ ending.ledger.emissions = [] ∧ ending.deliveries = [] := by
    rw [← startEq]
    exact ⟨framed, future_transverse tail.execution later tailFuture tail.transverse,
      framedSilent, framedDeliveries⟩
  let lead := (arrival.execution.append fire.execution).append fast.execution
  let e := lead.append ending
  have emissions : e.ledger.emissions = [(0, fire.final.time)] := by
    change (lead.append ending).ledger.emissions = _
    rw [Execution.emissions_append, endingSilent]
    change (((arrival.execution.append fire.execution).append fast.execution).ledger.emissions ++ []) = _
    rw [Execution.emissions_append, Execution.emissions_append, arrival.emissions,
      fire.emissions, fast.emissions, fire.date]
    rfl
  have finalReady : ReadyCoordinates (withFuture tail.final later) 0 :=
    ⟨(tail.ready 0).ready, (tail.ready 0).charge, (tail.ready 0).auxiliary⟩
  refine ⟨⟨_, e, ?_, finalReady, tail.rawNone 0, framedPending,
    tail.complete.1.le, ?_, (tail.recovery 0).trans b, ?_, fire.final.time, ?_, ?_⟩⟩
  · exact (Execution.contactsTransversal_append _ _).2
      ⟨(Execution.contactsTransversal_append _ _).2
        ⟨(Execution.contactsTransversal_append _ _).2
          ⟨arrival.contacts_transversal, fire.contacts_transversal⟩,
          fast.contacts_transversal⟩, endingPositive⟩
  · intro q
    change tail.final.x 0 (.z q) = _
    rw [tail.gain]
    change fast.final.x 0 (.z q) = _
    rw [fast.gains, fire.gain_preserved, arrival.gain_preserved]
  · change (lead.append ending).deliveries = _
    rw [Execution.deliveries_append, endingDeliveries]
    change (((arrival.execution.append fire.execution).append fast.execution).deliveries ++ []) = _
    rw [Execution.deliveries_append, Execution.deliveries_append, arrival.deliveries,
      fire.deliveries, fast.deliveries]
    rfl
  · rw [Execution.emissionTimes, emissions]
    rfl
  · rw [fire.date, date]
    constructor <;> linarith [fire.early, fire.deadline]

/-- Training of one port by a list of pulses, at least 24 time units apart.
The first `n` pulses meet a gain of at most `7/6` and each writes a dose.
The gain then lies in `[9/5, 11/5]` and every later pulse makes the cell
fire without changing any gain or the recovery rate. -/
theorem native_stop_training {θ ε} (box : @PhysicalBox 1 θ ε) {p : Port} {later : List (Delivery 1)}
    {horizon : ℝ} (dates : List ℝ) :
    ∀ (n : ℕ) (start : Snapshot 1),
      PhysicalInvariant θ start → ReadyCoordinates start 0 → (∀ q, start.raw 0 q = none) →
      start.time < horizon → (∀ d ∈ dates, start.time < d) → (∀ d ∈ dates, d + 24 ≤ horizon) →
      dates.Pairwise (fun a b => a + 24 ≤ b) →
      start.pending = conjunctionDoseTokens p dates ++ later → (∀ t ∈ later, horizon ≤ t.due) →
      (∀ k : ℕ, k < n → Real.exp (start.x 0 (.z p) + 3 / 5 * (k : ℝ)) ≤ 7 / 6) →
      (9 / 5 ≤ Real.exp (start.x 0 (.z p) + 3 / 5 * (n : ℝ)) ∧
        Real.exp (start.x 0 (.z p) + 3 / 5 * (n : ℝ)) ≤ 11 / 5) →
      n ≤ dates.length → start.x 0 .b = 2 / 25 →
      ∃ (final : Snapshot 1) (e : Execution θ (fun _ _ => []) start final),
        e.ContactsTransversal ∧ PhysicalInvariant θ final ∧ ReadyCoordinates final 0 ∧
        (∀ q, final.raw 0 q = none) ∧ final.time < horizon ∧ final.pending = later ∧
        (∀ q, final.x 0 (.z q) = start.x 0 (.z q) + (if q = p then 3 / 5 * (n : ℝ) else 0)) ∧
        final.x 0 .b = 2 / 25 ∧ e.deliveries = conjunctionDoseTokens p dates ∧
        (e.emissionTimes 0).length = dates.length - n := by
  induction dates with
  | nil =>
    intro n start physical ready rawNone before _ _ _ queue _ _ _ count recovery
    have zero : n = 0 := by simpa using count
    subst zero
    refine ⟨start, .nil _, trivial, physical, ready, rawNone, before,
      by simpa [conjunctionDoseTokens] using queue,
      ?_, recovery, rfl, by simp [Execution.emissionTimes, Execution.ledger, Ledger.zero]⟩
    intro q
    simp
  | cons d ds ih =>
    intro n start physical ready rawNone before future after separated queue beyond weak strong
      count recovery
    obtain ⟨gap, spaced⟩ := List.pairwise_cons.mp separated
    have headQueue : start.pending = ⟨0, p, d⟩ :: (conjunctionDoseTokens p ds ++ later) := by
      rw [queue]; rfl
    have nextSpacing : ∀ t ∈ conjunctionDoseTokens p ds ++ later, d + 24 ≤ t.due := by
      intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · obtain ⟨date, hd, rfl⟩ := List.mem_map.mp ht
        exact gap date hd
      · exact (after d (by simp)).trans (beyond t ht)
    cases n with
    | zero =>
      have strongNow : 9 / 5 ≤ Real.exp (start.x 0 (.z p)) ∧
          Real.exp (start.x 0 (.z p)) ≤ 11 / 5 := by simpa using strong
      obtain ⟨slot⟩ := firing_slot_exists box physical ready rawNone (future d (by simp))
        headQueue nextSpacing strongNow recovery
      obtain ⟨final, tail, positive, hphysical, hready, hraw, date, pending, hgain, hb,
          deliveries, fires⟩ :=
        ih 0 slot.final (slot.execution.physical_invariant box physical) slot.ready slot.rawNone
          (by linarith [slot.date, after d (by simp)])
          (fun t ht => by linarith [slot.date, gap t ht])
          (fun t ht => after t (by simp [ht])) spaced slot.pending beyond
          (fun k hk => absurd hk (Nat.not_lt_zero k))
          (by rw [slot.gain p]; simpa using strong) (Nat.zero_le _) slot.recovery
      refine ⟨final, slot.execution.append tail,
        (Execution.contactsTransversal_append _ _).2 ⟨slot.transverse, positive⟩,
        hphysical, hready, hraw, date, pending, ?_, hb, ?_, ?_⟩
      · intro q
        rw [hgain q, slot.gain q]
      · rw [Execution.deliveries_append, slot.deliveries, deliveries]
        rfl
      · rw [Execution.emissionTimes_append, List.length_append, slot.fired, fires]
        simp
        omega
    | succ m =>
      have weakNow : Real.exp (start.x 0 (.z p)) ≤ 7 / 6 := by
        simpa using weak 0 (Nat.succ_pos m)
      obtain ⟨slot⟩ := silent_slot_exists box physical ready rawNone (future d (by simp))
        headQueue nextSpacing weakNow recovery
      have stepped : slot.final.x 0 (.z p) = start.x 0 (.z p) + 3 / 5 := by
        rw [slot.gain p]; simp
      obtain ⟨final, tail, positive, hphysical, hready, hraw, date, pending, hgain, hb,
          deliveries, fires⟩ :=
        ih m slot.final (slot.execution.physical_invariant box physical) slot.ready slot.rawNone
          (by linarith [slot.date, after d (by simp)])
          (fun t ht => by linarith [slot.date, gap t ht])
          (fun t ht => after t (by simp [ht])) spaced slot.pending beyond
          (fun k hk => by
            have h := weak (k + 1) (Nat.succ_lt_succ hk)
            rw [stepped]
            push_cast at h
            rw [show start.x 0 (.z p) + 3 / 5 + 3 / 5 * (k : ℝ) =
              start.x 0 (.z p) + 3 / 5 * ((k : ℝ) + 1) by ring]
            exact h)
          (by
            rw [stepped]
            push_cast at strong
            rw [show start.x 0 (.z p) + 3 / 5 + 3 / 5 * (m : ℝ) =
              start.x 0 (.z p) + 3 / 5 * ((m : ℝ) + 1) by ring]
            exact strong)
          (by simpa using count) slot.recovery
      refine ⟨final, slot.execution.append tail,
        (Execution.contactsTransversal_append _ _).2 ⟨slot.transverse, positive⟩,
        hphysical, hready, hraw, date, pending, ?_, hb, ?_, ?_⟩
      · intro q
        rw [hgain q, slot.gain q]
        by_cases h : q = p
        · simp only [h, ite_true]
          push_cast
          ring
        · simp [h]
      · rw [Execution.deliveries_append, slot.deliveries, deliveries]
        rfl
      · rw [Execution.emissionTimes_append, List.length_append, slot.silent, fires]
        simp

/-- The gain reached by training lies in `[9/5, 11/5]` whatever the number
of doses the start gain required and whatever the number of pulses sent. -/
theorem native_stop_training_band {θ ε} (box : @PhysicalBox 1 θ ε) {p : Port}
    {later : List (Delivery 1)} {horizon : ℝ} (dates : List ℝ) (n : ℕ) (start : Snapshot 1)
    (physical : PhysicalInvariant θ start) (ready : ReadyCoordinates start 0)
    (rawNone : ∀ q, start.raw 0 q = none) (before : start.time < horizon)
    (future : ∀ d ∈ dates, start.time < d) (after : ∀ d ∈ dates, d + 24 ≤ horizon)
    (separated : dates.Pairwise (fun a b => a + 24 ≤ b))
    (queue : start.pending = conjunctionDoseTokens p dates ++ later)
    (beyond : ∀ t ∈ later, horizon ≤ t.due)
    (weak : ∀ k : ℕ, k < n → Real.exp (start.x 0 (.z p) + 3 / 5 * (k : ℝ)) ≤ 7 / 6)
    (strong : 9 / 5 ≤ Real.exp (start.x 0 (.z p) + 3 / 5 * (n : ℝ)) ∧
      Real.exp (start.x 0 (.z p) + 3 / 5 * (n : ℝ)) ≤ 11 / 5)
    (count : n ≤ dates.length) (recovery : start.x 0 .b = 2 / 25) :
    ∃ (final : Snapshot 1) (e : Execution θ (fun _ _ => []) start final),
      ReadyCoordinates final 0 ∧ final.time < horizon ∧ final.pending = later ∧
      9 / 5 ≤ Real.exp (final.x 0 (.z p)) ∧ Real.exp (final.x 0 (.z p)) ≤ 11 / 5 ∧
      (∀ q ≠ p, final.x 0 (.z q) = start.x 0 (.z q)) ∧ final.x 0 .b = 2 / 25 ∧
      (e.emissionTimes 0).length = dates.length - n := by
  obtain ⟨final, e, _, _, hready, _, date, pending, hgain, hb, _, fires⟩ :=
    native_stop_training box dates n start physical ready rawNone before future after separated
      queue beyond weak strong count recovery
  refine ⟨final, e, hready, date, pending, ?_, ?_, ?_, hb, fires⟩
  · rw [hgain p]; simpa using strong.1
  · rw [hgain p]; simpa using strong.2
  · intro q hq
    rw [hgain q]
    simp [hq]

/-- If the gain after `n` doses is at most `21/10`, every earlier gain is at
most `7/6`, so each of the first `n` pulses is silent. -/
theorem weak_before_strong {z : ℝ} {n : ℕ} (top : Real.exp (z + 3 / 5 * (n : ℝ)) ≤ 21 / 10) :
    ∀ k : ℕ, k < n → Real.exp (z + 3 / 5 * (k : ℝ)) ≤ 7 / 6 := by
  intro k hk
  have next : (k : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hk
  have step : z + 3 / 5 * (k : ℝ) ≤ z + 3 / 5 * (n : ℝ) - 3 / 5 := by linarith
  have h := Real.exp_le_exp.mpr step
  rw [Real.exp_sub] at h
  have dose := learnedProbe_gain.1
  have pos := Real.exp_pos (3 / 5 : ℝ)
  have ratio : Real.exp (z + 3 / 5 * (n : ℝ)) / Real.exp (3 / 5) ≤ 7 / 6 := by
    rw [div_le_iff₀ pos]
    linarith
  linarith

/-- Native training that stops at the first FIRE, stated by its target
alone. If `n` doses bring the gain of the port into `[9/5, 21/10]`, a train
of at least `n` pulses leaves it there. The first `n` pulses are silent and
all later pulses make the cell fire. Start gains that need different
numbers of doses end in the same band. -/
theorem native_stop_training_of_target {θ ε} (box : @PhysicalBox 1 θ ε) {p : Port}
    {later : List (Delivery 1)} {horizon : ℝ} (dates : List ℝ) (n : ℕ) (start : Snapshot 1)
    (physical : PhysicalInvariant θ start) (ready : ReadyCoordinates start 0)
    (rawNone : ∀ q, start.raw 0 q = none) (before : start.time < horizon)
    (future : ∀ d ∈ dates, start.time < d) (after : ∀ d ∈ dates, d + 24 ≤ horizon)
    (separated : dates.Pairwise (fun a b => a + 24 ≤ b))
    (queue : start.pending = conjunctionDoseTokens p dates ++ later)
    (beyond : ∀ t ∈ later, horizon ≤ t.due)
    (target : 9 / 5 ≤ Real.exp (start.x 0 (.z p) + 3 / 5 * (n : ℝ)) ∧
      Real.exp (start.x 0 (.z p) + 3 / 5 * (n : ℝ)) ≤ 21 / 10)
    (count : n ≤ dates.length) (recovery : start.x 0 .b = 2 / 25) :
    ∃ (final : Snapshot 1) (e : Execution θ (fun _ _ => []) start final),
      ReadyCoordinates final 0 ∧ final.time < horizon ∧ final.pending = later ∧
      final.x 0 (.z p) = start.x 0 (.z p) + 3 / 5 * (n : ℝ) ∧
      9 / 5 ≤ Real.exp (final.x 0 (.z p)) ∧ Real.exp (final.x 0 (.z p)) ≤ 21 / 10 ∧
      (∀ q ≠ p, final.x 0 (.z q) = start.x 0 (.z q)) ∧ final.x 0 .b = 2 / 25 ∧
      (e.emissionTimes 0).length = dates.length - n := by
  obtain ⟨final, e, _, _, hready, _, date, pending, hgain, hb, _, fires⟩ :=
    native_stop_training box dates n start physical ready rawNone before future after separated
      queue beyond (weak_before_strong target.2)
      ⟨target.1, target.2.trans (by norm_num)⟩ count recovery
  have reached : final.x 0 (.z p) = start.x 0 (.z p) + 3 / 5 * (n : ℝ) := by
    rw [hgain p]; simp
  refine ⟨final, e, hready, date, pending, reached, ?_, ?_, ?_, hb, fires⟩
  · rw [reached]; exact target.1
  · rw [reached]; exact target.2
  · intro q hq
    rw [hgain q]
    simp [hq]

end RecursiveLearning.Native
