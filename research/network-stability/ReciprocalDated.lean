import DatedNetwork
import ReciprocalReverseRows
import ReciprocalClosure

namespace NetworkStability.NativeReciprocal

open KernelR.Hybrid
open PhaseAdmission

/-- Two ports on the same cell have disjoint native admission epochs.
The forward wire is complete before the first reverse source. -/
def reciprocalDate (p : ReciprocalProbe) : Prop :=
  (p.input.1 = 0 ∧ p.input.2 = 0 ∧ p.due < 300) ∨
  (p.input.1 = 0 ∧ p.input.2 = 2 ∧ 320 ≤ p.due) ∨
  (p.input.1 = 1 ∧ p.input.2 = 1 ∧ p.due < 315) ∨
  (p.input.1 = 1 ∧ p.input.2 = 2 ∧ 320 ≤ p.due)

theorem reciprocal_dates_exclusive (p q : ReciprocalProbe)
    (hp : reciprocalDate p) (hq : reciprocalDate q)
    (sameCell : p.input.1 = q.input.1) (sameDate : p.due = q.due) : p = q := by
  rcases p with ⟨tp, ip, pp⟩
  rcases q with ⟨tq, iq, pq⟩
  change ip = iq at sameCell
  change tp = tq at sameDate
  subst iq
  subst tq
  simp only [reciprocalDate] at hp hq
  rcases hp with h | h | h | h <;> rcases hq with k | k | k | k
  all_goals
    first
    | have same := h.2.1.trans k.2.1.symm
      subst pq
      rfl
    | have impossible : (0 : Fin 2) = 1 := by first | exact h.1.symm.trans k.1 | exact k.1.symm.trans h.1
      exact (by decide : (0 : Fin 2) ≠ 1) impossible |>.elim
    | exfalso
      linarith [h.2.2, k.2.2]

/-- A route preserving the reciprocal date bands needs no same-cell
interleaving margin. A tied physical probe on the same cell has the
same port and the same occurrence key. -/
theorem reciprocal_tie_admissible (C : Calendar 2 ℝ ReciprocalInput) (d : Nat)
    (seed : List ReciprocalProbe) (cell : C.cell = Prod.fst)
    (sources : ∀ p ∈ seed, reciprocalDate p)
    (route : ∀ p, reciprocalDate p → ∀ q ∈ C.route p, reciprocalDate q) :
    TieAdmissible C d (MarkFeedback.initial 2 seed) := by
  intro s reach
  have known : ∀ x ∈ s.pending, reciprocalDate x := by
    induction reach with
    | refl => exact sources
    | @tail a b _ step ih =>
      obtain ⟨picked, rest, available, _, rfl⟩ := step
      have pickedDate := ih picked (available.mem_iff.mpr (by simp))
      intro x mem
      change x ∈ rest ++ MarkFeedback.emitted C.model picked (MarkFeedback.read C.model d a picked 0) at mem
      rcases List.mem_append.mp mem with pending | born
      · exact ih x (available.mem_iff.mpr (List.mem_cons_of_mem _ pending))
      · by_cases h : MarkFeedback.read C.model d a picked 0 = true
        · simp only [MarkFeedback.emitted, h, ite_true] at born
          exact route picked pickedDate x born
        · simp [MarkFeedback.emitted, h] at born
  intro p q ep eq ne sameCell
  have date : p.due = q.due := le_antisymm (ep.2 q eq.1) (eq.2 p ep.1)
  have same : p.input.1 = q.input.1 := by simpa [Calendar.model, cell] using sameCell
  exact (ne (reciprocal_dates_exclusive p q (known p ep.1) (known q eq.1) same date)).elim


def reciprocalOccurrence (token : Delivery 2) : ReciprocalProbe :=
  ⟨token.due, token.cell, token.port⟩

/-- Future B sources can be reserved at the start. All their dates
are after the physical birth. -/
noncomputable def reciprocalSeed : List ReciprocalProbe :=
  (nominalStart.pending.map liftDelivery ++ constructedBBirthSources).map reciprocalOccurrence

theorem reciprocal_seed_bands : ∀ p ∈ reciprocalSeed, reciprocalDate p := by
  intro probe mem
  obtain ⟨token, source, rfl⟩ := List.mem_map.mp mem
  rcases List.mem_append.mp source with old | new
  · obtain ⟨one, member, rfl⟩ := List.mem_map.mp old
    change one ∈ sourceTrain 0 0 0 8 16 ++ sourceTrain 0 0 160 8 16 at member
    rcases List.mem_append.mp member with early | late
    · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp early
      have cap : (k.val : ℝ) ≤ 15 := by exact_mod_cast (show k.val ≤ 15 by omega)
      exact Or.inl ⟨rfl, rfl, by
        change (0 : ℝ) + 8 * (k.val : ℝ) < 300
        linarith⟩
    · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp late
      have cap : (k.val : ℝ) ≤ 15 := by exact_mod_cast (show k.val ≤ 15 by omega)
      exact Or.inl ⟨rfl, rfl, by
        change (160 : ℝ) + 8 * (k.val : ℝ) < 300
        linarith⟩
  · rcases List.mem_append.mp new with early | late
    · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp early
      exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, by
        change (320 : ℝ) ≤ 320 + 8 * (k.val : ℝ)
        linarith [Nat.cast_nonneg (α := ℝ) k.val]⟩))
    · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp late
      exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, by
        change (320 : ℝ) ≤ 480 + 8 * (k.val : ℝ)
        linarith [Nat.cast_nonneg (α := ℝ) k.val]⟩))

theorem reciprocal_issued_bands {cell : Fin 2} {fire : ℝ} {token : Delivery 2}
    (issued : token ∈ reciprocalEntryRouter nominalDelay nominalDelay cell fire) :
    reciprocalDate (reciprocalOccurrence token) := by
  classical
  rcases List.mem_append.mp issued with forward | reverse
  · unfold Contact.route at forward
    split_ifs at forward with gated
    · have eq := List.mem_singleton.mp forward
      subst token
      refine Or.inr (Or.inr (Or.inl ⟨rfl, rfl, ?_⟩))
      have bound : fire < (310 : ℝ) := gated.2.2
      change fire + 7 / 20 < 315
      linarith
    · simp at forward
  · unfold Contact.route at reverse
    split_ifs at reverse with gated
    · have eq := List.mem_singleton.mp reverse
      subst token
      refine Or.inr (Or.inl ⟨rfl, rfl, ?_⟩)
      have opening : (320 : ℝ) ≤ fire := gated.2.1
      change (320 : ℝ) ≤ fire + 7 / 20
      linarith
    · simp at reverse

/-- The physical gates themselves imply the tie hypothesis for any
calendar assigning a FIRE clock to each probe. The clock has to be
certified separately to obtain a native replay. -/
theorem reciprocal_route_has_tie_room (C : Calendar 2 ℝ ReciprocalInput) (d : Nat)
    (cell : C.cell = Prod.fst) (fire : ReciprocalProbe → ℝ)
    (route : ∀ p, C.route p =
      (reciprocalEntryRouter nominalDelay nominalDelay p.input.1 (fire p)).map reciprocalOccurrence) :
    TieAdmissible C d (MarkFeedback.initial 2 reciprocalSeed) := by
  apply reciprocal_tie_admissible C d reciprocalSeed cell reciprocal_seed_bands
  intro p _ q mem
  rw [route p] at mem
  obtain ⟨token, issued, rfl⟩ := List.mem_map.mp mem
  exact reciprocal_issued_bands issued


/-- The two route gates are separated in time. For any causal assignment
of FIRE clocks, a routed probe can have at most one descendant. -/
theorem reciprocal_route_acyclic (C : Calendar 2 ℝ ReciprocalInput)
    (fire : ReciprocalProbe → ℝ) (latency : ∀ p, p.due ≤ fire p ∧ fire p < p.due + 1)
    (route : ∀ p, C.route p =
      (reciprocalEntryRouter nominalDelay nominalDelay p.input.1 (fire p)).map reciprocalOccurrence)
    {p q r : ReciprocalProbe} (child : q ∈ C.route p) (grandchild : r ∈ C.route q) : False := by
  classical
  rw [route] at child grandchild
  obtain ⟨a, first, rfl⟩ := List.mem_map.mp child
  obtain ⟨b, second, _⟩ := List.mem_map.mp grandchild
  rcases List.mem_append.mp first with sent | sent
  · unfold Contact.route at sent
    split_ifs at sent with window
    · have same := List.mem_singleton.mp sent
      subst a
      have before : fire p < (310 : ℝ) := window.2.2
      have hi := (latency (reciprocalOccurrence ((teachingContact nominalDelay).token (fire p)))).2
      change fire (reciprocalOccurrence ((teachingContact nominalDelay).token (fire p))) <
        fire p + 7 / 20 + 1 at hi
      rcases List.mem_append.mp second with left | right
      · unfold Contact.route at left
        split_ifs at left with sender
        · exact (by decide : (1 : Fin 2) ≠ 0) sender.1
        · simp at left
      · unfold Contact.route at right
        split_ifs at right with sender
        · have after : (320 : ℝ) ≤ fire (reciprocalOccurrence ((teachingContact nominalDelay).token (fire p))) :=
            sender.2.1
          linarith
        · simp at right
    · simp at sent
  · unfold Contact.route at sent
    split_ifs at sent with window
    · have same := List.mem_singleton.mp sent
      subst a
      have after : (320 : ℝ) ≤ fire p := window.2.1
      have lo := (latency (reciprocalOccurrence ((feedbackContact nominalDelay).token (fire p)))).1
      change fire p + 7 / 20 ≤ fire (reciprocalOccurrence ((feedbackContact nominalDelay).token (fire p))) at lo
      rcases List.mem_append.mp second with left | right
      · unfold Contact.route at left
        split_ifs at left with sender
        · have before : fire (reciprocalOccurrence ((feedbackContact nominalDelay).token (fire p))) < (310 : ℝ) :=
            sender.2.2
          linarith
        · simp at left
      · unfold Contact.route at right
        split_ifs at right with sender
        · exact (by decide : (0 : Fin 2) ≠ 1) sender.1
        · simp at right
    · simp at sent


theorem reciprocal_route_causal_at_admission (C : Calendar 2 ℝ ReciprocalInput)
    (fire : ReciprocalProbe → ℝ) (latency : ∀ p, p.due ≤ fire p)
    (route : ∀ p, C.route p =
      (reciprocalEntryRouter nominalDelay nominalDelay p.input.1 (fire p)).map reciprocalOccurrence) :
    Causal C := by
  intro p q mem
  rw [route] at mem
  obtain ⟨token, native, rfl⟩ := List.mem_map.mp mem
  exact (latency p).trans (reciprocal_route_causal p.input.1 (fire p) token native)

private theorem reciprocal_route_short (i : Fin 2) (time : ℝ) :
    (reciprocalEntryRouter nominalDelay nominalDelay i time).length ≤ 1 := by
  classical
  fin_cases i
  · have different : (0 : Fin 2) ≠ 1 := by decide
    simp [reciprocalEntryRouter, Contact.route, teachingContact, feedbackContact, different]
    split <;> simp
  · have different : (1 : Fin 2) ≠ 0 := by decide
    simp [reciprocalEntryRouter, Contact.route, teachingContact, feedbackContact, different]
    split <;> simp

noncomputable def reciprocalWeight (C : Calendar 2 ℝ ReciprocalInput) (p : ReciprocalProbe) : Nat :=
  if (C.route p).isEmpty then 1 else 2

/-- The fixed gates give a concrete rank for this witness. Its seed is
the sixty-four external occurrences of the physical protocol. -/
theorem reciprocal_rank_certificate (C : Calendar 2 ℝ ReciprocalInput)
    (fire : ReciprocalProbe → ℝ) (latency : ∀ p, p.due ≤ fire p ∧ fire p < p.due + 1)
    (route : ∀ p, C.route p =
      (reciprocalEntryRouter nominalDelay nominalDelay p.input.1 (fire p)).map reciprocalOccurrence) :
    Nonempty (MarkFeedback.Rank 64 1 C.model reciprocalSeed) := by
  have short (p : ReciprocalProbe) : (C.route p).length ≤ 1 := by
    rw [route, List.length_map]
    exact reciprocal_route_short p.input.1 (fire p)
  have last (p q : ReciprocalProbe) (child : q ∈ C.route p) : C.route q = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    exact fun r mem => reciprocal_route_acyclic C fire latency route child mem
  refine ⟨⟨reciprocalWeight C, by decide, ?_, ?_⟩⟩
  · intro p
    change AutonomousFeedback.mass (reciprocalWeight C) (C.route p) + 1 ≤ reciprocalWeight C p
    cases h : C.route p with
    | nil => simp [h, reciprocalWeight, AutonomousFeedback.mass]
    | cons q tail =>
      have tailEmpty : tail = [] := by
        have size := short p
        rw [h, List.length_cons] at size
        exact List.length_eq_zero_iff.mp (by omega)
      subst tail
      have member : q ∈ C.route p := by rw [h]; simp
      simp [h, last p q member, reciprocalWeight, AutonomousFeedback.mass]
  · have count : reciprocalSeed.length = 64 := by
      simp [reciprocalSeed, nominalStart, constructedBBirthSources, sourceTrain]
    have bounded : ∀ rows : List ReciprocalProbe,
        AutonomousFeedback.mass (reciprocalWeight C) rows ≤ 2 * rows.length := by
      intro rows
      induction rows with
      | nil => simp [AutonomousFeedback.mass]
      | cons p rest ih =>
        have one : reciprocalWeight C p ≤ 2 := by unfold reciprocalWeight; split <;> decide
        change reciprocalWeight C p + AutonomousFeedback.mass (reciprocalWeight C) rest ≤ 2 * (rest.length + 1)
        omega
    have cap := bounded reciprocalSeed
    rw [count] at cap
    exact cap


theorem reciprocal_reserve_certificate (C : Calendar 2 ℝ ReciprocalInput)
    (fire : ReciprocalProbe → ℝ) (latency : ∀ p, p.due ≤ fire p ∧ fire p < p.due + 1)
    (route : ∀ p, C.route p =
      (reciprocalEntryRouter nominalDelay nominalDelay p.input.1 (fire p)).map reciprocalOccurrence) :
    Nonempty (MarkFeedback.Reserve 256 C.model reciprocalSeed) := by
  obtain ⟨rank⟩ := reciprocal_rank_certificate C fire latency route
  have scale (rows : List ReciprocalProbe) :
      AutonomousFeedback.mass (fun p => 2 * rank.weight p) rows =
        2 * AutonomousFeedback.mass rank.weight rows := by
    induction rows with
    | nil => rfl
    | cons p rest ih =>
      change 2 * rank.weight p + AutonomousFeedback.mass _ rest =
        2 * (rank.weight p + AutonomousFeedback.mass rank.weight rest)
      rw [ih]
      omega
  refine ⟨⟨fun _ p => 2 * rank.weight p, ?_, ?_⟩⟩
  · intro p fired i
    rw [scale]
    have cost : MarkFeedback.footprint C.model p fired i ≤ 2 := by
      unfold MarkFeedback.footprint
      split <;> split <;> decide
    have lower := rank.decreases p
    change AutonomousFeedback.mass rank.weight (C.route p) + 1 ≤ rank.weight p at lower
    cases fired
    · change 2 * 0 + _ ≤ _
      omega
    · change 2 * AutonomousFeedback.mass rank.weight (C.route p) + _ ≤ _
      omega
  · intro i
    rw [scale]
    have bound := rank.seed_bound
    omega

theorem reciprocal_clipped_ties (C : Calendar 2 ℝ ReciprocalInput) (d : Nat)
    (horizon : ℝ) (cell : C.cell = Prod.fst) (fire : ReciprocalProbe → ℝ)
    (route : ∀ p, C.route p =
      (reciprocalEntryRouter nominalDelay nominalDelay p.input.1 (fire p)).map reciprocalOccurrence) :
    TieAdmissible (C.through (· ≤ ·) horizon) d
      (horizonCut (· ≤ ·) horizon (MarkFeedback.initial 2 reciprocalSeed)) := by
  refine reciprocal_tie_admissible (C.through (· ≤ ·) horizon) d
    (horizonCut (· ≤ ·) horizon (MarkFeedback.initial 2 reciprocalSeed)).pending cell ?_ ?_
  · intro p mem
    exact reciprocal_seed_bands p (List.mem_filter.mp mem).1
  · intro p _ q mem
    have inside : q ∈ C.route p := (List.mem_filter.mp mem).1
    rw [route] at inside
    obtain ⟨token, issued, rfl⟩ := List.mem_map.mp inside
    exact reciprocal_issued_bands issued

open AutonomousFeedback.Schedule (Config SafeMemory)
open AutonomousFeedback.Schedule.PortMemory (Address Coordinate)

/-- A native replay, when all transaction rows have been connected, can
use the dated network theorem with route-derived certificates directly. -/
theorem reciprocal_replay_network (C : Calendar 2 ℝ ReciprocalInput) (d : Nat)
    (cell : C.cell = Prod.fst) (fire : ReciprocalProbe → ℝ)
    (latency : ∀ p, p.due ≤ fire p ∧ fire p < p.due + 1)
    (route : ∀ p, C.route p =
      (reciprocalEntryRouter nominalDelay nominalDelay p.input.1 (fire p)).map reciprocalOccurrence)
    (epoch : NominalEpoch) {rows out}
    (replay : TransactionReplay C d (· ≤ ·) (MarkFeedback.initial 2 reciprocalSeed) rows out)
    (nativeCounts : ∀ i c, out.writes (Address.mk i c).encode = doseCount i c) :
    SafeMemory 256 d 0 (d * 256 + 1) (fun _ => 0) out ∧
      NominalTrace C d (· ≤ ·) (MarkFeedback.initial 2 reciprocalSeed) (Transaction.word rows) out ∧
      (∀ i c, epoch.final.x i (nativeCoordinate i c) =
        birthMemory i c + unitDose c * out.writes (Address.mk i c).encode) := by
  obtain ⟨reserve⟩ := reciprocal_reserve_certificate C fire latency route
  have causal := reciprocal_route_causal_at_admission C fire (fun p => (latency p).1) route
  have diamond := reciprocal_route_has_tie_room C d cell fire route
  obtain ⟨safe, replayClean, _, _, _, _, _, _⟩ :=
    dated_network_memory 256 d 0 (d * 256 + 1) 64 1 C reciprocalSeed reserve
      (fun _ => 0) (fun _ => Nat.le_refl _) (by omega) causal diamond
  refine ⟨(safe out (MarkFeedback.certified_projects replay.trace.certified)).1,
    replayClean out _ replay.trace, fun i c => ?_⟩
  rw [nativeCounts]
  exact reciprocal_counts epoch i c

end NetworkStability.NativeReciprocal
