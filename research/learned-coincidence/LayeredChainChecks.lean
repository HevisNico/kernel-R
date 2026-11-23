import LayeredChain

/-! Boolean checkers, with soundness, for the trace premises of the chain: the schedule,
the latencies and the external window. A witness or a generated gate reduces them with
`decide +kernel`. -/

namespace LearnedCoincidence.Layered

open TwoLayer (ReadObservation SlotTiming)

def checkScheduled (s : Nat → Rat) : (c : Cascade M L N) → ReadTrace c → Bool
  | .input, _ => true
  | .layer (L := L) lower _ _, r =>
    checkScheduled s lower r.1 && (List.finRange N).all fun i => decide ((r.2.1 i).start = s (L + 1))

def checkLatencies (lmin lmax : Nat → Rat) : (c : Cascade M L N) → ReadTrace c → Bool
  | .input, _ => true
  | .layer (L := L) lower _ _, r =>
    checkLatencies lmin lmax lower r.1 && (List.finRange N).all fun i =>
      (r.2.1 i).emissions.all fun t =>
        decide ((r.2.1 i).start + lmin (L + 1) ≤ t ∧ t ≤ (r.2.1 i).start + lmax (L + 1))

def checkExternalWindow (s0 w : Rat) (c : Cascade M L N) (r : ReadTrace c) : Bool :=
  (List.finRange M).all fun j =>
    match inputTrace c r j with
    | none => true
    | some t => decide (s0 ≤ t ∧ t ≤ s0 + w)

private theorem all_fin {n : Nat} {P : Fin n → Bool} :
    (List.finRange n).all P = true ↔ ∀ i, P i = true := by
  simp [List.all_eq_true]

theorem scheduled_checker_sound {s : Nat → Rat} {c : Cascade M L N} {r : ReadTrace c}
    (h : checkScheduled s c r = true) : Scheduled s c r := by
  induction c with
  | input => trivial
  | @layer L N B lower timing nodes ih =>
    simp only [checkScheduled, Bool.and_eq_true] at h
    exact ⟨ih h.1, fun i => of_decide_eq_true (all_fin.mp h.2 i)⟩

theorem latencies_checker_sound {lmin lmax : Nat → Rat} {c : Cascade M L N} {r : ReadTrace c}
    (h : checkLatencies lmin lmax c r = true) : Latencies lmin lmax c r := by
  induction c with
  | input => trivial
  | @layer L N B lower timing nodes ih =>
    simp only [checkLatencies, Bool.and_eq_true] at h
    exact ⟨ih h.1, fun i t mem => of_decide_eq_true (List.all_eq_true.mp (all_fin.mp h.2 i) t mem)⟩

theorem external_window_checker_sound {s0 w : Rat} {c : Cascade M L N} {r : ReadTrace c}
    (h : checkExternalWindow s0 w c r = true) : ExternalWindow s0 w c r := by
  intro j t arrived
  have port := all_fin.mp h j
  rw [arrived] at port
  exact of_decide_eq_true port

end LearnedCoincidence.Layered
