import KernelR.Chain.Induction
import KernelR.Cadence

/-! Dose, cut and terminal-time consequences of the local execution contracts.
Words specify physical cases whose realizability is a separate premise. -/
namespace KernelR.Chain
open Cadence

def countCases (f : PulseCase → ℕ) : List PulseCase → ℕ
  | [] => 0
  | c :: cs => f c + countCases f cs

theorem count_append (f : PulseCase → ℕ) (a b : List PulseCase) :
    countCases f (a ++ b) = countCases f a + countCases f b := by
  induction a with
  | nil => simp [countCases]
  | cons c cs ih => simp [countCases, ih, Nat.add_assoc]

theorem count_replicate (f : PulseCase → ℕ) (c : PulseCase) (n : ℕ) :
    countCases f (List.replicate n c) = n * f c := by
  induction n with
  | zero => simp [countCases]
  | succ n ih => simp [List.replicate_succ, countCases, ih, Nat.succ_mul, Nat.add_comm]

def leafWord (K : ℕ) : List PulseCase :=
  List.replicate 3 .weakError ++ [.fire, .markOnly, .fire, .markThenError] ++
    List.replicate (K - 7) .fire

def relayWord (m L : ℕ) : List PulseCase :=
  List.replicate m .fire ++ [.markOnly, .fire, .markThenError] ++
    List.replicate (L - 3) .fire

theorem leaf_errors (K : ℕ) : countCases PulseCase.errors (leafWord K) = 4 := by
  simp [leafWord, count_append, count_replicate, countCases, PulseCase.errors]

theorem leaf_marks (K : ℕ) : countCases PulseCase.marks (leafWord K) = 2 := by
  simp [leafWord, count_append, count_replicate, countCases, PulseCase.marks]

theorem leaf_emissions {K : ℕ} (hK : 9 ≤ K) :
    countCases PulseCase.fires (leafWord K) = K - 5 := by
  simp [leafWord, count_append, count_replicate, countCases, PulseCase.fires]
  omega

theorem relay_errors (m L : ℕ) : countCases PulseCase.errors (relayWord m L) = 1 := by
  simp [relayWord, count_append, count_replicate, countCases, PulseCase.errors]

theorem relay_marks (m L : ℕ) : countCases PulseCase.marks (relayWord m L) = 2 := by
  simp [relayWord, count_append, count_replicate, countCases, PulseCase.marks]

theorem relay_emissions {m L : ℕ} (hL : 5 ≤ L) :
    countCases PulseCase.fires (relayWord m L) = m + L - 2 := by
  simp [relayWord, count_append, count_replicate, countCases, PulseCase.fires]
  omega

theorem leaf_gain (z : ℝ) (K : ℕ) :
    Real.exp (z + countCases PulseCase.errors (leafWord K) * errorDose) =
      Real.exp z * Real.exp (12 / 5) := by
  rw [leaf_errors]
  exact four_error_doses_gain z

theorem relay_gain_after_preparation (z : ℝ) (m L : ℕ) :
    Real.exp (z + (3 + countCases PulseCase.errors (relayWord m L)) * errorDose) =
      Real.exp z * Real.exp (12 / 5) := by
  rw [relay_errors]
  norm_num
  exact four_error_doses_gain z

theorem learned_recovery {birth : ℝ}
    (h : (7999 / 100000 : ℝ) ≤ birth ∧ birth ≤ 8001 / 100000) :
    (37999 / 100000 : ℝ) ≤ birth + markDose + 2 * markDose ∧
    birth + markDose + 2 * markDose ≤ 38001 / 100000 :=
  final_recovery h

theorem learned_probe_word : countCases PulseCase.fires (List.replicate 8 .fire) = 8 := by
  decide

theorem prepared_relay_probe_word :
    countCases PulseCase.fires
      [.fire, .markOnly, .fire, .markOnly, .fire, .markOnly, .fire, .markOnly] = 4 := by
  decide

/-- Silence propagation after cutting the incoming edge at k; the local silence
rule must follow from the physical READY/no-current equations. -/
theorem cut_propagates (Silent : ℕ → Prop) (k : ℕ) (atCut : Silent k)
    (relaySilent : ∀ j, Silent j → Silent (j + 1)) :
    ∀ distance, Silent (k + distance) := by
  intro distance
  induction distance with
  | zero => simpa using atCut
  | succ d ih => simpa [Nat.add_assoc] using relaySilent (k + d) ih

theorem hop_allowance {latency delay : ℝ} (hl : latency ≤ 66 / 100)
    (hd : delay ≤ 2 / 5) : latency + delay ≤ 11 / 10 := by linarith

theorem latest_input_bound (latest : ℕ → ℝ) (lastSource : ℝ)
    (base : latest 0 ≤ lastSource)
    (step : ∀ j, latest (j + 1) ≤ latest j + 11 / 10) :
    ∀ j, latest j ≤ lastSource + (11 / 10) * j := by
  intro j
  induction j with
  | zero => simpa using base
  | succ j ih =>
    have h := step j
    push_cast
    linarith

theorem all_cells_quiescent_by
    (N K : ℕ) (hN : 0 < N)
    (latest : ℕ → ℝ) (quiet : ℕ → ℝ → Prop)
    (base : latest 0 ≤ 160 + 4 * ((K - 1 : ℕ) : ℝ))
    (hop : ∀ j, latest (j + 1) ≤ latest j + 11 / 10)
    (finish : ∀ j t, latest j + 8 ≤ t → quiet j t) :
    ∀ j, j < N →
      quiet j (160 + 4 * ((K - 1 : ℕ) : ℝ) +
        (11 / 10) * ((N - 1 : ℕ) : ℝ) + 8) := by
  intro j hj
  apply finish
  have h := latest_input_bound latest _ base hop j
  have hj' : j ≤ N - 1 := by omega
  have hc : (j : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by exact_mod_cast hj'
  linarith

/-- READY comparison uses the same realized gain, not independent latency boxes. -/
theorem same_gain_ready_comparison (r gain h : ℝ) {x decay : ℝ}
    (hx : 0 ≤ x) (hd : 0 ≤ decay) :
    r + gain * h ≤ r + x * decay + gain * h := by
  nlinarith [mul_nonneg hx hd]

theorem first_crossing_no_later
    (withResidual fromRest : ℝ → ℝ) (threshold t₁ t₂ : ℝ)
    (comparison : ∀ t, fromRest t ≤ withResidual t)
    (restCrosses : fromRest t₂ = threshold)
    (before : ∀ t, t < t₁ → withResidual t < threshold) : t₁ ≤ t₂ := by
  by_contra h
  have ht : t₂ < t₁ := lt_of_not_ge h
  have hlt := before t₂ ht
  have hle := comparison t₂
  linarith

end KernelR.Chain
