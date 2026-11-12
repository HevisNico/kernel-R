import Search.SuccessiveSearch

/-! A lag between a pulse and its effect. In a circuit the element that
applies a gain takes a short time to settle, so a pulse acts on the main
charge a little after it arrives. A lag that is the same for every pulse
of a cell shifts the FIRE dates of that cell by that lag. The decision
on two FIRE dates then depends only on the difference between the lags
of the two cells. -/

namespace RecursiveLearning.Native
open KernelR.Hybrid Set

/-- The coincidence decision with a lag on each side. The two read FIRE
dates are observed `lagL` and `lagR` later than the model gives them. If
the two lags differ by at most 3/100 of a unit, the observed dates are
closer than 3/20 exactly when the two cells are read at the same date. -/
theorem trained_dates_decide_lag {readL₁ readL₂ readR₁ readR₂ tfL tfR offset lagL lagR lag₀ : ℝ}
    (leftAfter : readL₁ + 239 / 1000 < tfL) (leftBefore : tfL ≤ readL₂ + 32 / 125)
    (rightAfter : readR₁ + 239 / 1000 < tfR) (rightBefore : tfR ≤ readR₂ + 32 / 125)
    (leftOrder : readL₁ ≤ readL₂ ∧ readL₂ ≤ readL₁ + 1 / 10)
    (rightOrder : readR₁ ≤ readR₂ ∧ readR₂ ≤ readR₁ + 1 / 10)
    (schedule : readR₁ = readL₁ + offset)
    (offsets : offset = -(3 / 10) ∨ offset = 0 ∨ offset = 3 / 10)
    (leftLag : lag₀ ≤ lagL ∧ lagL ≤ lag₀ + 3 / 100)
    (rightLag : lag₀ ≤ lagR ∧ lagR ≤ lag₀ + 3 / 100) :
    |(tfR + lagR) - (tfL + lagL)| < 3 / 20 ↔ offset = 0 := by
  constructor
  · intro close
    obtain ⟨lo, hi⟩ := abs_lt.mp close
    rcases offsets with h | h | h
    · exfalso; linarith
    · exact h
    · exfalso; linarith
  · intro zero
    exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- A network of any number of trained cells, each with its own lag. In
every complete run the last FIRE of each cell is its read FIRE, and for
any two cells read with an offset of −0.3, 0 or +0.3 units, the observed
dates are closer than 3/20 exactly when the offset is zero, as long as
the lags of the cells lie within 3/100 of a unit of each other. -/
theorem trained_network_lag {n : ℕ} (pos : 0 < n) {θ : Fin n → Fin 1 → Parameters}
    {ε T rest : ℝ} {s : Fin n → Snapshot 1} {p₁ p₂ : Fin n → Port}
    {u₁ l₁ u₂ l₂ level : Fin n → ℝ} {dates₁ dates₂ : Fin n → List ℝ}
    {middle read₁ read₂ : Fin n → ℝ} {r₁ r₂ : Fin n → ℕ}
    (cells : ∀ i, TrainedCell (θ i) ε (s i) (p₁ i) (p₂ i) (u₁ i) (l₁ i) (u₂ i) (l₂ i) (level i)
      (dates₁ i) (dates₂ i) (middle i) (read₁ i) (read₂ i) rest (r₁ i) (r₂ i))
    (start : ∀ i, (s i).time = T) (lag : Fin n → ℝ) (lag₀ : ℝ)
    (band : ∀ i, lag₀ ≤ lag i ∧ lag i ≤ lag₀ + 3 / 100) :
    ∃ (tf : Fin n → ℝ) (training : Fin n → List ℝ),
      (∀ i j offset, read₂ i ≤ read₁ i + 1 / 10 → read₂ j ≤ read₁ j + 1 / 10 →
        read₁ j = read₁ i + offset → (offset = -(3 / 10) ∨ offset = 0 ∨ offset = 3 / 10) →
        (|(tf j + lag j) - (tf i + lag i)| < 3 / 20 ↔ offset = 0)) ∧
      (∃ (u : Snapshot n) (ref : ParameterExecution (familyParameters θ) (fun _ _ => [])
        (Snapshot.family T s) u), ParameterCompleteThrough ref rest) ∧
      ∀ {u : Snapshot n} (ex : ParameterExecution (familyParameters θ) (fun _ _ => [])
        (Snapshot.family T s) u), ParameterCompleteThrough ex rest →
        ∀ i, ex.emissionTimes i = training i ++ [tf i] := by
  obtain ⟨tf, training, windows, _, ref, all⟩ := trained_network pos cells start
  refine ⟨tf, training, ?_, ref, all⟩
  intro i j offset staggerI staggerJ schedule offsets
  exact trained_dates_decide_lag (windows i).1 (windows i).2 (windows j).1 (windows j).2
    ⟨(cells i).order.1, staggerI⟩ ⟨(cells j).order.1, staggerJ⟩ schedule offsets (band i) (band j)

end RecursiveLearning.Native
