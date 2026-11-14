import RestTolerance.Need

namespace RecursiveLearning.Native.RestTolerance
open KernelR.Hybrid

/-- A finite train has m writes when each silent read writes once and FIRE
writes nothing. Soundness and completeness of the physical detection
envelopes remain premises, and can be applied at different levels per side. -/
theorem observed_training_count
    {lo hi level₀ ℓ : ℝ} {m : ℕ} {z : ℕ → ℝ}
    (silentNeed : NeedAlongBand lo hi (level₀ - ℓ) z m)
    (fireNeed : NeedAlongBand lo hi (level₀ + ℓ) z m)
    (charge : Fin (m + 1) → ℝ) (observed : Fin (m + 1) → Bool)
    (band : ∀ k, ChargeBand lo hi (charge k))
    (sound : ∀ k, observed k = true →
      PulseFires (charge k) (Real.exp (z k.val)) (level₀ - ℓ))
    (complete : ∀ k, PulseFires (charge k) (Real.exp (z k.val)) (level₀ + ℓ) →
      observed k = true) :
    List.ofFn observed = List.replicate m false ++ [true] ∧
      (List.ofFn observed).count false = m := by
  have prior : (fun k : Fin m => observed k.castSucc) = fun _ => false := by
    funext k
    cases result : observed k.castSucc with
    | false => rfl
    | true =>
      exact False.elim (silentNeed.1 k.val k.isLt _ (band k.castSucc) (sound k.castSucc result))
  have last : observed (Fin.last m) = true :=
    complete (Fin.last m) (fireNeed.2 m le_rfl _ (band (Fin.last m)))
  have shape : List.ofFn observed = List.replicate m false ++ [true] := by
    rw [List.ofFn_succ_last, prior, List.ofFn_const, last]
  refine ⟨shape, ?_⟩
  rw [shape]
  simp

/-- A1 with a two-sided rest band, under explicit measured gain and detection
premises. Gain is clamped at m, so this finite result has no post-prefix
gain premise. -/
theorem observed_training_count_a1
    {lo hi level₀ ℓ d₀ aSilent aFire BSilent BFire : ℝ} {m : ℕ}
    (gain charge : Fin (m + 1) → ℝ) (observed : Fin (m + 1) → Bool)
    (levelFloor : 19 / 20 ≤ level₀ - ℓ) (ellPos : 0 ≤ ℓ)
    (dosePos : 0 ≤ d₀) (loPos : 0 ≤ lo) (hiPos : 0 ≤ hi) (hiCap : hi ≤ 1 / 20)
    (gainUpper : gain 0 - needCentre level₀ d₀ m ≤ aSilent)
    (gainLower : needCentre level₀ d₀ m - gain 0 ≤ aFire)
    (cumulativeUpper : ∀ k : Fin (m + 1), k.val < m →
      gain k - gain 0 - (k.val : ℝ) * d₀ ≤ BSilent)
    (cumulativeLower : gain 0 + (m : ℝ) * d₀ - gain (Fin.last m) ≤ BFire)
    (silenceRoom : aSilent + BSilent + 20 / 17 * ℓ + silenceCost hi < d₀ / 2)
    (fireRoom : aFire + BFire + 20 / 17 * ℓ + fireCost lo ≤ d₀ / 2)
    (band : ∀ k, ChargeBand lo hi (charge k))
    (sound : ∀ k, observed k = true →
      PulseFires (charge k) (Real.exp (gain k)) (level₀ - ℓ))
    (complete : ∀ k, PulseFires (charge k) (Real.exp (gain k)) (level₀ + ℓ) →
      observed k = true) :
    List.ofFn observed = List.replicate m false ++ [true] ∧
      (List.ofFn observed).count false = m := by
  let z (k : ℕ) := gain ⟨min k m, Nat.lt_succ_of_le (Nat.min_le_right k m)⟩
  have gainAt (k : Fin (m + 1)) : z k.val = gain k := by
    simp [z, min_eq_left (Nat.le_of_lt_succ k.isLt)]
  have need (level : ℝ) (floor : 19 / 20 ≤ level) (near : |level - level₀| ≤ ℓ) :
      NeedAlongBand lo hi level z m := by
    have nominalFloor : 19 / 20 ≤ level₀ := by linarith
    apply needAlong_of_asymmetric_rest_tolerance
      (aSilent := aSilent) (aFire := aFire) (BSilent := BSilent) (BFire := BFire) (ℓ := ℓ)
      z floor nominalFloor
      dosePos loPos hiPos hiCap
    · intro n hn
      simp [z, min_eq_right hn]
    · simpa [z] using gainUpper
    · simpa [z] using gainLower
    · intro k hk
      let j : Fin (m + 1) := ⟨k, Nat.lt_succ_of_lt hk⟩
      have bound := cumulativeUpper j hk
      change gain j - gain 0 - (k : ℝ) * d₀ ≤ BSilent at bound
      rw [show z k = gain j from gainAt j]
      exact bound
    · simpa [z, Fin.last] using cumulativeLower
    · exact near
    · exact silenceRoom
    · exact fireRoom
  apply observed_training_count
    (need _ levelFloor (abs_le.mpr ⟨by linarith, by linarith⟩))
    (need _ (by linarith) (abs_le.mpr ⟨by linarith, by linarith⟩)) charge observed band
  · intro k fired
    simpa only [gainAt k] using sound k fired
  · intro k fires
    exact complete k (by simpa only [gainAt k] using fires)

/-- The common status-3 budget implies both directional budgets. -/
theorem status3_implies_a1_rooms {a B ℓ d₀ lo hi : ℝ}
    (room : a + B + 20 / 17 * ℓ + max (silenceCost hi) (fireCost lo) < d₀ / 2) :
    a + B + 20 / 17 * ℓ + silenceCost hi < d₀ / 2 ∧
    a + B + 20 / 17 * ℓ + fireCost lo ≤ d₀ / 2 := by
  exact ⟨by linarith [le_max_left (silenceCost hi) (fireCost lo)],
    by linarith [le_max_right (silenceCost hi) (fireCost lo)]⟩

/-- Symmetric status 3 on the same finite physical interface. -/
theorem observed_training_count_status3
    {lo hi level₀ ℓ d₀ a B : ℝ} {m : ℕ}
    (gain charge : Fin (m + 1) → ℝ) (observed : Fin (m + 1) → Bool)
    (levelFloor : 19 / 20 ≤ level₀ - ℓ) (ellPos : 0 ≤ ℓ)
    (dosePos : 0 ≤ d₀) (loPos : 0 ≤ lo) (hiPos : 0 ≤ hi) (hiCap : hi ≤ 1 / 20)
    (initial : |gain 0 - needCentre level₀ d₀ m| ≤ a)
    (cumulative : ∀ k : Fin (m + 1), |gain k - gain 0 - (k.val : ℝ) * d₀| ≤ B)
    (room : a + B + 20 / 17 * ℓ + max (silenceCost hi) (fireCost lo) < d₀ / 2)
    (band : ∀ k, ChargeBand lo hi (charge k))
    (sound : ∀ k, observed k = true →
      PulseFires (charge k) (Real.exp (gain k)) (level₀ - ℓ))
    (complete : ∀ k, PulseFires (charge k) (Real.exp (gain k)) (level₀ + ℓ) →
      observed k = true) :
    List.ofFn observed = List.replicate m false ++ [true] ∧
      (List.ofFn observed).count false = m := by
  obtain ⟨silenceRoom, fireRoom⟩ := status3_implies_a1_rooms room
  apply observed_training_count_a1 (aFire := a) (BFire := B) gain charge observed levelFloor ellPos dosePos
    loPos hiPos hiCap (abs_le.mp initial).2 ?_ ?_ ?_ silenceRoom fireRoom band sound complete
  · linarith [(abs_le.mp initial).1]
  · intro k _
    exact (abs_le.mp (cumulative k)).2
  · have lower := (abs_le.mp (cumulative (Fin.last m))).1
    change -B ≤ gain (Fin.last m) - gain 0 - (m : ℝ) * d₀ at lower
    linarith

end RecursiveLearning.Native.RestTolerance
