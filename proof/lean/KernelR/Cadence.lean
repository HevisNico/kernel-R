import KernelR.Doses
import KernelR.Flow

/-! Cadence-specific identities. The hybrid guards that justify each case and
the connection from physical executions to recorded traces remain hypotheses. -/
namespace KernelR.Cadence

/-- Unlike the old three-case abstraction, a protected input can produce both
a full MARK and a full ERROR after the main cell returns to READY. -/
inductive PulseCase where
  | weakError | fire | markOnly | markThenError
  deriving DecidableEq, Repr

def PulseCase.errors : PulseCase → Nat
  | .weakError | .markThenError => 1
  | _ => 0

def PulseCase.marks : PulseCase → Nat
  | .markOnly | .markThenError => 1
  | _ => 0

def PulseCase.fires : PulseCase → Nat
  | .fire => 1
  | _ => 0

theorem combined_case_has_both_doses : PulseCase.markThenError.errors = 1 ∧
    PulseCase.markThenError.marks = 1 ∧ PulseCase.markThenError.fires = 0 := by decide

structure RecordedStep where
  kind : PulseCase
  gainDoses : Nat
  protectedMarks : Nat
  deriving DecidableEq, Repr

/-- Check every recorded cumulative counter, not only the last totals. -/
def checkSteps (g m : Nat) : List RecordedStep → Bool
  | [] => true
  | s :: ss =>
    let g' := g + s.kind.errors
    let m' := m + s.kind.marks
    (s.gainDoses == g') && (s.protectedMarks == m') && checkSteps g' m' ss

def emissions (ss : List RecordedStep) : Nat := (ss.map fun s => s.kind.fires).sum
def errors (ss : List RecordedStep) : Nat := (ss.map fun s => s.kind.errors).sum
def marks (ss : List RecordedStep) : Nat := (ss.map fun s => s.kind.marks).sum

theorem two_additional_marks (b : ℝ) : b + 2 * markDose = b + 1 / 5 := by
  rw [markDose_exact]; ring

theorem final_recovery {birth : ℝ}
    (h : (7999 / 100000 : ℝ) ≤ birth ∧ birth ≤ 8001 / 100000) :
    (37999 / 100000 : ℝ) ≤ birth + markDose + 2 * markDose ∧
    birth + markDose + 2 * markDose ≤ 38001 / 100000 := by
  rw [markDose_exact]; constructor <;> linarith [h.1, h.2]

theorem four_error_doses_gain (z : ℝ) :
    Real.exp (z + 4 * errorDose) = Real.exp z * Real.exp (12 / 5) := by
  rw [errorDose_exact]
  have h : z + 4 * (3 / 5 : ℝ) = z + 12 / 5 := by ring
  rw [h, Real.exp_add]

theorem parent_extra_error (z : ℝ) :
    z + 3 * errorDose + errorDose = z + 4 * errorDose := by ring

/-- Actual integral of the declared exponential MARK recovery profile. -/
theorem mark_profile_integral (b : ℝ) {rate duration : ℝ} (hrate : rate ≠ 0) :
    (∫ t in (0 : ℝ)..duration, b + (1 / 2 : ℝ) * (1 - Real.exp (-rate * t))) =
      (b + 1 / 2) * duration + (Real.exp (-rate * duration) - 1) / (2 * rate) := by
  let primitive : ℝ → ℝ := fun t => (b + 1 / 2) * t + Real.exp (-rate * t) / (2 * rate)
  have hd (t : ℝ) : HasDerivAt primitive (b + (1 / 2 : ℝ) * (1 - Real.exp (-rate * t))) t := by
    convert ((hasDerivAt_id t).const_mul (b + 1 / 2)).add
      ((((hasDerivAt_id t).const_mul (-rate)).exp).div_const (2 * rate)) using 1
    · rfl
    · dsimp; field_simp; ring
  have hi : IntervalIntegrable
      (fun t : ℝ => b + (1 / 2 : ℝ) * (1 - Real.exp (-rate * t)))
      MeasureTheory.volume 0 duration := (by fun_prop : Continuous _).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi
  rw [h]
  dsimp [primitive]
  simp only [mul_zero, Real.exp_zero]
  ring

noncomputable def markDuration (rate : ℝ) : ℝ := Real.log (5 / 4) / rate
noncomputable def markDeficit (tau rate : ℝ) : ℝ :=
  tau / 10 + ((1 / 10 : ℝ) - (2 / 5) * Real.log (5 / 4)) / rate

/-- Integrate before, during and after MARK; the change in b is not instantaneous. -/
theorem accumulated_mark_formula (b tau u : ℝ) {rate : ℝ} (hrate : 0 < rate) :
    b * tau +
      (∫ t in (0 : ℝ)..markDuration rate, b + (1 / 2 : ℝ) * (1 - Real.exp (-rate * t))) +
      (b + 1 / 10) * (u - tau - markDuration rate) =
      (b + 1 / 10) * u - markDeficit tau rate := by
  rw [mark_profile_integral b (ne_of_gt hrate)]
  have he : Real.exp (-rate * markDuration rate) = (4 / 5 : ℝ) := by
    have h : -rate * markDuration rate = -Real.log (5 / 4) := by
      dsimp [markDuration]; field_simp
    rw [h, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 5 / 4)]
    norm_num
  rw [he]
  dsimp [markDuration, markDeficit]
  field_simp
  ring

/-- Algebraic return formula after MARK; guarding its domain is a separate obligation. -/
theorem return_integral_identity (b D J L : ℝ) (hb : b + 1 / 10 ≠ 0) :
    b * D + (b + 1 / 10) * ((L - b * D + J) / (b + 1 / 10)) - J = L := by
  rw [mul_div_cancel₀ _ hb]
  ring

theorem return_after_mark {b D J L endpoint : ℝ} (hb : 0 < b + 1 / 10)
    (h : b * D + (b + 1 / 10) * endpoint - J < L) :
    endpoint < (L - b * D + J) / (b + 1 / 10) := by
  apply (lt_div_iff₀ hb).2
  nlinarith

theorem post_mark_integral_strictMono {b D J : ℝ} (hb : 0 < b + 1 / 10) :
    StrictMono (fun u : ℝ => b * D + (b + 1 / 10) * u - J) := by
  intro x y hxy
  have := mul_lt_mul_of_pos_left hxy hb
  linarith

/-- A shared physical latency cancels; independent wire jitter does not. -/
theorem shared_latency_with_jitter (s t latency d₁ d₂ : ℝ) :
    (t + latency + d₂) - (s + latency + d₁) = (t - s) + (d₂ - d₁) := by ring

theorem period_four_one_wire {s t latency d₁ d₂ : ℝ} (hp : t - s = 4)
    (h₁ : (3 / 10 : ℝ) ≤ d₁ ∧ d₁ ≤ 2 / 5)
    (h₂ : (3 / 10 : ℝ) ≤ d₂ ∧ d₂ ≤ 2 / 5) :
    (39 / 10 : ℝ) ≤ (t + latency + d₂) - (s + latency + d₁) ∧
    (t + latency + d₂) - (s + latency + d₁) ≤ 41 / 10 := by
  constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]

theorem independent_jitter_changes_period :
    ((4 : ℝ) + 2 / 5) - (0 + 3 / 10) ≠ 4 := by norm_num

theorem two_wire_latency_with_jitter (s t c b dc₁ dc₂ db₁ db₂ : ℝ) :
    (t + c + dc₂ + b + db₂) - (s + c + dc₁ + b + db₁) =
      (t - s) + (dc₂ - dc₁) + (db₂ - db₁) := by ring

theorem period_four_two_wires {s t c b dc₁ dc₂ db₁ db₂ : ℝ} (hp : t - s = 4)
    (hc₁ : (3 / 10 : ℝ) ≤ dc₁ ∧ dc₁ ≤ 2 / 5)
    (hc₂ : (3 / 10 : ℝ) ≤ dc₂ ∧ dc₂ ≤ 2 / 5)
    (hb₁ : (3 / 10 : ℝ) ≤ db₁ ∧ db₁ ≤ 2 / 5)
    (hb₂ : (3 / 10 : ℝ) ≤ db₂ ∧ db₂ ≤ 2 / 5) :
    (19 / 5 : ℝ) ≤ (t + c + dc₂ + b + db₂) - (s + c + dc₁ + b + db₁) ∧
    (t + c + dc₂ + b + db₂) - (s + c + dc₁ + b + db₁) ≤ 21 / 5 := by
  constructor <;> linarith [hc₁.1, hc₁.2, hc₂.1, hc₂.2, hb₁.1, hb₁.2, hb₂.1, hb₂.2]

end KernelR.Cadence
