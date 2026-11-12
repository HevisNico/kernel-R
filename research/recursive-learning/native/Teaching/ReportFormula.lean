import Teaching.ScheduledCircuit

/-! A Boolean formula can be laid out as a native report circuit.
Disjunction and cardinality thresholds are built from AND and NOT. -/

namespace RecursiveLearning.Native
open KernelR.Hybrid

inductive ReportFormula (n : ℕ) where
  | input (i : Fin n)
  | neg (a : ReportFormula n)
  | both (a b : ReportFormula n)

def ReportFormula.eval {n} (bits : Fin n → Bool) : ReportFormula n → Bool
  | .input i => bits i
  | .neg a => !(a.eval bits)
  | .both a b => a.eval bits && b.eval bits

def ReportFormula.either {n} (a b : ReportFormula n) : ReportFormula n :=
  .neg (.both (.neg a) (.neg b))

theorem ReportFormula.eval_either {n} (bits : Fin n → Bool) (a b : ReportFormula n) :
    (a.either b).eval bits = (a.eval bits || b.eval bits) := by
  simp only [ReportFormula.either, ReportFormula.eval]
  cases a.eval bits <;> cases b.eval bits <;> rfl

def ReportFormula.constant {n} (anchor : Fin n) (value : Bool) : ReportFormula n :=
  let f := .both (.input anchor) (.neg (.input anchor))
  if value then .neg f else f

theorem ReportFormula.eval_constant {n} (bits : Fin n → Bool) (anchor : Fin n) (value : Bool) :
    (ReportFormula.constant anchor value).eval bits = value := by
  cases value <;> cases h : bits anchor <;> simp [ReportFormula.constant, ReportFormula.eval, h]

/-- This recurrence uses a disjunction of two sufficient cases. A passed
first report reduces the remaining count by one. -/
def ReportFormula.threshold {n} (anchor : Fin n) : List (Fin n) → ℕ → ReportFormula n
  | _, 0 => .constant anchor true
  | [], _ + 1 => .constant anchor false
  | i :: rest, k + 1 =>
    (ReportFormula.both (.input i) (threshold anchor rest k)).either (threshold anchor rest (k + 1))

theorem ReportFormula.eval_threshold {n} (bits : Fin n → Bool) (anchor : Fin n)
    (inputs : List (Fin n)) (k : ℕ) :
    (ReportFormula.threshold anchor inputs k).eval bits = decide (k ≤ (inputs.filter bits).length) := by
  induction inputs generalizing k with
  | nil =>
    cases k <;> simp [ReportFormula.threshold, ReportFormula.eval_constant]
  | cons i rest ih =>
    cases k with
    | zero => simp [ReportFormula.threshold, ReportFormula.eval_constant]
    | succ k =>
      rw [ReportFormula.threshold, ReportFormula.eval_either]
      simp only [ReportFormula.eval, ih]
      by_cases h : bits i = true
      · simp only [h, Bool.true_and, List.filter_cons_of_pos, List.length_cons]
        by_cases enough : k ≤ (rest.filter bits).length
        · simp [enough, show k + 1 ≤ (rest.filter bits).length + 1 by omega]
        · simp [enough, show ¬k + 1 ≤ (rest.filter bits).length by omega,
            show ¬k + 1 ≤ (rest.filter bits).length + 1 by omega]
      · have no : bits i = false := Bool.eq_false_iff.mpr h
        simp [no]

structure FormulaExtension {n m} (prior : ReportCircuit n m) (place : Fin n → Fin m)
    (f : ReportFormula n) where
  size : ℕ
  circuit : ReportCircuit n size
  output : Fin size
  carry : Fin m → Fin size
  preserves : ∀ bits i, circuit.eval bits (carry i) = prior.eval bits i
  computes : ∀ bits, circuit.eval bits output = f.eval (fun i => prior.eval bits (place i))

/-- Compile a formula at any point in a topologically ordered circuit.
The returned index embedding preserves every previously named report. -/
noncomputable def ReportFormula.append {n m} (prior : ReportCircuit n m) (place : Fin n → Fin m)
    (f : ReportFormula n) : FormulaExtension prior place f :=
  match f with
  | .input i => ⟨m, prior, place i, id, fun _ _ => rfl, fun _ => rfl⟩
  | .neg a =>
    let lhs := a.append prior place
    ⟨lhs.size + 1, .notGate lhs.circuit lhs.output, 0, fun i => (lhs.carry i).succ,
      lhs.preserves, fun bits => by
        change Bool.not (lhs.circuit.eval bits lhs.output) = _
        rw [lhs.computes]
        rfl⟩
  | .both a b =>
    let lhs := a.append prior place
    let rhs := b.append lhs.circuit (fun i => lhs.carry (place i))
    let lhsOutput := rhs.carry lhs.output
    ⟨rhs.size + 1, .andGate rhs.circuit lhsOutput [rhs.output], 0,
      fun i => (rhs.carry (lhs.carry i)).succ,
      fun bits i => (rhs.preserves bits (lhs.carry i)).trans (lhs.preserves bits i),
      fun bits => by
        change decide (∀ i ∈ [lhsOutput, rhs.output], rhs.circuit.eval bits i = true) = _
        have left : rhs.circuit.eval bits lhsOutput = a.eval (fun i => prior.eval bits (place i)) :=
          (rhs.preserves bits lhs.output).trans (lhs.computes bits)
        have right : rhs.circuit.eval bits rhs.output = b.eval (fun i => prior.eval bits (place i)) := by
          rw [rhs.computes]
          congr 1
          funext i
          exact lhs.preserves bits (place i)
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, left, ReportFormula.eval]
        cases a.eval (fun i => prior.eval bits (place i)) <;>
          cases hb : b.eval (fun i => prior.eval bits (place i)) <;> simp [right, hb]⟩

noncomputable def ReportFormula.compile {n} (f : ReportFormula n) :
    FormulaExtension (ReportCircuit.inputs : ReportCircuit n n) id f :=
  f.append .inputs id

/-- Any threshold formula, in particular OR at threshold one, runs on
ordinary R cells with a common outcome-independent schedule. -/
theorem threshold_report_network {n ε} (anchor : Fin n) (inputs : List (Fin n)) (k : ℕ)
    (time : ℝ) (kinds passed : Fin n → Bool) :
    let build := (ReportFormula.threshold anchor inputs k).compile
    let layout := build.circuit.compile (learnerReportLayout time kinds passed)
    let T := layout.last + 46
    ∀ θ (_box : @PhysicalBox build.size θ ε),
      ∃ run : CompiledRun θ layout T (build.circuit.eval passed),
        Reports run.execution build.output (layout.windows build.output)
          (decide (k ≤ (inputs.filter passed).length)) := by
  intro build layout T θ box
  obtain ⟨run⟩ := build.circuit.run_with_learners box time kinds passed (T := T)
    (by change layout.last + 45 < layout.last + 46; linarith)
  have value := build.computes passed
  change build.circuit.eval passed build.output =
    (ReportFormula.threshold anchor inputs k).eval passed at value
  rw [ReportFormula.eval_threshold] at value
  exact ⟨run, value ▸ run.reports build.output⟩

end RecursiveLearning.Native
