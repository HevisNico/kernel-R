import LayeredMonotoneTarget
import MonotoneCharacterization

namespace LearnedCoincidence.Layered

open TwoLayer (SlotTiming)
open MonotoneDNF (MonotoneFunction contains_iff)

private theorem gate_monotone (g : Gate) {x y : Pattern 2}
    (included : ∀ a, x a = true → y a = true) (hx : g.eval x = true) :
    g.eval y = true := by
  cases g with
  | off => contradiction
  | on => rfl
  | copy => exact included 0 hx
  | both =>
    obtain ⟨h₀, h₁⟩ := Bool.and_eq_true_iff.mp hx
    exact Bool.and_eq_true_iff.mpr ⟨included 0 h₀, included 1 h₁⟩
  | either =>
    rcases Bool.or_eq_true_iff.mp hx with h | h
    · exact Bool.or_eq_true_iff.mpr (Or.inl (included 0 h))
    · exact Bool.or_eq_true_iff.mpr (Or.inr (included 1 h))

private theorem prediction_monotone (c : Cascade M L N) (i : Fin N) :
    MonotoneFunction (fun x => c.predict x i) := by
  intro x y contained active
  induction c with
  | input => exact contains_iff.mp contained i active
  | layer lower timing nodes ih =>
    apply gate_monotone (nodes i).cell.gate _ active
    intro a on
    cases source : (nodes i).source a with
    | none => simp [Node.inputs, source] at on
    | some j =>
      have lowerOn : lower.predict x j = true := by simpa [Node.inputs, source] using on
      simpa [Node.inputs, source] using ih j lowerOn

private theorem ports (a : Fin 2) : a = 0 ∨ a = 1 := by omega

/-- A single dose gives 4 on a trained port. The AND needs 6, the other
gates use threshold 2, and the constant true gate supplies help 4. -/
def canonical (g : Gate) : Cell where
  gate := g
  initialGain := fun _ => 0
  help := if g = .on then 4 else 0
  threshold := if g = .both then 6 else 2
  trainError := 1
  testError := 1
  dose := 4
  maxWrites := 1
  rail := 5

theorem canonical_valid (g : Gate) : (canonical g).Valid := by
  refine ⟨by change 0 < 4; decide, ?_, ?_, ?_, ?_⟩
  · intro a active
    let p := canonical g
    have measured : p.stop a = 1 ∧ p.groupScore a 0 + p.trainError < p.threshold ∧
        p.threshold + p.trainError ≤ p.groupScore a 1 := by
      rcases ports a with rfl | rfl <;> cases g <;> first | decide +kernel | contradiction
    obtain ⟨stop, early, fire⟩ := measured
    change (0 < p.stop a ∧ p.stop a ≤ p.maxWrites) ∧
      (∀ k, k < p.stop a → p.groupScore a k + p.trainError < p.threshold) ∧
      p.threshold + p.trainError ≤ p.groupScore a (p.stop a)
    rw [stop]
    refine ⟨by change 0 < 1 ∧ 1 ≤ 1; decide, ?_, fire⟩
    intro k bound
    have zero : k = 0 := by omega
    simpa [zero] using early
  · intro a
    rcases ports a with rfl | rfl <;> cases g <;> decide +kernel
  · intro x silent
    cases h₀ : x 0 <;> cases h₁ : x 1 <;> cases g <;>
      simp [canonical, Gate.eval, h₀, h₁] at silent <;>
      simp only [Cell.score, h₀, h₁, Bool.false_eq_true, ite_false, ite_true] <;> decide +kernel
  · intro x member
    cases g <;> simp [canonical, Gate.anchors] at member
    all_goals first | (subst x; decide +kernel) | (rcases member with rfl | rfl <;> decide +kernel)

private def allOn : Pattern M := fun _ => true

private def makeNode (g : Gate) (a b : Option (Fin N)) (s t : Pattern M) : Node M N where
  cell := canonical g
  source := fun j => if j = 0 then a else b
  delay := fun _ => 0
  stimulus := fun j => if j = 0 then s else t

private def standardTiming : SlotTiming := ⟨0, 1, 2⟩

private theorem standardTiming_valid : standardTiming.Valid := by
  unfold SlotTiming.Valid
  decide

private theorem constant_valid (g : Gate) (mode : g = .off ∨ g = .on)
    (predict : Pattern M → Pattern N) :
    (makeNode g none none allOn allOn).Valid predict := by
  refine ⟨canonical_valid g, ?_, ?_⟩
  · rcases mode with rfl | rfl <;>
      simp [makeNode, canonical, Gate.uses]
  · rcases mode with rfl | rfl <;> simp [makeNode, canonical, Gate.groups]

private theorem copy_valid (predict : Pattern M → Pattern N) (i : Fin N)
    (hot : predict allOn i = true) :
    (makeNode .copy (some i) none allOn allOn).Valid predict := by
  refine ⟨canonical_valid .copy, ?_, ?_⟩
  · simp [makeNode, canonical, Gate.uses, Fin.forall_fin_two]
  · intro a active
    have zero : a = 0 := by
      change a.val < 1 at active
      omega
    subst a
    funext j
    revert j
    simp [Fin.forall_fin_two, Node.inputs, makeNode, canonical, Gate.groupMask, MonotoneDNF.singleton, hot]

private def extend (c : Cascade M L N) (d : Node M N) : Cascade M (L + 1) (N + 1) :=
  .layer c standardTiming
    (Fin.lastCases d (fun j => makeNode .copy (some j) none allOn allOn))

private theorem extend_valid {c : Cascade M L N} (valid : c.Valid)
    (hot : ∀ i, c.predict allOn i = true) {d : Node M N} (node : d.Valid c.predict) :
    (extend c d).Valid := by
  refine ⟨valid, standardTiming_valid, ?_⟩
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using node
  · simpa only [Fin.lastCases_castSucc] using copy_valid c.predict j (hot j)

private theorem extend_keep (c : Cascade M L N) (d : Node M N) (x : Pattern M) (i : Fin N) :
    (extend c d).predict x i.castSucc = c.predict x i := by
  simp [extend, Cascade.predict, Fin.lastCases_castSucc, makeNode, canonical, Gate.eval, Node.inputs]

private theorem extend_last (c : Cascade M L N) (d : Node M N) (x : Pattern M) :
    (extend c d).predict x (Fin.last N) = d.cell.gate.eval (d.inputs (c.predict x)) := by
  simp [extend, Cascade.predict, Fin.lastCases_last]

private inductive Binary where
  | both | either

private def Binary.gate : Binary → Gate
  | .both => .both
  | .either => .either

private def Binary.eval : Binary → Bool → Bool → Bool
  | .both, a, b => a && b
  | .either, a, b => a || b

private theorem binary_eval (op : Binary) (x : Pattern 2) :
    op.gate.eval x = op.eval (x 0) (x 1) := by cases op <;> rfl

private def Binary.Lessons (op : Binary) (l r : Pattern M → Bool) (s t : Pattern M) : Prop :=
  match op with
  | .both => True
  | .either => l s = true ∧ r s = false ∧ l t = false ∧ r t = true

private def binaryNode (op : Binary) (a b : Fin N) (s t : Pattern M) : Node M N :=
  makeNode op.gate (some a) (some b) (match op with | .both => allOn | .either => s) t

private theorem binary_node_valid {predict : Pattern M → Pattern N} {a b : Fin N}
    (op : Binary) (hot : ∀ i, predict allOn i = true) {s t : Pattern M}
    (lessons : op.Lessons (fun x => predict x a) (fun x => predict x b) s t) :
    (binaryNode op a b s t).Valid predict := by
  refine ⟨canonical_valid op.gate, ?_, ?_⟩
  · cases op <;> simp [binaryNode, makeNode, Binary.gate, canonical, Gate.uses, Fin.forall_fin_two]
  · intro group active
    cases op with
    | both =>
      have zero : group = 0 := by
        change group.val < 1 at active
        omega
      subst group
      funext j
      revert j
      simp [binaryNode, makeNode, Binary.gate, canonical, Gate.groupMask, fullMask,
        Node.inputs, Fin.forall_fin_two, hot]
    | either =>
      obtain ⟨left, notRight, notLeft, right⟩ := lessons
      rcases ports group with rfl | rfl <;>
        funext j <;> revert j <;>
        simp [binaryNode, makeNode, Binary.gate, canonical, Gate.groupMask, MonotoneDNF.singleton,
          Node.inputs, Fin.forall_fin_two, left, notRight, notLeft, right]

private theorem binary_node_eval (op : Binary) (a b : Fin N) (s t : Pattern M) (x : Pattern N) :
    op.gate.eval ((binaryNode op a b s t).inputs x) = op.eval (x a) (x b) := by
  simp [binary_eval, binaryNode, makeNode, Node.inputs]

private inductive Formula (M : Nat) where
  | wire : Fin M → Formula M
  | unit : Formula M
  | combine : Binary → Formula M → Formula M → Pattern M → Pattern M → Formula M

private def Formula.eval : Formula M → Pattern M → Bool
  | .wire a, x => x a
  | .unit, _ => true
  | .combine op l r _ _, x => op.eval (l.eval x) (r.eval x)

private def Formula.Trainable : Formula M → Prop
  | .wire _ | .unit => True
  | .combine op l r s t => l.Trainable ∧ r.Trainable ∧ op.Lessons l.eval r.eval s t

private structure Extension (c : Cascade M L N) (f : Pattern M → Bool) where
  layers : Nat
  width : Nat
  net : Cascade M layers width
  tap : Fin N → Fin width
  out : Fin width
  valid : net.Valid
  keeps : ∀ x i, net.predict x (tap i) = c.predict x i
  gives : ∀ x, net.predict x out = f x
  hot : ∀ i, net.predict allOn i = true

private def Extension.chain {c : Cascade M L N} {f g : Pattern M → Bool}
    (a : Extension c f) (b : Extension a.net g) : Extension c g where
  layers := b.layers
  width := b.width
  net := b.net
  tap := b.tap ∘ a.tap
  out := b.out
  valid := b.valid
  keeps := fun x i => (b.keeps x (a.tap i)).trans (a.keeps x i)
  gives := b.gives
  hot := b.hot

private def addNode {c : Cascade M L N} (valid : c.Valid)
    (hot : ∀ i, c.predict allOn i = true) {d : Node M N} (node : d.Valid c.predict)
    {f : Pattern M → Bool}
    (value : ∀ x, d.cell.gate.eval (d.inputs (c.predict x)) = f x)
    (on : f allOn = true) : Extension c f where
  layers := L + 1
  width := N + 1
  net := extend c d
  tap := Fin.castSucc
  out := Fin.last N
  valid := extend_valid valid hot node
  keeps := extend_keep c d
  gives := fun x => (extend_last c d x).trans (value x)
  hot := Fin.lastCases ((extend_last c d allOn).trans ((value allOn).trans on))
    (fun i => (extend_keep c d allOn i).trans (hot i))

private theorem compile (term : Formula M) :
    term.Trainable → ∀ {L N} (c : Cascade M L N), c.Valid →
      (∀ i, c.predict allOn i = true) →
      ∀ (input : Fin M → Fin N), (∀ x a, c.predict x (input a) = x a) →
      Nonempty (Extension c term.eval) := by
  induction term with
  | wire a =>
    intro _ L N c valid hot input wiring
    exact ⟨⟨L, N, c, id, input a, valid, fun _ _ => rfl, fun x => wiring x a, hot⟩⟩
  | unit =>
    intro _ L N c valid hot _ _
    exact ⟨addNode valid hot (constant_valid .on (Or.inr rfl) c.predict)
      (fun _ => rfl) rfl⟩
  | combine op l r s t ihl ihr =>
    intro lessons L N c valid hot input wiring
    obtain ⟨lt, rt, access⟩ := lessons
    obtain ⟨left⟩ := ihl lt c valid hot input wiring
    obtain ⟨right⟩ := ihr rt left.net left.valid left.hot (left.tap ∘ input)
      (fun x i => (left.keeps x (input i)).trans (wiring x i))
    let a := right.tap left.out
    let b := right.out
    have lValue (x : Pattern M) : right.net.predict x a = l.eval x :=
      (right.keeps x left.out).trans (left.gives x)
    have rValue (x : Pattern M) : right.net.predict x b = r.eval x := right.gives x
    have actualAccess : op.Lessons (fun x => right.net.predict x a)
        (fun x => right.net.predict x b) s t := by
      simpa only [lValue, rValue] using access
    let added : Extension right.net (Formula.combine op l r s t).eval :=
      addNode right.valid right.hot (binary_node_valid op right.hot actualAccess)
        (fun x => by
          change op.gate.eval ((binaryNode op a b s t).inputs (right.net.predict x)) =
            op.eval (l.eval x) (r.eval x)
          rw [binary_node_eval, lValue, rValue])
        (by
          change op.eval (l.eval allOn) (r.eval allOn) = true
          rw [← lValue, ← rValue, right.hot, right.hot]
          cases op <;> rfl)
    exact ⟨(left.chain right).chain added⟩

private def conjoin : List (Fin M) → Formula M
  | [] => .unit
  | a :: ports => .combine .both (.wire a) (conjoin ports) allOn allOn

private theorem conjoin_eval (ports : List (Fin M)) (x : Pattern M) :
    (conjoin ports).eval x = ports.all x := by
  induction ports with
  | nil => rfl
  | cons a ports ih => simp [conjoin, Formula.eval, Binary.eval, ih]

private theorem conjoin_trainable (ports : List (Fin M)) : (conjoin ports).Trainable := by
  induction ports with
  | nil => trivial
  | cons a ports ih => exact ⟨trivial, ih, trivial⟩

private def termFormula (p : Parameters A M) (a : Fin A) : Formula M :=
  conjoin ((List.finRange M).filter (p.target a))

private theorem term_eval (p : Parameters A M) (a : Fin A) (x : Pattern M) :
    (termFormula p a).eval x = predicted p x a := by
  rw [termFormula, conjoin_eval, Bool.eq_iff_iff, List.all_eq_true, predicted, contains_iff]
  constructor
  · intro fires j selected
    exact fires j (List.mem_filter.mpr ⟨List.mem_finRange j, selected⟩)
  · intro fires j selected
    exact fires j (List.mem_filter.mp selected).2

private def disjoin (p : Parameters A M) (a : Fin A) : List (Fin A) → Formula M
  | [] => termFormula p a
  | b :: rest => .combine .either (termFormula p a) (disjoin p b rest) (p.target a) (p.target b)

private theorem disjoin_eval (p : Parameters A M) (a : Fin A) (rest : List (Fin A)) (x : Pattern M) :
    (disjoin p a rest).eval x = (a :: rest).any (predicted p x) := by
  induction rest generalizing a with
  | nil => simp [disjoin, term_eval]
  | cons b rest ih => simp [disjoin, Formula.eval, Binary.eval, term_eval, ih]

private theorem disjoin_trainable (p : Parameters A M) (a : Fin A) (rest : List (Fin A))
    (unique : (a :: rest).Nodup)
    (isolate : ∀ b ∈ a :: rest, ∀ j, predicted p (p.target b) j = decide (j = b)) :
    (disjoin p a rest).Trainable := by
  induction rest generalizing a with
  | nil => exact conjoin_trainable _
  | cons b rest ih =>
    obtain ⟨notInTail, tailUnique⟩ := List.nodup_cons.mp unique
    have isolatedA := isolate a (by simp)
    have isolatedB := isolate b (by simp)
    have leftAtA : predicted p (p.target a) a = true := by simp [isolatedA]
    have leftAtB : predicted p (p.target b) a = false := by
      have distinct : a ≠ b := fun equal => notInTail (by simp [equal])
      simp [isolatedB, distinct]
    have rightAtA : (b :: rest).any (predicted p (p.target a)) = false := by
      apply List.any_eq_false.mpr
      intro j member
      have distinct : j ≠ a := fun equal => notInTail (equal ▸ member)
      simp [isolatedA, distinct]
    have rightAtB : (b :: rest).any (predicted p (p.target b)) = true :=
      List.any_eq_true.mpr ⟨b, by simp, by simp [isolatedB]⟩
    change (termFormula p a).Trainable ∧ (disjoin p b rest).Trainable ∧
      (termFormula p a).eval (p.target a) = true ∧
      (disjoin p b rest).eval (p.target a) = false ∧
      (termFormula p a).eval (p.target b) = false ∧
      (disjoin p b rest).eval (p.target b) = true
    refine ⟨conjoin_trainable _, ih b tailUnique (fun j mem => isolate j (List.mem_cons_of_mem _ mem)), ?_⟩
    simpa only [term_eval, disjoin_eval] using And.intro leftAtA
      (And.intro rightAtA (And.intro leftAtB rightAtB))

private theorem selected_isolated (p : MonotoneDNF.Cascade A B M) (valid : p.Valid)
    (i : Fin B) {a : Fin A} (selected : p.second.lines i a = true) (j : Fin A) :
    predicted p.first (p.first.target a) j = decide (j = a) := by
  simp only [MonotoneDNF.Cascade.Valid, MonotoneDNF.Cascade.check, Bool.and_eq_true] at valid
  obtain ⟨⟨⟨⟨_, _⟩, reachable⟩, _⟩, _⟩ := valid
  have chosen : (List.finRange B).any (fun k => p.second.lines k a) = true :=
    List.any_eq_true.mpr ⟨i, List.mem_finRange i, selected⟩
  have exactMask := MonotoneDNF.allPorts reachable a
  simp only [chosen, Bool.not_true, Bool.false_or] at exactMask
  exact beq_iff_eq.mp (MonotoneDNF.allPorts exactMask j)

private theorem constant_realized (M : Nat) (value : Bool) :
    ∃ (L N : Nat) (c : Cascade M L N) (i : Fin N), c.Valid ∧ ∀ x, c.predict x i = value := by
  let g := if value then Gate.on else Gate.off
  have mode : g = .off ∨ g = .on := by cases value <;> simp [g]
  let c : Cascade M 1 1 := .layer .input standardTiming (fun _ => makeNode g none none allOn allOn)
  refine ⟨1, 1, c, 0, ⟨trivial, standardTiming_valid, fun _ => constant_valid g mode id⟩, ?_⟩
  intro x
  cases value <;> rfl

/-- Every monotone DNF is compiled to consecutive layers of trainable gates.
An isolating input for a term also isolates the side of any OR containing it. -/
theorem layered_monotone_characterization : LayeredMonotoneCharacterization := by
  intro M f
  constructor
  · intro mono
    obtain ⟨A, B, p, i, valid, value⟩ := (MonotoneDNF.monotone_characterization M f).mp mono
    cases mode : p.second.alwaysFire i with
    | true =>
      obtain ⟨L, N, c, out, admissible, always⟩ := constant_realized M true
      refine ⟨L, N, c, out, admissible, fun x => (always x).trans ?_⟩
      simpa [MonotoneDNF.output, mode] using value x
    | false =>
      let selected := (List.finRange A).filter (p.second.lines i)
      have predicts (x : Pattern M) : selected.any (predicted p.first x) = f x := by
        simpa only [MonotoneDNF.output, mode, Bool.false_or, selected, List.any_filter] using value x
      cases listed : selected with
      | nil =>
        obtain ⟨L, N, c, out, valid, silent⟩ := constant_realized M false
        refine ⟨L, N, c, out, valid, fun x => (silent x).trans ?_⟩
        simpa [listed] using predicts x
      | cons a rest =>
        have unique : (a :: rest).Nodup := by
          rw [← listed]
          exact (List.nodup_finRange A).filter _
        have isolated (b : Fin A) (mem : b ∈ a :: rest) (j : Fin A) :
            predicted p.first (p.first.target b) j = decide (j = b) := by
          rw [← listed] at mem
          exact selected_isolated p valid i (List.mem_filter.mp mem).2 j
        obtain ⟨compiled⟩ := compile (disjoin p.first a rest)
          (disjoin_trainable p.first a rest unique isolated)
          (.input : Cascade M 0 M) trivial (fun _ => rfl) id (fun _ _ => rfl)
        refine ⟨compiled.layers, compiled.width, compiled.net, compiled.out, compiled.valid, ?_⟩
        intro x
        rw [compiled.gives, disjoin_eval, ← listed]
        exact predicts x
  · rintro ⟨L, N, c, i, _, value⟩
    intro x y contained active
    rw [← value x] at active
    rw [← value y]
    exact prediction_monotone c i x y contained active

end LearnedCoincidence.Layered
