import KernelR.HybridExecutionTools
import KernelR.HybridInputBalance
import Mathlib.Data.List.OfFn
/-! Actual delivery cuts and exact finite source trains, with token multiplicities retained. -/
namespace KernelR.Hybrid

structure DeliveryStep {n θ route s u} (e : @Execution n θ route s u)
    (d : Delivery n) (ds : List (Delivery n)) where
  beforeArrival : Snapshot n
  afterArrival : Snapshot n
  span : Execution θ route s beforeArrival
  entry : Jump route beforeArrival afterArrival
  rest : Execution θ route afterArrival u
  reconstruct : e = span.append (.cons (.jump entry) rest)
  no_earlier : span.deliveries = []
  delivery : entry.deliveries = [d]
  later : rest.deliveries = ds

theorem Execution.first_delivery {n θ route s u} (e : @Execution n θ route s u)
    (d : Delivery n) (ds : List (Delivery n)) (hd : e.deliveries = d :: ds) :
    Nonempty (DeliveryStep e d ds) := by
  induction e with
  | nil => simp [deliveries] at hd
  | @cons s v u move rest ih =>
    cases move with
    | flow f =>
      obtain ⟨cut⟩ := ih (by simpa [deliveries,Move.deliveries] using hd)
      exact ⟨{
        beforeArrival := cut.beforeArrival
        afterArrival := cut.afterArrival
        span := .cons (.flow f) cut.span
        entry := cut.entry
        rest := cut.rest
        reconstruct := by simp only [append,cut.reconstruct]
        no_earlier := by simpa [deliveries,Move.deliveries] using cut.no_earlier
        delivery := cut.delivery
        later := cut.later
      }⟩
    | jump j =>
      by_cases hj : j.deliveries = []
      · obtain ⟨cut⟩ := ih (by simpa [deliveries,Move.deliveries,hj] using hd)
        exact ⟨{
          beforeArrival := cut.beforeArrival
          afterArrival := cut.afterArrival
          span := .cons (.jump j) cut.span
          entry := cut.entry
          rest := cut.rest
          reconstruct := by simp only [append,cut.reconstruct]
          no_earlier := by simpa [deliveries,Move.deliveries,hj] using cut.no_earlier
          delivery := cut.delivery
          later := cut.later
        }⟩
      · cases j with
        | arrive token before after queue due free =>
          have heq : token = d ∧ rest.deliveries = ds := by
            simpa [deliveries,Move.deliveries,Jump.deliveries] using hd
          exact ⟨⟨s,_,.nil _,.arrive s token before after queue due free,rest,rfl,rfl,
            by simp [Jump.deliveries,heq.1],heq.2⟩⟩
        | _ => simp [Jump.deliveries] at hj

theorem Jump.delivery_snapshot {n route s u} (j : @Jump n route s u)
    (d : Delivery n) (hd : d ∈ j.deliveries) :
    ∃ before after, s.pending = before ++ d :: after ∧ d.due = s.time ∧
      s.raw d.cell d.port = none ∧
      u = { (setRaw s d.cell d.port (some s.time)) with pending := before ++ after } := by
  cases j <;> simp only [Jump.deliveries,List.mem_nil_iff,List.mem_singleton] at hd
  case arrive token before after queue due free =>
    subst d
    exact ⟨before,after,queue,due,free,rfl⟩

theorem DeliveryStep.date {n θ route s u d ds} {e : @Execution n θ route s u}
    (cut : DeliveryStep e d ds) : cut.beforeArrival.time = d.due ∧ cut.afterArrival.time = d.due := by
  have hd : d ∈ cut.entry.deliveries := by rw [cut.delivery]; simp
  exact ⟨(cut.entry.delivery_due d hd).symm,
    cut.entry.time_unchanged.trans (cut.entry.delivery_due d hd).symm⟩

theorem DeliveryStep.raw_after {n θ route s u d ds} {e : @Execution n θ route s u}
    (cut : DeliveryStep e d ds) : cut.afterArrival.raw d.cell d.port = some cut.afterArrival.time := by
  have hd : d ∈ cut.entry.deliveries := by rw [cut.delivery]; simp
  obtain ⟨before,after,hq,ht,hfree,he⟩ := cut.entry.delivery_snapshot d hd
  rw [he]
  simp [setRaw]

theorem DeliveryStep.no_arrivals_before {n θ route s u d ds} {e : @Execution n θ route s u}
    (cut : DeliveryStep e d ds) : ∀ i p, NoArrivalAt cut.span i p := by
  intro i p
  simp [NoArrivalAt,cut.no_earlier]

/-- With one receiving slot and no routing, chronological delivery of all
source tokens fixes their entire ordered list, including multiplicities. -/
theorem Execution.deliveries_exact_one_slot {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (T : ℝ) (hc : CompleteThrough e T)
    (hs : ∀ d ∈ s.pending, d.due ≤ T) (hr : ∀ i t, route i t = [])
    (hslot : ∀ d ∈ s.pending, d.cell = i ∧ d.port = p)
    (horder : s.pending.Pairwise (fun d f => d.due ≤ f.due)) : e.deliveries = s.pending := by
  have hp := e.deliveries_perm_sources T hc hs hr
  apply List.Perm.eq_of_pairwise (le := fun d f : Delivery n => d.due ≤ f.due)
    ?_ e.deliveries_chronological horder hp
  intro a b ha hb hab hba
  have hsa := hslot a (hp.mem_iff.mp ha)
  have hsb := hslot b hb
  have ht := le_antisymm hab hba
  cases a
  cases b
  simp_all

/-- A finite train of source tokens; it specifies inputs, not pulse cases. -/
def sourceTrain {n} (i : Fin n) (p : Port) (start gap : ℝ) (count : ℕ) : List (Delivery n) :=
  List.ofFn (fun k : Fin count => ⟨i,p,start + gap * k.val⟩)

theorem sourceTrain_succ {n} (i : Fin n) (p : Port) (start gap : ℝ) (count : ℕ) :
    sourceTrain i p start gap (count + 1) =
      ⟨i,p,start⟩ :: sourceTrain i p (start + gap) gap count := by
  simp only [sourceTrain,List.ofFn_succ,Fin.val_zero,Nat.cast_zero,mul_zero,add_zero]
  congr 1
  apply congrArg List.ofFn
  funext k
  simp only [Fin.val_succ,Nat.cast_add,Nat.cast_one]
  congr 1
  ring

theorem Execution.source_train_deliveries {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (start gap : ℝ) (count : ℕ) (T : ℝ)
    (hc : CompleteThrough e T) (hq : s.pending = sourceTrain i p start gap count)
    (hgap : 0 ≤ gap) (hT : start + gap * count ≤ T) (hr : ∀ i t, route i t = []) :
    e.deliveries = sourceTrain i p start gap count := by
  have hs : ∀ d ∈ s.pending, d.due ≤ T := by
    intro d hd
    rw [hq] at hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    have hk : (k.val : ℝ) ≤ count := by exact_mod_cast k.isLt.le
    exact (add_le_add (le_refl start) (mul_le_mul_of_nonneg_left hk hgap)).trans hT
  have hslot : ∀ d ∈ s.pending, d.cell = i ∧ d.port = p := by
    intro d hd
    rw [hq] at hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    exact ⟨rfl,rfl⟩
  have horder : s.pending.Pairwise (fun d f => d.due ≤ f.due) := by
    rw [hq]
    apply List.pairwise_ofFn.mpr
    intro k l hkl
    have hk : (k.val : ℝ) ≤ l.val := by exact_mod_cast hkl.le
    exact add_le_add (le_refl start) (mul_le_mul_of_nonneg_left hk hgap)
  exact (e.deliveries_exact_one_slot i p T hc hs hr hslot horder).trans hq

theorem DeliveryStep.modes_after {n θ route s u d ds} {e : @Execution n θ route s u}
    (cut : DeliveryStep e d ds) :
    cut.afterArrival.main = cut.beforeArrival.main ∧ cut.afterArrival.aux = cut.beforeArrival.aux := by
  have hd : d ∈ cut.entry.deliveries := by rw [cut.delivery]; simp
  obtain ⟨before,after,hq,ht,hfree,he⟩ := cut.entry.delivery_snapshot d hd
  rw [he]
  exact ⟨rfl,rfl⟩

theorem DeliveryStep.raw_other {n θ route s u d ds} {e : @Execution n θ route s u}
    (cut : DeliveryStep e d ds) (i : Fin n) (p : Port) (h : i ≠ d.cell ∨ p ≠ d.port) :
    cut.afterArrival.raw i p = cut.beforeArrival.raw i p := by
  have hd : d ∈ cut.entry.deliveries := by rw [cut.delivery]; simp
  obtain ⟨before,after,hq,ht,hfree,he⟩ := cut.entry.delivery_snapshot d hd
  rw [he]
  rcases h with hi | hp
  · simp [setRaw,hi]
  · by_cases hi : i = d.cell
    · subst i; simp [setRaw,hp]
    · simp [setRaw,hi]

end KernelR.Hybrid
