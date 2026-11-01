import KernelR.HybridFeedbackSenderFastEnd
import KernelR.HybridQuietLeftWireArrival
import KernelR.HybridPrefixStableMemory

/-! The first actual B-to-A receipt. Its token comes from the real B FIRE,
and its sender cut retains every auxiliary and RAW event at the receipt clock. -/
namespace KernelR.Hybrid

structure FirstReverseWiredArrival {θ forward backward start}
    {w : FeedbackWeakEntry θ (reciprocalEntryRouter forward backward) start}
    (f : FeedbackFirstFire w) where
  fast : PortFastCompletion f.parametersB (fun _ _ => []) f.localB 2
  cutH : fast.execution.BeforeFlowCut (f.final.time + backward f.final.time)
  receipt : QuietLeftWireArrival f.parametersA f.parametersB (reciprocalEntryRouter forward backward)
    f.localA f.localB cutH.state w.final.pending 2
  final : Snapshot 2
  execution : Execution θ (reciprocalEntryRouter forward backward) f.final final
  final_eq : final = receipt.final
  date : final.time = f.final.time + backward f.final.time
  window : 344 + (7 / 10 : ℝ) < final.time ∧ final.time < 344 + 13 / 10
  pending : final.pending = w.final.pending
  a_prepared : PreparedSection final 0
  a_charge : final.x 0 .q = 1 / 10
  raw_active : final.raw 0 2 = some final.time
  raw_other_a : ∀ p, p ≠ 2 → final.raw 0 p = none
  b_values : final.x 1 = cutH.state.x 0
  b_main : final.main 1 = cutH.state.main 0
  b_aux : ∀ p, final.aux 1 p = cutH.state.aux 0 p
  b_raw : ∀ p, final.raw 1 p = cutH.state.raw 0 p
  gains : ∀ i p, final.x i (.z p) = f.final.x i (.z p)
  recovery : ∀ i, final.x i .b = f.final.x i .b
  emissions : execution.ledger.emissions = []
  deliveries : execution.deliveries = [f.reverseToken]
  physical : PhysicalInvariant θ final
  raw_valid : RawValid final
  complete : CompleteThrough execution final.time

/-- Complete B's actual FAST path, select its maximal cut at the independently
delayed date, then consume exactly the occurrence issued by its original FIRE. -/
theorem first_reverse_wired_arrival_exists {θ ε forward backward start}
    {w : FeedbackWeakEntry θ (reciprocalEntryRouter forward backward) start}
    (f : FeedbackFirstFire w) (hb : PhysicalBox θ ε)
    (hg : Real.exp (w.final.x 1 (.z 2)) ≤ 2)
    (hdelay : ∀ time, (3 / 10 : ℝ) ≤ backward time ∧ backward time ≤ 2 / 5) :
    Nonempty (FirstReverseWiredArrival f) := by
  let H := f.final.time + backward f.final.time
  obtain ⟨fast⟩ := f.sender_fast_end_exists hb hg
  obtain ⟨cut⟩ := fast.execution.before_flow_cut_exists H
    (by rw [f.localB_clock]; dsimp [H]; linarith [(hdelay f.final.time).1])
    (by rw [fast.date,f.localB_clock]; dsimp [H]; linarith [(hdelay f.final.time).2])
  have heCut : cut.cut.ledger.emissions = [] :=
    (List.append_eq_nil_iff.mp (cut.emissions.symm.trans fast.emissions)).1
  have hdCut : cut.cut.deliveries = [] :=
    (List.append_eq_nil_iff.mp (cut.deliveries.symm.trans fast.deliveries)).1
  have hwindow : 344 + (7 / 10 : ℝ) < H ∧ H < 344 + 13 / 10 := by
    dsimp [H]
    constructor <;> linarith [f.fire_after_four_tenths hg,f.window.2,
      (hdelay f.final.time).1,(hdelay f.final.time).2]
  have hQ : ∀ d ∈ w.final.pending, cut.state.time < d.due := by
    intro d hd
    rw [w.pending] at hd
    rw [cut.date]
    rcases List.mem_append.mp hd with hd | hd
    all_goals
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
      dsimp
      nlinarith [hwindow.2,Nat.cast_nonneg (α := ℝ) k.val]
  have hsource : f.localA.product f.localB
      (w.final.pending ++ [⟨0,2,cut.state.time⟩]) = f.final := by
    rw [cut.date]
    exact f.product_pending
  have hbProduct : PhysicalBox (extendParameters f.parametersA (f.parametersB 0)) ε := by
    rw [f.parameters_product]
    exact hb
  have hfProduct : PhysicalInvariant (extendParameters f.parametersA (f.parametersB 0))
      (f.localA.product f.localB (w.final.pending ++ [⟨0,2,cut.state.time⟩])) := by
    rw [f.parameters_product,hsource]
    exact f.firing.physical
  have hvProduct : RawValid (f.localA.product f.localB
      (w.final.pending ++ [⟨0,2,cut.state.time⟩])) := by
    rw [hsource]
    exact f.firing.raw_valid
  obtain ⟨r⟩ := quiet_left_wire_arrival_exists (route := reciprocalEntryRouter forward backward)
    hbProduct cut.cut heCut hdCut f.localA rfl
    (by rw [f.localB_clock,cut.date]; dsimp [H]; linarith [(hdelay f.final.time).1])
    (f.localA_ready 0) (f.localA_raw_none 0) f.localA_pending w.final.pending 2
    (fun d hd => (hQ d hd).le) hfProduct hvProduct
  let translated := r.execution.cast_parameters f.parameters_product
  let e : Execution θ (reciprocalEntryRouter forward backward) f.final r.final :=
    translated.cast_source hsource.symm
  have hledger : e.ledger = r.execution.ledger :=
    (translated.cast_source_ledger hsource.symm).trans (r.execution.cast_parameters_ledger f.parameters_product)
  have hdel : e.deliveries = r.execution.deliveries :=
    (translated.cast_source_deliveries hsource.symm).trans (r.execution.cast_parameters_deliveries f.parameters_product)
  have hga : ∀ p, r.final.x 0 (.z p) = f.final.x 0 (.z p) := by
    intro p
    rw [r.receiver_values]
    rfl
  have hgb : ∀ p, r.final.x 1 (.z p) = f.final.x 1 (.z p) := by
    intro p
    rw [r.sender_values]
    exact cut.isPrefix.gain_eq_of_final (f.localB_box hb) 0 p (fast.gains 0 p)
  have hra : r.final.x 0 .b = f.final.x 0 .b := by
    rw [r.receiver_values]
    rfl
  have hrb : r.final.x 1 .b = f.final.x 1 .b := by
    rw [r.sender_values]
    exact cut.isPrefix.recovery_eq_of_final (f.localB_box hb) 0 (fast.recovery 0)
  have hprepared : PreparedSection r.final 0 :=
    ⟨r.receiver_ready.ready,r.receiver_ready.charge,by rw [hra]; exact f.a_prepared.recovery,
      r.receiver_ready.auxiliary⟩
  have hcharge : r.final.x 0 .q = 1 / 10 := by
    rw [r.receiver_values]
    simp only [quietAt,quietValues,f.localA_charge,relax,sub_self,zero_mul,add_zero]
  have hcomplete : CompleteThrough e r.final.time := by
    simpa only [CompleteThrough,r.date] using r.complete_of_next cut.flow hQ
  refine ⟨{
    fast := fast, cutH := cut, receipt := r, final := r.final, execution := e, final_eq := rfl
    date := r.date.trans cut.date, window := ?_, pending := r.pending
    a_prepared := hprepared, a_charge := hcharge, raw_active := ?_, raw_other_a := r.raw_other
    b_values := r.sender_values, b_main := r.sender_main, b_aux := r.sender_aux, b_raw := r.sender_raw
    gains := ?_, recovery := ?_, emissions := ?_, deliveries := ?_
    physical := e.physical_invariant hb f.firing.physical
    raw_valid := e.raw_valid f.firing.raw_valid, complete := hcomplete
  }⟩
  · rw [r.date,cut.date]
    exact hwindow
  · rw [r.date]
    exact r.raw_active
  · intro i p
    rcases (show i = 0 ∨ i = 1 by omega) with hi | hi <;> subst i
    · exact hga p
    · exact hgb p
  · intro i
    rcases (show i = 0 ∨ i = 1 by omega) with hi | hi <;> subst i
    · exact hra
    · exact hrb
  · rw [hledger,r.emissions]
  · rw [hdel,r.deliveries,cut.date]
    rfl

namespace FirstReverseWiredArrival
variable {θ forward backward start}
  {w : FeedbackWeakEntry θ (reciprocalEntryRouter forward backward) start}
  {f : FeedbackFirstFire w} (r : FirstReverseWiredArrival f)

theorem pending_length : r.final.pending.length = 28 := by rw [r.pending]; exact w.pending_length

theorem wire_provenance : r.final.time = f.final.time + backward f.final.time := r.date

end FirstReverseWiredArrival
end KernelR.Hybrid
