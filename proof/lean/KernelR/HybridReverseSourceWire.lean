import KernelR.HybridShortLearnedCycle
import KernelR.HybridFirstReceiverFire
import KernelR.HybridQuietLeftWireArrival
import KernelR.HybridPrefixStableMemory

/-! A real B source response issues and delivers its reverse wire while A
continues quietly from its actual cut. A needs only strict READY guards at
the source; preparation at the later receipt is a separate derived fact. -/
namespace KernelR.Hybrid

noncomputable def reverseSourceLocalA (s : Snapshot 2) : Snapshot 1 := s.cellProjection 0 []
noncomputable def reverseSourceLocalB (s : Snapshot 2) : Snapshot 1 := s.cellProjection 1 []

structure ReverseSourceWire (θA θB : Fin 1 → Parameters) (forward backward : ℝ → ℝ)
    (source : Snapshot 2) (cycle : ShortLearnedCycle θB (reverseSourceLocalB source) 2) where
  cutH : cycle.fast.execution.BeforeFlowCut (cycle.fire.final.time + backward cycle.fire.final.time)
  final : Snapshot 2
  execution : Execution (extendParameters θA (θB 0)) (reciprocalEntryRouter forward backward) source final
  date : final.time = cycle.fire.final.time + backward cycle.fire.final.time
  window : source.time + 7 / 10 < final.time ∧ final.time < source.time + 11 / 10
  pending : final.pending = source.pending
  a_values : final.x 0 = (quietAt (reverseSourceLocalA source) final.time).x 0
  a_main : final.main 0 = source.main 0
  a_aux : ∀ q, final.aux 0 q = source.aux 0 q
  raw_active : final.raw 0 2 = some final.time
  raw_other_a : ∀ q, q ≠ 2 → final.raw 0 q = none
  b_values : final.x 1 = cutH.state.x 0
  b_main : final.main 1 = cutH.state.main 0
  b_aux : ∀ q, final.aux 1 q = cutH.state.aux 0 q
  b_raw : ∀ q, final.raw 1 q = cutH.state.raw 0 q
  gains : ∀ i q, final.x i (.z q) = source.x i (.z q)
  recovery : ∀ i, final.x i .b = source.x i .b
  emissions : execution.ledger.emissions = [(1,cycle.fire.final.time)]
  deliveries : execution.deliveries = [⟨0,2,final.time⟩]
  physical : PhysicalInvariant (extendParameters θA (θB 0)) final
  raw_valid : RawValid final
  complete : CompleteThrough execution final.time

/-- The input cycle is an actually constructed one-cell B response. The
only global FIRE is lifted explicitly and is the unique origin of the wire.
The quiet A coordinate is neither clamped nor required to be prepared. -/
theorem reverse_source_wire_exists {θA θB ε forward backward}
    (source : Snapshot 2) (cycle : ShortLearnedCycle θB (reverseSourceLocalB source) 2)
    (hb : PhysicalBox (extendParameters θA (θB 0)) ε)
    (hf : PhysicalInvariant (extendParameters θA (θB 0)) source) (hv : RawValid source)
    (hs : 320 ≤ source.time ∧ source.time ≤ 440)
    (hmA : source.main 0 = .ready) (haA : ∀ q, source.aux 0 q = .ready)
    (hrA : ∀ q, source.raw 0 q = none) (hqA : source.x 0 .q < 1)
    (hxA : ∀ q, source.x 0 (.m q) < 1)
    (hQ : ∀ d ∈ source.pending, source.time + 8 ≤ d.due)
    (hdelay : ∀ t, (3 / 10 : ℝ) ≤ backward t ∧ backward t ≤ 2 / 5) :
    Nonempty (ReverseSourceWire θA θB forward backward source cycle) := by
  have hbB : PhysicalBox θB ε := by
    refine ⟨hb.1,?_⟩
    intro j q
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact hb.2 1 q
  let sA := reverseSourceLocalA source
  let sB := reverseSourceLocalB source
  let F := cycle.fire.final.time
  let H := F + backward F
  let route := reciprocalEntryRouter forward backward
  let Q := source.pending
  have hF : source.time + 2 / 5 < F ∧ F < source.time + 7 / 10 := cycle.fire_bounds
  have hH : source.time + 7 / 10 < H ∧ H < source.time + 11 / 10 := by
    constructor <;> dsimp [H] <;> linarith [(hdelay F).1,(hdelay F).2]
  have hSource : sA.product sB Q = source := source.cellProjection_product [] []
  have hFA : sA.time < F := by change source.time < F; linarith [hF.1]
  have hFH : F < H := by dsimp [H]; linarith [(hdelay F).1]
  let flowA : Flow θA sA (quietAt sA F) := quietFlow sA hFA
    (fun _ => hmA) (fun _ q => haA q) (fun _ q => hrA q)
    (fun _ => hqA) (fun _ q => hxA q)
    (by intro d hd; change d ∈ ([] : List (Delivery 1)) at hd; contradiction)
  let preA : Execution θA (fun _ _ => []) sA (quietAt sA F) := .cons (.flow flowA) (.nil _)
  have hQF : ∀ d ∈ Q, (quietAt sA F).time ≤ d.due := by
    intro d hd
    change F ≤ d.due
    linarith [hQ d hd]
  obtain ⟨lifted,heL,hdL⟩ := preA.product_neutral cycle.fire.portBeforeExecution rfl rfl
    rfl rfl cycle.fire.portBefore_emissions cycle.fire.portBefore_deliveries Q hQF route
  let before := (quietAt sA F).product cycle.fire.portBefore Q
  let after := (quietAt sA F).product cycle.fire.final (Q ++ route 1 F)
  let pre : Execution (extendParameters θA (θB 0)) route source before := lifted.cast_source hSource.symm
  have hafter : after = {(setMain before 1 .fast) with pending := before.pending ++ route 1 before.time} := by
    dsimp [after,before]
    rw [cycle.fire.port_final_empty,Snapshot.product_setMain_right]
    rfl
  let fire : Jump route before after := hafter.symm ▸
    Jump.fire before 1 (cycle.fire.firstSilent.main_ready 0) cycle.fire.threshold
  have heFire : fire.ledger.emissions = [(1,F)] :=
    fire.ready_main_departure_emission 1 (cycle.fire.firstSilent.main_ready 0)
      (by have h : after.main 1 = .fast := cycle.fire.main_fast; rw [h]; decide)
  have hdFire : fire.deliveries = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro d hd
    have h := fire.no_emissions_of_delivery d hd
    rw [heFire] at h
    contradiction
  let firing := pre.append (.cons (.jump fire) (.nil _))
  have hePre : pre.ledger.emissions = [] := by rw [Execution.cast_source_ledger]; exact heL
  have hdPre : pre.deliveries = [] := by rw [Execution.cast_source_deliveries]; exact hdL
  have heFiring : firing.ledger.emissions = [(1,F)] := by
    simp only [firing,Execution.emissions_append,hePre,Execution.ledger,Move.ledger,heFire,
      Ledger.add,Ledger.zero,List.nil_append,List.append_nil]
  have hdFiring : firing.deliveries = [] := by
    simp only [firing,Execution.deliveries_append,hdPre,Execution.deliveries,Move.deliveries,hdFire,
      List.append_nil]
  obtain ⟨cut⟩ := cycle.fast.execution.before_flow_cut_exists H hFH.le
    (by rw [cycle.fast.date]; dsimp [H,F]; linarith [(hdelay cycle.fire.final.time).2])
  have heCut : cut.cut.ledger.emissions = [] :=
    (List.append_eq_nil_iff.mp (cut.emissions.symm.trans cycle.fast.emissions)).1
  have hdCut : cut.cut.deliveries = [] :=
    (List.append_eq_nil_iff.mp (cut.deliveries.symm.trans cycle.fast.deliveries)).1
  have hroute : route 1 F = [⟨0,2,cut.state.time⟩] := by
    have hw : (320 : ℝ) ≤ F ∧ F < 470 := by constructor <;> linarith [hs.1,hs.2,hF.1,hF.2]
    rw [cut.date]
    dsimp [route]
    simp [reciprocalEntryRouter,Contact.route,teachingContact,feedbackContact,Contact.token,hw.1,hw.2,H]
  have hAfter : after = (quietAt sA F).product cycle.fire.final (Q ++ [⟨0,2,cut.state.time⟩]) := by
    dsimp [after]
    rw [hroute]
  have hQH : ∀ d ∈ Q, cut.state.time < d.due := by
    intro d hd
    rw [cut.date]
    linarith [hQ d hd,hH.2]
  have hfuture : ∀ d ∈ Q ++ [⟨0,2,cut.state.time⟩], cut.state.time ≤ d.due := by
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact (hQH d hd).le
    · have he : d = (⟨0,2,cut.state.time⟩ : Delivery 2) := List.mem_singleton.mp hd
      subst d
      exact le_rfl
  have hAstart : sA.time ≤ F := hFA.le
  let flowAH : Flow θA (quietAt sA F) (quietAt (quietAt sA F) cut.state.time) :=
    quietFlow (quietAt sA F) (by rw [cut.date]; exact hFH)
      (fun _ => hmA) (fun _ q => haA q) (fun _ q => hrA q)
      (fun _ => relax_lt (by norm_num) hAstart hqA (by norm_num))
      (fun _ q => relax_lt (by norm_num) hAstart (hxA q) (by norm_num))
      (by intro d hd; change d ∈ ([] : List (Delivery 1)) at hd; contradiction)
  let waitA : Execution θA (fun _ _ => []) (quietAt sA F) (quietAt (quietAt sA F) cut.state.time) :=
    .cons (.flow flowAH) (.nil _)
  obtain ⟨wireSpan,heW,hdW⟩ := waitA.product_neutral cut.cut rfl rfl rfl rfl heCut hdCut
    (Q ++ [⟨0,2,cut.state.time⟩]) hfuture route
  let beforeWire := (quietAt (quietAt sA F) cut.state.time).product cut.state
    (Q ++ [⟨0,2,cut.state.time⟩])
  let final : Snapshot 2 := {(setRaw beforeWire 0 2 (some beforeWire.time)) with pending := Q ++ []}
  have hfree : beforeWire.raw 0 2 = none := hrA 2
  let arrival : Jump route beforeWire final := .arrive beforeWire ⟨0,2,cut.state.time⟩ Q [] rfl rfl hfree
  have haEm : arrival.ledger.emissions = [] := rfl
  have haDel : arrival.deliveries = [⟨0,2,cut.state.time⟩] := rfl
  let wire := wireSpan.append (.cons (.jump arrival) (.nil _))
  let wireTrace : Execution (extendParameters θA (θB 0)) route after final := wire.cast_source hAfter
  have heWire : wireTrace.ledger.emissions = [] := by
    rw [Execution.cast_source_ledger]
    simp only [wire,Execution.emissions_append,heW,Execution.ledger,Move.ledger,haEm,
      Ledger.add,Ledger.zero,List.nil_append]
  have hdWire : wireTrace.deliveries = [⟨0,2,cut.state.time⟩] := by
    rw [Execution.cast_source_deliveries]
    simp only [wire,Execution.deliveries_append,hdW,Execution.deliveries,Move.deliveries,haDel,
      List.nil_append,List.append_nil]
  let trace := firing.append wireTrace
  have hvaluesA : final.x 0 = (quietAt sA final.time).x 0 := by
    change (quietAt (quietAt sA F) cut.state.time).x 0 = (quietAt sA cut.state.time).x 0
    rw [quietAt_quietAt]
  have hgainB : ∀ q, final.x 1 (.z q) = source.x 1 (.z q) := by
    intro q
    change cut.state.x 0 (.z q) = source.x 1 (.z q)
    have h := cut.isPrefix.gain_eq_of_final hbB 0 q (cycle.fast.gains 0 q)
    exact h.trans (cycle.fire.gain_preserved 0 q)
  have hrecB : final.x 1 .b = source.x 1 .b := by
    have h := cut.isPrefix.recovery_eq_of_final hbB 0 (cycle.fast.recovery 0)
    exact h.trans (cycle.fire.recovery_preserved 0)
  have hrawActive : final.raw 0 2 = some final.time := by
    simp [final,setRaw,beforeWire,Snapshot.product,quietAt]
  have hrawOther : ∀ q, q ≠ 2 → final.raw 0 q = none := by
    intro q hq
    have h : beforeWire.raw 0 q = none := hrA q
    simpa [final,setRaw,Function.update_apply,hq] using h
  have hBraw : ∀ q, final.raw 1 q = cut.state.raw 0 q := by
    intro q
    have h : beforeWire.raw 1 q = cut.state.raw 0 q := rfl
    simpa [final,setRaw,Function.update_apply] using h
  have hAq : final.x 0 .q < 1 := by
    rw [hvaluesA]
    exact relax_lt (by norm_num) (hFA.le.trans (by change F ≤ cut.state.time; rw [cut.date]; exact hFH.le)) hqA (by norm_num)
  have hAm : ∀ q, final.x 0 (.m q) < 1 := by
    intro q
    rw [hvaluesA]
    exact relax_lt (by norm_num) (hFA.le.trans (by change F ≤ cut.state.time; rw [cut.date]; exact hFH.le)) (hxA q) (by norm_num)
  have hrawFuture : ∀ d ∈ final.pending, final.time < d.due := by
    intro d hd
    change d ∈ Q ++ [] at hd
    simp only [List.append_nil] at hd
    exact hQH d hd
  have hcomplete : CompleteThrough trace final.time := by
    refine ⟨rfl,?_,hrawFuture⟩
    intro u
    apply BeforeGuards.no_jump
    · constructor
      · intro i
        rcases (show i = (0 : Fin 2) ∨ i = (1 : Fin 2) by fin_cases i <;> norm_num) with hi | hi <;> subst i
        · have hm : final.main 0 = .ready := hmA
          rw [hm]; exact hAq
        · have hm : final.main 1 = cut.state.main 0 := rfl
          have hx : final.x 1 = cut.state.x 0 := rfl
          rw [hm,hx]; exact cut.before_guards.1 0
      · intro i q
        rcases (show i = (0 : Fin 2) ∨ i = (1 : Fin 2) by fin_cases i <;> norm_num) with hi | hi <;> subst i
        · have hm : final.aux 0 q = .ready := haA q
          rw [hm]; exact hAm q
        · have hm : final.aux 1 q = cut.state.aux 0 q := rfl
          have hx : final.x 1 = cut.state.x 0 := rfl
          rw [hm,hx]; exact cut.before_guards.2 0 q
    · intro i q origin hr
      rcases (show i = (0 : Fin 2) ∨ i = (1 : Fin 2) by fin_cases i <;> norm_num) with hi | hi <;> subst i
      · by_cases hq : q = 2
        · subst q
          have ho : origin = final.time := Option.some.inj (hr.symm.trans hrawActive)
          rw [ho]; linarith
        · rw [hrawOther q hq] at hr; contradiction
      · rw [hBraw] at hr
        exact cut.flow.initial_raw_strict 0 q origin hr
    · exact hrawFuture
  refine ⟨{
    cutH := cut, final := final, execution := trace, date := cut.date
    window := ?_, pending := by simp [final,Q]
    a_values := hvaluesA, a_main := rfl, a_aux := fun _ => rfl
    raw_active := hrawActive, raw_other_a := hrawOther
    b_values := rfl, b_main := rfl, b_aux := fun _ => rfl, b_raw := hBraw
    gains := ?_, recovery := ?_, emissions := ?_, deliveries := ?_
    physical := trace.physical_invariant hb hf, raw_valid := trace.raw_valid hv, complete := hcomplete
  }⟩
  · change source.time + 7 / 10 < cut.state.time ∧ cut.state.time < source.time + 11 / 10
    rw [cut.date]
    exact hH
  · intro i q
    rcases (show i = (0 : Fin 2) ∨ i = (1 : Fin 2) by fin_cases i <;> norm_num) with hi | hi <;> subst i
    · rw [hvaluesA]; rfl
    · exact hgainB q
  · intro i
    rcases (show i = (0 : Fin 2) ∨ i = (1 : Fin 2) by fin_cases i <;> norm_num) with hi | hi <;> subst i
    · rw [hvaluesA]; rfl
    · exact hrecB
  · rw [Execution.emissions_append,heFiring,heWire,List.append_nil]
  · rw [Execution.deliveries_append,hdFiring,hdWire,List.nil_append]
    rfl

namespace ReverseSourceWire
variable {θA θB forward backward source cycle}
  (r : ReverseSourceWire θA θB forward backward source cycle)

/-- Callers derive this quiet-state preparation from their retained actual
weak continuation and the real inter-receipt lower bound. It is not needed
to construct the wire or its receipt. -/
theorem receiver_prepared
    (h : PreparedSection (quietAt (reverseSourceLocalA source) r.final.time) 0) :
    PreparedSection r.final 0 := by
  refine ⟨?_,?_,?_,?_⟩
  · exact r.a_main.trans h.ready
  · rw [r.a_values]; exact h.charge
  · rw [r.a_values]; exact h.recovery
  · intro q
    refine ⟨(r.a_aux q).trans (h.auxiliary q).1,?_⟩
    rw [r.a_values]; exact (h.auxiliary q).2

theorem error_zero (i : Fin 2) (q : Port) : r.execution.ledger.error i q = 0 := by
  have h := r.execution.gain_balance i q
  rw [r.gains] at h
  linarith

theorem recovery_zero (i : Fin 2) : r.execution.ledger.recovery i = 0 := by
  have h := r.execution.recovery_balance i
  rw [r.recovery] at h
  linarith

end ReverseSourceWire
end KernelR.Hybrid
