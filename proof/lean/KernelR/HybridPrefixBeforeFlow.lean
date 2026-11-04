import KernelR.HybridFlowCuts
import KernelR.HybridGuardNoJump
import KernelR.HybridContactTransversality

/-! A finite existing execution has a prefix just before a positive flow at
any strictly interior clock. All zero-time jumps at that clock are consumed. -/
namespace KernelR.Hybrid

/-- The next genuine positive flow supplies strict terminal guards. The
remaining execution is retained; no new continuation is postulated. -/
structure Execution.BeforeFlowCut {n θ route s u} (e : @Execution n θ route s u) (H : ℝ) where
  state : Snapshot n
  cut : Execution θ route s state
  isPrefix : e.IsPrefix cut
  date : state.time = H
  nextState : Snapshot n
  flow : Flow θ state nextState
  rest : Execution θ route nextState u
  rest_contacts_transversal : e.ContactsTransversal → rest.ContactsTransversal
  deliveries : e.deliveries = cut.deliveries ++ rest.deliveries
  emissions : e.ledger.emissions = cut.ledger.emissions ++ rest.ledger.emissions

/-- Selection is after all actual jumps at H and before the first subsequent
positive flow. Finiteness of the supplied trace and H < its endpoint suffice. -/
theorem Execution.before_flow_cut_exists {n θ route s u} (e : @Execution n θ route s u)
    (H : ℝ) (hstart : s.time ≤ H) (hend : H < u.time) :
    Nonempty (e.BeforeFlowCut H) := by
  induction e with
  | nil s => exact False.elim (not_lt_of_ge hstart hend)
  | @cons s v u move rest ih =>
    cases move with
    | jump j =>
      obtain ⟨r⟩ := ih (by rw [j.time_unchanged]; exact hstart) hend
      refine ⟨{
        state := r.state
        cut := .cons (.jump j) r.cut
        isPrefix := .step (.jump j) rest r.cut r.isPrefix
        date := r.date
        nextState := r.nextState
        flow := r.flow
        rest := r.rest
        rest_contacts_transversal := fun positive => r.rest_contacts_transversal positive.2
        deliveries := ?_
        emissions := ?_
      }⟩
      · simp only [Execution.deliveries,r.deliveries,List.append_assoc]
      · simp only [Execution.ledger,Move.ledger,Ledger.add,r.emissions,List.append_assoc]
    | flow f =>
      by_cases heq : H = s.time
      · refine ⟨{
          state := s
          cut := .nil s
          isPrefix := .nil _
          date := heq.symm
          nextState := v
          flow := f
          rest := rest
          rest_contacts_transversal := fun positive => positive
          deliveries := rfl
          emissions := rfl
        }⟩
      · have hpos : s.time < H := lt_of_le_of_ne hstart (Ne.symm heq)
        by_cases hinside : H < v.time
        · refine ⟨{
            state := f.at H
            cut := .cons (.flow (f.prefix hpos hinside.le)) (.nil _)
            isPrefix := .flowCut f rest hpos hinside.le
            date := rfl
            nextState := v
            flow := f.suffix hpos.le hinside
            rest := rest
            rest_contacts_transversal := fun positive => positive
            deliveries := rfl
            emissions := rfl
          }⟩
        · obtain ⟨r⟩ := ih (le_of_not_gt hinside) hend
          refine ⟨{
            state := r.state
            cut := .cons (.flow f) r.cut
            isPrefix := .step (.flow f) rest r.cut r.isPrefix
            date := r.date
            nextState := r.nextState
            flow := r.flow
            rest := r.rest
            rest_contacts_transversal := fun positive => r.rest_contacts_transversal positive
            deliveries := ?_
            emissions := ?_
          }⟩
          · exact r.deliveries
          · exact r.emissions

/-- A simple existential interface to the same maximal clock prefix. -/
theorem Execution.prefix_before_flow {n θ route s u} (e : @Execution n θ route s u)
    (H : ℝ) (hstart : s.time ≤ H) (hend : H < u.time) :
    ∃ v, ∃ cut : Execution θ route s v, e.IsPrefix cut ∧ v.time = H ∧
      ∃ w, Nonempty (Flow θ v w) := by
  obtain ⟨r⟩ := e.before_flow_cut_exists H hstart hend
  exact ⟨r.state,r.cut,r.isPrefix,r.date,r.nextState,⟨r.flow⟩⟩

/-- A true following positive flow excludes a guard at its initial state. -/
theorem Flow.initial_before_guards {n θ s u} (f : @Flow n θ s u) : BeforeGuards s s.x := by
  have h := f.guards s.time ⟨le_rfl,f.positive⟩
  simpa only [f.initial] using h

theorem Flow.initial_raw_strict {n θ s u} (f : @Flow n θ s u)
    (i : Fin n) (p : Port) (origin : ℝ) (hr : s.raw i p = some origin) :
    s.time < origin + 1 :=
  f.positive.trans_le (f.raw_support i p origin hr).2

theorem Flow.initial_pending_strict {n θ s u} (f : @Flow n θ s u) :
    ∀ d ∈ s.pending, s.time < d.due := by
  intro d hd
  exact f.positive.trans_le (f.pending_urgent d hd)

theorem Execution.BeforeFlowCut.before_guards {n θ route s u H} {e : @Execution n θ route s u}
    (r : e.BeforeFlowCut H) : BeforeGuards r.state r.state.x := r.flow.initial_before_guards

theorem Execution.BeforeFlowCut.raw_strict {n θ route s u H} {e : @Execution n θ route s u}
    (r : e.BeforeFlowCut H) (i : Fin n) (p : Port) (origin : ℝ)
    (hr : r.state.raw i p = some origin) : H < origin + 1 := by
  rw [← r.date]
  exact r.flow.initial_raw_strict i p origin hr

theorem Execution.BeforeFlowCut.pending_strict {n θ route s u H} {e : @Execution n θ route s u}
    (r : e.BeforeFlowCut H) : ∀ d ∈ r.state.pending, H < d.due := by
  intro d hd
  rw [← r.date]
  exact r.flow.initial_pending_strict d hd

/-- Terminal saturation is a consequence of the next actual flow, rather
than an added assumption about the chosen interior section. -/
theorem Execution.BeforeFlowCut.complete {n θ route s u H} {e : @Execution n θ route s u}
    (r : e.BeforeFlowCut H) : CompleteThrough r.cut H := by
  refine ⟨r.date,?_,r.pending_strict⟩
  exact fun v => r.before_guards.no_jump
    (fun i p origin hr => r.flow.initial_raw_strict i p origin hr)
    r.flow.initial_pending_strict v

/-- Every strictly interior date of an existing finite execution admits a
saturated actual prefix. This does not assert existence beyond that trace. -/
theorem Execution.complete_prefix_at {n θ route s u} (e : @Execution n θ route s u)
    (H : ℝ) (hstart : s.time ≤ H) (hend : H < u.time) :
    ∃ v, ∃ cut : Execution θ route s v, e.IsPrefix cut ∧ CompleteThrough cut H := by
  obtain ⟨r⟩ := e.before_flow_cut_exists H hstart hend
  exact ⟨r.state,r.cut,r.isPrefix,r.complete⟩

end KernelR.Hybrid
