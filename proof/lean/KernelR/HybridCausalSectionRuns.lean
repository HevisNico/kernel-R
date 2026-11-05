import KernelR.HybridSectionRuns
import KernelR.HybridCausalHeadJump

/-! Actual section steps survive causal product jumps and exact product paths.
Open sections remain open when another cell jumps or a flow is subdivided. -/
namespace KernelR.Hybrid
open Set

theorem SectionStep.flow_shape {n θ route kind i p s u a b k}
    {f : @Flow n θ s u} (step : @SectionStep n θ route kind i p s u (.flow f) a b k) :
    a = b ∧ k = 0 := by
  cases step <;> exact ⟨rfl,rfl⟩

theorem SectionRun.flow_cons {n θ route kind i p s v u first last count}
    {flow : @Flow n θ s v} {rest : Execution θ route v u}
    (run : SectionRun kind i p (.cons (.flow flow) rest) first last count) :
    SectionStep (route := route) kind i p (.flow flow) first first 0 ∧
      SectionRun kind i p rest first last count := by
  obtain ⟨middle,stepCount,tailCount,hcount,step,tail⟩ := SectionRun.cons_iff.mp run
  obtain ⟨rfl,rfl⟩ := step.flow_shape
  simp only [zero_add] at hcount
  subst count
  exact ⟨step,tail⟩

theorem SectionStep.prependQueued_tail_jump {n θ θH route kind i p s u a b k}
    {jump : @Jump n route s u}
    (step : @SectionStep n θ route kind i p s u (.jump jump) a b k)
    (head : Snapshot 1) (Q Q' : List (Delivery (n+1))) (contacts : HeadRoutes n)
    (global : Jump (prependRouted route contacts)
      (s.prependQueued head Q) (u.prependQueued head Q')) :
    @SectionStep (n+1) (prependParameters θH θ) (prependRouted route contacts)
      kind i.succ p _ _ (.jump global) a b k := by
  cases step with
  | inactive _ h => exact .inactive (.jump global) (by cases kind <;> trivial)
  | enter _ before after => exact .enter global before after
  | jump _ before after => exact .jump global before after
  | exit _ before after => exact .exit global before after

theorem SectionStep.prependQueued_head_jump {n θ θH route kind p s u a b k}
    {jump : Jump (fun _ _ => []) s u}
    (step : @SectionStep 1 θH (fun _ _ => []) kind 0 p s u (.jump jump) a b k)
    (tail : Snapshot n) (Q Q' : List (Delivery (n+1))) (contacts : HeadRoutes n)
    (global : Jump (prependRouted route contacts)
      (tail.prependQueued s Q) (tail.prependQueued u Q')) :
    @SectionStep (n+1) (prependParameters θH θ) (prependRouted route contacts)
      kind 0 p _ _ (.jump global) a b k := by
  cases step with
  | inactive _ h => exact .inactive (.jump global) (by cases kind <;> trivial)
  | enter _ before after => exact .enter global before after
  | jump _ before after => exact .jump global before after
  | exit _ before after => exact .exit global before after

theorem SectionStep.prependQueued_idle_head {n θ θH route kind p head active}
    {s u : Snapshot n}
    (valid : kind.Valid 0 p active head)
    (Q Q' : List (Delivery (n+1))) (contacts : HeadRoutes n)
    (global : Jump (prependRouted route contacts)
      (s.prependQueued head Q) (u.prependQueued head Q')) :
    @SectionStep (n+1) (prependParameters θH θ) (prependRouted route contacts)
      kind 0 p _ _ (.jump global) active active 0 := by
  cases active with
  | false => exact .inactive (.jump global) (by cases kind <;> trivial)
  | true => exact .jump global (valid rfl) (valid rfl)

theorem SectionStep.prependQueued_idle_tail {n θ θH route kind i p tail s u active}
    (valid : kind.Valid i p active tail)
    (Q Q' : List (Delivery (n+1))) (contacts : HeadRoutes n)
    (global : Jump (prependRouted route contacts)
      (tail.prependQueued s Q) (tail.prependQueued u Q')) :
    @SectionStep (n+1) (prependParameters θH θ) (prependRouted route contacts)
      kind i.succ p _ _ (.jump global) active active 0 := by
  cases active with
  | false => exact .inactive (.jump global) (by cases kind <;> trivial)
  | true => exact .jump global (valid rfl) (valid rfl)

theorem SectionStep.prependQueued_tail_flow {n θ θH route kind i p s u head final a b k}
    {flow : @Flow n θ s u}
    (step : @SectionStep n θ route kind i p s u (.flow flow) a b k)
    (Q : List (Delivery (n+1))) (contacts : HeadRoutes n)
    (global : Flow (prependParameters θH θ) (s.prependQueued head Q) (u.prependQueued final Q))
    (path : ∀ t c, global.path t i.succ c = flow.path t i c) :
    @SectionStep (n+1) (prependParameters θH θ) (prependRouted route contacts)
      kind i.succ p _ _ (.flow global) a b k := by
  cases step with
  | inactive _ inactive =>
    exact .inactive (.flow global) (by cases kind <;> exact inactive)
  | flow _ exposed =>
    apply SectionStep.flow
    cases kind <;>
      refine ⟨exposed.1, exposed.2.1, ?_⟩ <;>
      intro t ht <;>
      simpa only [path, prependParameters, Fin.cases_succ, Fin.cases_zero] using exposed.2.2 t ht

theorem SectionStep.prependQueued_head_flow {n θ θH route kind p head final a b k}
    {s u : Snapshot n}
    {flow : @Flow 1 θH head final}
    (step : @SectionStep 1 θH (fun _ _ => []) kind 0 p head final (.flow flow) a b k)
    (hstart : s.time = head.time) (hfinish : u.time = final.time)
    (Q : List (Delivery (n+1))) (contacts : HeadRoutes n)
    (global : Flow (prependParameters θH θ) (s.prependQueued head Q) (u.prependQueued final Q))
    (path : ∀ t c, global.path t 0 c = flow.path t 0 c) :
    @SectionStep (n+1) (prependParameters θH θ) (prependRouted route contacts)
      kind 0 p _ _ (.flow global) a b k := by
  cases step with
  | inactive _ inactive =>
    exact .inactive (.flow global) (by cases kind <;> exact inactive)
  | flow _ exposed =>
    apply SectionStep.flow
    cases kind <;>
      refine ⟨exposed.1, exposed.2.1, ?_⟩ <;>
      intro t ht
    all_goals
      change t ∈ Icc s.time u.time at ht
      rw [hstart, hfinish] at ht
      simpa only [path, prependParameters, Fin.cases_succ, Fin.cases_zero] using exposed.2.2 t ht

theorem SectionStep.flow_cut_prefix {n θ route kind i p s u a b k t}
    {flow : @Flow n θ s u}
    (step : @SectionStep n θ route kind i p s u (.flow flow) a b k)
    (_ht : s.time < t) (hu : t < u.time)
    (beforeFlow : Flow θ s (flow.at t)) (path : beforeFlow.path = flow.path) :
    @SectionStep n θ route kind i p s (flow.at t) (.flow beforeFlow) a b k := by
  cases step with
  | inactive _ inactive => exact .inactive (.flow beforeFlow) (by cases kind <;> exact inactive)
  | flow _ exposed =>
    apply SectionStep.flow
    cases kind <;>
      refine ⟨exposed.1, exposed.2.1, ?_⟩ <;>
      intro v hv
    all_goals
      rw [path]
      exact exposed.2.2 v ⟨hv.1,hv.2.trans hu.le⟩

theorem SectionStep.flow_cut_suffix {n θ route kind i p s u a b k t}
    {flow : @Flow n θ s u}
    (step : @SectionStep n θ route kind i p s u (.flow flow) a b k)
    (ht : s.time < t) (_hu : t < u.time)
    (afterFlow : Flow θ (flow.at t) u) (path : afterFlow.path = flow.path) :
    @SectionStep n θ route kind i p (flow.at t) u (.flow afterFlow) a b k := by
  cases step with
  | inactive _ inactive => exact .inactive (.flow afterFlow) (by cases kind <;> exact inactive)
  | flow _ exposed =>
    apply SectionStep.flow
    cases kind <;>
      refine ⟨exposed.1, exposed.2.1, ?_⟩ <;>
      intro v hv
    all_goals
      rw [path]
      exact exposed.2.2 v ⟨ht.le.trans hv.1,hv.2⟩

end KernelR.Hybrid
