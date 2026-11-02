import KernelR.HybridEmissionRouterTransport
import KernelR.HybridCTeachingRouter
import KernelR.HybridCadenceRouter

/-! One fixed gated routing law covers genuine C teaching and the later
cadence. Retargeting preserves actual issued queues, complete ledgers and
physical traces, so the concatenation introduces no implicit router switch. -/
namespace KernelR.Hybrid

noncomputable def teachingCadenceRouter (oldDelay forward backward : ℝ → ℝ) : Router 3 :=
  fun i t => cTeachingRouter oldDelay i t ++ cadenceRouter forward backward i t

theorem cTeachingRouter.after_close (delay : ℝ → ℝ) (i : Fin 3) {t : ℝ}
    (ht : 630 ≤ t) : cTeachingRouter delay i t = [] := by
  classical
  unfold cTeachingRouter Contact.route
  split_ifs with h
  · have hg : t < (630 : ℝ) := h.2.2
    linarith
  · rfl

theorem teachingCadenceRouter.teaching_before_open (oldDelay forward backward : ℝ → ℝ)
    (i : Fin 3) {t : ℝ} (ht : t < 640) :
    cTeachingRouter oldDelay i t = teachingCadenceRouter oldDelay forward backward i t := by
  rw [teachingCadenceRouter,cadenceRouter.before_open forward backward i ht,List.append_nil]

theorem teachingCadenceRouter.cadence_after_close (oldDelay forward backward : ℝ → ℝ)
    (i : Fin 3) {t : ℝ} (ht : 630 ≤ t) :
    cadenceRouter forward backward i t = teachingCadenceRouter oldDelay forward backward i t := by
  rw [teachingCadenceRouter,cTeachingRouter.after_close oldDelay i ht,List.nil_append]

theorem teachingCadenceRouter.causal (oldDelay forward backward : ℝ → ℝ)
    (ho : ∀ t, 0 ≤ oldDelay t) (hf : ∀ t, 0 ≤ forward t) (hb : ∀ t, 0 ≤ backward t) :
    CausalRouter (teachingCadenceRouter oldDelay forward backward) := by
  intro i t d hd
  rcases List.mem_append.mp hd with hd | hd
  · exact cTeachingRouter.causal oldDelay ho i t d hd
  · exact cadenceRouter.causal forward backward hf hb i t d hd

/-- Actual teaching FIREs before640 use the very same token lists under the
single combined law. Both endpoints and every queue occurrence are identical. -/
theorem Execution.teaching_to_combined {θ s u} (oldDelay forward backward : ℝ → ℝ)
    (e : @Execution 3 θ (cTeachingRouter oldDelay) s u) (hEnd : u.time < 640) :
    ∃ lifted : Execution θ (teachingCadenceRouter oldDelay forward backward) s u,
      lifted.ledger = e.ledger ∧ lifted.deliveries = e.deliveries := by
  apply e.retarget_router (teachingCadenceRouter oldDelay forward backward)
  intro event he
  exact teachingCadenceRouter.teaching_before_open oldDelay forward backward event.1
    ((e.emission_time_bounds event he).2.trans_lt hEnd)

/-- At and after630 the old contact is closed, so a real cadence trace also
uses the same single fixed gated routing law. -/
theorem Execution.cadence_to_combined {θ s u} (oldDelay forward backward : ℝ → ℝ)
    (e : @Execution 3 θ (cadenceRouter forward backward) s u) (hStart : 630 ≤ s.time) :
    ∃ lifted : Execution θ (teachingCadenceRouter oldDelay forward backward) s u,
      lifted.ledger = e.ledger ∧ lifted.deliveries = e.deliveries := by
  apply e.retarget_router (teachingCadenceRouter oldDelay forward backward)
  intro event he
  exact teachingCadenceRouter.cadence_after_close oldDelay forward backward event.1
    (hStart.trans (e.emission_time_bounds event he).1)

theorem Execution.teaching_to_combined_complete {θ s u T} (oldDelay forward backward : ℝ → ℝ)
    (e : @Execution 3 θ (cTeachingRouter oldDelay) s u) (hEnd : u.time < 640)
    (hComplete : CompleteThrough e T) :
    ∃ lifted : Execution θ (teachingCadenceRouter oldDelay forward backward) s u,
      lifted.ledger = e.ledger ∧ lifted.deliveries = e.deliveries ∧ CompleteThrough lifted T := by
  apply e.retarget_router_complete (teachingCadenceRouter oldDelay forward backward) _ hComplete
  intro event he
  exact teachingCadenceRouter.teaching_before_open oldDelay forward backward event.1
    ((e.emission_time_bounds event he).2.trans_lt hEnd)

theorem Execution.cadence_to_combined_complete {θ s u T} (oldDelay forward backward : ℝ → ℝ)
    (e : @Execution 3 θ (cadenceRouter forward backward) s u) (hStart : 630 ≤ s.time)
    (hComplete : CompleteThrough e T) :
    ∃ lifted : Execution θ (teachingCadenceRouter oldDelay forward backward) s u,
      lifted.ledger = e.ledger ∧ lifted.deliveries = e.deliveries ∧ CompleteThrough lifted T := by
  apply e.retarget_router_complete (teachingCadenceRouter oldDelay forward backward) _ hComplete
  intro event he
  exact teachingCadenceRouter.cadence_after_close oldDelay forward backward event.1
    (hStart.trans (e.emission_time_bounds event he).1)

private theorem append_transport_ledger {n θ route s v u} (e : @Execution n θ route s v)
    (f : Execution θ route v u) : (e.append f).ledger = e.ledger.add f.ledger := by
  induction e with
  | nil => simp [Execution.append,Execution.ledger,Ledger.zero,Ledger.add]
  | cons step rest ih =>
    simp only [Execution.append,Execution.ledger,ih,Ledger.add,add_assoc,List.append_assoc]

/-- A single fixed three-cell router supports both actual pieces. Their
states, issue dates, delivered occurrences and complete dose ledger are kept. -/
theorem teaching_cadence_append_exists {θ s v u T} (oldDelay forward backward : ℝ → ℝ)
    (teaching : @Execution 3 θ (cTeachingRouter oldDelay) s v)
    (cadence : Execution θ (cadenceRouter forward backward) v u)
    (hOldEnd : v.time < 640) (hNewStart : 630 ≤ v.time)
    (hComplete : CompleteThrough cadence T) :
    ∃ combined : Execution θ (teachingCadenceRouter oldDelay forward backward) s u,
      combined.ledger = teaching.ledger.add cadence.ledger ∧
      combined.deliveries = teaching.deliveries ++ cadence.deliveries ∧ CompleteThrough combined T := by
  obtain ⟨old,hOldL,hOldD⟩ := teaching.teaching_to_combined oldDelay forward backward hOldEnd
  obtain ⟨next,hNewL,hNewD,hNewC⟩ := cadence.cadence_to_combined_complete oldDelay forward backward hNewStart hComplete
  refine ⟨old.append next,?_,?_,hNewC⟩
  · rw [append_transport_ledger,hOldL,hNewL]
  · rw [Execution.deliveries_append,hOldD,hNewD]

end KernelR.Hybrid
