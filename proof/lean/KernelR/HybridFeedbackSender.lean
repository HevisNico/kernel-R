import KernelR.HybridPreparedLearningTrain
import KernelR.HybridResidualPreparedCalendar
/-! The B feedback sender: three derived silent inputs and thirteen actual outputs. -/
namespace KernelR.Hybrid

structure FeedbackSender {θ route s u} (e : @Execution 2 θ route s u) where
  learning : PreparedLearningTrain e 1 2 13
  first : ℝ
  first_lower : 3 / 10 < first
  first_upper : first < 9 / 10
  first_le_rest : first ≤ restLatency (Real.exp (s.x 1 (.z 2) + 9 / 5))
  emissions : e.emissionTimes 1 = (344 + first) :: List.ofFn (fun k : Fin 12 =>
    (352 : ℝ) + 8 * (k.val : ℝ) + restLatency (Real.exp (s.x 1 (.z 2) + 9 / 5)))

/-- The direct sources after the active source at 320 are actual arrivals.
Silent behavior, learned gain, thirteen emissions and the first residual
latency are all derived while retaining the original multicell execution. -/
theorem Execution.feedback_sender {θ ε route s u} (e : @Execution 2 θ route s u)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (hs : PreparedSection s 1) (hq : 1 / 10 ≤ s.x 1 .q)
    (hz : Real.log (3 / 10) - 1 / 100000 ≤ s.x 1 (.z 2) ∧
      s.x 1 (.z 2) ≤ Real.log (3 / 10) + 1 / 100000)
    (hr : s.raw 1 2 = some s.time) (ho : ∀ q, q ≠ 2 → s.raw 1 q = none)
    (ht : s.time = 320) (hu : u.time = 4599 / 10)
    (hcalendar : e.cellDeliveries 1 = sourceTrain 1 2 328 8 15) : Nonempty (FeedbackSender e) := by
  let tail : List ℝ := List.ofFn (fun k : Fin 12 => (352 : ℝ) + 8 * (k.val : ℝ))
  have htrain : sourceTrain (1 : Fin 2) 2 328 8 15 =
      ⟨1,2,328⟩ :: ⟨1,2,336⟩ :: ⟨1,2,344⟩ :: sourceTrain 1 2 352 8 12 := by
    rw [sourceTrain_succ,show (328 : ℝ) + 8 = 336 by norm_num,
      sourceTrain_succ,show (336 : ℝ) + 8 = 344 by norm_num,
      sourceTrain_succ,show (344 : ℝ) + 8 = 352 by norm_num]
  have hcal : e.cellDeliveries 1 = (328 :: 336 :: 344 :: tail).map (fun t => ⟨1,2,t⟩) := by
    rw [hcalendar,htrain]
    simp only [List.map_cons,tail,sourceTrain,List.map_ofFn,Function.comp_def]
  have hfull : sourceTrain (1 : Fin 2) 2 320 8 16 =
      ⟨1,2,320⟩ :: ⟨1,2,328⟩ :: ⟨1,2,336⟩ :: ⟨1,2,344⟩ :: sourceTrain 1 2 352 8 12 := by
    rw [sourceTrain_succ,show (320 : ℝ) + 8 = 328 by norm_num,htrain]
  have hdates : (320 : ℝ) :: 328 :: 336 :: 344 :: tail =
      List.ofFn (fun k : Fin 16 => (320 : ℝ) + 8 * (k.val : ℝ)) := by
    have h := congrArg (List.map Delivery.due) hfull
    simpa only [sourceTrain,tail,List.map_ofFn,Function.comp_def,List.map_cons] using h.symm
  have hspace : (s.time :: 328 :: 336 :: 344 :: tail).Pairwise (fun t v => t + 15 / 2 ≤ v) := by
    rw [ht,hdates]
    apply List.pairwise_ofFn.mpr
    intro k l hkl
    have hk : (k.val : ℝ) + 1 ≤ l.val := by exact_mod_cast (Nat.add_one_le_iff.mpr hkl)
    linarith
  have hquiet : ∀ t ∈ s.time :: 328 :: 336 :: 344 :: tail, t + 15 / 2 ≤ u.time := by
    intro t hm
    rw [ht,hdates] at hm
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hm
    have hk : (k.val : ℝ) ≤ 15 := by exact_mod_cast (show k.val ≤ 15 by omega)
    rw [hu]
    linarith
  obtain ⟨learning⟩ := e.prepared_learning_train hb hf hv 1 2 hs hz hr ho 328 336 344 tail hcal hspace hquiet
  have hlearning : PreparedLearningTrain e 1 2 13 := by
    simpa only [tail,List.length_ofFn] using learning
  obtain ⟨warm⟩ := e.prepared_learning_warmup hb hf hv 1 2 hs hz hr ho 328 336 344 tail hcal hspace
  have hentrydate : warm.entry.time = 344 := by
    simpa only [List.getLastD_cons,List.getLastD_nil] using warm.date
  have hgain : warm.entry.x 1 (.z 2) = s.x 1 (.z 2) + 9 / 5 := by
    have h := warm.gain_target
    norm_num at h
    exact h
  have hlog : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ warm.entry.x 1 (.z 2) ∧
      warm.entry.x 1 (.z 2) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000 := by
    rw [hgain]
    constructor <;> linarith [hz.1,hz.2]
  have hstrong : 9 / 5 ≤ Real.exp (warm.entry.x 1 (.z 2)) ∧
      Real.exp (warm.entry.x 1 (.z 2)) ≤ 12 / 5 := by
    have h := learned_gain_bounds hlog.1 hlog.2
    exact ⟨h.1,by linarith [h.2]⟩
  have hspaceStrong : (warm.entry.time :: tail).Pairwise (fun t v => t + 15 / 2 ≤ v) := by
    rw [hentrydate]
    exact (List.pairwise_cons.mp (List.pairwise_cons.mp (List.pairwise_cons.mp hspace).2).2).2
  have hquietStrong : ∀ t ∈ warm.entry.time :: tail, t + 15 / 2 ≤ u.time := by
    rw [hentrydate]
    intro t hm
    exact hquiet t (by simp only [List.mem_cons] at hm ⊢; tauto)
  obtain ⟨first,hlo,hhi,hle,hem⟩ := prepared_cell_residual_calendar_of_valid hb 1 2 tail warm.rest
    (warm.head.upper_region hb hf.region) (warm.head.raw_valid hv) warm.prepared (warm.charge_lower hq)
    hstrong warm.raw_active warm.raw_other warm.calendar hspaceStrong hquietStrong
  rw [hgain] at hle hem
  rw [hentrydate] at hem
  have hsplit := congrArg (fun actual => actual.emissionTimes 1) warm.reconstruct
  rw [Execution.emissionTimes_append,warm.emissions,List.nil_append] at hsplit
  refine ⟨⟨hlearning,first,hlo,hhi,hle,?_⟩⟩
  rw [hsplit,hem]
  simp only [tail,List.map_ofFn,Function.comp_def]

end KernelR.Hybrid
