import KernelR.HybridPreparedFirstSource
import KernelR.HybridCadenceRestRoot

/-! Finite learned input prefixes with nonuniform actual dates. Each next
token is consumed after a genuine cycle and quiet continuation. -/
namespace KernelR.Hybrid

def LearnedPrefixSpacing (start : ℝ) : List ℝ → Prop
  | [] => True
  | H :: rest => start + 69 / 10 < H ∧ LearnedPrefixSpacing H rest

def learnedPrefixEnd (start : ℝ) : List ℝ → ℝ
  | [] => start
  | H :: rest => learnedPrefixEnd H rest

def learnedPrefixResponses (start : ℝ) : List ℝ → List ℝ
  | [] => []
  | H :: rest => start :: learnedPrefixResponses H rest

theorem LearnedPrefixSpacing.end_ge {start times} (h : LearnedPrefixSpacing start times) :
    start ≤ learnedPrefixEnd start times := by
  induction times generalizing start with
  | nil => exact le_rfl
  | cons H rest ih =>
    have hs : start ≤ H := by linarith [h.1]
    exact hs.trans (ih h.2)

theorem LearnedPrefixSpacing.input_gt {start times} (h : LearnedPrefixSpacing start times)
    (t : ℝ) (ht : t ∈ times) : start < t := by
  induction times generalizing start with
  | nil => simp at ht
  | cons H rest ih =>
    rcases List.mem_cons.mp ht with rfl | ht
    · linarith [h.1]
    · exact lt_trans (by linarith [h.1] : start < H) (ih h.2 ht)

structure LearnedSourcePrefix (θ : Fin 1 → Parameters) (s : Snapshot 1) (p : Port)
    (times : List ℝ) (later : List (Delivery 1)) where
  final : Snapshot 1
  execution : Execution θ (fun _ _ => []) s final
  contacts_transversal : execution.ContactsTransversal
  date : final.time = learnedPrefixEnd s.time times
  prepared : PreparedSection final 0
  charge : final.x 0 .q = 1 / 10
  raw_active : final.raw 0 p = some final.time
  raw_other : ∀ q, q ≠ p → final.raw 0 q = none
  pending : final.pending = later
  gains : ∀ q, final.x 0 (.z q) = s.x 0 (.z q)
  recovery : final.x 0 .b = s.x 0 .b
  calendar : execution.emissionTimes 0 =
    (learnedPrefixResponses s.time times).map (fun T => T + restLatency (Real.exp (s.x 0 (.z p))))
  emission_count : (execution.emissionTimes 0).length = times.length
  deliveries : execution.deliveries = times.map (fun T => ⟨0,p,T⟩)
  physical : PhysicalInvariant θ final
  raw_valid : RawValid final
  complete : CompleteThrough execution final.time

theorem learned_source_prefix_exists {θ ε} (hb : PhysicalBox θ ε) (s : Snapshot 1)
    (p : Port) (times : List ℝ) (later : List (Delivery 1))
    (hf : PhysicalInvariant θ s) (hv : RawValid s) (hs : PreparedSection s 0)
    (hq : s.x 0 .q = 1 / 10)
    (hg : 9 / 5 ≤ Real.exp (s.x 0 (.z p)) ∧ Real.exp (s.x 0 (.z p)) ≤ 11 / 5)
    (hr : s.raw 0 p = some s.time) (ho : ∀ q, q ≠ p → s.raw 0 q = none)
    (hqueue : s.pending = times.map (fun T => ⟨0,p,T⟩) ++ later)
    (hspace : LearnedPrefixSpacing s.time times)
    (hLater : ∀ d ∈ later, learnedPrefixEnd s.time times < d.due) :
    Nonempty (LearnedSourcePrefix θ s p times later) := by
  induction times generalizing s with
  | nil =>
    let execution : Execution θ (fun _ _ => []) s s := .nil _
    have hGuard : BeforeGuards s s.x := by
      constructor
      · intro i
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        rw [hs.ready,hq]
        norm_num
      · intro i q
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        rw [(hs.auxiliary q).1]
        linarith [(hs.auxiliary q).2.2]
    have hFuture : ∀ d ∈ s.pending, s.time < d.due := by
      intro d hd
      rw [hqueue] at hd
      exact hLater d hd
    have hc : CompleteThrough execution s.time := by
      refine ⟨rfl,?_,hFuture⟩
      intro u
      apply hGuard.no_jump
      · intro i q origin hraw
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        by_cases hp : q = p
        · subst q
          have hOrigin : origin = s.time := Option.some.inj (hraw.symm.trans hr)
          rw [hOrigin]
          linarith
        · rw [ho q hp] at hraw
          contradiction
      · exact hFuture
    exact ⟨{
      final := s, execution := execution, contacts_transversal := trivial, date := rfl, prepared := hs, charge := hq
      raw_active := hr, raw_other := ho, pending := hqueue, gains := fun _ => rfl, recovery := rfl
      calendar := rfl, emission_count := rfl, deliveries := rfl
      physical := hf, raw_valid := hv, complete := hc
    }⟩
  | cons H rest ih =>
    let nextQueue : List (Delivery 1) := rest.map (fun T => ⟨0,p,T⟩) ++ later
    have hFuture : ∀ d ∈ nextQueue, H < d.due := by
      intro d hd
      rcases List.mem_append.mp hd with hd | hd
      · obtain ⟨T,hT,rfl⟩ := List.mem_map.mp hd
        exact hspace.2.input_gt T hT
      · exact lt_of_le_of_lt hspace.2.end_ge (hLater d hd)
    obtain ⟨step⟩ := short_learned_next_source_exists hb s p H nextQueue hf hv hs hg hr ho
      hqueue hspace.1 hFuture
    have hSpace : LearnedPrefixSpacing step.final.time rest := by rw [step.date]; exact hspace.2
    have hTail : ∀ d ∈ later, learnedPrefixEnd step.final.time rest < d.due := by
      rw [step.date]
      exact hLater
    have hGain : 9 / 5 ≤ Real.exp (step.final.x 0 (.z p)) ∧
        Real.exp (step.final.x 0 (.z p)) ≤ 11 / 5 := by rw [step.gains]; exact hg
    obtain ⟨tail⟩ := ih step.final step.physical step.raw_valid (step.prepared 0) step.charge hGain
      (by rw [step.date]; exact step.raw_active) step.raw_other step.pending hSpace hTail
    let execution := step.execution.append tail.execution
    have hRoot : readyPulse (1 / 10) (Real.exp (s.x 0 (.z p))) 0 step.cycle.fire.latency = 1 := by
      simpa only [shortLearnedLocalState,hq,readyPulse,add_sub_cancel_left,sub_zero]
        using step.cycle.fire.response_root
    have hLatency : step.cycle.fire.latency = restLatency (Real.exp (s.x 0 (.z p))) :=
      restLatency_unique ⟨hg.1,by linarith [hg.2]⟩
        ⟨by linarith [step.cycle.fire.early],step.cycle.fire.deadline.le⟩ hRoot
    have hFire : step.cycle.fire.final.time = s.time + restLatency (Real.exp (s.x 0 (.z p))) := by
      rw [step.cycle.fire.date,hLatency]
      rfl
    have hCalendar : execution.emissionTimes 0 =
        (learnedPrefixResponses s.time (H :: rest)).map
          (fun T => T + restLatency (Real.exp (s.x 0 (.z p)))) := by
      rw [Execution.emissionTimes_append,tail.calendar]
      have hHead : step.execution.emissionTimes 0 = [step.cycle.fire.final.time] := by
        simp [Execution.emissionTimes,step.emissions]
      rw [hHead,hFire,step.date,step.gains]
      rfl
    refine ⟨{
      final := tail.final
      execution := execution
      contacts_transversal := by
        simpa only [execution, Execution.contactsTransversal_append] using
          (And.intro step.contacts_transversal tail.contacts_transversal)
      date := ?_
      prepared := tail.prepared
      charge := tail.charge, raw_active := tail.raw_active, raw_other := tail.raw_other
      pending := tail.pending, gains := ?_, recovery := ?_, calendar := hCalendar
      emission_count := ?_, deliveries := ?_, physical := tail.physical, raw_valid := tail.raw_valid
      complete := by simpa only [CompleteThrough] using tail.complete
    }⟩
    · rw [tail.date,step.date]
      rfl
    · intro q
      rw [tail.gains,step.gains]
    · rw [tail.recovery,step.recovery]
    · rw [Execution.emissionTimes_append,List.length_append,step.emission_count,tail.emission_count]
      simp [Nat.add_comm]
    · rw [Execution.deliveries_append,step.deliveries,tail.deliveries]
      rfl

end KernelR.Hybrid
