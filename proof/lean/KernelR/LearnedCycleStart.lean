import KernelR.LearnedCycle

/-! A reacting physical prefix from the learned section: consume the actual
source token, flow to the auxiliary's first guard, then enter MARK. No execution
existence or desired pulse-case word is assumed. -/
namespace KernelR.Hybrid
open Set

def receivedInput (s : Snapshot 1) (port : Port) : Snapshot 1 :=
  { (setRaw s 0 port (some s.time)) with pending := [] }

theorem receivedInput_amplitude {theta active s} (hs : LearnedRest theta active s) (port : Port) :
    mainAmplitude (receivedInput s port) 0 = Real.exp (s.x 0 (.z port)) := by
  unfold mainAmplitude
  rw [Finset.sum_eq_single port]
  · simp [frozenRawAmplitude, receivedInput, setRaw]
  · intro other _ hne
    simp [frozenRawAmplitude, receivedInput, setRaw, hne, hs.raw]
  · simp

theorem receivedInput_main_charge {theta active s} (hs : LearnedRest theta active s)
    (port : Port) (t : ℝ) :
    frozenValues theta (receivedInput s port) t 0 .q =
      learnedHead (Real.exp (s.x 0 (.z port))) (t-s.time) := by
  have hm : (receivedInput s port).main 0 = .ready := hs.main 0
  simp only [frozenValues, frozenBody, frozenMain, hm]
  rw [receivedInput_amplitude hs port]
  simp [receivedInput, setRaw, readyPulse, learnedHead, hs.charge]

theorem receivedInput_active_charge {theta active s} (hs : LearnedRest theta active s)
    (port : Port) (t : ℝ) :
    frozenValues theta (receivedInput s port) t 0 (.m port) =
      auxPulse (s.x 0 (.m port)) ((theta 0).inputGain port) 0 (t-s.time) := by
  have hm : (receivedInput s port).aux 0 port = .ready := hs.aux 0 port
  simp only [frozenValues, frozenBody, frozenAux, hm, ite_true]
  have hr : frozenRawAmplitude (receivedInput s port) 0 port = 1 := by
    simp [frozenRawAmplitude, receivedInput, setRaw]
  rw [hr, mul_one]
  simp [receivedInput, setRaw, auxPulse, readyPulse]

theorem receivedInput_passive_charge {theta active s} (hs : LearnedRest theta active s)
    (port other : Port) (hne : other ≠ port) (t : ℝ) :
    frozenValues theta (receivedInput s port) t 0 (.m other) = idleValues s t 0 (.m other) := by
  have hm : (receivedInput s port).aux 0 other = .ready := hs.aux 0 other
  simp only [frozenValues, frozenBody, frozenAux, hm, ite_true]
  have hr : frozenRawAmplitude (receivedInput s port) 0 other = 0 := by
    simp [frozenRawAmplitude, receivedInput, setRaw, hne, hs.raw]
  rw [hr, mul_zero]
  simp [receivedInput, setRaw, auxPulse, readyPulse, idleValues]
  ring

structure FirstMarkPrefix (theta : Fin 1 → Parameters) (s : Snapshot 1) (port : Port) where
  clock : LearnedClock (theta 0) port (Real.exp (s.x 0 (.z port))) (s.x 0 (.m port))
  last : Snapshot 1
  physical_state : last =
    setAux (frozenAt theta (receivedInput s port) (s.time+clock.auxiliary)) 0 port .mark
  execution : Execution theta (fun _ _ => []) (withFuture s [sourceToken 0 port s.time]) last
  date : last.time = s.time + clock.auxiliary
  main_ready : last.main 0 = .ready
  auxiliary_mark : last.aux 0 port = .mark
  memory : SameMemory s last
  emissions : execution.ledger.emissions = []
  reserve : 50 ≤ last.x 0 .energy ∧ last.x 0 .energy ≤ 100

theorem learned_first_mark_prefix {theta epsilon active s}
    (hs : LearnedRest theta active s) (hb : PhysicalBox theta epsilon) :
    Nonempty (FirstMarkPrefix theta s (active 0)) := by
  let port := active 0
  obtain ⟨clock⟩ := learned_clock_exists hb 0 port (hs.gain 0) (hs.sensor 0 port)
  let incoming := receivedInput s port
  have hfrozen : FrozenModes incoming := by
    constructor
    · intro i p _; rw [show incoming.aux i p = .ready from hs.aux i p]; decide
    · intro i p _; exact hs.main i
  have hpositive : incoming.time < s.time+clock.auxiliary := by
    change s.time < s.time+clock.auxiliary
    linarith [clock.auxiliary_lower]
  have hguards : ∀ t ∈ Ico incoming.time (s.time+clock.auxiliary),
      BeforeGuards incoming (frozenValues theta incoming t) := by
    intro t ht
    constructor
    · intro i
      have he : i = 0 := Subsingleton.elim _ _
      subst i
      have hm : incoming.main 0 = .ready := hs.main 0
      simp only [hm]
      rw [receivedInput_main_charge hs port t]
      apply learned_head_early (hs.gain 0)
      change s.time ≤ t ∧ t < s.time+clock.auxiliary at ht
      constructor <;> linarith [ht.1, ht.2, clock.auxiliary_upper]
    · intro i p
      have he : i = 0 := Subsingleton.elim _ _
      subst i
      have hm : incoming.aux 0 p = .ready := hs.aux 0 p
      simp only [hm]
      by_cases hp : p = port
      · subst p
        rw [receivedInput_active_charge hs port t]
        apply clock.auxiliary_before
        change s.time ≤ t ∧ t < s.time+clock.auxiliary at ht
        constructor <;> linarith [ht.1, ht.2]
      · rw [receivedInput_passive_charge hs port p hp t]
        have hh := (abs_le.mp (idleValues_sensor hs ht.1 0 p)).2
        linarith
  have hraw : ∀ i p origin, incoming.raw i p = some origin →
      origin ≤ incoming.time ∧ s.time+clock.auxiliary ≤ origin+1 := by
    intro i p origin hraw
    have he : i = 0 := Subsingleton.elim _ _
    subst i
    by_cases hp : p = port
    · subst p
      have ho : origin = s.time := by simpa [incoming, receivedInput, setRaw] using hraw.symm
      subst origin
      constructor
      · exact le_rfl
      · linarith [clock.auxiliary_upper]
    · simp [incoming, receivedInput, setRaw, hp, hs.raw] at hraw
  let flow := frozenFlow hfrozen hpositive hguards hraw (by simp [incoming, receivedInput])
  let endpoint := frozenAt theta incoming (s.time+clock.auxiliary)
  have hmark : endpoint.x 0 (.m port) = 1 := by
    change frozenValues theta incoming (s.time+clock.auxiliary) 0 (.m port) = 1
    rw [receivedInput_active_charge hs port]
    simpa using clock.auxiliary_value
  let arrival : Jump (fun _ _ => []) (withFuture s [sourceToken 0 port s.time]) incoming := by
    exact Jump.arrive _ (sourceToken 0 port s.time) [] []
      (by simp [withFuture, hs.pending]) rfl (hs.raw 0 port)
  let mark : Jump (fun _ _ => []) endpoint (setAux endpoint 0 port .mark) :=
    Jump.mark endpoint 0 port (hs.aux 0 port) hmark
  let run : Execution theta (fun _ _ => []) (withFuture s [sourceToken 0 port s.time])
      (setAux endpoint 0 port .mark) :=
    .cons (.jump arrival) (.cons (.flow flow) (.cons (.jump mark) (.nil _)))
  refine ⟨⟨clock, setAux endpoint 0 port .mark, rfl, run, rfl, hs.main 0, ?_, ?_, ?_, ?_⟩⟩
  · simp [setAux, port]
  · intro i; exact ⟨rfl, fun _ => rfl⟩
  · rfl
  · exact run.reserve_invariant 0 (hs.reserve 0)
      (run.actual_work_bound hb hs.upper_region hs.cap 0)

end KernelR.Hybrid
