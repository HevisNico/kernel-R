import KernelR.HybridParameterTransport

/-! Retarget a queued delivery before it is admitted. The continuous
states and all events already performed are preserved. -/
namespace RecursiveLearning.Native
open KernelR.Hybrid

def mapPending {n} (edit : Delivery n → Delivery n) (s : Snapshot n) : Snapshot n :=
  { s with pending := s.pending.map edit }

def jumpInputs {n θ route s u} (j : @ParameterJump n θ route s u) : List (Delivery n) :=
  match j with
  | .arrive _ d _ _ _ _ _ => [d]
  | _ => []

def executionInputs {n θ route s u} : @ParameterExecution n θ route s u → List (Delivery n)
  | .nil _ => []
  | .cons (.flow _) tail => executionInputs tail
  | .cons (.jump j) tail => jumpInputs j ++ executionInputs tail

private noncomputable def mappedFlow {n θ s u} (f : @ParameterFlow n θ s u)
    (edit : Delivery n → Delivery n) (dates : ∀ d, (edit d).due = d.due) :
    ParameterFlow θ (mapPending edit s) (mapPending edit u) where
  positive := f.positive
  path := f.path
  initial := f.initial
  final := f.final
  main_fixed := f.main_fixed
  aux_fixed := f.aux_fixed
  raw_fixed := f.raw_fixed
  queue_fixed := congrArg (List.map edit) f.queue_fixed
  continuous := f.continuous
  integrable := f.integrable
  mark_integrable := f.mark_integrable
  integral_eq := f.integral_eq
  guards := f.guards
  raw_support := f.raw_support
  pending_urgent := by
    intro d hd
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hd
    rw [dates]
    exact f.pending_urgent x hx

private theorem mappedJump {n θ s u}
    (j : @ParameterJump n θ (fun _ _ => []) s u)
    (edit : Delivery n → Delivery n)
    (done : ∀ d ∈ jumpInputs j, edit d = d) :
    ∃ k : ParameterJump θ (fun _ _ => []) (mapPending edit s) (mapPending edit u),
      k.emissions = j.emissions := by
  cases j with
  | fire i mode guard =>
    let source := mapPending edit s
    have endEq : mapPending edit { (setMain s i .fast) with pending := s.pending ++ [] } =
        {(setMain source i .fast) with pending := source.pending ++ []} := by
      simp [mapPending, source, setMain]
    rw [endEq]
    exact ⟨ParameterJump.fire source i mode guard, rfl⟩
  | fastEnd i mode guard => exact ⟨ParameterJump.fastEnd (mapPending edit s) i mode guard, rfl⟩
  | reopen i mode guard => exact ⟨ParameterJump.reopen (mapPending edit s) i mode guard, rfl⟩
  | mark i p mode guard => exact ⟨ParameterJump.mark (mapPending edit s) i p mode guard, rfl⟩
  | silent i p mode guard => exact ⟨ParameterJump.silent (mapPending edit s) i p mode guard, rfl⟩
  | error i p mode guard => exact ⟨ParameterJump.error (mapPending edit s) i p mode guard, rfl⟩
  | auxReady i p mode guard => exact ⟨ParameterJump.auxReady (mapPending edit s) i p mode guard, rfl⟩
  | rawEnd i p origin active due => exact ⟨ParameterJump.rawEnd (mapPending edit s) i p origin active due, rfl⟩
  | arrive d before after queue due free =>
    have unchanged : edit d = d := done d (by simp [jumpInputs])
    let source := mapPending edit s
    have newQueue : source.pending = before.map edit ++ d :: after.map edit := by
      change s.pending.map edit = _
      rw [queue, List.map_append, List.map_cons, unchanged]
    have endEq : mapPending edit
        { (setRaw s d.cell d.port (some s.time)) with pending := before ++ after } =
        { (setRaw source d.cell d.port (some source.time)) with pending := before.map edit ++ after.map edit } := by
      simp [mapPending, source, setRaw, List.map_append]
    rw [endEq]
    exact ⟨ParameterJump.arrive source d (before.map edit) (after.map edit) newQueue due free, rfl⟩

/-- A date-preserving edit of the pending queue transports an execution
provided all deliveries actually admitted by it are fixed by the edit. -/
theorem map_execution_pending {n θ s u} (e : @ParameterExecution n θ (fun _ _ => []) s u)
    (edit : Delivery n → Delivery n) (dates : ∀ d, (edit d).due = d.due)
    (done : ∀ d ∈ executionInputs e, edit d = d) :
    ∃ ex : ParameterExecution θ (fun _ _ => []) (mapPending edit s) (mapPending edit u),
      ex.emissions = e.emissions := by
  induction e with
  | nil => exact ⟨.nil _, rfl⟩
  | cons m tail ih =>
    cases m with
    | flow f =>
      obtain ⟨newTail, same⟩ := ih done
      exact ⟨.cons (.flow (mappedFlow f edit dates)) newTail, same⟩
    | jump j =>
      obtain ⟨k, same⟩ := mappedJump j edit (fun d hd =>
        done d (List.mem_append_left _ hd))
      obtain ⟨newTail, tailSame⟩ := ih (fun d hd => done d (List.mem_append_right _ hd))
      exact ⟨.cons (.jump k) newTail, by simp [ParameterExecution.emissions, same, tailSame]⟩

theorem executionInputs_append {n θ route s u v} (e : @ParameterExecution n θ route s u)
    (tail : ParameterExecution θ route u v) :
    executionInputs (e.append tail) = executionInputs e ++ executionInputs tail := by
  induction e with
  | nil => rfl
  | cons m r ih =>
    cases m <;> simp [ParameterExecution.append, executionInputs, ih, List.append_assoc]

end RecursiveLearning.Native
