import RoutedProduct

/-! A cascade of trained cells. Two trained cells are read by source
pulses. Their read FIREs travel on two wires to the two ports of a third
trained cell, which they read. No gain and no FIRE level is set by hand
in any of the three cells. -/

namespace RecursiveLearning.Native
open KernelR.Hybrid Set

/-- A cell with two read pulses added at the end of its queue. -/
def withReads (s : Snapshot 1) (p₁ p₂ : Port) (ρ₁ ρ₂ : ℝ) : Snapshot 1 :=
  { s with pending := s.pending ++ [(⟨0, p₁, ρ₁⟩ : Delivery 1), (⟨0, p₂, ρ₂⟩ : Delivery 1)] }

/-- The wires of the cascade. A FIRE of cell 0 after `gateA` reaches port
`p₁` of cell 2 after the delay `wA`. A FIRE of cell 1 after `gateB`
reaches port `p₂` of cell 2 after the delay `wB`. The gates keep the
FIRE events of training off the wires. -/
noncomputable def cascadeRoute (gateA gateB wA wB : ℝ) (p₁ p₂ : Port) : Router 3 := fun i t =>
  if i = 0 then (if gateA < t then [⟨2, p₁, t + wA⟩] else [])
  else if i = 1 then (if gateB < t then [⟨2, p₂, t + wB⟩] else [])
  else []

theorem cascadeRoute_causal {gateA gateB wA wB : ℝ} {p₁ p₂ : Port} (wireA : 0 < wA)
    (wireB : 0 < wB) :
    ∀ i t d, d ∈ cascadeRoute gateA gateB wA wB p₁ p₂ i t → t < d.due := by
  intro i t d hd
  fin_cases i <;> simp [cascadeRoute] at hd
  · obtain ⟨_, rfl⟩ := hd
    show t < t + wA
    linarith
  · obtain ⟨_, rfl⟩ := hd
    show t < t + wB
    linarith

theorem gated_flatMap {α : Type} (training : List ℝ) (tf gate : ℝ) (g : ℝ → α)
    (early : ∀ t ∈ training, t ≤ gate) (late : gate < tf) :
    (training ++ [tf]).flatMap (fun t => if gate < t then [g t] else []) = [g tf] := by
  rw [List.flatMap_append]
  have quiet : training.flatMap (fun t => if gate < t then [g t] else []) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro t ht
    simp [not_lt.mpr (early t ht)]
  rw [quiet]
  simp [late]

theorem familyQueue_empty {n : ℕ} {u : Fin n → Snapshot 1} (h : ∀ i, (u i).pending = []) :
    familyQueue u = [] := by
  simp [familyQueue, h]

theorem execution_cast {n : ℕ} {θ : Fin n → Parameters} {route : Router n}
    {a a' b b' : Snapshot n} (ha : a = a') (hb : b = b') (E : ParameterExecution θ route a b) :
    ∃ E' : ParameterExecution θ route a' b', ∀ i, E'.emissionTimes i = E.emissionTimes i := by
  subst ha
  subst hb
  exact ⟨E, fun _ => rfl⟩

/-- A cascade of three trained cells, as a routed network. Cells 0 and 1
are trained and read by source pulses. Their read FIREs travel on two
wires to the two ports of cell 2, which is trained by its own source
pulses. In every complete run of the network, cell 2 fires its read
later than 0.239 units after the pulse from cell 0 arrives and no later
than 0.256 units after the pulse from cell 1 arrives. No pulse reaches
cell 2 from the FIRE events of training. -/
theorem trained_cascade {θA θB θC : Fin 1 → Parameters} {ε T rest wA wB : ℝ}
    {sA sB sC : Snapshot 1} {pA₁ pA₂ pB₁ pB₂ pC₁ pC₂ : Port}
    {uA₁ lA₁ uA₂ lA₂ levelA uB₁ lB₁ uB₂ lB₂ levelB uC₁ lC₁ uC₂ lC₂ levelC : ℝ}
    {datesA₁ datesA₂ datesB₁ datesB₂ datesC₁ datesC₂ : List ℝ}
    {middleA readA₁ readA₂ middleB readB₁ readB₂ middleC : ℝ}
    {rA₁ rA₂ rB₁ rB₂ rC₁ rC₂ : ℕ}
    (cellA : TrainedCell θA ε sA pA₁ pA₂ uA₁ lA₁ uA₂ lA₂ levelA datesA₁ datesA₂ middleA
      readA₁ readA₂ rest rA₁ rA₂)
    (cellB : TrainedCell θB ε sB pB₁ pB₂ uB₁ lB₁ uB₂ lB₂ levelB datesB₁ datesB₂ middleB
      readB₁ readB₂ rest rB₁ rB₂)
    (cellC : ∀ ρ₁ ρ₂, readA₁ + 239 / 1000 + wA < ρ₁ → ρ₁ ≤ readA₂ + 32 / 125 + wA →
      readB₁ + 239 / 1000 + wB < ρ₂ → ρ₂ ≤ readB₂ + 32 / 125 + wB →
      TrainedCell θC ε (withReads sC pC₁ pC₂ ρ₁ ρ₂) pC₁ pC₂ uC₁ lC₁ uC₂ lC₂ levelC
        datesC₁ datesC₂ middleC ρ₁ ρ₂ rest rC₁ rC₂)
    (startA : sA.time = T) (startB : sB.time = T) (startC : sC.time = T)
    (wireA : 0 < wA) (wireB : 0 < wB) :
    ∃ (tfA tfB tfC : ℝ) (trainingA trainingB trainingC : List ℝ),
      (readA₁ + 239 / 1000 < tfA ∧ tfA ≤ readA₂ + 32 / 125) ∧
      (readB₁ + 239 / 1000 < tfB ∧ tfB ≤ readB₂ + 32 / 125) ∧
      (tfA + wA + 239 / 1000 < tfC ∧ tfC ≤ tfB + wB + 32 / 125) ∧
      (∃ (u : Snapshot 3) (ref : ParameterExecution (familyParameters ![θA, θB, θC])
        (cascadeRoute readA₁ readB₁ wA wB pC₁ pC₂) (Snapshot.family T ![sA, sB, sC]) u),
        ParameterCompleteThrough ref rest) ∧
      ∀ {u : Snapshot 3} (ex : ParameterExecution (familyParameters ![θA, θB, θC])
        (cascadeRoute readA₁ readB₁ wA wB pC₁ pC₂) (Snapshot.family T ![sA, sB, sC]) u),
        ParameterCompleteThrough ex rest →
        ex.emissionTimes 0 = trainingA ++ [tfA] ∧ ex.emissionTimes 1 = trainingB ++ [tfB] ∧
        ex.emissionTimes 2 = trainingC ++ [tfC] := by
  obtain ⟨uA, tfA, trainingA, cA, afterA, beforeA, reachA, restedA, dateA, pendA, earlyA⟩ :=
    cellA.run_rest
  obtain ⟨uB, tfB, trainingB, cB, afterB, beforeB, reachB, restedB, dateB, pendB, earlyB⟩ :=
    cellB.run_rest
  have cC := cellC (tfA + wA) (tfB + wB) (by linarith) (by linarith) (by linarith) (by linarith)
  obtain ⟨uC, tfC, trainingC, cCn, afterC, beforeC, reachC, restedC, dateC, pendC, _⟩ :=
    cC.run_rest
  let sLocal := withReads sC pC₁ pC₂ (tfA + wA) (tfB + wB)
  let θ : Fin 3 → Fin 1 → Parameters := ![θA, θB, θC]
  let route := cascadeRoute readA₁ readB₁ wA wB pC₁ pC₂
  let s : Fin 3 → Snapshot 1 := ![sA, sB, sLocal]
  let u : Fin 3 → Snapshot 1 := ![uA, uB, uC]
  let dates : Fin 3 → List ℝ := ![trainingA ++ [tfA], trainingB ++ [tfB], trainingC ++ [tfC]]
  let count : Fin 3 → ℕ := ![cA, cB, cCn]
  have reach : ∀ i, Reach (θ i) (s i) (u i) (dates i) (count i) := by
    intro i
    fin_cases i
    · exact reachA
    · exact reachB
    · exact reachC
  have start : ∀ i, (s i).time = T := by
    intro i
    fin_cases i
    · exact startA
    · exact startB
    · exact startC
  have finish : ∀ i, (u i).time = rest := by
    intro i
    fin_cases i
    · exact dateA
    · exact dateB
    · exact dateC
  -- The balance of the queues at the start.
  have sEq : s = Function.update ![sA, sB, sC] 2 sLocal := by
    funext i
    fin_cases i <;> rfl
  obtain ⟨L, R, parts⟩ := familyQueue_split ![sA, sB, sC] 2
  have source := parts sC
  have same : Function.update ![sA, sB, sC] 2 sC = ![sA, sB, sC] := by
    funext i
    fin_cases i <;> rfl
  rw [same] at source
  have h₀ : (dates 0).flatMap (route 0) = [(⟨2, pC₁, tfA + wA⟩ : Delivery 3)] := by
    have r : route 0 = fun t => if readA₁ < t then [(⟨2, pC₁, t + wA⟩ : Delivery 3)] else [] := by
      funext t
      simp [route, cascadeRoute]
    rw [r]
    exact gated_flatMap trainingA tfA readA₁ _ earlyA (by linarith)
  have h₁ : (dates 1).flatMap (route 1) = [(⟨2, pC₂, tfB + wB⟩ : Delivery 3)] := by
    have r : route 1 = fun t => if readB₁ < t then [(⟨2, pC₂, t + wB⟩ : Delivery 3)] else [] := by
      funext t
      simp [route, cascadeRoute]
    rw [r]
    exact gated_flatMap trainingB tfB readB₁ _ earlyB (by linarith)
  have h₂ : (dates 2).flatMap (route 2) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro t _
    simp [route, cascadeRoute]
  have balance : (familyQueue s : Multiset (Delivery 3)) =
      (familyQueue ![sA, sB, sC] : Multiset (Delivery 3)) + promised route dates := by
    unfold promised
    rw [Fin.sum_univ_three, h₀, h₁, h₂, sEq, parts sLocal, source]
    show ((L ++ (sC.pending ++ [(⟨0, pC₁, tfA + wA⟩ : Delivery 1), ⟨0, pC₂, tfB + wB⟩]).map
      (Delivery.inCell 2) ++ R : List (Delivery 3)) : Multiset (Delivery 3)) = _
    simp only [List.map_append, List.map_cons, List.map_nil, Delivery.inCell, Multiset.coe_nil,
      add_zero, ← Multiset.coe_add, ← Multiset.cons_coe, ← Multiset.singleton_add]
    abel
  obtain ⟨P', E, times, final⟩ := routed_execution (by norm_num : 0 < 3) (θ := θ) route
    (cascadeRoute_causal wireA wireB) _ T rest s u dates count (familyQueue ![sA, sB, sC]) rfl
    reach start finish balance
  have empty : ∀ i, (u i).pending = [] := by
    intro i
    fin_cases i
    · exact pendA
    · exact pendB
    · exact pendC
  have hP : P' = [] := by
    rw [familyQueue_empty empty] at final
    exact (Multiset.coe_eq_coe.mp final).eq_nil
  have startEq : Snapshot.familyWith T s (familyQueue ![sA, sB, sC]) =
      Snapshot.family T ![sA, sB, sC] := by
    apply Snapshot.family_congr rfl
    · intro j c; fin_cases j <;> rfl
    · intro j; fin_cases j <;> rfl
    · intro j p; fin_cases j <;> rfl
    · intro j p; fin_cases j <;> rfl
    · rfl
  have endEq : Snapshot.familyWith rest u P' = Snapshot.family rest u := by
    rw [hP]
    exact Snapshot.family_congr rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl) (familyQueue_empty empty).symm
  obtain ⟨E', keep⟩ := execution_cast startEq endEq E
  have times' : ∀ i, E'.emissionTimes i = dates i := fun i => (keep i).trans (times i)
  have complete : ParameterCompleteThrough E' rest :=
    family_complete (θ := θ) (level := ![levelA, levelB, levelC])
      (by
        intro i
        fin_cases i
        · exact cellA.config₁.cell
        · exact cellB.config₁.cell
        · exact cC.config₁.cell)
      (by
        intro i
        fin_cases i
        · exact cellA.fire.1
        · exact cellB.fire.1
        · exact cC.fire.1)
      (by
        intro i
        fin_cases i
        · exact restedA
        · exact restedB
        · exact restedC)
      empty E'
  have box : PhysicalBox (familyParameters θ) ε := by
    refine ⟨cellA.box.1, ?_⟩
    intro i p
    fin_cases i
    · exact cellA.box.2 0 p
    · exact cellB.box.2 0 p
    · exact cC.box.2 0 p
  have bA := cell_threshold_bounds cellA.config₁.cell cellA.fire
  have bB := cell_threshold_bounds cellB.config₁.cell cellB.fire
  have bC := cell_threshold_bounds cC.config₁.cell cC.fire
  have bounds : ParameterThresholdBounds (familyParameters θ) := by
    constructor
    · intro i; fin_cases i; exact bA.fire 0; exact bB.fire 0; exact bC.fire 0
    · intro i; fin_cases i; exact bA.fastEnd 0; exact bB.fastEnd 0; exact bC.fastEnd 0
    · intro i; fin_cases i; exact bA.fastBelowFire 0; exact bB.fastBelowFire 0
      exact bC.fastBelowFire 0
    · intro i; fin_cases i; exact bA.reopen 0; exact bB.reopen 0; exact bC.reopen 0
    · intro i p; fin_cases i; exact bA.mark 0 p; exact bB.mark 0 p; exact bC.mark 0 p
    · intro i p; fin_cases i; exact bA.silent 0 p; exact bB.silent 0 p; exact bC.silent 0 p
    · intro i p; fin_cases i; exact bA.error 0 p; exact bB.error 0 p; exact bC.error 0 p
    · intro i p; fin_cases i; exact bA.auxReady 0 p; exact bB.auxReady 0 p
      exact bC.auxReady 0 p
  have iA := cellA.state.physical
  have iB := cellB.state.physical
  have iC := cC.state.physical
  have birth : ParameterPhysicalInvariant (familyParameters θ)
      (Snapshot.family T ![sA, sB, sC]) := by
    constructor
    · intro i; fin_cases i; exact iA.charge 0; exact iB.charge 0; exact iC.charge 0
    · intro i p; fin_cases i; exact iA.sensor 0 p; exact iB.sensor 0 p; exact iC.sensor 0 p
    · intro i p; fin_cases i; exact iA.gain 0 p; exact iB.gain 0 p; exact iC.gain 0 p
    · intro i; fin_cases i; exact iA.recovery 0; exact iB.recovery 0; exact iC.recovery 0
    · intro i; fin_cases i; exact iA.reserve 0; exact iB.reserve 0; exact iC.reserve 0
  refine ⟨tfA, tfB, tfC, trainingA, trainingB, trainingC, ⟨afterA, beforeA⟩, ⟨afterB, beforeB⟩,
    ⟨afterC, beforeC⟩, ⟨_, E', complete⟩, ?_⟩
  intro w ex done
  exact ⟨(ex.emissionTimes_unique E' box bounds birth done complete 0).trans (times' 0),
    (ex.emissionTimes_unique E' box bounds birth done complete 1).trans (times' 1),
    (ex.emissionTimes_unique E' box bounds birth done complete 2).trans (times' 2)⟩

/-! ### The hypotheses are satisfiable -/

/-- The same trained cell with other read dates. Only the queue, the
spacing before the first read and the final wait depend on them. -/
theorem TrainedCell.reread {θ ε s p₁ p₂ u₁ l₁ u₂ l₂ level dates₁ dates₂ middle read₁ read₂ rest
    r₁ r₂}
    (cell : TrainedCell θ ε s p₁ p₂ u₁ l₁ u₂ l₂ level dates₁ dates₂ middle read₁ read₂ rest r₁ r₂)
    {s' : Snapshot 1} {ρ₁ ρ₂ rest' : ℝ} (hx : s'.x = s.x) (hmain : s'.main = s.main)
    (haux : s'.aux = s.aux) (hraw : s'.raw = s.raw) (htime : s'.time = s.time)
    (queue : s'.pending = (⟨0, p₁, s'.time⟩ : Delivery 1) ::
      (dates₁.map (fun D => (⟨0, p₁, D⟩ : Delivery 1)) ++
        (⟨0, p₂, middle⟩ : Delivery 1) ::
          (dates₂.map (fun D => (⟨0, p₂, D⟩ : Delivery 1)) ++
            [(⟨0, p₁, ρ₁⟩ : Delivery 1), (⟨0, p₂, ρ₂⟩ : Delivery 1)])))
    (spaced₂ : Spaced middle dates₂ ρ₁) (order : ρ₁ ≤ ρ₂ ∧ ρ₂ ≤ ρ₁ + 1 / 4)
    (wait : ρ₁ + 22 ≤ rest') :
    TrainedCell θ ε s' p₁ p₂ u₁ l₁ u₂ l₂ level dates₁ dates₂ middle ρ₁ ρ₂ rest' r₁ r₂ where
  box := cell.box
  distinct := cell.distinct
  config₁ := cell.config₁
  config₂ := cell.config₂
  fire := cell.fire
  entry₁ := cell.entry₁
  exit₁ := cell.exit₁
  entry₂ := cell.entry₂
  exit₂ := cell.exit₂
  dose₁ := cell.dose₁
  dose₂ := cell.dose₂
  state := {
    main := by rw [hmain]; exact cell.state.main
    aux := fun q => by rw [haux]; exact cell.state.aux q
    raw := fun q => by rw [hraw]; exact cell.state.raw q
    charge := by rw [hx]; exact cell.state.charge
    sensors := fun q => by rw [hx]; exact cell.state.sensors q
    recovery := by rw [hx]; exact cell.state.recovery
    energy := by rw [hx]; exact cell.state.energy
    caps := fun q => by rw [hx]; exact cell.state.caps q }
  recovery := by rw [hx]; exact cell.recovery
  queue := queue
  spaced₁ := by rw [htime]; exact cell.spaced₁
  spaced₂ := spaced₂
  order := order
  wait := wait
  below₁ := by rw [hx]; exact cell.below₁
  below₂ := by rw [hx]; exact cell.below₂
  reach₁ := by rw [hx]; exact cell.reach₁
  reach₂ := by rw [hx]; exact cell.reach₂
  enough₁ := cell.enough₁
  enough₂ := cell.enough₂

/-- The explicit cell with its two pulse trains and no read pulse. -/
noncomputable def witnessSource : Snapshot 1 :=
  { witnessStart with
    pending := (⟨0, 0, 0⟩ : Delivery 1) ::
      ((train 0 21).map (fun D => (⟨0, 0, D⟩ : Delivery 1)) ++
        (⟨0, 1, 484⟩ : Delivery 1) :: (train 484 21).map (fun D => (⟨0, 1, D⟩ : Delivery 1))) }

/-- A cascade of three copies of the explicit cell satisfies the
hypotheses. The two first cells are read at date 968. Their read FIREs
reach the third cell after 1 and 11/10 units. In every complete run of
the routed network, the third cell fires its read between 969.478 and
969.612, after the FIRE events of its own training. -/
theorem trained_cascade_witness :
    ∃ (tfC : ℝ) (trainingC : List ℝ),
      (969478 / 1000 < tfC ∧ tfC ≤ 969612 / 1000) ∧
      (∃ (u : Snapshot 3) (ref : ParameterExecution
        (familyParameters ![fun _ => witnessParameters, fun _ => witnessParameters,
          fun _ => witnessParameters])
        (cascadeRoute 968 968 1 (11 / 10) 0 1)
        (Snapshot.family 0 ![witnessStart, witnessStart, witnessSource]) u),
        ParameterCompleteThrough ref 1000) ∧
      ∀ {u : Snapshot 3} (ex : ParameterExecution
        (familyParameters ![fun _ => witnessParameters, fun _ => witnessParameters,
          fun _ => witnessParameters])
        (cascadeRoute 968 968 1 (11 / 10) 0 1)
        (Snapshot.family 0 ![witnessStart, witnessStart, witnessSource]) u),
        ParameterCompleteThrough ex 1000 → ex.emissionTimes 2 = trainingC ++ [tfC] := by
  have first : TrainedCell (fun _ => witnessParameters) (1 / 10) witnessStart 0 1
      (2 / 25) (59 / 800) (2 / 25) (59 / 800) 1 (train 0 21) (train 484 21) 484 968 968 1000
      10 10 :=
    trainedCell_witness.reread rfl rfl rfl rfl rfl rfl (train_spaced 484 21 968 (by norm_num))
      ⟨le_rfl, by norm_num⟩ (by norm_num)
  obtain ⟨tfA, tfB, tfC, _, _, trainingC, ⟨afterA, beforeA⟩, ⟨afterB, beforeB⟩, ⟨afterC, beforeC⟩,
      ref, all⟩ :=
    trained_cascade (wA := 1) (wB := 11 / 10) (sC := witnessSource) (T := 0) first first
      (fun ρ₁ ρ₂ lo₁ hi₁ lo₂ hi₂ =>
        trainedCell_witness.reread (s' := withReads witnessSource 0 1 ρ₁ ρ₂) rfl rfl rfl rfl rfl
          (by
            simp [withReads, witnessSource]
            rfl)
          (train_spaced 484 21 ρ₁ (by norm_num; linarith))
          ⟨by linarith, by linarith⟩ (by linarith))
      rfl rfl rfl (by norm_num) (by norm_num)
  exact ⟨tfC, trainingC, ⟨by linarith, by linarith⟩, ref, fun ex done => (all ex done).2.2⟩

end RecursiveLearning.Native
