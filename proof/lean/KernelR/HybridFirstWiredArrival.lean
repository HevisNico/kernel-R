import KernelR.HybridTwoCellFirstFire
import KernelR.HybridPrefixBeforeFlow
import KernelR.HybridQuietWireArrival
import KernelR.HybridLearnedFastEnd

namespace KernelR.Hybrid

structure FirstWiredArrival {θ born fresh newborn forward backward}
    {c : ConstructedBirthPreparation θ born}
    (b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources) where
  fire : TwoCellFirstFire b
  fast : LearnedFastEnd fire.firelocal
  cut : fast.execution.BeforeFlowCut (fire.final.time + forward fire.final.time)
  receipt : QuietWireArrival θ (fun _ : Fin 1 => fresh) (reciprocalEntryRouter forward backward)
    fire.firelocal.final (quietAt b.localB fire.final.time) cut.state constructedBBirthQueue 1
  source_eq : fire.final = fire.firelocal.final.product (quietAt b.localB fire.final.time)
    (constructedBBirthQueue ++ [⟨1,1,cut.state.time⟩])
  receipt_complete : CompleteThrough receipt.execution (fire.final.time + forward fire.final.time)

noncomputable def FirstWiredArrival.final {θ born fresh newborn forward backward}
    {c : ConstructedBirthPreparation θ born}
    {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
    (r : FirstWiredArrival b) : Snapshot 2 := r.receipt.final

noncomputable def FirstWiredArrival.receiptTrace {θ born fresh newborn forward backward}
    {c : ConstructedBirthPreparation θ born}
    {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
    (r : FirstWiredArrival b) : Execution (extendParameters θ fresh)
      (reciprocalEntryRouter forward backward) r.fire.final r.final :=
  r.receipt.execution.cast_source r.source_eq

noncomputable def FirstWiredArrival.execution {θ born fresh newborn forward backward}
    {c : ConstructedBirthPreparation θ born}
    {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
    (r : FirstWiredArrival b) : Execution (extendParameters θ fresh)
      (reciprocalEntryRouter forward backward) b.final r.final :=
  r.fire.execution.append r.receiptTrace

noncomputable def FirstWiredArrival.staged {θ born fresh newborn forward backward}
    {c : ConstructedBirthPreparation θ born}
    {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
    (r : FirstWiredArrival b) : StagedExecution θ fresh (fun _ _ => [])
      (reciprocalEntryRouter forward backward) born r.final :=
  { b.staged with after := b.staged.after.append r.execution }

/-- Build the wire's real delivery after its real issuing FIRE, using the
actual local sender continuation and the newborn's quiet trajectory. -/
theorem first_wired_arrival_exists {θ born fresh ε newborn forward backward}
    {c : ConstructedBirthPreparation θ born}
    (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources)
    (hdelay : ∀ t, (3 / 10 : ℝ) ≤ forward t ∧ forward t ≤ 2 / 5) :
    Nonempty (FirstWiredArrival b) := by
  obtain ⟨f⟩ := two_cell_first_fire_exists hb b
  have hclock : f.firelocal.final.time = f.final.time :=
    (congrArg Snapshot.time f.product_final).symm
  have hother : ∀ p, p ≠ 0 → b.localA.raw 0 p = none :=
    fun p hp => b.raw_other 0 p (Or.inr hp)
  have hlocal_future : ∀ d ∈ b.localA.pending, b.localA.time + 8 ≤ d.due := by
    intro d hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    change b.final.time + 8 ≤ 168 + 8 * (k.val : ℝ)
    rw [b.date]
    nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  obtain ⟨fast⟩ := f.firelocal.learned_fast_end_exists hb.extend_old (b.localA_ready 0)
    (b.localA_gain hb.extend_old).2 hother hlocal_future
  let H := f.final.time + forward f.final.time
  obtain ⟨cut⟩ := fast.execution.before_flow_cut_exists H
    (by rw [hclock]; dsimp [H]; linarith [(hdelay f.final.time).1])
    (by rw [fast.date,hclock]; dsimp [H]; linarith [(hdelay f.final.time).2])
  have he : cut.cut.ledger.emissions = [] := by
    have h : cut.cut.ledger.emissions ++ cut.rest.ledger.emissions = [] :=
      cut.emissions.symm.trans fast.emissions
    cases hm : cut.cut.ledger.emissions with
    | nil => rfl
    | cons a as => simp [hm] at h
  have hd : cut.cut.deliveries = [] := by
    have h : cut.cut.deliveries ++ cut.rest.deliveries = [] :=
      cut.deliveries.symm.trans fast.deliveries
    cases hm : cut.cut.deliveries with
    | nil => rfl
    | cons a as => simp [hm] at h
  have hBtime : b.localB.time ≤ f.final.time := by
    change b.final.time ≤ f.final.time
    rw [b.date]
    linarith [f.early]
  have hBready := quietAt_ready_coordinates b.localB 0 b.localB_ready hBtime
  have hQ : ∀ d ∈ constructedBBirthQueue, cut.state.time < d.due := by
    intro d hd
    rw [cut.date]
    dsimp [H]
    linarith [ConstructedBBirth.queue_future d hd,f.deadline,(hdelay f.final.time).2]
  have hsource : f.final = f.firelocal.final.product (quietAt b.localB f.final.time)
      (constructedBBirthQueue ++ [⟨1,1,cut.state.time⟩]) := by
    have h := f.product_final
    rw [f.protocol_route] at h
    rw [cut.date]
    exact h
  have hphysical : PhysicalInvariant (extendParameters θ fresh)
      (f.firelocal.final.product (quietAt b.localB f.final.time)
        (constructedBBirthQueue ++ [⟨1,1,cut.state.time⟩])) := by
    rw [← hsource]
    exact f.physical
  have hrawvalid : RawValid (f.firelocal.final.product (quietAt b.localB f.final.time)
      (constructedBBirthQueue ++ [⟨1,1,cut.state.time⟩])) := by
    rw [← hsource]
    exact f.raw_valid
  obtain ⟨receipt⟩ := quiet_wire_arrival_exists (route := reciprocalEntryRouter forward backward)
    (θB := fun _ : Fin 1 => fresh) hb cut.cut he hd (quietAt b.localB f.final.time)
    (by change f.firelocal.final.time = f.final.time; exact hclock)
    hBready (fun p => b.localB_raw_none p) constructedBBirthQueue 1
    (fun d hd => (hQ d hd).le) hphysical hrawvalid
  have hc := receipt.complete_of_next cut.flow hQ
  exact ⟨⟨f,fast,cut,receipt,hsource,by simpa only [cut.date] using hc⟩⟩

namespace FirstWiredArrival
variable {θ born fresh newborn forward backward} {c : ConstructedBirthPreparation θ born}
  {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
  (r : FirstWiredArrival b)

theorem date : r.final.time = r.fire.final.time + forward r.fire.final.time :=
  r.receipt.date.trans r.cut.date

theorem date_bounds (hdelay : ∀ t, (3 / 10 : ℝ) ≤ forward t ∧ forward t ≤ 2 / 5) :
    (160 + 7 / 10 : ℝ) < r.final.time ∧ r.final.time < 160 + 13 / 10 := by
  rw [r.date]
  constructor <;> linarith [r.fire.early,r.fire.deadline,(hdelay r.fire.final.time).1,
    (hdelay r.fire.final.time).2]

theorem pending : r.final.pending = constructedBBirthQueue := r.receipt.pending

theorem pending_length : r.final.pending.length = 47 := by
  rw [r.pending]
  simp [constructedBBirthQueue,constructedBBirthSources,sourceTrain]

theorem raw_receiver : r.final.raw 1 1 = some r.final.time := by
  change r.receipt.final.raw 1 1 = some r.receipt.final.time
  rw [r.receipt.date]
  exact r.receipt.raw_active

theorem receiver_gain (p : Port) : r.final.x 1 (.z p) = newborn.x (.z p) := by
  change r.receipt.final.x 1 (.z p) = newborn.x (.z p)
  rw [r.receipt.receiver_values]
  change b.final.x 1 (.z p) = newborn.x (.z p)
  exact congrFun b.b_coordinates (.z p)

theorem receiver_recovery : r.final.x 1 .b = newborn.x .b := by
  change r.receipt.final.x 1 .b = newborn.x .b
  rw [r.receipt.receiver_values]
  change b.final.x 1 .b = newborn.x .b
  exact congrFun b.b_coordinates .b

theorem receiver_charge : 1 / 10 - 1 / 100000 ≤ r.final.x 1 .q ∧
    r.final.x 1 .q ≤ 1 / 10 + 1 / 100000 := by
  have hb : 1 / 10 - 1 / 100000 ≤ b.localB.x 0 .q ∧
      b.localB.x 0 .q ≤ 1 / 10 + 1 / 100000 := by
    change 1 / 10 - 1 / 100000 ≤ b.final.x 1 .q ∧ b.final.x 1 .q ≤ 1 / 10 + 1 / 100000
    rw [b.b_coordinates]
    exact newborn.charge
  have hclock : r.fire.firelocal.final.time = r.fire.final.time :=
    (congrArg Snapshot.time r.fire.product_final).symm
  have hmono := r.cut.cut.time_monotone
  rw [hclock] at hmono
  have ht : b.localB.time ≤ r.cut.state.time := by
    change b.final.time ≤ r.cut.state.time
    rw [b.date]
    linarith [r.fire.early]
  change 1 / 10 - 1 / 100000 ≤ r.receipt.final.x 1 .q ∧
    r.receipt.final.x 1 .q ≤ 1 / 10 + 1 / 100000
  rw [r.receipt.receiver_values]
  change (quietAt (quietAt b.localB r.fire.final.time) r.cut.state.time).x 0 .q ∈
    Set.Icc (1 / 10 - 1 / 100000) (1 / 10 + 1 / 100000)
  rw [quietAt_quietAt]
  exact relax_mem_Icc (by norm_num) ht hb (by constructor <;> norm_num)

theorem emissions : r.execution.ledger.emissions = [(0,r.fire.final.time)] := by
  change (r.fire.execution.append (r.receipt.execution.cast_source r.source_eq)).ledger.emissions = _
  rw [Execution.emissions_append,r.receipt.execution.cast_source_ledger r.source_eq,
    r.fire.emissions,r.receipt.emissions,List.append_nil]

theorem deliveries : r.execution.deliveries = [⟨1,1,r.final.time⟩] := by
  change (r.fire.execution.append (r.receipt.execution.cast_source r.source_eq)).deliveries =
    [⟨1,1,r.receipt.final.time⟩]
  rw [Execution.deliveries_append,r.receipt.execution.cast_source_deliveries r.source_eq,
    r.fire.deliveries,r.receipt.deliveries,List.nil_append]
  rw [r.receipt.date]

theorem complete : CompleteThrough r.execution r.final.time := by
  rw [r.date]
  exact r.receipt_complete

theorem staged_complete : CompleteThrough r.staged.after r.final.time := r.complete

end FirstWiredArrival

/-- Original-birth existence reaches the first actual contact delivery. Its
issuing emission and physical delay are constructed inside this witness. -/
theorem birth_protocol_first_wired_arrival_exists {θ born fresh ε}
    (hborn : @BirthState 1 born) (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (ha : ∀ p, born.aux 0 p = .ready)
    (hqueue : born.pending = sourceTrain 0 0 0 8 16 ++ sourceTrain 0 0 160 8 16)
    (newborn : Newborn) (forward backward : ℝ → ℝ)
    (hdelay : ∀ t, (3 / 10 : ℝ) ≤ forward t ∧ forward t ≤ 2 / 5) :
    ∃ c : ConstructedBirthPreparation θ born,
      ∃ b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources,
        ∃ r : FirstWiredArrival b, CompleteThrough r.staged.after r.final.time ∧ r.final.pending.length = 47 := by
  obtain ⟨c,⟨b⟩⟩ := birth_protocol_b_birth_exists hborn hb ha hqueue newborn forward backward
  obtain ⟨r⟩ := first_wired_arrival_exists hb b hdelay
  exact ⟨c,b,r,r.staged_complete,r.pending_length⟩

end KernelR.Hybrid
