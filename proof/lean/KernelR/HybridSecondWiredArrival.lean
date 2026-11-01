import KernelR.HybridSecondSenderFire
import KernelR.HybridQuietWireArrival
import KernelR.HybridLearnedFastEnd
import KernelR.HybridMidGainSchedule

namespace KernelR.Hybrid

structure SecondWiredArrival {θ born fresh newborn forward backward}
    {c : ConstructedBirthPreparation θ born}
    {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
    {r : FirstWiredArrival b} (s : FirstInterleavedPair r) where
  fire : SecondSenderFire s
  fast : LearnedFastEnd fire.firelocal
  cut : fast.execution.BeforeFlowCut (fire.final.time + forward fire.final.time)
  receipt : QuietWireArrival θ (fun _ : Fin 1 => fresh) (reciprocalEntryRouter forward backward)
    fire.firelocal.final (quietAt s.localB fire.final.time) cut.state firstInterleavedPending 1
  source_eq : fire.final = fire.firelocal.final.product (quietAt s.localB fire.final.time)
    (firstInterleavedPending ++ [⟨1,1,cut.state.time⟩])
  receipt_complete : CompleteThrough receipt.execution (fire.final.time + forward fire.final.time)

noncomputable def SecondWiredArrival.final {θ born fresh newborn forward backward}
    {c : ConstructedBirthPreparation θ born}
    {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
    {r : FirstWiredArrival b} {s : FirstInterleavedPair r} (w : SecondWiredArrival s) : Snapshot 2 :=
  w.receipt.final

noncomputable def SecondWiredArrival.execution {θ born fresh newborn forward backward}
    {c : ConstructedBirthPreparation θ born}
    {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
    {r : FirstWiredArrival b} {s : FirstInterleavedPair r} (w : SecondWiredArrival s) :
    Execution (extendParameters θ fresh) (reciprocalEntryRouter forward backward) s.final w.final :=
  w.fire.execution.append (w.receipt.execution.cast_source w.source_eq)

noncomputable def SecondWiredArrival.staged {θ born fresh newborn forward backward}
    {c : ConstructedBirthPreparation θ born}
    {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
    {r : FirstWiredArrival b} {s : FirstInterleavedPair r} (w : SecondWiredArrival s) :
    StagedExecution θ fresh (fun _ _ => []) (reciprocalEntryRouter forward backward) born w.final :=
  { s.staged with after := s.staged.after.append w.execution }

/-- The next received input follows another real FIRE. Equality of the
sender's own response roots supplies its timing; it is not a calendar premise. -/
theorem second_wired_arrival_exists {θ born fresh ε newborn forward backward}
    {c : ConstructedBirthPreparation θ born}
    {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
    {r : FirstWiredArrival b}
    (hb : @PhysicalBox 2 (extendParameters θ fresh) ε) (s : FirstInterleavedPair r)
    (hdelay : ∀ t, (3 / 10 : ℝ) ≤ forward t ∧ forward t ≤ 2 / 5) :
    Nonempty (SecondWiredArrival s) := by
  obtain ⟨f⟩ := second_sender_fire_exists hb s hdelay
  have hclock : f.firelocal.final.time = f.final.time :=
    (congrArg Snapshot.time f.product_final).symm
  have hother : ∀ p, p ≠ 0 → s.localA.raw 0 p = none := fun p hp => s.raw_other_a p hp
  obtain ⟨fast⟩ := f.firelocal.learned_fast_end_exists hb.extend_old (s.localA_ready 0)
    (s.localA_gain hb.extend_old).2 hother (by
      intro d hd
      change d ∈ ([] : List (Delivery 1)) at hd
      contradiction)
  let H := f.final.time + forward f.final.time
  obtain ⟨cut⟩ := fast.execution.before_flow_cut_exists H
    (by rw [hclock]; dsimp [H]; linarith [(hdelay f.final.time).1])
    (by rw [fast.date,hclock]; dsimp [H]; linarith [(hdelay f.final.time).2])
  have he : cut.cut.ledger.emissions = [] := by
    have h := cut.emissions.symm.trans fast.emissions
    exact (List.append_eq_nil_iff.mp h).1
  have hd : cut.cut.deliveries = [] := by
    have h := cut.deliveries.symm.trans fast.deliveries
    exact (List.append_eq_nil_iff.mp h).1
  have hBfinish : r.final.time + 15 / 2 ≤ f.final.time := by
    rw [r.date,f.firing_gap]
    linarith [(hdelay r.fire.final.time).2]
  have hBready := s.receiver.quiet_after_cut_ready hb hdelay hBfinish
  have hQ : ∀ d ∈ firstInterleavedPending, cut.state.time < d.due := by
    intro d hd
    rw [cut.date]
    dsimp [H]
    linarith [FirstInterleavedPair.queue_future d hd,f.deadline,(hdelay f.final.time).2]
  have hsource : f.final = f.firelocal.final.product (quietAt s.localB f.final.time)
      (firstInterleavedPending ++ [⟨1,1,cut.state.time⟩]) := by
    have h := f.product_final
    rw [f.protocol_route] at h
    rw [cut.date]
    exact h
  have hf : PhysicalInvariant (extendParameters θ fresh)
      (f.firelocal.final.product (quietAt s.localB f.final.time)
        (firstInterleavedPending ++ [⟨1,1,cut.state.time⟩])) := by
    rw [← hsource]
    exact f.physical
  have hv : RawValid (f.firelocal.final.product (quietAt s.localB f.final.time)
      (firstInterleavedPending ++ [⟨1,1,cut.state.time⟩])) := by
    rw [← hsource]
    exact f.raw_valid
  obtain ⟨receipt⟩ := quiet_wire_arrival_exists (route := reciprocalEntryRouter forward backward)
    (θB := fun _ : Fin 1 => fresh) hb cut.cut he hd (quietAt s.localB f.final.time)
    (by change f.firelocal.final.time = f.final.time; exact hclock)
    hBready (fun p => s.receiver.cut_raw_none hdelay p) firstInterleavedPending 1
    (fun d hd => (hQ d hd).le) hf hv
  have hc := receipt.complete_of_next cut.flow hQ
  exact ⟨⟨f,fast,cut,receipt,hsource,by simpa only [cut.date] using hc⟩⟩

namespace SecondWiredArrival
variable {θ born fresh newborn forward backward} {c : ConstructedBirthPreparation θ born}
  {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
  {r : FirstWiredArrival b} {s : FirstInterleavedPair r} (w : SecondWiredArrival s)

theorem date : w.final.time = w.fire.final.time + forward w.fire.final.time :=
  w.receipt.date.trans w.cut.date

theorem date_bounds (hdelay : ∀ t, (3 / 10 : ℝ) ≤ forward t ∧ forward t ≤ 2 / 5) :
    (168 + 7 / 10 : ℝ) < w.final.time ∧ w.final.time < 168 + 13 / 10 := by
  rw [w.date]
  constructor <;> linarith [w.fire.early,w.fire.deadline,(hdelay w.fire.final.time).1,
    (hdelay w.fire.final.time).2]

theorem received_gap (hdelay : ∀ t, (3 / 10 : ℝ) ≤ forward t ∧ forward t ≤ 2 / 5) :
    (79 / 10 : ℝ) ≤ w.final.time - r.final.time ∧ w.final.time - r.final.time ≤ 81 / 10 := by
  rw [w.date]
  exact w.fire.received_gap hdelay

theorem pending : w.final.pending = firstInterleavedPending := w.receipt.pending

theorem pending_length : w.final.pending.length = 46 := by
  rw [w.pending]
  simp [firstInterleavedPending,constructedBBirthSources,sourceTrain]

theorem receiver_ready : ReadyCoordinates w.final 1 := w.receipt.receiver_ready

theorem receiver_gain_target {ε} (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (hdelay : ∀ t, (3 / 10 : ℝ) ≤ forward t ∧ forward t ≤ 2 / 5) :
    w.final.x 1 (.z 1) = newborn.x (.z 1) + 3 / 5 := by
  change w.receipt.final.x 1 (.z 1) = _
  rw [w.receipt.receiver_values]
  change s.receiver.cut168.state.x 0 (.z 1) = _
  rw [s.receiver.cut_gain_target hb hdelay]
  change r.final.x 1 (.z 1) + 3 / 5 = _
  rw [r.receiver_gain]

theorem receiver_gain_bounds {ε} (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (hdelay : ∀ t, (3 / 10 : ℝ) ≤ forward t ∧ forward t ≤ 2 / 5) :
    9 / 5 ≤ Real.exp (w.final.x 1 (.z 1)) ∧ Real.exp (w.final.x 1 (.z 1)) ≤ 11 / 5 := by
  have hz := newborn.gain (1 : Port)
  simp only [nominalGain,ite_true] at hz
  apply fast_learned_gain_sharp_bounds
  · rw [w.receiver_gain_target hb hdelay]
    linarith [hz.1]
  · rw [w.receiver_gain_target hb hdelay]
    linarith [hz.2]

theorem receiver_recovery : w.final.x 1 .b = newborn.x .b := by
  change w.receipt.final.x 1 .b = _
  rw [w.receipt.receiver_values]
  change s.receiver.cut168.state.x 0 .b = _
  rw [s.receiver.cut_recovery]
  exact r.receiver_recovery

theorem raw_receiver : w.final.raw 1 1 = some w.final.time := by
  change w.receipt.final.raw 1 1 = some w.receipt.final.time
  rw [w.receipt.date]
  exact w.receipt.raw_active

theorem raw_receiver_other (p : Port) (hp : p ≠ 1) : w.final.raw 1 p = none :=
  w.receipt.raw_other p hp

theorem emissions : w.execution.ledger.emissions = [(0,w.fire.final.time)] := by
  change (w.fire.execution.append (w.receipt.execution.cast_source w.source_eq)).ledger.emissions = _
  rw [Execution.emissions_append,w.receipt.execution.cast_source_ledger w.source_eq,
    w.fire.emissions,w.receipt.emissions,List.append_nil]

theorem deliveries : w.execution.deliveries = [⟨1,1,w.final.time⟩] := by
  change (w.fire.execution.append (w.receipt.execution.cast_source w.source_eq)).deliveries =
    [⟨1,1,w.receipt.final.time⟩]
  rw [Execution.deliveries_append,w.receipt.execution.cast_source_deliveries w.source_eq,
    w.fire.deliveries,w.receipt.deliveries,List.nil_append,w.receipt.date]

theorem complete : CompleteThrough w.execution w.final.time := by
  rw [w.date]
  exact w.receipt_complete

theorem staged_complete : CompleteThrough w.staged.after w.final.time := w.complete

end SecondWiredArrival

theorem birth_protocol_second_wired_arrival_exists {θ born fresh ε}
    (hborn : @BirthState 1 born) (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (ha : ∀ p, born.aux 0 p = .ready)
    (hqueue : born.pending = sourceTrain 0 0 0 8 16 ++ sourceTrain 0 0 160 8 16)
    (newborn : Newborn) (forward backward : ℝ → ℝ)
    (hdelay : ∀ t, (3 / 10 : ℝ) ≤ forward t ∧ forward t ≤ 2 / 5) :
    ∃ c : ConstructedBirthPreparation θ born,
      ∃ b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources,
        ∃ r : FirstWiredArrival b, ∃ s : FirstInterleavedPair r, ∃ w : SecondWiredArrival s,
          CompleteThrough w.staged.after w.final.time ∧ w.final.pending.length = 46 := by
  obtain ⟨c,b,r,s,_,_⟩ := birth_protocol_first_interleaved_pair_exists hborn hb ha hqueue newborn forward backward hdelay
  obtain ⟨w⟩ := second_wired_arrival_exists hb s hdelay
  exact ⟨c,b,r,s,w,w.staged_complete,w.pending_length⟩

end KernelR.Hybrid
