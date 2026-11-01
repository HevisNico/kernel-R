import KernelR.HybridFirstReceiverFire
import KernelR.HybridFirstReceiverFastEnd

namespace KernelR.Hybrid

namespace FirstReceiverFire
variable {θ born fresh newborn forward backward} {c : ConstructedBirthPreparation θ born}
  {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
  {r : FirstWiredArrival b} {s : FirstInterleavedPair r} {w : SecondWiredArrival s} (f : FirstReceiverFire w)

/-- The new B emission extends the constructed original-birth witness. -/
noncomputable def staged : StagedExecution θ fresh (fun _ _ => [])
    (reciprocalEntryRouter forward backward) born f.final :=
  { w.staged with after := w.staged.after.append f.execution }

theorem staged_complete : CompleteThrough f.staged.after f.final.time := f.complete

theorem date_bounds (hdelay : ∀ t, (3 / 10 : ℝ) ≤ forward t ∧ forward t ≤ 2 / 5) :
    (169 + 1 / 10 : ℝ) < f.final.time ∧ f.final.time < 170 + 1 / 5 := by
  constructor <;> linarith [f.early,f.deadline,(w.date_bounds hdelay).1,(w.date_bounds hdelay).2]

/-- Both A outputs and the first B output are read from the actual post-birth
execution. In particular the closed reverse contact does not erase B's FIRE. -/
theorem staged_emissions : f.staged.after.ledger.emissions =
    [(0,r.fire.final.time),(0,w.fire.final.time),(1,f.final.time)] := by
  change (((b.staged.after.append r.execution).append s.execution).append
    w.execution |>.append f.execution).ledger.emissions = _
  simp only [Execution.emissions_append,r.emissions,s.emissions,w.emissions,f.emissions]
  have hb : b.staged.after.ledger.emissions = [] := by
    change (Execution.cons (.jump b.arrival) (.nil _)).ledger.emissions = []
    simp only [Execution.ledger,Move.ledger,b.arrival_emissions,Ledger.add,Ledger.zero,List.append_nil]
  rw [hb]
  rfl

theorem staged_deliveries : f.staged.after.deliveries =
    [⟨0,0,160⟩,⟨1,1,r.final.time⟩,⟨0,0,168⟩,⟨1,1,w.final.time⟩] := by
  change (((b.staged.after.append r.execution).append s.execution).append
    w.execution |>.append f.execution).deliveries = _
  simp only [Execution.deliveries_append,r.deliveries,s.deliveries,w.deliveries,f.deliveries]
  have hb : b.staged.after.deliveries = [⟨0,0,160⟩] := by
    change (Execution.cons (.jump b.arrival) (.nil _)).deliveries = _
    simp only [Execution.deliveries,Move.deliveries,b.arrival_deliveries,List.append_nil]
  rw [hb]
  rfl

end FirstReceiverFire

namespace FirstReceiverFastEnd
variable {θ born fresh newborn forward backward} {c : ConstructedBirthPreparation θ born}
  {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
  {r : FirstWiredArrival b} {s : FirstInterleavedPair r} {w : SecondWiredArrival s}
  {f : FirstReceiverFire w} (g : FirstReceiverFastEnd f)

noncomputable def staged : StagedExecution θ fresh (fun _ _ => [])
    (reciprocalEntryRouter forward backward) born g.final :=
  { f.staged with after := f.staged.after.append g.execution }

theorem staged_complete : CompleteThrough g.staged.after g.final.time := g.complete

theorem date_bounds (hdelay : ∀ t, (3 / 10 : ℝ) ≤ forward t ∧ forward t ≤ 2 / 5) :
    (170 + 1 / 10 : ℝ) < g.final.time ∧ g.final.time < 171 + 1 / 5 := by
  rw [g.date]
  constructor <;> linarith [(f.date_bounds hdelay).1,(f.date_bounds hdelay).2]

theorem staged_emissions : g.staged.after.ledger.emissions =
    [(0,r.fire.final.time),(0,w.fire.final.time),(1,f.final.time)] := by
  change (f.staged.after.append g.execution).ledger.emissions = _
  rw [Execution.emissions_append,f.staged_emissions,g.emissions,List.append_nil]

theorem staged_deliveries : g.staged.after.deliveries =
    [⟨0,0,160⟩,⟨1,1,r.final.time⟩,⟨0,0,168⟩,⟨1,1,w.final.time⟩] := by
  change (f.staged.after.append g.execution).deliveries = _
  rw [Execution.deliveries_append,f.staged_deliveries,g.deliveries,List.append_nil]

end FirstReceiverFastEnd

/-- No reaching execution, desired response count or firing date is supplied:
the first B output is constructed from the original A birth and a genuine B birth. -/
theorem birth_protocol_first_receiver_fire_exists {θ born fresh ε}
    (hborn : @BirthState 1 born) (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (ha : ∀ p, born.aux 0 p = .ready)
    (hqueue : born.pending = sourceTrain 0 0 0 8 16 ++ sourceTrain 0 0 160 8 16)
    (newborn : Newborn) (forward backward : ℝ → ℝ)
    (hdelay : ∀ t, (3 / 10 : ℝ) ≤ forward t ∧ forward t ≤ 2 / 5) :
    ∃ c : ConstructedBirthPreparation θ born,
      ∃ b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources,
        ∃ r : FirstWiredArrival b, ∃ s : FirstInterleavedPair r, ∃ w : SecondWiredArrival s,
          ∃ f : FirstReceiverFire w,
            CompleteThrough f.staged.after f.final.time ∧ f.final.pending.length = 46 := by
  obtain ⟨c,b,r,s,w,_,_⟩ := birth_protocol_second_wired_arrival_exists hborn hb ha hqueue
    newborn forward backward hdelay
  obtain ⟨f⟩ := first_receiver_fire_exists hb w hdelay
  exact ⟨c,b,r,s,w,f,f.staged_complete,f.pending_length⟩

/-- The same birth witness also reaches B's real FAST exit, without adding
an output or source occurrence and with its RAW physically expired. -/
theorem birth_protocol_first_receiver_fast_end_exists {θ born fresh ε}
    (hborn : @BirthState 1 born) (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (ha : ∀ p, born.aux 0 p = .ready)
    (hqueue : born.pending = sourceTrain 0 0 0 8 16 ++ sourceTrain 0 0 160 8 16)
    (newborn : Newborn) (forward backward : ℝ → ℝ)
    (hdelay : ∀ t, (3 / 10 : ℝ) ≤ forward t ∧ forward t ≤ 2 / 5) :
    ∃ c : ConstructedBirthPreparation θ born,
      ∃ b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources,
        ∃ r : FirstWiredArrival b, ∃ s : FirstInterleavedPair r, ∃ w : SecondWiredArrival s,
          ∃ f : FirstReceiverFire w, ∃ g : FirstReceiverFastEnd f,
            CompleteThrough g.staged.after g.final.time ∧ g.final.pending.length = 46 := by
  obtain ⟨c,b,r,s,w,f,_,_⟩ := birth_protocol_first_receiver_fire_exists hborn hb ha hqueue
    newborn forward backward hdelay
  obtain ⟨g⟩ := first_receiver_fast_end_exists hb f hdelay
  exact ⟨c,b,r,s,w,f,g,g.staged_complete,g.pending_length⟩

end KernelR.Hybrid
