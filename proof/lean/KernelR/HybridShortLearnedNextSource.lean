import KernelR.HybridShortLearnedCycle
import KernelR.HybridContactTransversalityFrame

/-! A genuine local learned cycle can serve a next source after6.9, without
the older cycle constructor's7.75 queue-spacing premise. Construct the same
finite path first, then frame its actual future queue and consume its head.
Global routed wire issuance remains a separate reconstruction obligation. -/
namespace KernelR.Hybrid

/-- Construction metadata only. The final execution below starts at the
original snapshot with its complete actual source queue. -/
def shortLearnedLocalState (s : Snapshot 1) : Snapshot 1 := {s with pending := []}

structure ShortLearnedNextSource (θ : Fin 1 → Parameters) (s : Snapshot 1)
    (p : Port) (H : ℝ) (later : List (Delivery 1)) where
  cycle : ShortLearnedCycle θ (shortLearnedLocalState s) p
  quietFlow : Flow θ cycle.returned.final (quietAt cycle.returned.final H)
  quiet : Execution θ (fun _ _ => []) cycle.returned.final (quietAt cycle.returned.final H)
  quiet_reconstruct : quiet = .cons (.flow quietFlow) (.nil _)
  offline : Execution θ (fun _ _ => []) (shortLearnedLocalState s) (quietAt cycle.returned.final H)
  offline_reconstruct : offline = cycle.execution.append quiet
  before : Snapshot 1
  before_state : before = appendPending (quietAt cycle.returned.final H) (⟨0,p,H⟩ :: later)
  framed : Execution θ (fun _ _ => []) s before
  framed_ledger : framed.ledger = offline.ledger
  final : Snapshot 1
  final_state : final = {setRaw before 0 p (some before.time) with pending := later}
  arrival : Jump (fun _ _ => []) before final
  execution : Execution θ (fun _ _ => []) s final
  reconstruct : execution = framed.append (.cons (.jump arrival) (.nil _))
  contacts_transversal : execution.ContactsTransversal
  date : final.time = H
  values : final.x = (quietAt cycle.returned.final H).x
  prepared : ∀ j, PreparedSection final j
  charge : final.x 0 .q = 1 / 10
  raw_active : final.raw 0 p = some H
  raw_other : ∀ q, q ≠ p → final.raw 0 q = none
  pending : final.pending = later
  gains : ∀ j q, final.x j (.z q) = s.x j (.z q)
  recovery : ∀ j, final.x j .b = s.x j .b
  emissions : execution.ledger.emissions = [(0,cycle.fire.final.time)]
  deliveries : execution.deliveries = [⟨0,p,H⟩]
  error_zero : ∀ q, execution.ledger.error 0 q = 0
  mark_zero : ∀ q, execution.ledger.mark 0 q = 0
  recovery_zero : execution.ledger.recovery 0 = 0
  physical : PhysicalInvariant θ final
  raw_valid : RawValid final
  complete : CompleteThrough execution H

/-- A current prepared physical source and its actual future queue suffice.
The next date only needs H>S+6.9. No reaching execution or H≥S+7.75 is given. -/
theorem short_learned_next_source_exists {θ ε} (hb : PhysicalBox θ ε)
    (s : Snapshot 1) (p : Port) (H : ℝ) (later : List (Delivery 1))
    (hf : PhysicalInvariant θ s) (hv : RawValid s) (hs : PreparedSection s 0)
    (hg : 9 / 5 ≤ Real.exp (s.x 0 (.z p)) ∧ Real.exp (s.x 0 (.z p)) ≤ 11 / 5)
    (hr : s.raw 0 p = some s.time) (ho : ∀ q, q ≠ p → s.raw 0 q = none)
    (hqueue : s.pending = ⟨0,p,H⟩ :: later) (hgap : s.time + 69 / 10 < H)
    (hLater : ∀ d ∈ later, H < d.due) :
    Nonempty (ShortLearnedNextSource θ s p H later) := by
  let s0 := shortLearnedLocalState s
  have hf0 : PhysicalInvariant θ s0 := ⟨hf.region,hf.gain_cap,hf.recovery_cap,hf.reserve⟩
  have hv0 : RawValid s0 := hv
  have hs0 : PreparedSection s0 0 := ⟨hs.ready,hs.charge,hs.recovery,hs.auxiliary⟩
  obtain ⟨cycle⟩ := short_learned_cycle_exists hb s0 p hf0 hv0 hs0 hg hr ho
    (by intro d hd; change d ∈ ([] : List (Delivery 1)) at hd; contradiction)
  have hEnd : cycle.returned.final.time < H := by rw [cycle.date]; exact hgap
  have hEmpty : cycle.returned.final.pending = [] := cycle.pending
  let flow : Flow θ cycle.returned.final (quietAt cycle.returned.final H) :=
    quietFlow cycle.returned.final hEnd (fun j => (cycle.ready j).ready)
      (fun j q => ((cycle.ready j).auxiliary q).1) cycle.raw_none
      (fun j => by linarith [(cycle.ready j).charge.2])
      (fun j q => by linarith [((cycle.ready j).auxiliary q).2.2])
      (by intro d hd; rw [hEmpty] at hd; contradiction)
  let quiet : Execution θ (fun _ _ => []) cycle.returned.final (quietAt cycle.returned.final H) :=
    .cons (.flow flow) (.nil _)
  let offline := cycle.execution.append quiet
  have heOffline : offline.ledger.emissions = [(0,cycle.fire.final.time)] := by
    rw [Execution.emissions_append,cycle.emissions]; rfl
  have hdOffline : offline.deliveries = [] := by rw [Execution.deliveries_append,cycle.deliveries]; rfl
  have hQuietMark (q : Port) : quiet.ledger.mark 0 q = 0 := by
    simp [quiet,Execution.ledger,Move.ledger,Flow.ledger,Ledger.add,Ledger.zero,markAct,((cycle.ready 0).auxiliary q).1]
  have hOfflineMark (q : Port) : offline.ledger.mark 0 q = 0 := by
    rw [Execution.mark_append,cycle.mark_zero,hQuietMark,zero_add]
  let future : List (Delivery 1) := ⟨0,p,H⟩ :: later
  obtain ⟨framed0,hFrame,hFrameDel,hFrameTrans⟩ := offline.appendFuture_emptyRoute_transversal future
    (by intro d hd; rcases List.mem_cons.mp hd with he | hd
        · subst d; exact le_rfl
        · exact (hLater d hd).le)
  have hSource : s = appendPending s0 future := by
    simp only [s0,shortLearnedLocalState,appendPending,future,List.nil_append]
    rw [← hqueue]
  let before := appendPending (quietAt cycle.returned.final H) future
  let framed : Execution θ (fun _ _ => []) s before := framed0.cast_source hSource
  have hFramedLedger : framed.ledger = offline.ledger := (framed0.cast_source_ledger hSource).trans hFrame
  have heFramed : framed.ledger.emissions = [(0,cycle.fire.final.time)] :=
    (congrArg (fun L : Ledger 1 => L.emissions) hFramedLedger).trans heOffline
  have hdFramed : framed.deliveries = [] := (framed0.cast_source_deliveries hSource).trans (hFrameDel.trans hdOffline)
  have hBeforeQueue : before.pending = [] ++ (⟨0,p,H⟩ : Delivery 1) :: later := by
    change cycle.returned.final.pending ++ future = _
    rw [hEmpty]
  let final : Snapshot 1 := {setRaw before 0 p (some before.time) with pending := later}
  let arrival : Jump (fun _ _ => []) before final := .arrive before ⟨0,p,H⟩ [] later hBeforeQueue rfl (cycle.raw_none 0 p)
  let trace := framed.append (.cons (.jump arrival) (.nil _))
  have hQuietReady : ∀ j, ReadyCoordinates (quietAt cycle.returned.final H) j := fun j =>
    quietAt_ready_coordinates cycle.returned.final j (cycle.ready j) hEnd.le
  have hReady : ∀ j, ReadyCoordinates final j := fun j =>
    ⟨(hQuietReady j).ready,(hQuietReady j).charge,(hQuietReady j).auxiliary⟩
  have hPrepared : ∀ j, PreparedSection final j := fun j =>
    ⟨(hReady j).ready,(hReady j).charge,(cycle.prepared j).recovery,(hReady j).auxiliary⟩
  have hCharge : final.x 0 .q = 1 / 10 := by
    change relax (1 / 2) (1 / 10) (cycle.returned.final.x 0 .q) cycle.returned.final.time H = _
    rw [cycle.charge]; simp [relax]
  have hRaw : final.raw 0 p = some H := by simp [final,setRaw,before,appendPending,quietAt]
  have hOther (q : Port) (hq : q ≠ p) : final.raw 0 q = none := by
    change (setRaw before 0 p (some before.time)).raw 0 q = none
    rw [raw_update_other _ _ _ _ _ _ (Or.inr hq)]
    exact cycle.raw_none 0 q
  have hGains : ∀ j q, final.x j (.z q) = s.x j (.z q) := cycle.gains
  have hRecovery : ∀ j, final.x j .b = s.x j .b := cycle.recovery
  have heTrace : trace.ledger.emissions = [(0,cycle.fire.final.time)] := by
    have hj : arrival.ledger.emissions = [] := rfl
    simp only [trace,Execution.emissions_append,heFramed,Execution.ledger,Move.ledger,hj,
      Ledger.add,Ledger.zero,List.append_nil]
  have hdTrace : trace.deliveries = [⟨0,p,H⟩] := by
    have hj : arrival.deliveries = [⟨0,p,H⟩] := rfl
    simp only [trace,Execution.deliveries_append,hdFramed,Execution.deliveries,Move.deliveries,hj,
      List.nil_append,List.append_nil]
  have hError (q : Port) : trace.ledger.error 0 q = 0 := by
    have h := trace.gain_balance 0 q
    rw [hGains] at h; linarith
  have hMark (q : Port) : trace.ledger.mark 0 q = 0 := by
    have h := congrArg (fun L : Ledger 1 => L.mark 0 q) hFramedLedger
    have hj : arrival.ledger.mark 0 q = 0 := rfl
    change (framed.append (.cons (.jump arrival) (.nil _))).ledger.mark 0 q = 0
    rw [Execution.mark_append,h,hOfflineMark]
    simp only [Execution.ledger,Move.ledger,Ledger.add,Ledger.zero,hj,add_zero]
  have hRecoveryZero : trace.ledger.recovery 0 = 0 := by
    have h := trace.recovery_balance 0
    rw [hRecovery] at h; linarith
  have hFuture : ∀ d ∈ final.pending, final.time < d.due := hLater
  have hComplete : CompleteThrough trace H := by
    refine ⟨rfl,?_,hLater⟩
    intro u
    apply BeforeGuards.no_jump
    · constructor
      · intro j
        have hj : j = 0 := Subsingleton.elim _ _
        subst j
        rw [(hPrepared 0).ready,hCharge]; norm_num
      · intro j q
        rw [((hPrepared j).auxiliary q).1]
        linarith [((hPrepared j).auxiliary q).2.2]
    · intro j q origin hraw
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      by_cases hq : q = p
      · subst q
        have ho : origin = H := Option.some.inj (hraw.symm.trans hRaw)
        rw [ho]
        change H < H + 1
        linarith
      · rw [hOther q hq] at hraw; contradiction
    · exact hFuture
  refine ⟨{
    cycle := cycle, quietFlow := flow, quiet := quiet, quiet_reconstruct := rfl
    offline := offline, offline_reconstruct := rfl, before := before, before_state := rfl
    framed := framed, framed_ledger := hFramedLedger, arrival := arrival
    final := final, final_state := rfl, execution := trace, reconstruct := rfl
    contacts_transversal := by
      have hOffline : offline.ContactsTransversal := by
        simp [offline, quiet, cycle.contacts_transversal, Execution.ContactsTransversal]
      have hFramed : framed.ContactsTransversal := by
        simpa only [framed, Execution.contactsTransversal_cast_source] using hFrameTrans.mpr hOffline
      simpa [trace, arrival, Execution.ContactsTransversal, Jump.ContactTransversal] using hFramed
    date := rfl, values := rfl, prepared := hPrepared, charge := hCharge
    raw_active := hRaw, raw_other := hOther, pending := rfl, gains := hGains, recovery := hRecovery
    emissions := heTrace, deliveries := hdTrace, error_zero := hError, mark_zero := hMark
    recovery_zero := hRecoveryZero, physical := trace.physical_invariant hb hf
    raw_valid := trace.raw_valid hv, complete := hComplete
  }⟩

namespace ShortLearnedNextSource
variable {θ s p H later} (r : ShortLearnedNextSource θ s p H later)

theorem emission_count : (r.execution.emissionTimes 0).length = 1 := by
  simp [Execution.emissionTimes,r.emissions]

/-- The current root and forced energy path are the retained cycle's actual
ones; quiet transport preserves its prepared return instead of resetting it. -/
theorem fire_bounds : s.time + 2 / 5 < r.cycle.fire.final.time ∧
    r.cycle.fire.final.time < s.time + 7 / 10 := r.cycle.fire_bounds

end ShortLearnedNextSource
end KernelR.Hybrid
