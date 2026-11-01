import KernelR.HybridArrivals
import KernelR.HybridDueSources

namespace KernelR.Hybrid

/-- One explicitly constructed delivery removes exactly one source occurrence. -/
structure SourceDelivery {n} (route : Router n) (s : Snapshot n) (d : Delivery n) where
  afterArrival : Snapshot n
  jump : Jump route s afterArrival
  pending : (d :: afterArrival.pending).Perm s.pending
  deliveries : jump.deliveries = [d]
  emissions : jump.ledger.emissions = []
  coordinates : afterArrival.x = s.x
  time : afterArrival.time = s.time
  main : afterArrival.main = s.main
  auxiliary : afterArrival.aux = s.aux
  raw_active : afterArrival.raw d.cell d.port = some s.time
  raw_other : ∀ i p, i ≠ d.cell ∨ p ≠ d.port → afterArrival.raw i p = s.raw i p

theorem source_delivery_exists {n route s} (d : Delivery n)
    (hmem : d ∈ s.pending) (hdue : d.due = s.time) (hfree : s.raw d.cell d.port = none) :
    Nonempty (SourceDelivery route s d) := by
  obtain ⟨before,after,hqueue⟩ := List.mem_iff_append.mp hmem
  let target : Snapshot n := { (setRaw s d.cell d.port (some s.time)) with pending := before ++ after }
  let j : Jump route s target := .arrive s d before after hqueue hdue hfree
  refine ⟨{
    afterArrival := target
    jump := j
    pending := ?_
    deliveries := rfl
    emissions := rfl
    coordinates := rfl
    time := rfl
    main := rfl
    auxiliary := rfl
    raw_active := ?_
    raw_other := ?_
  }⟩
  · change (d :: (before ++ after)).Perm s.pending
    rw [hqueue]
    exact List.perm_middle.symm
  · simp [target,setRaw]
  · intro i p h
    rcases h with hi | hp
    · simp [target,setRaw,hi]
    · by_cases hi : i = d.cell
      · subst i; simp [target,setRaw,hp]
      · simp [target,setRaw,hi]

theorem pending_earliest_exists {n} (s : Snapshot n) (hne : s.pending ≠ []) :
    ∃ d ∈ s.pending, ∀ f ∈ s.pending, d.due ≤ f.due := by
  have hlist : ∀ queue : List (Delivery n), queue ≠ [] →
      ∃ d ∈ queue, ∀ f ∈ queue, d.due ≤ f.due := by
    intro queue
    induction queue with
    | nil => simp
    | cons d ds ih =>
      intro _
      by_cases hds : ds = []
      · subst ds
        refine ⟨d,by simp,?_⟩
        intro f hf
        have heq := List.mem_singleton.mp hf
        subst f
        exact le_rfl
      obtain ⟨m,hm,hmin⟩ := ih hds
      by_cases hdm : d.due ≤ m.due
      · refine ⟨d,by simp,?_⟩
        intro f hf
        rcases List.mem_cons.mp hf with rfl | hf
        · exact le_rfl
        · exact hdm.trans (hmin f hf)
      · refine ⟨m,List.mem_cons_of_mem _ hm,?_⟩
        intro f hf
        rcases List.mem_cons.mp hf with rfl | hf
        · exact le_of_not_ge hdm
        · exact hmin f hf
  exact hlist s.pending hne

theorem pending_earliest_future {n} (s : Snapshot n) (hne : s.pending ≠ []) (hf : PendingFuture s) :
    ∃ d ∈ s.pending, s.time ≤ d.due ∧ ∀ f ∈ s.pending, d.due ≤ f.due := by
  obtain ⟨d,hd,hmin⟩ := pending_earliest_exists s hne
  exact ⟨d,hd,hf d hd,hmin⟩

/-- This alternative constructs an eligible jump now, or supplies a strictly
later next source date for a separate waiting-flow construction. -/
theorem source_delivery_or_wait {n route s} (hne : s.pending ≠ []) (hf : @PendingFuture n s)
    (hraw : ∀ i p, s.raw i p = none) :
    (∃ d, Nonempty (SourceDelivery route s d)) ∨
      ∃ T : ℝ, s.time < T ∧ ∀ d ∈ s.pending, T ≤ d.due := by
  obtain ⟨d,hd,hstart,hmin⟩ := pending_earliest_future s hne hf
  by_cases heq : d.due = s.time
  · exact Or.inl ⟨d,source_delivery_exists d hd heq (hraw d.cell d.port)⟩
  · exact Or.inr ⟨d.due,lt_of_le_of_ne hstart (Ne.symm heq),hmin⟩

def DisjointDeliverySlots {n} (d f : Delivery n) : Prop :=
  d.cell ≠ f.cell ∨ d.port ≠ f.port

structure SourceBatch {n} (θ : Fin n → Parameters) (route : Router n) (s : Snapshot n)
    (tokens later : List (Delivery n)) where
  final : Snapshot n
  execution : Execution θ route s final
  deliveries : execution.deliveries = tokens
  pending : final.pending.Perm later
  emissions : execution.ledger.emissions = []
  coordinates : final.x = s.x
  time : final.time = s.time
  main : final.main = s.main
  auxiliary : final.aux = s.aux
  raw_active : ∀ d ∈ tokens, final.raw d.cell d.port = some s.time
  raw_other : ∀ i p, (∀ d ∈ tokens, i ≠ d.cell ∨ p ≠ d.port) → final.raw i p = s.raw i p

/-- Any chosen finite ordering of simultaneous deliveries to disjoint slots
is executable. Other queue occurrences, including duplicates, are retained.
No completeness or event-priority assertion is made about the terminal state. -/
theorem simultaneous_deliveries_exists {n θ route} (tokens later : List (Delivery n))
    (s : Snapshot n) (hq : s.pending.Perm (tokens ++ later))
    (hdue : ∀ d ∈ tokens, d.due = s.time)
    (hfree : ∀ d ∈ tokens, s.raw d.cell d.port = none)
    (hslots : tokens.Pairwise DisjointDeliverySlots) :
    Nonempty (SourceBatch θ route s tokens later) := by
  induction tokens generalizing s with
  | nil =>
    exact ⟨⟨s,.nil _,rfl,by simpa using hq,rfl,rfl,rfl,rfl,rfl,
      by simp,by intro i p _; rfl⟩⟩
  | cons d ds ih =>
    have hmem : d ∈ s.pending := hq.mem_iff.mpr (by simp)
    obtain ⟨head⟩ := source_delivery_exists (route := route) d hmem
      (hdue d (by simp)) (hfree d (by simp))
    have hqueue : head.afterArrival.pending.Perm (ds ++ later) := by
      apply List.Perm.cons_inv
      exact head.pending.trans hq
    have hdistinct := (List.pairwise_cons.mp hslots).1
    have htailSlots := (List.pairwise_cons.mp hslots).2
    have htailDue : ∀ f ∈ ds, f.due = head.afterArrival.time := by
      intro f hf
      exact (hdue f (List.mem_cons_of_mem _ hf)).trans head.time.symm
    have htailFree : ∀ f ∈ ds, head.afterArrival.raw f.cell f.port = none := by
      intro f hf
      have hother : f.cell ≠ d.cell ∨ f.port ≠ d.port := by
        rcases hdistinct f hf with h | h
        · exact Or.inl (Ne.symm h)
        · exact Or.inr (Ne.symm h)
      rw [head.raw_other f.cell f.port hother]
      exact hfree f (List.mem_cons_of_mem _ hf)
    obtain ⟨tail⟩ := ih head.afterArrival hqueue htailDue htailFree htailSlots
    let whole : Execution θ route s tail.final := .cons (.jump head.jump) tail.execution
    refine ⟨{
      final := tail.final
      execution := whole
      deliveries := ?_
      pending := tail.pending
      emissions := ?_
      coordinates := tail.coordinates.trans head.coordinates
      time := tail.time.trans head.time
      main := tail.main.trans head.main
      auxiliary := tail.auxiliary.trans head.auxiliary
      raw_active := ?_
      raw_other := ?_
    }⟩
    · simp only [whole,Execution.deliveries,Move.deliveries,head.deliveries,tail.deliveries,List.singleton_append]
    · simp only [whole,Execution.ledger,Move.ledger,Ledger.add,head.emissions,tail.emissions,List.nil_append]
    · intro f hf
      rcases List.mem_cons.mp hf with heq | hf
      · subst f
        rw [tail.raw_other d.cell d.port (fun f hf => hdistinct f hf),head.raw_active]
      · rw [tail.raw_active f hf,head.time]
    · intro i p hother
      rw [tail.raw_other i p (fun f hf => hother f (List.mem_cons_of_mem _ hf))]
      exact head.raw_other i p (hother d (by simp))

/-- The first real protocol token is deliverable from every declared birth;
this is a concrete one-jump witness, not an assumed reaching execution. -/
theorem birth_protocol_first_arrival {θ route born}
    (hs : @BirthState 1 born)
    (hq : born.pending = sourceTrain 0 0 0 8 16 ++ sourceTrain 0 0 160 8 16) :
    Nonempty (@SourceBatch 1 θ route born [⟨0,0,0⟩]
      (sourceTrain 0 0 8 8 15 ++ sourceTrain 0 0 160 8 16)) := by
  apply simultaneous_deliveries_exists
  · apply List.Perm.of_eq
    rw [hq,sourceTrain_succ]
    norm_num
  · intro d hd
    have heq := List.mem_singleton.mp hd
    subst d
    exact hs.1.symm
  · intro d hd
    have heq := List.mem_singleton.mp hd
    subst d
    exact hs.2.1 0 0
  · exact .cons (by simp) .nil

/-- The exact first protocol successor keeps all thirty-one later sources. -/
noncomputable def birthProtocolFirstAfter (born : Snapshot 1) : Snapshot 1 :=
  { (setRaw born 0 0 (some born.time)) with
    pending := sourceTrain 0 0 8 8 15 ++ sourceTrain 0 0 160 8 16 }

noncomputable def birth_protocol_first_jump {route born} (hs : @BirthState 1 born)
    (hq : born.pending = sourceTrain 0 0 0 8 16 ++ sourceTrain 0 0 160 8 16) :
    Jump route born (birthProtocolFirstAfter born) := by
  have hhead : born.pending = [] ++ (⟨0,0,0⟩ : Delivery 1) ::
      (sourceTrain 0 0 8 8 15 ++ sourceTrain 0 0 160 8 16) := by
    rw [hq,sourceTrain_succ]
    norm_num
  exact .arrive born ⟨0,0,0⟩ [] _ hhead hs.1.symm (hs.2.1 0 0)

theorem birth_protocol_first_execution {θ route born} (hs : @BirthState 1 born)
    (hq : born.pending = sourceTrain 0 0 0 8 16 ++ sourceTrain 0 0 160 8 16) :
    ∃ e : Execution θ route born (birthProtocolFirstAfter born),
      e.deliveries = [⟨0,0,0⟩] ∧ e.ledger.emissions = [] ∧
      (birthProtocolFirstAfter born).pending.length = 31 := by
  refine ⟨.cons (.jump (birth_protocol_first_jump hs hq)) (.nil _),rfl,rfl,?_⟩
  simp only [birthProtocolFirstAfter,List.length_append,sourceTrain,List.length_ofFn]

/-- Token conservation supplies the next source occurrence without assuming
a continuation or a complete terminal run. Availability of its raw slot is
kept explicit, since it does not follow from queue membership alone. -/
theorem Execution.next_source_delivery {n θ route s u} (e : @Execution n θ route s u)
    (past later : List (Delivery n)) (d : Delivery n)
    (hq : s.pending = past ++ d :: later) (hd : e.deliveries.Perm past)
    (hroute : ∀ i t, route i t = []) (hdue : d.due = u.time)
    (hfree : u.raw d.cell d.port = none) :
    ∃ progress : SourceDelivery route u d, progress.afterArrival.pending.Perm later := by
  have hp := e.pending_perm_of_prefix past (d :: later) hq hd hroute
  obtain ⟨progress⟩ := source_delivery_exists d (hp.mem_iff.mpr (by simp)) hdue hfree
  exact ⟨progress,(progress.pending.trans hp).cons_inv⟩

end KernelR.Hybrid
