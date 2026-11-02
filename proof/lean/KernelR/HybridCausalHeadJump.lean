import KernelR.HybridCausalHeadQueue

/-! Actual dynamic-queue jump lifts for a feed-forward head extension.
An arrival is lifted only when its token is present in the true shared queue.
The preceding ghost balance supplies that availability at the chosen clock. -/
namespace KernelR.Hybrid

@[simp] theorem Snapshot.requeue_setMain {n} (s : Snapshot n) (Q : List (Delivery n))
    (i : Fin n) (mode : MainMode) :
    (setMain s i mode).requeue Q = setMain (s.requeue Q) i mode := rfl

@[simp] theorem Snapshot.requeue_setAux {n} (s : Snapshot n) (Q : List (Delivery n))
    (i : Fin n) (p : Port) (mode : AuxMode) :
    (setAux s i p mode).requeue Q = setAux (s.requeue Q) i p mode := rfl

@[simp] theorem Snapshot.requeue_setRaw {n} (s : Snapshot n) (Q : List (Delivery n))
    (i : Fin n) (p : Port) (origin : Option ℝ) :
    (setRaw s i p origin).requeue Q = setRaw (s.requeue Q) i p origin := rfl

@[simp] theorem Snapshot.prependQueued_setMain_tail {n} (s : Snapshot n) (a : Snapshot 1)
    (Q : List (Delivery (n + 1))) (i : Fin n) (mode : MainMode) :
    (setMain s i mode).prependQueued a Q = setMain (s.prependQueued a Q) i.succ mode := by
  simp only [Snapshot.prependQueued,Snapshot.prependQuiet_setMain,Snapshot.requeue_setMain]

@[simp] theorem Snapshot.prependQueued_setAux_tail {n} (s : Snapshot n) (a : Snapshot 1)
    (Q : List (Delivery (n + 1))) (i : Fin n) (p : Port) (mode : AuxMode) :
    (setAux s i p mode).prependQueued a Q = setAux (s.prependQueued a Q) i.succ p mode := by
  simp only [Snapshot.prependQueued,Snapshot.prependQuiet_setAux,Snapshot.requeue_setAux]

@[simp] theorem Snapshot.prependQueued_setRaw_tail {n} (s : Snapshot n) (a : Snapshot 1)
    (Q : List (Delivery (n + 1))) (i : Fin n) (p : Port) (origin : Option ℝ) :
    (setRaw s i p origin).prependQueued a Q = setRaw (s.prependQueued a Q) i.succ p origin := by
  simp only [Snapshot.prependQueued,Snapshot.prependQuiet_setRaw,Snapshot.requeue_setRaw]

@[simp] theorem Snapshot.prependQueued_setMain_head {n} (s : Snapshot n) (a : Snapshot 1)
    (Q : List (Delivery (n + 1))) (mode : MainMode) :
    s.prependQueued (setMain a 0 mode) Q = setMain (s.prependQueued a Q) 0 mode := by
  simp only [Snapshot.prependQueued,Snapshot.prependQuiet_setMain_head,Snapshot.requeue_setMain]

@[simp] theorem Snapshot.prependQueued_setRaw_head {n} (s : Snapshot n) (a : Snapshot 1)
    (Q : List (Delivery (n + 1))) (p : Port) (origin : Option ℝ) :
    s.prependQueued (setRaw a 0 p origin) Q = setRaw (s.prependQueued a Q) 0 p origin := by
  simp only [Snapshot.prependQueued,Snapshot.prependQuiet_setRaw_head,Snapshot.requeue_setRaw]

private theorem jump_cast_target {n route s u v} (j : @Jump n route s u) (h : u = v) :
    ∃ out : Jump route s v,
      out.ledger.emissions = j.ledger.emissions ∧ out.deliveries = j.deliveries := by
  subst v
  exact ⟨j,rfl,rfl⟩

/-- Guard/expiry jumps use no token and retain the arbitrary shared queue. -/
theorem Jump.requeue_guard {n route s u} (j : @Jump n route s u)
    (hn : j.QueueNeutral) (Q : List (Delivery n)) :
    ∃ out : Jump route (s.requeue Q) (u.requeue Q),
      out.ledger.emissions = [] ∧ out.deliveries = [] := by
  cases j with
  | fire => exact hn.elim
  | arrive => exact hn.elim
  | fastEnd i hm hq =>
    rw [Snapshot.requeue_setMain]
    exact ⟨.fastEnd _ i hm hq,rfl,rfl⟩
  | reopen i hm hq =>
    rw [Snapshot.requeue_setMain]
    exact ⟨.reopen _ i hm hq,rfl,rfl⟩
  | mark i p hm hq =>
    rw [Snapshot.requeue_setAux]
    exact ⟨.mark _ i p hm hq,rfl,rfl⟩
  | silent i p hm hq =>
    rw [Snapshot.requeue_setAux]
    exact ⟨.silent _ i p hm hq,rfl,rfl⟩
  | error i p hm hq =>
    rw [Snapshot.requeue_setAux]
    exact ⟨.error _ i p hm hq,rfl,rfl⟩
  | auxReady i p hm hq =>
    rw [Snapshot.requeue_setAux]
    exact ⟨.auxReady _ i p hm hq,rfl,rfl⟩
  | rawEnd i p origin hr ht =>
    rw [Snapshot.requeue_setRaw]
    exact ⟨.rawEnd _ i p origin hr ht,rfl,rfl⟩

private theorem neutral_events {n route s u} (j : @Jump n route s u) (hn : j.QueueNeutral) :
    j.ledger.emissions = [] ∧ j.deliveries = [] := by
  cases j <;> simp_all [Jump.QueueNeutral,Jump.ledger,Jump.deliveries,Ledger.zero]

/-- All tail jumps lift under the real extended router. The only availability
premise concerns occurrences delivered by this particular actual jump. -/
theorem Jump.prependQueued_tail {n route s u} (j : @Jump n route s u)
    (a : Snapshot 1) (Q : List (Delivery (n + 1))) (contacts : HeadRoutes n)
    (havailable : ∀ d ∈ j.deliveries, d.succ ∈ Q) :
    ∃ (Q' : List (Delivery (n + 1)))
      (out : Jump (prependRouted route contacts) (s.prependQueued a Q) (u.prependQueued a Q')),
      out.ledger.emissions = j.ledger.emissions.map (fun ev => (ev.1.succ,ev.2)) ∧
      out.deliveries = j.deliveries.map Delivery.succ := by
  by_cases hn : j.QueueNeutral
  · have he := (neutral_events j hn).1
    have hd := (neutral_events j hn).2
    obtain ⟨g,heG,hdG⟩ := j.prependQuiet_neutral he a (prependRouted route contacts)
    have hdG0 : g.deliveries = [] := by rw [hdG,hd,List.map_nil]
    obtain ⟨out,heOut,hdOut⟩ := g.requeue_guard (g.queueNeutral_of_no_events heG hdG0) Q
    refine ⟨Q,out,?_,?_⟩
    · exact heOut.trans (by rw [he,List.map_nil])
    · exact hdOut.trans (by rw [hd,List.map_nil])
  · cases j <;> try exact (hn (by trivial)).elim
    case fire i hm hq =>
      let before := s.prependQueued a Q
      let Q' := Q ++ prependRouted route contacts i.succ s.time
      let step := Jump.fire (route := prependRouted route contacts) before i.succ hm hq
      have target : {setMain before i.succ .fast with pending := Q'} =
          ({setMain s i .fast with pending := s.pending ++ route i s.time} : Snapshot n).prependQueued a Q' := by
        change setMain (s.prependQueued a Q') i.succ .fast = (setMain s i .fast).prependQueued a Q'
        exact (Snapshot.prependQueued_setMain_tail s a Q' i .fast).symm
      obtain ⟨out,heOut,hdOut⟩ := jump_cast_target step target
      exact ⟨Q',out,by rw [heOut]; rfl,by rw [hdOut]; rfl⟩
    case arrive d before after hqueue hdue hfree =>
      have hd : d.succ ∈ Q := havailable d (by simp only [Jump.deliveries,List.mem_singleton])
      obtain ⟨left,right,hQ⟩ := List.append_of_mem hd
      let Q' := left ++ right
      let step := Jump.arrive (route := prependRouted route contacts) (s.prependQueued a Q)
        d.succ left right hQ hdue hfree
      have target : {setRaw (s.prependQueued a Q) d.cell.succ d.port (some s.time) with pending := Q'} =
          ({setRaw s d.cell d.port (some s.time) with pending := before ++ after} : Snapshot n).prependQueued a Q' := by
        change setRaw (s.prependQueued a Q') d.cell.succ d.port (some s.time) =
          (setRaw s d.cell d.port (some s.time)).prependQueued a Q'
        exact (Snapshot.prependQueued_setRaw_tail s a Q' d.cell d.port (some s.time)).symm
      obtain ⟨out,heOut,hdOut⟩ := jump_cast_target step target
      exact ⟨Q',out,by rw [heOut]; rfl,by rw [hdOut]; rfl⟩

/-- A local head FIRE remains a genuine global FIRE with the closed head
contact. A local arrival consumes an actual shared-queue occurrence. -/
theorem Jump.prependQueued_head {route : Router 1} {a b : Snapshot 1}
    (j : Jump route a b) (_hroute : ∀ i t, route i t = [])
    {n} (s : Snapshot n) (hclock : s.time = a.time)
    (Q : List (Delivery (n + 1))) (tailRoute : Router n) (contacts : HeadRoutes n)
    (havailable : ∀ d ∈ j.deliveries, Delivery.head (n := n) d ∈ Q) :
    ∃ (Q' : List (Delivery (n + 1)))
      (out : Jump (prependRouted tailRoute contacts) (s.prependQueued a Q) (s.prependQueued b Q')),
      out.ledger.emissions = j.ledger.emissions.map (fun ev => ((0 : Fin (n + 1)),ev.2)) ∧
      out.deliveries = j.deliveries.map (Delivery.head (n := n)) := by
  by_cases hn : j.QueueNeutral
  · have he := (neutral_events j hn).1
    have hd := (neutral_events j hn).2
    obtain ⟨g,heG,hdG⟩ := j.prependHead_neutral he hd s hclock (prependRouted tailRoute contacts)
    obtain ⟨out,heOut,hdOut⟩ := g.requeue_guard (g.queueNeutral_of_no_events heG hdG) Q
    refine ⟨Q,out,?_,?_⟩
    · exact heOut.trans (by rw [he,List.map_nil])
    · exact hdOut.trans (by rw [hd,List.map_nil])
  · cases j <;> try exact (hn (by trivial)).elim
    case fire i hm hq =>
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      let before := s.prependQueued a Q
      let step := Jump.fire (route := prependRouted tailRoute contacts) before 0 hm hq
      have target : {setMain before 0 .fast with pending := Q ++ []} =
          s.prependQueued ({setMain a 0 .fast with pending := a.pending ++ route 0 a.time} : Snapshot 1) Q := by
        rw [List.append_nil]
        change setMain (s.prependQueued a Q) 0 .fast = s.prependQueued (setMain a 0 .fast) Q
        exact (Snapshot.prependQueued_setMain_head s a Q .fast).symm
      obtain ⟨out,heOut,hdOut⟩ := jump_cast_target step target
      refine ⟨Q,out,?_,by rw [hdOut]; rfl⟩
      rw [heOut]
      change [(0,s.time)] = [(0,a.time)]
      rw [hclock]
    case arrive d before after hqueue hdue hfree =>
      have hd : Delivery.head (n := n) d ∈ Q :=
        havailable d (by simp only [Jump.deliveries,List.mem_singleton])
      obtain ⟨left,right,hQ⟩ := List.append_of_mem hd
      have hcell : d.cell = 0 := Subsingleton.elim _ _
      let Q' := left ++ right
      let step := Jump.arrive (route := prependRouted tailRoute contacts) (s.prependQueued a Q)
        (Delivery.head (n := n) d) left right hQ (hdue.trans hclock.symm)
        (by change a.raw 0 d.port = none; simpa only [hcell] using hfree)
      have target : {setRaw (s.prependQueued a Q) 0 d.port (some s.time) with pending := Q'} =
          s.prependQueued ({setRaw a d.cell d.port (some a.time) with pending := before ++ after} : Snapshot 1) Q' := by
        change setRaw (s.prependQueued a Q') 0 d.port (some s.time) =
          s.prependQueued (setRaw a d.cell d.port (some a.time)) Q'
        rw [hclock,hcell]
        exact (Snapshot.prependQueued_setRaw_head s a Q' d.port (some a.time)).symm
      obtain ⟨out,heOut,hdOut⟩ := jump_cast_target step target
      exact ⟨Q',out,by rw [heOut]; rfl,by rw [hdOut]; rfl⟩

end KernelR.Hybrid
