import KernelR.HybridQuietExecutionProduct

/-! A quiet cell before an active network. The active network keeps its genuine
FIREs, arrivals, and queue; its indices are shifted by one, without synthetic
sources or a permutation of the operational semantics. -/
namespace KernelR.Hybrid
open Set MeasureTheory

/-- Shift an actual network token past the quiet head cell. -/
def Delivery.succ {n} (d : Delivery n) : Delivery (n + 1) :=
  ⟨d.cell.succ, d.port, d.due⟩

/-- Parameters in head/network order. -/
def prependParameters {n} (head : Fin 1 → Parameters) (network : Fin n → Parameters) :
    Fin (n + 1) → Parameters := Fin.cases (head 0) network

/-- The clock and entire queue come from the actual active network. -/
noncomputable def Snapshot.prependQuiet {n} (network : Snapshot n) (head : Snapshot 1) :
    Snapshot (n + 1) where
  time := network.time
  x := Fin.cases (head.x 0) network.x
  main := Fin.cases (head.main 0) network.main
  aux := Fin.cases (head.aux 0) network.aux
  raw := Fin.cases (head.raw 0) network.raw
  pending := network.pending.map Delivery.succ

/-- Empty-queue projection of the quiet head cell. -/
noncomputable def Snapshot.quietHead {n} (s : Snapshot (n + 1)) : Snapshot 1 where
  time := s.time
  x := fun _ => s.x 0
  main := fun _ => s.main 0
  aux := fun _ => s.aux 0
  raw := fun _ => s.raw 0
  pending := []

/-- Active cells with their own exact queue, supplied for reconstruction. -/
noncomputable def Snapshot.activeTail {n} (s : Snapshot (n + 1))
    (Q : List (Delivery n)) : Snapshot n where
  time := s.time
  x := fun i => s.x i.succ
  main := fun i => s.main i.succ
  aux := fun i => s.aux i.succ
  raw := fun i => s.raw i.succ
  pending := Q

/-- No state reset occurs when the queue has no head-cell token. -/
theorem Snapshot.prependQuiet_reconstruct {n} (s : Snapshot (n + 1))
    (Q : List (Delivery n)) (hQ : s.pending = Q.map Delivery.succ) :
    (s.activeTail Q).prependQuiet s.quietHead = s := by
  cases s
  simp only [Snapshot.activeTail, Snapshot.quietHead, Snapshot.prependQuiet]
  congr 1
  all_goals first
    | exact hQ.symm
    | (funext i; exact Fin.cases rfl (fun _ => rfl) i)

/-- Parameters use exactly the same head/active-cell ordering. -/
theorem prependParameters_reconstruct {n} (θ : Fin (n + 1) → Parameters) :
    prependParameters (fun _ : Fin 1 => θ 0) (fun i => θ i.succ) = θ := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

@[simp] theorem Snapshot.prependQuiet_setMain {n} (s : Snapshot n) (a : Snapshot 1)
    (i : Fin n) (mode : MainMode) :
    (setMain s i mode).prependQuiet a = setMain (s.prependQuiet a) i.succ mode := by
  cases s
  simp only [Snapshot.prependQuiet, setMain]
  congr 1
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [Fin.succ_ne_zero, eq_comm]
  · simp [Function.update_apply, eq_comm]

@[simp] theorem Snapshot.prependQuiet_setAux {n} (s : Snapshot n) (a : Snapshot 1)
    (i : Fin n) (p : Port) (mode : AuxMode) :
    (setAux s i p mode).prependQuiet a = setAux (s.prependQuiet a) i.succ p mode := by
  cases s
  simp only [Snapshot.prependQuiet, setAux]
  congr 1
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [Fin.succ_ne_zero, eq_comm]
  · simp [Function.update_apply, eq_comm]

@[simp] theorem Snapshot.prependQuiet_setRaw {n} (s : Snapshot n) (a : Snapshot 1)
    (i : Fin n) (p : Port) (origin : Option ℝ) :
    (setRaw s i p origin).prependQuiet a = setRaw (s.prependQuiet a) i.succ p origin := by
  cases s
  simp only [Snapshot.prependQuiet, setRaw]
  congr 1
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [Fin.succ_ne_zero, eq_comm]
  · simp [Function.update_apply, eq_comm]

/-- Prepend a genuine synchronous flow. The local head queue is deliberately
absent from the product; pending urgency comes from the network flow. -/
noncomputable def Flow.prependQuiet {n θ θA s u a b}
    (f : @Flow n θ s u) (g : @Flow 1 θA a b)
    (hstart : s.time = a.time) (hfinish : u.time = b.time) :
    Flow (prependParameters θA θ) (s.prependQuiet a) (u.prependQuiet b) where
  positive := f.positive
  path := fun t => Fin.cases (g.path t 0) (f.path t)
  initial := by
    funext i c
    refine Fin.cases ?_ (fun j => ?_) i
    · change g.path s.time 0 c = a.x 0 c
      rw [hstart, g.initial]
    · exact congrFun (congrFun f.initial j) c
  final := by
    funext i c
    refine Fin.cases ?_ (fun j => ?_) i
    · change g.path u.time 0 c = b.x 0 c
      rw [hfinish, g.final]
    · exact congrFun (congrFun f.final j) c
  main_fixed := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact congrFun g.main_fixed 0
    · exact congrFun f.main_fixed j
  aux_fixed := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact congrFun g.aux_fixed 0
    · exact congrFun f.aux_fixed j
  raw_fixed := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact congrFun g.raw_fixed 0
    · exact congrFun f.raw_fixed j
  queue_fixed := by
    change u.pending.map Delivery.succ = s.pending.map Delivery.succ
    rw [f.queue_fixed]
  continuous := by
    intro i c
    refine Fin.cases ?_ (fun j => ?_) i
    · change ContinuousOn (fun t => g.path t 0 c) (Icc s.time u.time)
      rw [hstart, hfinish]
      exact g.continuous 0 c
    · exact f.continuous j c
  integrable := by
    intro i c
    refine Fin.cases ?_ (fun j => ?_) i
    · change IntervalIntegrable (fun t => field θA a (g.path t) t 0 c) volume s.time u.time
      rw [hstart, hfinish]
      exact g.integrable 0 c
    · change IntervalIntegrable (fun t => field θ s (f.path t) t j c) volume s.time u.time
      exact f.integrable j c
  mark_integrable := by
    intro i p
    refine Fin.cases ?_ (fun j => ?_) i
    · change IntervalIntegrable (fun t => markAct θA a (g.path t) 0 p) volume s.time u.time
      rw [hstart, hfinish]
      exact g.mark_integrable 0 p
    · exact f.mark_integrable j p
  integral_eq := by
    intro t ht i c
    change t ∈ Icc s.time u.time at ht
    refine Fin.cases ?_ (fun j => ?_) i
    · change g.path t 0 c = a.x 0 c + ∫ v in s.time..t, field θA a (g.path v) v 0 c
      rw [hstart]
      exact g.integral_eq t (by simpa only [hstart, hfinish] using ht) 0 c
    · exact f.integral_eq t ht j c
  guards := by
    intro t ht
    change t ∈ Ico s.time u.time at ht
    have hf := f.guards t ht
    have hg := g.guards t (by simpa only [hstart, hfinish] using ht)
    constructor
    · intro i
      exact Fin.cases (hg.1 0) (fun j => hf.1 j) i
    · intro i p
      exact Fin.cases (hg.2 0 p) (fun j => hf.2 j p) i
  raw_support := by
    intro i p origin hr
    revert hr
    refine Fin.cases ?_ (fun j => ?_) i
    · intro hr
      have hh := g.raw_support 0 p origin hr
      change origin ≤ s.time ∧ u.time ≤ origin + 1
      simpa only [← hstart, ← hfinish] using hh
    · intro hr
      exact f.raw_support j p origin hr
  pending_urgent := by
    intro d hd
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hd
    exact f.pending_urgent v hv

/-- Lift each actual network jump, including FIRE issuance and token arrival.
The global router is required to agree only at the active network cells. -/
theorem Jump.prependQuiet {n route s u} (j : @Jump n route s u)
    (a : Snapshot 1) (global : Router (n + 1))
    (hroute : ∀ i t, global i.succ t = (route i t).map Delivery.succ) :
    ∃ lifted : Jump global (s.prependQuiet a) (u.prependQuiet a),
      lifted.ledger.emissions = j.ledger.emissions.map (fun e => (e.1.succ, e.2)) ∧
      lifted.deliveries = j.deliveries.map Delivery.succ := by
  cases j with
  | fire i hm hq =>
    have heq : ({ setMain s i .fast with pending := s.pending ++ route i s.time } : Snapshot n).prependQuiet a =
        { setMain (s.prependQuiet a) i.succ .fast with
          pending := (s.prependQuiet a).pending ++ global i.succ (s.prependQuiet a).time } := by
      simp only [Snapshot.prependQuiet, setMain, List.map_append, hroute]
      congr 1
      funext k
      refine Fin.cases ?_ (fun l => ?_) k <;> simp [Function.update_apply, Fin.succ_ne_zero, eq_comm]
    rw [heq]
    exact ⟨.fire _ i.succ hm hq, rfl, rfl⟩
  | fastEnd i hm hq =>
    rw [Snapshot.prependQuiet_setMain]
    exact ⟨.fastEnd _ i.succ hm hq, rfl, rfl⟩
  | reopen i hm hq =>
    rw [Snapshot.prependQuiet_setMain]
    exact ⟨.reopen _ i.succ hm hq, rfl, rfl⟩
  | mark i p hm hq =>
    rw [Snapshot.prependQuiet_setAux]
    exact ⟨.mark _ i.succ p hm hq, rfl, rfl⟩
  | silent i p hm hq =>
    rw [Snapshot.prependQuiet_setAux]
    exact ⟨.silent _ i.succ p hm hq, rfl, rfl⟩
  | error i p hm hq =>
    rw [Snapshot.prependQuiet_setAux]
    exact ⟨.error _ i.succ p hm hq, rfl, rfl⟩
  | auxReady i p hm hq =>
    rw [Snapshot.prependQuiet_setAux]
    exact ⟨.auxReady _ i.succ p hm hq, rfl, rfl⟩
  | arrive d before after hq hd hf =>
    have heq : ({ setRaw s d.cell d.port (some s.time) with pending := before ++ after } : Snapshot n).prependQuiet a =
        { setRaw (s.prependQuiet a) d.cell.succ d.port (some s.time) with
          pending := before.map Delivery.succ ++ after.map Delivery.succ } := by
      simp only [Snapshot.prependQuiet, setRaw, List.map_append]
      congr 1
      funext k
      refine Fin.cases ?_ (fun l => ?_) k <;> simp [Function.update_apply, Fin.succ_ne_zero, eq_comm]
    rw [heq]
    refine ⟨.arrive _ d.succ (before.map Delivery.succ) (after.map Delivery.succ) ?_ hd hf, rfl, ?_⟩
    · change s.pending.map Delivery.succ = _
      rw [hq, List.map_append, List.map_cons]
    · simp only [Jump.deliveries, List.map_cons, List.map_nil]
  | rawEnd i p origin hr ht =>
    rw [Snapshot.prependQuiet_setRaw]
    exact ⟨.rawEnd _ i.succ p origin hr ht, rfl, rfl⟩

/-- Endpoint equality transports events without altering the execution. -/
private theorem execution_cast_target_events {n θ route s u v} (e : @Execution n θ route s u)
    (h : u = v) : ∃ out : Execution θ route s v,
      out.ledger.emissions = e.ledger.emissions ∧ out.deliveries = e.deliveries := by
  subst v
  exact ⟨e, rfl, rfl⟩

/-- Run a real active network beside a READY, RAW-free head cell. Every local
flow is paired with a constructed quiet flow; all active events retain their
original order, exact queue, and dates. -/
theorem Execution.prepend_quiet {n θ route s u} (e : @Execution n θ route s u)
    (θA : Fin 1 → Parameters) (a : Snapshot 1) (hstart : s.time = a.time)
    (ha : ∀ i, ReadyCoordinates a i) (hr : ∀ i p, a.raw i p = none) (hq : a.pending = [])
    (global : Router (n + 1))
    (hroute : ∀ i t, global i.succ t = (route i t).map Delivery.succ) :
    ∃ lifted : Execution (prependParameters θA θ) global (s.prependQuiet a)
        (u.prependQuiet (quietAt a u.time)),
      lifted.ledger.emissions = e.ledger.emissions.map (fun ev => (ev.1.succ, ev.2)) ∧
      lifted.deliveries = e.deliveries.map Delivery.succ := by
  induction e generalizing a with
  | nil s =>
    rw [hstart, quietAt_self]
    exact ⟨.nil _, rfl, rfl⟩
  | @cons s v u m rest ih =>
    cases m with
    | flow f =>
      have ht : a.time < v.time := by rw [← hstart]; exact f.positive
      let g := quietFlow (θ := θA) a ht (fun i => (ha i).ready)
        (fun i p => ((ha i).auxiliary p).1) hr
        (fun i => by linarith [(ha i).charge.2])
        (fun i p => by linarith [((ha i).auxiliary p).2.2])
        (by intro d hd; rw [hq] at hd; contradiction)
      obtain ⟨tail₀, he₀, hd₀⟩ := ih (quietAt a v.time) rfl
        (fun i => quietAt_ready_coordinates a i (ha i) ht.le) hr hq
      have target : u.prependQuiet (quietAt (quietAt a v.time) u.time) =
          u.prependQuiet (quietAt a u.time) := congrArg (fun b => u.prependQuiet b)
            (quietAt_quietAt a v.time u.time)
      obtain ⟨tail, heT, hdT⟩ := execution_cast_target_events tail₀ target
      have he := heT.trans he₀
      have hd := hdT.trans hd₀
      let lifted := Execution.cons (.flow (f.prependQuiet g hstart rfl)) tail
      refine ⟨lifted, ?_, ?_⟩
      · simpa only [lifted, Execution.ledger, Ledger.add, Move.ledger, Flow.ledger,
          List.nil_append, List.map_nil] using he
      · simpa only [lifted, Execution.deliveries, Move.deliveries,
          List.nil_append, List.map_nil] using hd
    | jump j =>
      obtain ⟨step, heS, hdS⟩ := j.prependQuiet a global hroute
      obtain ⟨tail, he, hd⟩ := ih a (j.time_unchanged.trans hstart) ha hr hq
      let lifted := Execution.cons (.jump step) tail
      refine ⟨lifted, ?_, ?_⟩
      · change step.ledger.emissions ++ tail.ledger.emissions = _
        rw [heS, he]
        exact List.map_append.symm
      · change step.deliveries ++ tail.deliveries = _
        rw [hdS, hd]
        exact List.map_append.symm

end KernelR.Hybrid
