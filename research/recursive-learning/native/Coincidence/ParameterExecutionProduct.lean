import KernelR.HybridParameterUniversalExecution
import KernelR.HybridTwoCellJumpProduct

/-! Synchronized products of independent one-cell executions with realized
thresholds. The two local delivery queues share the joint clock. -/

namespace KernelR.Hybrid
open Set MeasureTheory

private noncomputable def ParameterFlow.prefix {n θ s u} (f : @ParameterFlow n θ s u) {t : ℝ}
    (hstart : s.time < t) (hend : t ≤ u.time) : ParameterFlow θ s (f.at t) where
  positive := hstart
  path := f.path
  initial := f.initial
  final := rfl
  main_fixed := rfl
  aux_fixed := rfl
  raw_fixed := rfl
  queue_fixed := rfl
  continuous := fun i c => (f.continuous i c).mono (Icc_subset_Icc le_rfl hend)
  integrable := fun i c => (f.integrable i c).mono_set (by
    dsimp only [ParameterFlow.at]
    rw [uIcc_of_le hstart.le, uIcc_of_le f.positive.le]
    exact Icc_subset_Icc le_rfl hend)
  mark_integrable := fun i p => (f.mark_integrable i p).mono_set (by
    dsimp only [ParameterFlow.at]
    rw [uIcc_of_le hstart.le, uIcc_of_le f.positive.le]
    exact Icc_subset_Icc le_rfl hend)
  integral_eq := fun v hv i c => f.integral_eq v ⟨hv.1, hv.2.trans hend⟩ i c
  guards := fun v hv => f.guards v ⟨hv.1, hv.2.trans_le hend⟩
  raw_support := fun i p origin hraw =>
    ⟨(f.raw_support i p origin hraw).1, hend.trans (f.raw_support i p origin hraw).2⟩
  pending_urgent := fun d hd => hend.trans (f.pending_urgent d hd)

private noncomputable def ParameterFlow.productWithQueue {θA θB : Fin 1 → Parameters} {sA uA sB uB : Snapshot 1}
    (fA : ParameterFlow θA sA uA) (fB : ParameterFlow θB sB uB)
    (hstart : sA.time = sB.time) (hfinish : uA.time = uB.time)
    (Q : List (Delivery 2)) (hp : ∀ d ∈ Q, uA.time ≤ d.due) :
    ParameterFlow (extendParameters θA (θB 0)) (sA.product sB Q) (uA.product uB Q) where
  positive := fA.positive
  path := fun t => (fA.path t).product (fB.path t)
  initial := by
    change (fA.path sA.time).product (fB.path sA.time) = sA.x.product sB.x
    rw [fA.initial,hstart,fB.initial]
  final := by
    change (fA.path uA.time).product (fB.path uA.time) = uA.x.product uB.x
    rw [fA.final,hfinish,fB.final]
  main_fixed := by
    funext i
    fin_cases i
    · exact congrFun fA.main_fixed 0
    · exact congrFun fB.main_fixed 0
  aux_fixed := by
    funext i
    fin_cases i
    · exact congrFun fA.aux_fixed 0
    · exact congrFun fB.aux_fixed 0
  raw_fixed := by
    funext i
    fin_cases i
    · exact congrFun fA.raw_fixed 0
    · exact congrFun fB.raw_fixed 0
  queue_fixed := rfl
  continuous := by
    intro i c
    fin_cases i
    · exact fA.continuous 0 c
    · change ContinuousOn (fun t => fB.path t 0 c) (Icc sA.time uA.time)
      rw [hstart,hfinish]
      exact fB.continuous 0 c
  integrable := by
    intro i c
    fin_cases i
    · exact fA.integrable 0 c
    · change IntervalIntegrable
        (fun t => field (extendParameters θA (θB 0)) (sA.product sB Q)
          ((fA.path t).product (fB.path t)) t 1 c) volume sA.time uA.time
      simp only [product_field_one]
      rw [hstart,hfinish]
      exact fB.integrable 0 c
  mark_integrable := by
    intro i p
    fin_cases i
    · exact fA.mark_integrable 0 p
    · change IntervalIntegrable
        (fun t => markAct (extendParameters θA (θB 0)) (sA.product sB Q)
          ((fA.path t).product (fB.path t)) 1 p) volume sA.time uA.time
      simp only [product_mark_one]
      rw [hstart,hfinish]
      exact fB.mark_integrable 0 p
  integral_eq := by
    intro t ht i c
    change t ∈ Icc sA.time uA.time at ht
    fin_cases i
    · change fA.path t 0 c = sA.x 0 c + ∫ v in sA.time..t,
        field (extendParameters θA (θB 0)) (sA.product sB Q)
          ((fA.path v).product (fB.path v)) v 0 c
      simp only [product_field_zero]
      exact fA.integral_eq t ht 0 c
    · change fB.path t 0 c = sB.x 0 c + ∫ v in sA.time..t,
        field (extendParameters θA (θB 0)) (sA.product sB Q)
          ((fA.path v).product (fB.path v)) v 1 c
      simp only [product_field_one]
      rw [hstart]
      exact fB.integral_eq t (by simpa only [hstart,hfinish] using ht) 0 c
  guards := by
    intro t ht
    change t ∈ Ico sA.time uA.time at ht
    have ha := fA.guards t ht
    have hb := fB.guards t (by simpa only [hstart,hfinish] using ht)
    constructor
    · intro i
      fin_cases i
      · exact ha.1 0
      · exact hb.1 0
    · intro i p
      fin_cases i
      · exact ha.2 0 p
      · exact hb.2 0 p
  raw_support := by
    intro i p origin hr
    fin_cases i
    · exact fA.raw_support 0 p origin hr
    · have h := fB.raw_support 0 p origin hr
      simpa only [Snapshot.product,hstart,hfinish] using h
  pending_urgent := hp


def Delivery.productAt (i : Fin 2) (d : Delivery 1) : Delivery 2 :=
  ⟨i, d.port, d.due⟩

noncomputable def Snapshot.independentPair (a b : Snapshot 1) : Snapshot 2 :=
  a.product b (a.pending.map (Delivery.productAt 0) ++ b.pending.map (Delivery.productAt 1))

private noncomputable def ParameterFlow.independentPair {θA θB : Fin 1 → Parameters}
    {sA uA sB uB : Snapshot 1} (fA : ParameterFlow θA sA uA) (fB : ParameterFlow θB sB uB)
    (hstart : sA.time = sB.time) (hfinish : uA.time = uB.time) :
    ParameterFlow (extendParameters θA (θB 0)) (sA.independentPair sB) (uA.independentPair uB) := by
  unfold Snapshot.independentPair
  rw [fA.queue_fixed, fB.queue_fixed]
  apply fA.productWithQueue fB hstart hfinish
  intro d hd
  simp only [List.mem_append, List.mem_map] at hd
  rcases hd with ⟨d, hd, rfl⟩ | ⟨d, hd, rfl⟩
  · exact fA.pending_urgent d hd
  · rw [hfinish]
    exact fB.pending_urgent d hd

private theorem ParameterJump.independentLeft {θA θB : Fin 1 → Parameters} {s u : Snapshot 1}
    (j : ParameterJump θA (fun _ _ => []) s u) (b : Snapshot 1) :
    ∃ k : ParameterJump (extendParameters θA (θB 0)) (fun _ _ => [])
        (s.independentPair b) (u.independentPair b),
      k.emissions = j.emissions.map (fun event => (0, event.2)) := by
  cases j with
  | fire i mode hit =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    let Q := s.pending.map (Delivery.productAt 0) ++ b.pending.map (Delivery.productAt 1)
    let post : Snapshot 1 := {(setMain s 0 .fast) with pending := s.pending ++ []}
    change ∃ k : ParameterJump (extendParameters θA (θB 0)) (fun _ _ => [])
      (s.independentPair b) (post.independentPair b), k.emissions = [(0, s.time)]
    have post_eq : post = setMain s 0 .fast := by simp [post, setMain]
    rw [post_eq]
    change ∃ k : ParameterJump (extendParameters θA (θB 0)) (fun _ _ => [])
      (s.product b Q) ((setMain s 0 .fast).product b Q), k.emissions = [(0, s.time)]
    rw [Snapshot.product_setMain_left]
    let source := (s.product b Q)
    have after : ({(setMain source 0 .fast) with pending := source.pending ++ []} : Snapshot 2) =
        setMain source 0 .fast := by simp [setMain]
    rw [← after]
    refine ⟨ParameterJump.fire (θ := extendParameters θA (θB 0)) source 0 mode hit, ?_⟩
    rfl
  | fastEnd i mode hit =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    let Q := s.pending.map (Delivery.productAt 0) ++ b.pending.map (Delivery.productAt 1)
    change ∃ k : ParameterJump (extendParameters θA (θB 0)) (fun _ _ => [])
      (s.product b Q) ((setMain s 0 .slow).product b Q), k.emissions = []
    rw [Snapshot.product_setMain_left]
    exact ⟨ParameterJump.fastEnd (s.product b Q) 0 mode hit, rfl⟩
  | reopen i mode hit =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    let Q := s.pending.map (Delivery.productAt 0) ++ b.pending.map (Delivery.productAt 1)
    change ∃ k : ParameterJump (extendParameters θA (θB 0)) (fun _ _ => [])
      (s.product b Q) ((setMain s 0 .ready).product b Q), k.emissions = []
    rw [Snapshot.product_setMain_left]
    exact ⟨ParameterJump.reopen (s.product b Q) 0 mode hit, rfl⟩
  | mark i p mode hit =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    let Q := s.pending.map (Delivery.productAt 0) ++ b.pending.map (Delivery.productAt 1)
    change ∃ k : ParameterJump (extendParameters θA (θB 0)) (fun _ _ => [])
      (s.product b Q) ((setAux s 0 p .mark).product b Q), k.emissions = []
    rw [Snapshot.product_setAux_left]
    exact ⟨ParameterJump.mark (s.product b Q) 0 p mode hit, rfl⟩
  | silent i p mode hit =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    let Q := s.pending.map (Delivery.productAt 0) ++ b.pending.map (Delivery.productAt 1)
    change ∃ k : ParameterJump (extendParameters θA (θB 0)) (fun _ _ => [])
      (s.product b Q) ((setAux s 0 p .silent).product b Q), k.emissions = []
    rw [Snapshot.product_setAux_left]
    exact ⟨ParameterJump.silent (s.product b Q) 0 p mode hit, rfl⟩
  | error i p mode hit =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    let Q := s.pending.map (Delivery.productAt 0) ++ b.pending.map (Delivery.productAt 1)
    change ∃ k : ParameterJump (extendParameters θA (θB 0)) (fun _ _ => [])
      (s.product b Q) ((setAux s 0 p .error).product b Q), k.emissions = []
    rw [Snapshot.product_setAux_left]
    exact ⟨ParameterJump.error (s.product b Q) 0 p mode hit, rfl⟩
  | auxReady i p mode hit =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    let Q := s.pending.map (Delivery.productAt 0) ++ b.pending.map (Delivery.productAt 1)
    change ∃ k : ParameterJump (extendParameters θA (θB 0)) (fun _ _ => [])
      (s.product b Q) ((setAux s 0 p .ready).product b Q), k.emissions = []
    rw [Snapshot.product_setAux_left]
    exact ⟨ParameterJump.auxReady (s.product b Q) 0 p mode hit, rfl⟩
  | rawEnd i p origin active due =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    let Q := s.pending.map (Delivery.productAt 0) ++ b.pending.map (Delivery.productAt 1)
    change ∃ k : ParameterJump (extendParameters θA (θB 0)) (fun _ _ => [])
      (s.product b Q) ((setRaw s 0 p none).product b Q), k.emissions = []
    rw [Snapshot.product_setRaw_left]
    exact ⟨ParameterJump.rawEnd (s.product b Q) 0 p origin active due, rfl⟩
  | arrive d before after queue due free =>
    have hi : d.cell = 0 := Subsingleton.elim _ _
    let A := before.map (Delivery.productAt 0)
    let B := after.map (Delivery.productAt 0) ++ b.pending.map (Delivery.productAt 1)
    let Q := A ++ B
    change ∃ k : ParameterJump (extendParameters θA (θB 0)) (fun _ _ => [])
        (s.independentPair b) ((setRaw s d.cell d.port (some s.time)).product b
          ((before ++ after).map (Delivery.productAt 0) ++ b.pending.map (Delivery.productAt 1))),
      k.emissions = []
    have queues : (before ++ after).map (Delivery.productAt 0) ++ b.pending.map (Delivery.productAt 1) = Q :=
      by simp [Q, A, B, List.append_assoc]
    rw [hi, queues, Snapshot.product_setRaw_left]
    exact ⟨ParameterJump.arrive (s.independentPair b) (d.productAt 0) A B
      (by simp [Snapshot.independentPair, Snapshot.product, queue, A, B, List.append_assoc])
      due (by change s.raw 0 d.port = none; simpa only [hi] using free), rfl⟩

private theorem ParameterJump.independentRight {θA θB : Fin 1 → Parameters} {s u : Snapshot 1}
    (j : ParameterJump θB (fun _ _ => []) s u) (a : Snapshot 1) (clock : a.time = s.time) :
    ∃ k : ParameterJump (extendParameters θA (θB 0)) (fun _ _ => [])
        (a.independentPair s) (a.independentPair u),
      k.emissions = j.emissions.map (fun event => (1, event.2)) := by
  cases j with
  | fire i mode hit =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    let Q := a.pending.map (Delivery.productAt 0) ++ s.pending.map (Delivery.productAt 1)
    let post : Snapshot 1 := {(setMain s 0 .fast) with pending := s.pending ++ []}
    change ∃ k : ParameterJump (extendParameters θA (θB 0)) (fun _ _ => [])
      (a.independentPair s) (a.independentPair post), k.emissions = [(1, s.time)]
    have post_eq : post = setMain s 0 .fast := by simp [post, setMain]
    rw [post_eq]
    change ∃ k : ParameterJump (extendParameters θA (θB 0)) (fun _ _ => [])
      (a.product s Q) (a.product (setMain s 0 .fast) Q), k.emissions = [(1, s.time)]
    rw [Snapshot.product_setMain_right]
    let source := (a.product s Q)
    have after : ({(setMain source 1 .fast) with pending := source.pending ++ []} : Snapshot 2) =
        setMain source 1 .fast := by simp [setMain]
    rw [← after]
    refine ⟨ParameterJump.fire (θ := extendParameters θA (θB 0)) source 1 mode hit, ?_⟩
    exact congrArg (fun t => [(1, t)]) clock
  | fastEnd i mode hit =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    let Q := a.pending.map (Delivery.productAt 0) ++ s.pending.map (Delivery.productAt 1)
    change ∃ k : ParameterJump (extendParameters θA (θB 0)) (fun _ _ => [])
      (a.product s Q) (a.product (setMain s 0 .slow) Q), k.emissions = []
    rw [Snapshot.product_setMain_right]
    exact ⟨ParameterJump.fastEnd (a.product s Q) 1 mode hit, rfl⟩
  | reopen i mode hit =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    let Q := a.pending.map (Delivery.productAt 0) ++ s.pending.map (Delivery.productAt 1)
    change ∃ k : ParameterJump (extendParameters θA (θB 0)) (fun _ _ => [])
      (a.product s Q) (a.product (setMain s 0 .ready) Q), k.emissions = []
    rw [Snapshot.product_setMain_right]
    exact ⟨ParameterJump.reopen (a.product s Q) 1 mode hit, rfl⟩
  | mark i p mode hit =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    let Q := a.pending.map (Delivery.productAt 0) ++ s.pending.map (Delivery.productAt 1)
    change ∃ k : ParameterJump (extendParameters θA (θB 0)) (fun _ _ => [])
      (a.product s Q) (a.product (setAux s 0 p .mark) Q), k.emissions = []
    rw [Snapshot.product_setAux_right]
    exact ⟨ParameterJump.mark (a.product s Q) 1 p mode hit, rfl⟩
  | silent i p mode hit =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    let Q := a.pending.map (Delivery.productAt 0) ++ s.pending.map (Delivery.productAt 1)
    change ∃ k : ParameterJump (extendParameters θA (θB 0)) (fun _ _ => [])
      (a.product s Q) (a.product (setAux s 0 p .silent) Q), k.emissions = []
    rw [Snapshot.product_setAux_right]
    exact ⟨ParameterJump.silent (a.product s Q) 1 p mode hit, rfl⟩
  | error i p mode hit =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    let Q := a.pending.map (Delivery.productAt 0) ++ s.pending.map (Delivery.productAt 1)
    change ∃ k : ParameterJump (extendParameters θA (θB 0)) (fun _ _ => [])
      (a.product s Q) (a.product (setAux s 0 p .error) Q), k.emissions = []
    rw [Snapshot.product_setAux_right]
    exact ⟨ParameterJump.error (a.product s Q) 1 p mode hit, rfl⟩
  | auxReady i p mode hit =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    let Q := a.pending.map (Delivery.productAt 0) ++ s.pending.map (Delivery.productAt 1)
    change ∃ k : ParameterJump (extendParameters θA (θB 0)) (fun _ _ => [])
      (a.product s Q) (a.product (setAux s 0 p .ready) Q), k.emissions = []
    rw [Snapshot.product_setAux_right]
    exact ⟨ParameterJump.auxReady (a.product s Q) 1 p mode hit, rfl⟩
  | rawEnd i p origin active due =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    let Q := a.pending.map (Delivery.productAt 0) ++ s.pending.map (Delivery.productAt 1)
    change ∃ k : ParameterJump (extendParameters θA (θB 0)) (fun _ _ => [])
      (a.product s Q) (a.product (setRaw s 0 p none) Q), k.emissions = []
    rw [Snapshot.product_setRaw_right]
    exact ⟨ParameterJump.rawEnd (a.product s Q) 1 p origin active (clock.trans due), rfl⟩
  | arrive d before after queue due free =>
    have hi : d.cell = 0 := Subsingleton.elim _ _
    let A := a.pending.map (Delivery.productAt 0) ++ before.map (Delivery.productAt 1)
    let B := after.map (Delivery.productAt 1)
    let Q := A ++ B
    change ∃ k : ParameterJump (extendParameters θA (θB 0)) (fun _ _ => [])
        (a.independentPair s)
        (a.product (setRaw s d.cell d.port (some s.time))
          (a.pending.map (Delivery.productAt 0) ++ (before ++ after).map (Delivery.productAt 1))),
      k.emissions = []
    have queues : a.pending.map (Delivery.productAt 0) ++ (before ++ after).map (Delivery.productAt 1) = Q :=
      by simp [Q, A, B, List.append_assoc]
    rw [hi, queues, Snapshot.product_setRaw_right, ← clock]
    exact ⟨ParameterJump.arrive (a.independentPair s) (d.productAt 1) A B
      (by simp [Snapshot.independentPair, Snapshot.product, queue, A, B, List.append_assoc])
      (due.trans clock.symm) (by change s.raw 0 d.port = none; simpa only [hi] using free), rfl⟩

private def datesAt {n : ℕ} (i : Fin n) (events : List (Fin n × ℝ)) : List ℝ :=
  (events.filter (fun event => event.1 = i)).map Prod.snd

private theorem datesAt_append {n : ℕ} (i : Fin n) (xs ys : List (Fin n × ℝ)) :
    datesAt i (xs ++ ys) = datesAt i xs ++ datesAt i ys := by
  simp [datesAt]

private theorem datesAt_map_product (i j : Fin 2) (xs : List (Fin 1 × ℝ)) :
    datesAt i (xs.map (fun event => (j, event.2))) = if j = i then datesAt 0 xs else [] := by
  induction xs with
  | nil => by_cases h : j = i <;> simp [h, datesAt]
  | cons x xs ih =>
    have hx : x.1 = 0 := Subsingleton.elim _ _
    by_cases h : j = i <;> simp_all [datesAt]

private theorem prependProductLeft {θA θB : Fin 1 → Parameters} {a a' uA b uB : Snapshot 1}
    (j : ParameterJump θA (fun _ _ => []) a a')
    (left : ParameterExecution θA (fun _ _ => []) a' uA)
    (right : ParameterExecution θB (fun _ _ => []) b uB)
    (tail : ∃ e : ParameterExecution (extendParameters θA (θB 0)) (fun _ _ => [])
        (a'.independentPair b) (uA.independentPair uB),
      e.emissionTimes 0 = left.emissionTimes 0 ∧ e.emissionTimes 1 = right.emissionTimes 0) :
    ∃ e : ParameterExecution (extendParameters θA (θB 0)) (fun _ _ => [])
        (a.independentPair b) (uA.independentPair uB),
      e.emissionTimes 0 = (ParameterExecution.cons (.jump j) left).emissionTimes 0 ∧
      e.emissionTimes 1 = right.emissionTimes 0 := by
  obtain ⟨k, kLabels⟩ := j.independentLeft (θB := θB) b
  obtain ⟨e, l, r⟩ := tail
  refine ⟨.cons (.jump k) e, ?_, ?_⟩
  · change datesAt 0 (k.emissions ++ e.emissions) = datesAt 0 (j.emissions ++ left.emissions)
    simp [datesAt_append, kLabels, datesAt_map_product,
      show datesAt 0 e.emissions = datesAt 0 left.emissions from l]
  · change datesAt 1 (k.emissions ++ e.emissions) = datesAt 0 right.emissions
    simp [datesAt_append, kLabels, datesAt_map_product,
      show datesAt 1 e.emissions = datesAt 0 right.emissions from r]

private theorem prependProductRight {θA θB : Fin 1 → Parameters} {a uA b b' uB : Snapshot 1}
    (j : ParameterJump θB (fun _ _ => []) b b') (clock : a.time = b.time)
    (left : ParameterExecution θA (fun _ _ => []) a uA)
    (right : ParameterExecution θB (fun _ _ => []) b' uB)
    (tail : ∃ e : ParameterExecution (extendParameters θA (θB 0)) (fun _ _ => [])
        (a.independentPair b') (uA.independentPair uB),
      e.emissionTimes 0 = left.emissionTimes 0 ∧ e.emissionTimes 1 = right.emissionTimes 0) :
    ∃ e : ParameterExecution (extendParameters θA (θB 0)) (fun _ _ => [])
        (a.independentPair b) (uA.independentPair uB),
      e.emissionTimes 0 = left.emissionTimes 0 ∧
      e.emissionTimes 1 = (ParameterExecution.cons (.jump j) right).emissionTimes 0 := by
  obtain ⟨k, kLabels⟩ := j.independentRight (θA := θA) a clock
  obtain ⟨e, l, r⟩ := tail
  refine ⟨.cons (.jump k) e, ?_, ?_⟩
  · change datesAt 0 (k.emissions ++ e.emissions) = datesAt 0 left.emissions
    simp [datesAt_append, kLabels, datesAt_map_product,
      show datesAt 0 e.emissions = datesAt 0 left.emissions from l]
  · change datesAt 1 (k.emissions ++ e.emissions) = datesAt 0 (j.emissions ++ right.emissions)
    simp [datesAt_append, kLabels, datesAt_map_product,
      show datesAt 1 e.emissions = datesAt 0 right.emissions from r]

/-- Weave independent parameterized executions with synchronized endpoints.
Cuts split a longer flow at the shorter flow's endpoint. Both per-cell
ordered firing lists are preserved. -/
theorem ParameterExecution.independentPair {θA θB : Fin 1 → Parameters}
    {sA uA sB uB : Snapshot 1}
    (left : ParameterExecution θA (fun _ _ => []) sA uA)
    (right : ParameterExecution θB (fun _ _ => []) sB uB)
    (start : sA.time = sB.time) (finish : uA.time = uB.time) :
    ∃ e : ParameterExecution (extendParameters θA (θB 0)) (fun _ _ => [])
        (sA.independentPair sB) (uA.independentPair uB),
      e.emissionTimes 0 = left.emissionTimes 0 ∧ e.emissionTimes 1 = right.emissionTimes 0 := by
  suffices all : ∀ n : ℕ, ∀ {a b : Snapshot 1}
      (l : ParameterExecution θA (fun _ _ => []) a uA)
      (r : ParameterExecution θB (fun _ _ => []) b uB),
      l.moveCount + r.moveCount = n → a.time = b.time →
      ∃ e : ParameterExecution (extendParameters θA (θB 0)) (fun _ _ => [])
          (a.independentPair b) (uA.independentPair uB),
        e.emissionTimes 0 = l.emissionTimes 0 ∧ e.emissionTimes 1 = r.emissionTimes 0 by
    exact all _ left right rfl start
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro a b l r size clock
    have recur {a' b' : Snapshot 1}
        (l' : ParameterExecution θA (fun _ _ => []) a' uA)
        (r' : ParameterExecution θB (fun _ _ => []) b' uB)
        (smaller : l'.moveCount + r'.moveCount < n) (sync : a'.time = b'.time) :=
      ih _ smaller l' r' rfl sync
    cases l with
    | nil =>
      cases r with
      | nil => exact ⟨.nil _, rfl, rfl⟩
      | @cons _ middle _ move tail =>
        cases move with
        | jump j =>
          apply prependProductRight j clock (.nil _) tail
          apply recur
          · simp only [ParameterExecution.moveCount] at size ⊢
            omega
          · exact clock.trans j.time_unchanged.symm
        | flow f => exact False.elim (by linarith [f.positive, tail.time_monotone])
    | @cons _ middleA _ moveA tailA =>
      cases moveA with
      | jump j =>
        apply prependProductLeft j tailA r
        apply recur
        · simp only [ParameterExecution.moveCount] at size ⊢
          omega
        · exact j.time_unchanged.trans clock
      | flow fA =>
        cases r with
        | nil => exact False.elim (by linarith [fA.positive, tailA.time_monotone])
        | @cons _ middleB _ moveB tailB =>
          cases moveB with
          | jump j =>
            apply prependProductRight j clock (.cons (.flow fA) tailA) tailB
            apply recur
            · simp only [ParameterExecution.moveCount] at size ⊢
              omega
            · exact clock.trans j.time_unchanged.symm
          | flow fB =>
            rcases lt_trichotomy middleA.time middleB.time with earlier | same | later
            · have pos : b.time < middleA.time := clock ▸ fA.positive
              let firstB := fB.prefix pos earlier.le
              let restB : ParameterExecution θB (fun _ _ => []) (fB.at middleA.time) uB :=
                .cons (.flow (fB.suffix pos.le earlier)) tailB
              obtain ⟨e, lEq, rEq⟩ := recur tailA restB
                (by simp only [restB, ParameterExecution.moveCount] at size ⊢; omega) rfl
              exact ⟨.cons (.flow (fA.independentPair firstB clock rfl)) e, lEq, rEq⟩
            · obtain ⟨e, lEq, rEq⟩ := recur tailA tailB
                (by simp only [ParameterExecution.moveCount] at size ⊢; omega) same
              exact ⟨.cons (.flow (fA.independentPair fB clock same)) e, lEq, rEq⟩
            · have pos : a.time < middleB.time := clock.symm ▸ fB.positive
              let firstA := fA.prefix pos later.le
              let restA : ParameterExecution θA (fun _ _ => []) (fA.at middleB.time) uA :=
                .cons (.flow (fA.suffix pos.le later)) tailA
              obtain ⟨e, lEq, rEq⟩ := recur restA tailB
                (by simp only [restA, ParameterExecution.moveCount] at size ⊢; omega) rfl
              exact ⟨.cons (.flow (firstA.independentPair fB clock rfl)) e, lEq, rEq⟩

/-- Local completeness at a shared horizon gives joint completeness. -/
theorem ParameterCompleteThrough.independentPair {θA θB : Fin 1 → Parameters}
    {sA uA sB uB : Snapshot 1} {T : ℝ}
    {left : ParameterExecution θA (fun _ _ => []) sA uA}
    {right : ParameterExecution θB (fun _ _ => []) sB uB}
    (l : ParameterCompleteThrough left T) (r : ParameterCompleteThrough right T)
    (paired : ParameterExecution (extendParameters θA (θB 0)) (fun _ _ => [])
      (sA.independentPair sB) (uA.independentPair uB)) :
    ParameterCompleteThrough paired T := by
  have date : (uA.independentPair uB).time = T := l.1
  have pending : ∀ d ∈ (uA.independentPair uB).pending, T < d.due := by
    intro d hd
    change d ∈ uA.pending.map (Delivery.productAt 0) ++ uB.pending.map (Delivery.productAt 1) at hd
    simp only [List.mem_append, List.mem_map] at hd
    rcases hd with ⟨d, hd, rfl⟩ | ⟨d, hd, rfl⟩
    · exact l.2.2 d hd
    · exact r.2.2 d hd
  refine ⟨date, ?_, pending⟩
  intro v
  refine ⟨?_⟩
  intro j
  cases j with
  | fire i mode hit =>
    fin_cases i
    · exact (l.2.1 _).false (ParameterJump.fire uA 0 mode hit)
    · exact (r.2.1 _).false (ParameterJump.fire uB 0 mode hit)
  | fastEnd i mode hit =>
    fin_cases i
    · exact (l.2.1 _).false (ParameterJump.fastEnd uA 0 mode hit)
    · exact (r.2.1 _).false (ParameterJump.fastEnd uB 0 mode hit)
  | reopen i mode hit =>
    fin_cases i
    · exact (l.2.1 _).false (ParameterJump.reopen uA 0 mode hit)
    · exact (r.2.1 _).false (ParameterJump.reopen uB 0 mode hit)
  | mark i p mode hit =>
    fin_cases i
    · exact (l.2.1 _).false (ParameterJump.mark uA 0 p mode hit)
    · exact (r.2.1 _).false (ParameterJump.mark uB 0 p mode hit)
  | silent i p mode hit =>
    fin_cases i
    · exact (l.2.1 _).false (ParameterJump.silent uA 0 p mode hit)
    · exact (r.2.1 _).false (ParameterJump.silent uB 0 p mode hit)
  | error i p mode hit =>
    fin_cases i
    · exact (l.2.1 _).false (ParameterJump.error uA 0 p mode hit)
    · exact (r.2.1 _).false (ParameterJump.error uB 0 p mode hit)
  | auxReady i p mode hit =>
    fin_cases i
    · exact (l.2.1 _).false (ParameterJump.auxReady uA 0 p mode hit)
    · exact (r.2.1 _).false (ParameterJump.auxReady uB 0 p mode hit)
  | rawEnd i p origin active due =>
    fin_cases i
    · exact (l.2.1 _).false (ParameterJump.rawEnd uA 0 p origin active due)
    · exact (r.2.1 _).false (ParameterJump.rawEnd uB 0 p origin active
        ((r.1.trans date.symm).trans due))
  | arrive d before after queue due _ =>
    have hd : d ∈ (uA.independentPair uB).pending := by
      rw [queue]
      simp
    linarith [pending d hd, due, date]

end KernelR.Hybrid
