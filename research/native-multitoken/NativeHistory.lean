import TrainingStage
import LaunchReceiptChain
import PhysicalRefinement

namespace NetworkStability.NativeMultiToken

open KernelR.Hybrid

private theorem amplitude_windows {p : Parameters N} (accepted : p.check = true) (i : Fin N) :
    0 < (p.amplitude i : ℝ) ∧ (p.amplitude i : ℝ) ≤ 7 / 6 ∧
    (p.amplitude i : ℝ) * Real.exp (3 / 5) ≤ 7 / 6 ∧
    9 / 5 ≤ launchAmplitude p i ∧ launchAmplitude p i ≤ 2 := by
  have one := Real.exp_bound (x := (3 / 5 : ℝ)) (n := 9) (by norm_num) (by decide)
  norm_num [Finset.sum_range_succ, Nat.factorial] at one
  have oneLo : (182211 / 100000 : ℝ) ≤ Real.exp (3 / 5) := by
    linarith [(abs_le.mp one).1]
  have oneHi : Real.exp (3 / 5) ≤ (182212 / 100000 : ℝ) := by
    linarith [(abs_le.mp one).2]
  have two : (3320 / 1000 : ℝ) ≤ Real.exp (6 / 5) ∧
      Real.exp (6 / 5) ≤ (3321 / 1000 : ℝ) := by
    rw [show (6 / 5 : ℝ) = 3 / 5 + 3 / 5 by norm_num, Real.exp_add]
    constructor <;> nlinarith [mul_nonneg (Real.exp_pos (3 / 5 : ℝ)).le
      (sub_nonneg.mpr oneLo), mul_nonneg (Real.exp_pos (3 / 5 : ℝ)).le (sub_nonneg.mpr oneHi)]
  obtain ⟨lo, hi⟩ := (of_decide_eq_true accepted : p.Valid).2.1 i
  change 9 / 5 ≤ (3320 / 1000 : ℚ) * p.amplitude i at lo
  change (3321 / 1000 : ℚ) * p.amplitude i ≤ 2 at hi
  have loR : (9 / 5 : ℝ) ≤ (3320 / 1000) * (p.amplitude i : ℝ) := by
    simpa using (Rat.cast_le (K := ℝ)).mpr lo
  have hiR : (3321 / 1000 : ℝ) * (p.amplitude i : ℝ) ≤ 2 := by
    simpa using (Rat.cast_le (K := ℝ)).mpr hi
  have positive : 0 < (p.amplitude i : ℝ) := by linarith
  unfold launchAmplitude
  exact ⟨positive, by linarith, by
    linarith [mul_le_mul_of_nonneg_left oneHi positive.le], by
    linarith [mul_le_mul_of_nonneg_left two.1 positive.le], by
    linarith [mul_le_mul_of_nonneg_left two.2 positive.le]⟩

private theorem weak_headroom {x : ℝ} (window : Real.exp x ≤ 7 / 6) :
    x ≤ Real.log (6 / 5) + 1 / 1000 := by
  have lower : Real.exp x ≤ (6 / 5 : ℝ) := window.trans (by norm_num)
  rw [← Real.exp_log (by norm_num : (0 : ℝ) < 6 / 5)] at lower
  linarith [Real.exp_le_exp.mp lower]

private def waveAt (N : Nat) (date : ℝ) : List (Delivery N) :=
  waveTokens date (fun _ => 0) (List.finRange N)

private theorem waveAt_due (N : Nat) (date : ℝ) (token : Delivery N)
    (mem : token ∈ waveAt N date) : token.due = date := by
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp mem
  rfl

private theorem seed_queue (p : Parameters N) :
    (prepared p).pending = waveAt N firstDate ++ waveAt N (secondDate p) ++ waveAt N (launchDate p) := by
  simp only [prepared, seed, waveAt, waveTokens, List.map_append, List.map_map]
  all_goals rfl

/-- A native witness with the training cuts and the all-children-in-flight
cut retained as actual execution factors. -/
structure NativeHistory (p : Parameters N) where
  firstStart : Snapshot N
  start : Execution (nativeParameters N) (router p) (prepared p) firstStart
  first : TrainingStage (p := p) firstStart (secondDate p)
  second : TrainingStage (p := p) first.next (launchDate p)
  launched : Snapshot N
  wireCut : Snapshot N
  last : Snapshot N
  launchIntake : Execution (nativeParameters N) (router p) second.next launched
  launch : Execution (nativeParameters N) (router p) launched wireCut
  receipts : Execution (nativeParameters N) (router p) wireCut last
  startNoArrivals : start.deliveries = []
  startContacts : start.ContactsTransversal
  startSilent : start.ledger.emissions = []
  startGain : ∀ i q, firstStart.x i (.z q) = (prepared p).x i (.z q)
  startRecovery : ∀ i, firstStart.x i .b = (prepared p).x i .b
  firstDate : firstStart.time = NetworkStability.NativeMultiToken.firstDate
  launchContacts : launchIntake.ContactsTransversal ∧ launch.ContactsTransversal ∧ receipts.ContactsTransversal
  receiptQuiet : ReceiptQuietCut p receipts
  wireDate : wireCut.time = launchDate p + 19 / 10
  wireSection : WireSection p wireCut
  complete : CompleteThrough receipts (horizon p)
  finalQueue : last.pending = []
  launchInputs : launchIntake.deliveries = waveAt N (launchDate p)
  launchSilent : launchIntake.ledger.emissions = []
  launchNoArrivals : launch.deliveries = []
  receiptNoFires : receipts.ledger.emissions = []
  fires : ∀ i, launch.emissionTimes i = [launchDate p + latency p i]
  receiptInputs : wireCut.pending.Perm receipts.deliveries
  endpointGain : ∀ i q, last.x i (.z q) = (prepared p).x i (.z q) + if q = 0 then 6 / 5 else 0
  endpointRecovery : ∀ i, last.x i .b = 7 / 25

noncomputable def NativeHistory.throughWire {p : Parameters N} (h : NativeHistory p) :
    Execution (nativeParameters N) (router p) (prepared p) h.wireCut :=
  h.start.append
    (h.first.intake.append (h.first.wave.append (h.first.quiet.append
      (h.second.intake.append (h.second.wave.append (h.second.quiet.append
        (h.launchIntake.append h.launch)))))))

noncomputable def NativeHistory.run {p : Parameters N} (h : NativeHistory p) :
    Execution (nativeParameters N) (router p) (prepared p) h.last :=
  h.throughWire.append h.receipts

theorem NativeHistory.emissions {p : Parameters N} (h : NativeHistory p) :
    h.run.ledger.emissions = h.launch.ledger.emissions := by
  simp only [NativeHistory.run, NativeHistory.throughWire, Execution.emissions_append, h.startSilent, h.first.noFires.1, h.first.noFires.2.1,
    h.first.noFires.2.2, h.second.noFires.1, h.second.noFires.2.1, h.second.noFires.2.2,
    h.launchSilent, h.receiptNoFires, List.nil_append, List.append_nil]

theorem NativeHistory.contacts_transversal {p : Parameters N} (h : NativeHistory p) :
    h.run.ContactsTransversal := by
  simp [NativeHistory.run, NativeHistory.throughWire, h.startContacts,
    h.first.contacts.1, h.first.contacts.2.1, h.first.contacts.2.2,
    h.second.contacts.1, h.second.contacts.2.1, h.second.contacts.2.2,
    h.launchContacts.1, h.launchContacts.2.1, h.launchContacts.2.2]

theorem native_history_exists {p : Parameters N} (accepted : p.check = true) :
    Nonempty (NativeHistory p) := by
  classical
  let s := prepared p
  let box := native_box N
  have gaps := (of_decide_eq_true accepted : p.Valid).2.2.1
  have gap1 : (8 : ℝ) ≤ p.gap1 := by exact_mod_cast gaps.1
  have gap2 : (8 : ℝ) ≤ p.gap2 := by exact_mod_cast gaps.2
  have firstGap : firstDate + 15 / 2 < secondDate p := by unfold secondDate; linarith
  have secondGap : secondDate p + 15 / 2 < launchDate p := by unfold launchDate; linarith
  have future : secondDate p ≤ launchDate p := by unfold launchDate; linarith
  have ready (i : Fin N) : ReadyCoordinates s i := by
    refine ⟨rfl, ?_, fun _ => ⟨rfl, ?_⟩⟩ <;> norm_num [s, prepared, RestBand]
  have pending (token : Delivery N) (mem : token ∈ s.pending) : firstDate ≤ token.due := by
    change token ∈ (prepared p).pending at mem
    rw [seed_queue, List.append_assoc] at mem
    rcases List.mem_append.mp mem with first | rest
    · rw [waveAt_due _ _ _ first]
    · rcases List.mem_append.mp rest with second | launch
      · rw [waveAt_due _ _ _ second]; linarith
      · rw [waveAt_due _ _ _ launch]; linarith
  let initialFlow : Flow (nativeParameters N) s (quietAt s firstDate) :=
    quietFlow s (by change (0 : ℝ) < firstDate; norm_num [firstDate])
      (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ => by norm_num [s, prepared]) (fun _ _ => by norm_num [s, prepared]) pending
  let initial : Execution (nativeParameters N) (router p) s (quietAt s firstDate) :=
    .cons (.flow initialFlow) (.nil _)
  let a := quietAt s firstDate
  have rawA : RawValid a := by intro _ _ _ h; cases h
  have physA : PhysicalInvariant (nativeParameters N) a :=
    initial.physical_invariant box (prepared_physical accepted)
  have chargeA (i : Fin N) : a.x i .q = 1 / 10 := by
    change relax (1 / 2) (1 / 10) (1 / 10) 0 firstDate = _
    simp [relax]
  have ampA (i : Fin N) : Real.exp (a.x i (.z 0)) = (p.amplitude i : ℝ) := by
    change Real.exp (Real.log (p.amplitude i : ℝ)) = _
    exact Real.exp_log (amplitude_windows accepted i).1
  obtain ⟨first, queueB⟩ := training_stage_exists (p := p) box a physA rawA
    (fun i => quietAt_ready_coordinates s i (ready i) (by change (0 : ℝ) ≤ firstDate; norm_num [firstDate]))
    (fun _ _ => rfl) (fun i => by rw [ampA]; exact (amplitude_windows accepted i).2.1)
    (fun i => weak_headroom (by rw [ampA]; exact (amplitude_windows accepted i).2.1))
    (waveAt N (secondDate p) ++ waveAt N (launchDate p))
    (by change (prepared p).pending = _; rw [seed_queue, List.append_assoc]; rfl)
    (secondDate p) firstGap (by
      intro token mem
      rcases List.mem_append.mp mem with second | launch
      · rw [waveAt_due _ _ _ second]
      · rw [waveAt_due _ _ _ launch]; exact future)
  have ampB (i : Fin N) :
      Real.exp (first.next.x i (.z 0)) = (p.amplitude i : ℝ) * Real.exp (3 / 5) := by
    rw [first.gains i 0]
    simp only [ite_true, Real.exp_add, ampA]
  have headroomB (i : Fin N) : Real.exp (first.next.x i (.z 0)) ≤ 7 / 6 := by
    rw [ampB]
    exact (amplitude_windows accepted i).2.2.1
  obtain ⟨second, queueC⟩ := training_stage_exists (p := p) box first.next first.physical first.valid first.ready
    first.raw headroomB (fun i => weak_headroom (headroomB i)) (waveAt N (launchDate p))
    (by rw [queueB, first.date]; rfl) (launchDate p)
    (by rw [first.date]; exact secondGap)
    (fun token mem => by rw [waveAt_due _ _ _ mem])
  have ampC (i : Fin N) : Real.exp (second.next.x i (.z 0)) = launchAmplitude p i := by
    unfold launchAmplitude
    rw [second.gains i 0, ite_eq_left rfl, Real.exp_add, ampB, mul_assoc, ← Real.exp_add]
    norm_num
  have firstCharge (i : Fin N) :
      first.next.x i .q = afterSilent (1 / 10) (p.amplitude i : ℝ) p.gap1 := by
    rw [first.charge, chargeA, ampA]
    simp [secondDate, show a.time = firstDate from rfl]
  have secondCharge (i : Fin N) : second.next.x i .q = launchCharge p i := by
    rw [second.charge, firstCharge, ampB, launchCharge]
    simp [launchDate, first.date]
  have recoveryC (i : Fin N) : second.next.x i .b = 9 / 50 :=
    (second.recovery i).trans (first.recovery i)
  let b := admittedWave second.next (fun _ => 0) (List.finRange N) []
  obtain ⟨intake, intakeWord, noIntakeFire, intakeContacts⟩ :=
    admit_wave (θ := nativeParameters N) (route := router p) second.next (fun _ => 0)
      (List.finRange N) (List.nodup_finRange N) [] (by rw [queueC, List.append_nil, second.date]; rfl)
      (fun i _ => second.raw i 0)
  have bWindow (i : Fin N) : 9 / 5 ≤ Real.exp (b.x i (.z 0)) ∧ Real.exp (b.x i (.z 0)) ≤ 2 := by
    change 9 / 5 ≤ Real.exp (second.next.x i (.z 0)) ∧ Real.exp (second.next.x i (.z 0)) ≤ 2
    rw [ampC]
    exact (amplitude_windows accepted i).2.2.2
  have sectionB (i : Fin N) : PreparedSection b i :=
    ⟨(second.ready i).ready, (second.ready i).charge, by
      change 17999 / 100000 ≤ second.next.x i .b ∧ second.next.x i .b ≤ 18001 / 100000
      rw [recoveryC]
      norm_num, (second.ready i).auxiliary⟩
  obtain ⟨wire, last, launch, receipts, wireDate, complete, finalQueue, noArrive, noFire, fires, paid,
      wireSection, launchContacts, receiptContacts, receiptQuiet, outcome⟩ :=
    launch_receipt_chain accepted box b (intake.physical_invariant box second.physical)
      (intake.raw_valid second.valid) second.date sectionB secondCharge ampC bWindow recoveryC
      (fun i => by simp [b, admittedWave]) (fun i q ne => by simp [b, admittedWave, ne, second.raw]) rfl
  refine ⟨{
    firstStart := a, start := initial, first := first, second := second, launched := b
    wireCut := wire, last := last, launchIntake := intake, launch := launch, receipts := receipts
    startNoArrivals := rfl, startSilent := rfl, startContacts := trivial, startGain := fun _ _ => rfl,
    startRecovery := fun _ => rfl, firstDate := rfl,
    launchContacts := ⟨intakeContacts, launchContacts, receiptContacts⟩, receiptQuiet := receiptQuiet
    wireDate := wireDate, wireSection := wireSection
    complete := complete, finalQueue := finalQueue
    launchInputs := intakeWord.trans (by rw [second.date]; rfl), launchSilent := noIntakeFire
    launchNoArrivals := noArrive, receiptNoFires := noFire, fires := fires, receiptInputs := paid
    endpointGain := ?_, endpointRecovery := ?_ }⟩
  · intro i q
    have h := ((outcome i).2.2.2 q).1
    change last.x i (.z q) = second.next.x i (.z q) at h
    have startGain : a.x i (.z q) = (prepared p).x i (.z q) := rfl
    rw [h, second.gains, first.gains, startGain]
    by_cases selected : q = 0
    · simp only [ite_eq_left selected]
      ring
    · simp [selected]
  · intro i
    have warm := receipts.recovery_balance i
    rw [(outcome i).2.2.1, wireSection.recovery i] at warm
    linarith

/-- Parameter headroom at the prepared snapshot and at the first settled
training cut. These are the anchors of the two exact weak-pulse windows. -/
theorem native_training_headroom {p : Parameters N} (accepted : p.check = true)
    (history : NativeHistory p) (i : Fin N) :
    (prepared p).x i (.z 0) ≤ Real.log (6 / 5) + 1 / 1000 ∧
      history.first.settled.x i (.z 0) ≤ Real.log (6 / 5) + 1 / 1000 := by
  obtain ⟨positive, first, second, _⟩ := amplitude_windows accepted i
  have initial : Real.exp ((prepared p).x i (.z 0)) = (p.amplitude i : ℝ) := by
    change Real.exp (Real.log (p.amplitude i : ℝ)) = _
    exact Real.exp_log positive
  refine ⟨weak_headroom (initial ▸ first), weak_headroom ?_⟩
  rw [history.first.settledGains, history.startGain, ite_eq_left rfl, Real.exp_add, initial]
  exact second

theorem native_endpoint_below_rail {p : Parameters N} (accepted : p.check = true)
    (history : NativeHistory p) : BelowRail history.last.x := by
  constructor
  · intro i q
    rw [history.endpointGain]
    by_cases selected : q = 0
    · subst q
      have positive := (amplitude_windows accepted i).1
      have bound := (amplitude_windows accepted i).2.2.2.2
      change Real.log (p.amplitude i : ℝ) + (6 / 5) < Real.log 4
      apply Real.exp_lt_exp.mp
      rw [Real.exp_add, Real.exp_log positive, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
      exact bound.trans_lt (by norm_num)
    · have bound : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
      simpa [prepared, selected, nativeParameters, KernelR.FutureControls.parameters] using bound
  · intro i
    rw [history.endpointRecovery]
    norm_num

end NetworkStability.NativeMultiToken
