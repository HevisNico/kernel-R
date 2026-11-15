import MonotoneSupport

namespace LearnedCoincidence.MonotoneDNF

open TwoLayer (SlotTiming ReadObservation CalibratedAdditiveRead RoutedBatch
  observedCount settledCount LearningCertificate)

private theorem calibrated_fire {p : Parameters N M} {i : Fin N} {k : Nat} {x : Pattern M}
    {budget : Nat} {timing : SlotTiming} {r : ReadObservation M}
    (h : CalibratedAdditiveRead p i k x budget timing r)
    (margin : p.threshold i + budget ≤ score p i k x) : r.fired = true := by
  rw [h.2.2.2.2.1]
  have lower := h.2.2.2.2.2.1
  exact decide_eq_true (by omega)

private theorem calibrated_silence {p : Parameters N M} {i : Fin N} {k : Nat} {x : Pattern M}
    {budget : Nat} {timing : SlotTiming} {r : ReadObservation M}
    (h : CalibratedAdditiveRead p i k x budget timing r)
    (margin : score p i k x + budget < p.threshold i) : r.fired = false := by
  rw [h.2.2.2.2.1]
  have upper := h.2.2.2.2.2.2
  exact decide_eq_false (by omega)

private def ReadMargin (level budget value : Nat) (decision : Bool) : Prop :=
  if decision then level + budget ≤ value else value + budget < level

private theorem read_of_margin {p : Parameters N M} {i : Fin N} {k : Nat} {x : Pattern M}
    {budget : Nat} {timing : SlotTiming} {r : ReadObservation M} {decision : Bool}
    (h : CalibratedAdditiveRead p i k x budget timing r)
    (margin : ReadMargin (p.threshold i) budget (score p i k x) decision) : r.fired = decision := by
  cases decision
  · exact calibrated_silence h margin
  · exact calibrated_fire h margin

private theorem threshold_of_margin {level budget value : Nat} {decision : Bool}
    (margin : ReadMargin level budget value decision) : decide (level ≤ value) = decision := by
  cases decision
  · have h : value + budget < level := margin
    exact decide_eq_false (by omega)
  · have h : level + budget ≤ value := margin
    exact decide_eq_true (by omega)

private theorem first_certificate (p : Parameters A M) (check : checkConjunctions p = true)
    (timing : SlotTiming) (trace : Nat → Fin A → ReadObservation M)
    (training : ∀ r, r ≤ p.maxWrites → ∀ a,
      CalibratedAdditiveRead p a (observedCount trace a r) (p.target a)
        (p.trainingError a) timing (trace r a)) :
    LearningCertificate p trace := by
  simp only [checkConjunctions, Bool.and_eq_true] at check
  obtain ⟨⟨⟨⟨⟨_, early⟩, stop⟩, rail⟩, _⟩, _⟩ := check
  have stops (i : Fin A) : need p i ≤ p.maxWrites ∧
      p.threshold i + p.trainingError i ≤ score p i (need p i) (p.target i) := by
    have h := Bool.and_eq_true_iff.mp (allPorts stop i)
    exact ⟨(of_decide_eq_true h.1 : 0 < need p i ∧ need p i ≤ p.maxWrites).2,
      of_decide_eq_true h.2⟩
  have step (r : Nat) (bound : r ≤ p.maxWrites) (i : Fin A)
      (count : observedCount trace i r = min r (need p i)) :
      (trace r i).fired = decide (need p i ≤ r) := by
    have read := training r bound i
    rw [count] at read
    by_cases stopped : need p i ≤ r
    · rw [Nat.min_eq_right stopped] at read
      rw [decide_eq_true stopped]
      exact calibrated_fire read (stops i).2
    · have before : r < need p i := by omega
      have h := List.all_eq_true.mp (allPorts early i) r (List.mem_range.mpr before)
      rw [Nat.min_eq_left (Nat.le_of_lt before)] at read
      rw [decide_eq_false stopped]
      exact calibrated_silence read (of_decide_eq_true h)
  have count (r : Nat) (bound : r ≤ p.maxWrites + 1) (i : Fin A) :
      observedCount trace i r = min r (need p i) := by
    induction r with
    | zero => simp [observedCount]
    | succ r ih =>
      have prior := ih (by omega)
      rw [observedCount, prior, step r (by omega) i prior]
      by_cases stopped : need p i ≤ r
      · have next : need p i ≤ r + 1 := by omega
        simp [stopped, Nat.min_eq_right next]
      · have now : r ≤ need p i := by omega
        have next : r + 1 ≤ need p i := by omega
        simp [stopped, Nat.min_eq_left now, Nat.min_eq_left next]
  refine ⟨count, fun r bound i => step r bound i (count r (by omega) i), ?_⟩
  intro r bound i j
  rw [count r bound i]
  have le : min r (need p i) ≤ need p i := Nat.min_le_right _ _
  refine ⟨?_, Nat.lt_of_le_of_lt (gain_le p i j le) (of_decide_eq_true (allPorts (allPorts rail i) j))⟩
  unfold portWrites
  split
  · exact Nat.le_trans le (stops i).1
  · exact Nat.zero_le _

private theorem first_margin (p : Parameters A M) (check : checkConjunctions p = true)
    (i : Fin A) (x : Pattern M) :
    ReadMargin (p.threshold i) (p.testingError i) (score p i (need p i) x) (predicted p x i) := by
  simp only [checkConjunctions, Bool.and_eq_true] at check
  obtain ⟨⟨_, positive⟩, negative⟩ := check
  unfold predicted
  cases hit : contains x (p.target i) with
  | true =>
    have margin : p.threshold i + p.testingError i ≤ score p i (need p i) (p.target i) :=
      of_decide_eq_true (allPorts positive i)
    exact Nat.le_trans margin (score_le p i (Nat.le_refl _) (contains_iff.mp hit))
  | false =>
    obtain ⟨j, active, absent⟩ := missingPort hit
    have h := List.all_eq_true.mp (allPorts negative i) j
      (List.mem_filter.mpr ⟨List.mem_finRange j, active⟩)
    have margin : score p i (need p i) (omits j) + p.testingError i < p.threshold i :=
      of_decide_eq_true h
    have subset (q : Fin M) (on : x q = true) : omits j q = true := by
      apply decide_eq_true
      intro same
      subst q
      rw [absent] at on
      contradiction
    have smaller := score_le p i (Nat.le_refl (need p i)) subset
    exact Nat.lt_of_le_of_lt (Nat.add_le_add_right smaller _) margin

private theorem first_read (p : Parameters A M) (check : checkConjunctions p = true)
    {timing : SlotTiming} {trace : Nat → Fin A → ReadObservation M}
    (cert : LearningCertificate p trace) {i : Fin A} {x : Pattern M} {r : ReadObservation M}
    (read : CalibratedAdditiveRead p i (settledCount p trace i) x (p.testingError i) timing r) :
    r.fired = predicted p x i := by
  have checkParts := check
  simp only [checkConjunctions, Bool.and_eq_true] at checkParts
  obtain ⟨⟨⟨⟨_, stop⟩, _⟩, _⟩, _⟩ := checkParts
  have stopBound : need p i ≤ p.maxWrites :=
    (of_decide_eq_true (Bool.and_eq_true_iff.mp (allPorts stop i)).1 :
      0 < need p i ∧ need p i ≤ p.maxWrites).2
  have enough : need p i ≤ p.maxWrites + 1 := by omega
  unfold settledCount at read
  rw [cert.1 _ (Nat.le_refl _) i, Nat.min_eq_right enough] at read
  exact read_of_margin read (first_margin p check i x)

private theorem routed_input {delay : Fin A → Rat} {left : Fin A → ReadObservation M}
    {right : ReadObservation A} (route : RoutedBatch delay left right) (a : Fin A) :
    right.input a = (left a).fired := by
  unfold ReadObservation.input ReadObservation.fired
  rw [route a]
  cases (left a).emissions <;> rfl

private theorem view_gains (p : Disjunctions B A) (w : Counts B A) (i : Fin B) :
    gain (readView p w) i 0 = fun a => lineGain p i a (w i a) := by
  funext a
  have noWrite : portWrites (readView p w) i a 0 = 0 := by
    unfold portWrites
    split <;> rfl
  unfold gain
  rw [noWrite]
  simp [readView]

private theorem singleton_score (p : Disjunctions B A) (w : Counts B A) (i : Fin B) (a : Fin A) :
    score (readView p w) i 0 (singleton a) = lineScore p i a (w i a) := by
  unfold score singleton
  rw [filter_single (List.nodup_finRange A) (List.mem_finRange a), view_gains]
  simp [readView, lineScore]

private theorem line_gain_le (p : Disjunctions B A) (i : Fin B) (a : Fin A) {k l : Nat}
    (hle : k ≤ l) : lineGain p i a k ≤ lineGain p i a l :=
  Nat.add_le_add_left (Nat.mul_le_mul_left _ hle) _

private theorem disjunction_cell {p : Disjunctions B A} (check : p.check = true) (i : Fin B) :
    ((List.finRange A).all (fun a => decide (lineGain p i a (expectedWrites p i a) < p.rail))) = true ∧
    (if p.alwaysFire i then
      !(List.finRange A).any (p.lines i) && robustFire (p.threshold i) (p.testingError i) (p.help i)
    else
      (List.finRange A).all (fun a => !p.lines i a ||
        (decide (0 < lineNeed p i a ∧ lineNeed p i a ≤ p.maxWrites) &&
          (List.range (lineNeed p i a)).all (fun n =>
            robustSilence (p.threshold i) (p.trainingError i) (lineScore p i a n)) &&
          robustFire (p.threshold i) (p.trainingError i) (lineScore p i a (lineNeed p i a)) &&
          robustFire (p.threshold i) (p.testingError i) (lineScore p i a (lineNeed p i a)))) &&
      robustSilence (p.threshold i) (p.testingError i)
        (score (readView p (expectedWrites p)) i 0 (fun a => !p.lines i a))) = true := by
  unfold Disjunctions.check at check
  exact Bool.and_eq_true_iff.mp (allPorts (Bool.and_eq_true_iff.mp check).2 i)

private theorem line_certificate {p : Disjunctions B A} (check : p.check = true) (i : Fin B) (a : Fin A)
    (selected : p.lines i a = true) :
    lineNeed p i a ≤ p.maxWrites ∧
    (∀ k, k < lineNeed p i a → lineScore p i a k + p.trainingError i < p.threshold i) ∧
    p.threshold i + p.trainingError i ≤ lineScore p i a (lineNeed p i a) ∧
    p.threshold i + p.testingError i ≤ lineScore p i a (lineNeed p i a) := by
  have cell := (disjunction_cell check i).2
  cases mode : p.alwaysFire i with
  | true =>
    rw [ite_eq_left mode] at cell
    have noLines := (Bool.and_eq_true_iff.mp cell).1
    have existsLine : (List.finRange A).any (p.lines i) = true :=
      List.any_eq_true.mpr ⟨a, List.mem_finRange a, selected⟩
    simp [existsLine] at noLines
  | false =>
    rw [ite_eq_right (by simp [mode])] at cell
    have line := allPorts (Bool.and_eq_true_iff.mp cell).1 a
    rw [selected] at line
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true] at line
    exact ⟨(of_decide_eq_true line.1.1.1 : 0 < lineNeed p i a ∧ lineNeed p i a ≤ p.maxWrites).2,
      fun k before => of_decide_eq_true (List.all_eq_true.mp line.1.1.2 k (List.mem_range.mpr before)),
      of_decide_eq_true line.1.2, of_decide_eq_true line.2⟩

private theorem expected_le {p : Disjunctions B A} (check : p.check = true) (i : Fin B) (a : Fin A) :
    expectedWrites p i a ≤ p.maxWrites := by
  unfold expectedWrites
  split
  · next selected => exact (line_certificate check i a selected).1
  · exact Nat.zero_le _

private theorem lesson_selected {p : Cascade A B M} {n : Nat} {L : Lesson A B}
    (atIndex : (lessons p)[n]? = some L) : p.second.lines L.cell L.line = true := by
  obtain ⟨within, equal⟩ := List.getElem?_eq_some_iff.mp atIndex
  have member : L ∈ lessons p := equal ▸ List.getElem_mem within
  unfold lessons at member
  obtain ⟨_, _, member⟩ := List.mem_flatMap.mp member
  obtain ⟨_, _, member⟩ := List.mem_flatMap.mp member
  obtain ⟨a, selected, rfl⟩ := List.mem_map.mp member
  exact (List.mem_filter.mp selected).2

private theorem addresses_advance {p : Cascade A B M} {n : Nat} {L : Lesson A B}
    (atIndex : (lessons p)[n]? = some L) (i : Fin B) (a : Fin A) :
    attempts p (n + 1) i a = attempts p n i a + if L.cell = i ∧ L.line = a then 1 else 0 := by
  obtain ⟨within, equal⟩ := List.getElem?_eq_some_iff.mp atIndex
  unfold attempts
  rw [List.take_succ_eq_append_getElem within, equal, List.filter_append, List.length_append]
  by_cases addressed : L.cell = i ∧ L.line = a <;> simp [addressed]

private theorem repeated_block_count {α β : Type} (rounds : List α) (block : List β) (f : β → Bool) :
    ((rounds.flatMap (fun _ => block)).filter f).length = rounds.length * (block.filter f).length := by
  induction rounds with
  | nil => simp
  | cons r rest ih => simp [ih, Nat.succ_mul, Nat.add_comm]

private theorem count_full_schedule (p : Cascade A B M) (i : Fin B) (a : Fin A)
    (selected : p.second.lines i a = true) :
    attempts p (lessons p).length i a = p.second.maxWrites + 1 := by
  let cellBlock (j : Fin B) := ((List.finRange A).filter (p.second.lines j)).map (fun b : Fin A => (⟨j, b⟩ : Lesson A B))
  let matchPair (L : Lesson A B) := decide (L.cell = i ∧ L.line = a)
  have oneCell (j : Fin B) :
      (cellBlock j).filter matchPair = (if j = i then [⟨i, a⟩] else []) := by
    unfold cellBlock matchPair
    rw [List.filter_map]
    by_cases equal : j = i
    · subst j
      rw [List.filter_filter]
      simp only [Function.comp_def, true_and, ↓reduceIte]
      have check : (List.finRange A).filter
          (fun b => decide (b = a) && p.second.lines i b) =
          (List.finRange A).filter (fun b => decide (b = a)) := by
        apply List.filter_congr
        intro b _
        by_cases eq : b = a
        · subst b
          simp [selected]
        · simp [eq]
      rw [check, filter_single (List.nodup_finRange A) (List.mem_finRange a)]
      rfl
    · simp [equal, Function.comp_def]
  have measure (cells : List (Fin B)) :
      (cells.flatMap fun j => (cellBlock j).filter matchPair).length =
        (cells.filter (fun j => decide (j = i))).length := by
    induction cells with
    | nil => rfl
    | cons j rest ih =>
      rw [List.flatMap_cons, List.length_append, ih, oneCell]
      by_cases h : j = i <;> simp [h, Nat.add_comm]
  unfold attempts
  rw [List.take_length]
  change (((List.range (p.second.maxWrites + 1)).flatMap
    (fun _ => (List.finRange B).flatMap cellBlock)).filter matchPair).length = _
  rw [repeated_block_count, List.filter_flatMap, measure,
    filter_single (List.nodup_finRange B) (List.mem_finRange i)]
  simp

private theorem singleton_teaching {p : Cascade A B M}
    (firstCheck : checkConjunctions p.first = true) (reachable : p.reachable = true)
    {o : Observations A B M} {left right : SlotTiming}
    (calibration : CascadeCalibration p left right o)
    (cert : LearningCertificate p.first o.firstTrain) {n : Nat} {L : Lesson A B}
    (atIndex : (lessons p)[n]? = some L) : (o.secondTrain n).input = singleton L.line := by
  have selected := lesson_selected atIndex
  have used : (List.finRange B).any (fun i => p.second.lines i L.line) = true :=
    List.any_eq_true.mpr ⟨L.cell, List.mem_finRange L.cell, selected⟩
  have reach := allPorts reachable L.line
  rw [used] at reach
  simp only [Bool.not_true, Bool.false_or] at reach
  obtain ⟨teach, route, _⟩ := calibration.2.1 n L atIndex
  funext a
  rw [routed_input route a, first_read p.first firstCheck cert (teach a)]
  exact (beq_iff_eq ..).mp (allPorts reach a)

private theorem second_decision {p : Cascade A B M} (check : p.second.check = true)
    {o : Observations A B M} {left right : SlotTiming}
    (calibration : CascadeCalibration p left right o) {n : Nat} {L : Lesson A B}
    (atIndex : (lessons p)[n]? = some L) (isolated : (o.secondTrain n).input = singleton L.line)
    (count : lessonCounts p o n L.cell L.line =
      min (attempts p n L.cell L.line) (expectedWrites p.second L.cell L.line)) :
    (o.secondTrain n).fired = decide (lineNeed p.second L.cell L.line ≤ attempts p n L.cell L.line) := by
  have selected := lesson_selected atIndex
  obtain ⟨_, early, firesAtNeed, _⟩ := line_certificate check L.cell L.line selected
  have read := (calibration.2.1 n L atIndex).2.2
  rw [isolated] at read
  have scoreEq :
      score (readView p.second (lessonCounts p o n)) L.cell 0 (singleton L.line) =
      lineScore p.second L.cell L.line (min (attempts p n L.cell L.line) (lineNeed p.second L.cell L.line)) := by
    rw [singleton_score, count]
    simp [expectedWrites, selected]
  by_cases stopped : lineNeed p.second L.cell L.line ≤ attempts p n L.cell L.line
  · rw [decide_eq_true stopped]
    apply calibrated_fire read
    rw [scoreEq, Nat.min_eq_right stopped]
    exact firesAtNeed
  · have before : attempts p n L.cell L.line < lineNeed p.second L.cell L.line := by omega
    rw [decide_eq_false stopped]
    apply calibrated_silence read
    rw [scoreEq, Nat.min_eq_left (Nat.le_of_lt before)]
    exact early _ before

private theorem counts_on_lessons {p : Cascade A B M} (check : p.second.check = true)
    {o : Observations A B M} {left right : SlotTiming}
    (calibration : CascadeCalibration p left right o)
    (isolation : ∀ n L, (lessons p)[n]? = some L → (o.secondTrain n).input = singleton L.line) :
    ∀ n, n ≤ (lessons p).length → ∀ i a,
      lessonCounts p o n i a = min (attempts p n i a) (expectedWrites p.second i a) := by
  intro n
  induction n with
  | zero => intro _ i a; simp [lessonCounts, attempts]
  | succ n ih =>
    intro within i a
    have lt : n < (lessons p).length := by omega
    let L := (lessons p)[n]
    have atIndex : (lessons p)[n]? = some L := List.getElem?_eq_some_iff.mpr ⟨lt, rfl⟩
    have isolated := isolation n L atIndex
    have decision := second_decision check calibration atIndex isolated (ih (by omega) L.cell L.line)
    simp only [lessonCounts, atIndex]
    rw [addresses_advance atIndex]
    unfold advance
    rw [ih (by omega), isolated, decision]
    by_cases sameCell : L.cell = i
    · subst i
      by_cases sameLine : L.line = a
      · subst a
        have selected := lesson_selected atIndex
        have expected : expectedWrites p.second L.cell L.line = lineNeed p.second L.cell L.line := by
          simp [expectedWrites, selected]
        rw [expected]
        by_cases done : lineNeed p.second L.cell L.line ≤ attempts p n L.cell L.line
        · have next : lineNeed p.second L.cell L.line ≤ attempts p n L.cell L.line + 1 := by omega
          simp [singleton, done, Nat.min_eq_right done, Nat.min_eq_right next]
        · have current : attempts p n L.cell L.line ≤ lineNeed p.second L.cell L.line := by omega
          have next : attempts p n L.cell L.line + 1 ≤ lineNeed p.second L.cell L.line := by omega
          simp [singleton, done, Nat.min_eq_left current, Nat.min_eq_left next]
      · simp [singleton, sameLine, Ne.symm sameLine]
    · simp [sameCell, Ne.symm sameCell]

private theorem completed_counts {p : Cascade A B M} {o : Observations A B M}
    (check : p.second.check = true)
    (counts : ∀ n, n ≤ (lessons p).length → ∀ i a,
      lessonCounts p o n i a = min (attempts p n i a) (expectedWrites p.second i a)) :
    ∀ i a, lessonCounts p o (lessons p).length i a = expectedWrites p.second i a := by
  intro i a
  rw [counts _ (Nat.le_refl _) i a]
  cases selected : p.second.lines i a with
  | false => simp [expectedWrites, selected]
  | true =>
    rw [count_full_schedule p i a selected]
    have bound := expected_le check i a
    exact Nat.min_eq_right (by omega)

private theorem second_margin (p : Disjunctions B A) (check : p.check = true)
    (i : Fin B) (x : Pattern A) :
    ReadMargin (p.threshold i) (p.testingError i) (score (readView p (expectedWrites p)) i 0 x)
      (p.alwaysFire i || (List.finRange A).any fun a => p.lines i a && x a) := by
  have cell := (disjunction_cell check i).2
  cases mode : p.alwaysFire i with
  | true =>
    rw [ite_eq_left mode] at cell
    have margin : p.threshold i + p.testingError i ≤ p.help i :=
      of_decide_eq_true (Bool.and_eq_true_iff.mp cell).2
    simp only [Bool.true_or]
    exact Nat.le_trans margin (Nat.le_add_right ..)
  | false =>
    rw [ite_eq_right (by simp [mode])] at cell
    simp only [Bool.false_or]
    cases active : (List.finRange A).any (fun a => p.lines i a && x a) with
    | true =>
      obtain ⟨a, _, on⟩ := List.any_eq_true.mp active
      have ⟨selected, arrived⟩ := Bool.and_eq_true_iff.mp on
      have support (b : Fin A) (on : singleton a b = true) : x b = true := by
        have same : b = a := of_decide_eq_true on
        exact same ▸ arrived
      have enough := (line_certificate check i a selected).2.2.2
      have scoreAtLine : score (readView p (expectedWrites p)) i 0 (singleton a) =
          lineScore p i a (lineNeed p i a) := by
        rw [singleton_score]
        simp [expectedWrites, selected]
      exact Nat.le_trans (scoreAtLine ▸ enough) (score_le _ i (Nat.le_refl _) support)
    | false =>
      have margin : score (readView p (expectedWrites p)) i 0 (fun a => !p.lines i a) +
          p.testingError i < p.threshold i := of_decide_eq_true (Bool.and_eq_true_iff.mp cell).2
      have support (a : Fin A) (arrived : x a = true) : (!p.lines i a) = true := by
        cases selected : p.lines i a with
        | false => rfl
        | true =>
          have h : (List.finRange A).any (fun b => p.lines i b && x b) = true :=
            List.any_eq_true.mpr ⟨a, List.mem_finRange a, Bool.and_eq_true_iff.mpr ⟨selected, arrived⟩⟩
          rw [active] at h
          contradiction
      have lesser := score_le (readView p (expectedWrites p)) i (Nat.le_refl 0) support
      exact Nat.lt_of_le_of_lt (Nat.add_le_add_right lesser _) margin

/-- At settled memory, the two guarded thresholds are increasing in their
active sets because each port contributes a natural-valued gain. -/
theorem output_monotone (p : Cascade A B M) (valid : p.Valid) (i : Fin B) :
    MonotoneFunction (output p i) := by
  intro x y included active
  simp only [Cascade.Valid, Cascade.check, Bool.and_eq_true] at valid
  obtain ⟨⟨⟨⟨firstCheck, secondCheck⟩, _⟩, _⟩, _⟩ := valid
  have firstDec (z : Pattern M) (a : Fin A) :
      decide (p.first.threshold a ≤ score p.first a (need p.first a) z) =
        predicted p.first z a := threshold_of_margin (first_margin p.first firstCheck a z)
  have upstream (a : Fin A) (firesX : predicted p.first x a = true) :
      predicted p.first y a = true := by
    rw [← firstDec x a] at firesX
    rw [← firstDec y a]
    exact decide_eq_true (Nat.le_trans (of_decide_eq_true firesX)
      (score_le p.first a (Nat.le_refl _) (contains_iff.mp included)))
  have secondDec (z : Pattern M) :
      decide (p.second.threshold i ≤ score (readView p.second (expectedWrites p.second)) i 0
        (fun a => predicted p.first z a)) = output p i z :=
    threshold_of_margin (second_margin p.second secondCheck i (fun a => predicted p.first z a))
  rw [← secondDec x] at active
  rw [← secondDec y]
  exact decide_eq_true (Nat.le_trans (of_decide_eq_true active)
    (score_le (readView p.second (expectedWrites p.second)) i (Nat.le_refl 0) upstream))

/-- The same calibrated observations that determine the routed singleton
lessons also determine every post-training decision on the Boolean cube. -/
theorem two_layer_monotone_recognition : TwoLayerMonotoneRecognition := by
  intro A B M p valid left right o _separation calibration
  simp only [Cascade.Valid, Cascade.check, Bool.and_eq_true] at valid
  obtain ⟨⟨⟨⟨firstCheck, secondCheck⟩, reachable⟩, _⟩, _⟩ := valid
  have firstCert := first_certificate p.first firstCheck left o.firstTrain calibration.1
  have isolated (n : Nat) (L : Lesson A B) (atIndex : (lessons p)[n]? = some L) :=
    singleton_teaching firstCheck reachable calibration firstCert atIndex
  have counts := counts_on_lessons secondCheck calibration isolated
  have settled := completed_counts secondCheck counts
  refine ⟨firstCert, ?_, ?_, settled, ?_⟩
  · intro n L atIndex
    have bound : n < (lessons p).length := (List.getElem?_eq_some_iff.mp atIndex).choose
    exact ⟨isolated n L atIndex, second_decision secondCheck calibration atIndex
      (isolated n L atIndex) (counts n (Nat.le_of_lt bound) L.cell L.line)⟩
  · intro n bound i a
    have count := counts n bound i a
    have le : lessonCounts p o n i a ≤ expectedWrites p.second i a := count ▸ Nat.min_le_right _ _
    exact ⟨count, Nat.le_trans le (expected_le secondCheck i a),
      Nat.lt_of_le_of_lt (line_gain_le p.second i a le)
        (of_decide_eq_true (allPorts (disjunction_cell secondCheck i).1 a))⟩
  · intro x i
    obtain ⟨route, read⟩ := calibration.2.2.2 x i
    have sameCounts : lessonCounts p o (lessons p).length = expectedWrites p.second :=
      funext fun j => funext (settled j)
    rw [sameCounts] at read
    have input : (o.secondTest x i).input = fun a => predicted p.first x a := by
      funext a
      rw [routed_input route a, first_read p.first firstCheck firstCert (calibration.2.2.1 x a)]
    have decision := read_of_margin read (second_margin p.second secondCheck i (o.secondTest x i).input)
    rw [decision, input]
    rfl

end LearnedCoincidence.MonotoneDNF
