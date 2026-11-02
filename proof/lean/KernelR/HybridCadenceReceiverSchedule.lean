import KernelR.HybridCadencePacketGaps
import KernelR.HybridLearnedSourcePrefix
import KernelR.HybridLocalCadenceHighJitterTrain

/-! Finite segments of actual input dates, with spacing derived from the
packet. These lists describe source tokens and never prescribe output dates. -/
namespace KernelR.Hybrid

noncomputable def cadenceDates (f : ℕ → ℝ) (offset count : ℕ) : List ℝ :=
  List.ofFn (fun k : Fin count => f (offset + k.val))

noncomputable def cadenceSources (f : ℕ → ℝ) (p : Port) (offset count : ℕ) : List (Delivery 1) :=
  (cadenceDates f offset count).map (fun time => ⟨0,p,time⟩)

@[simp] theorem cadenceDates_zero (f : ℕ → ℝ) (offset : ℕ) : cadenceDates f offset 0 = [] := rfl

@[simp] theorem cadenceDates_length (f : ℕ → ℝ) (offset count : ℕ) :
    (cadenceDates f offset count).length = count := by simp [cadenceDates]

theorem cadenceDates_succ (f : ℕ → ℝ) (offset count : ℕ) :
    cadenceDates f offset (count + 1) = f offset :: cadenceDates f (offset + 1) count := by
  simp only [cadenceDates,List.ofFn_succ,Fin.val_zero,add_zero,Fin.val_succ]
  congr 1
  apply congrArg List.ofFn
  funext k
  congr 1
  omega

theorem cadenceDates_add (f : ℕ → ℝ) (offset a b : ℕ) :
    cadenceDates f offset (a + b) = cadenceDates f offset a ++ cadenceDates f (offset + a) b := by
  simp only [cadenceDates,List.ofFn_add,Fin.val_castLE,Fin.val_natAdd]
  congr 1
  apply congrArg List.ofFn
  funext k
  congr 1
  omega

@[simp] theorem cadenceSources_zero (f : ℕ → ℝ) (p : Port) (offset : ℕ) :
    cadenceSources f p offset 0 = [] := rfl

theorem cadenceSources_succ (f : ℕ → ℝ) (p : Port) (offset count : ℕ) :
    cadenceSources f p offset (count + 1) = ⟨0,p,f offset⟩ :: cadenceSources f p (offset + 1) count := by
  simp only [cadenceSources,cadenceDates_succ,List.map_cons]

theorem cadenceSources_add (f : ℕ → ℝ) (p : Port) (offset a b : ℕ) :
    cadenceSources f p offset (a + b) =
      cadenceSources f p offset a ++ cadenceSources f p (offset + a) b := by
  simp only [cadenceSources,cadenceDates_add,List.map_append]

@[simp] theorem cadenceSources_ofFn (f : ℕ → ℝ) (p : Port) (offset count : ℕ) :
    cadenceSources f p offset count = List.ofFn (fun k : Fin count => (⟨0,p,f (offset + k.val)⟩ : Delivery 1)) := by
  simp only [cadenceSources,cadenceDates,List.map_ofFn,Function.comp_def]

theorem cadenceSources_head_of_pos (f : ℕ → ℝ) (p : Port) (offset count : ℕ)
    (hc : 1 ≤ count) : cadenceSources f p offset count =
      ⟨0,p,f offset⟩ :: cadenceSources f p (offset + 1) (count - 1) := by
  have he : count = (count - 1) + 1 := by omega
  conv_lhs => rw [he,cadenceSources_succ]

theorem cadenceSources_head_prefix (f : ℕ → ℝ) (p : Port) (m L : ℕ) (hm : 1 ≤ m) :
    cadenceSources f p 0 (m + L) = ⟨0,p,f 0⟩ ::
      (cadenceSources f p 1 (m - 1) ++ cadenceSources f p m L) := by
  rw [cadenceSources_add,cadenceSources_head_of_pos f p 0 m hm]
  simp only [zero_add,List.cons_append]

theorem cadenceDates_snoc (f : ℕ → ℝ) (offset count : ℕ) (hc : 1 ≤ count) :
    cadenceDates f offset count = cadenceDates f offset (count - 1) ++ [f (offset + count - 1)] := by
  have he : count = (count - 1) + 1 := by omega
  conv_lhs => rw [he,cadenceDates_add,cadenceDates_succ]
  simp only [cadenceDates_zero]
  congr 2
  congr 1
  omega

theorem cadenceSources_four (f : ℕ → ℝ) (p : Port) (offset count : ℕ) (hc : 4 ≤ count) :
    cadenceSources f p offset count =
      [⟨0,p,f offset⟩,⟨0,p,f (offset + 1)⟩,⟨0,p,f (offset + 2)⟩,⟨0,p,f (offset + 3)⟩] ++
        cadenceSources f p (offset + 4) (count - 4) := by
  have he : count = 4 + (count - 4) := by omega
  conv_lhs => rw [he,cadenceSources_add]
  norm_num [cadenceSources,cadenceDates,List.ofFn_succ,Nat.add_assoc]

theorem cadenceSources_later {f : ℕ → ℝ} (hf : StrictMono f) (p : Port)
    (i offset count : ℕ) (hi : i < offset) :
    ∀ d ∈ cadenceSources f p offset count, f i < d.due := by
  intro d hd
  rw [cadenceSources_ofFn] at hd
  obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
  exact hf (by omega)

theorem learnedPrefixEnd_cadenceDates (f : ℕ → ℝ) (offset count : ℕ) :
    learnedPrefixEnd (f offset) (cadenceDates f (offset + 1) count) = f (offset + count) := by
  induction count generalizing offset with
  | zero => simp [learnedPrefixEnd]
  | succ count ih =>
    rw [cadenceDates_succ]
    change learnedPrefixEnd (f (offset + 1)) (cadenceDates f (offset + 1 + 1) count) = _
    rw [ih]
    congr 1
    omega

theorem learnedPrefixResponses_cadenceDates (f : ℕ → ℝ) (offset count : ℕ) :
    learnedPrefixResponses (f offset) (cadenceDates f (offset + 1) count) = cadenceDates f offset count := by
  induction count generalizing offset with
  | zero => rfl
  | succ count ih =>
    rw [cadenceDates_succ]
    change f offset :: learnedPrefixResponses (f (offset + 1)) (cadenceDates f (offset + 1 + 1) count) = _
    rw [ih,cadenceDates_succ]

theorem packet_learned_prefix_spacing {m L J} (packet : KernelR.Chain.Packet m L J)
    (hJ : J ≤ 1 / 10) (offset count : ℕ) (hend : offset + count < m) :
    LearnedPrefixSpacing (packet.actual offset) (cadenceDates packet.actual (offset + 1) count) := by
  induction count generalizing offset with
  | zero => trivial
  | succ count ih =>
    rw [cadenceDates_succ]
    constructor
    · have h := packet.cadence_prefix_gap hJ offset (by omega)
      linarith [h.1]
    · apply ih
      omega

theorem packet_high_jitter_schedule {m L J} (packet : KernelR.Chain.Packet m L J)
    (hJ : J ≤ 1 / 10) (offset count : ℕ) (terminal : ℝ)
    (hend : packet.actual (offset + count) + 19 / 5 ≤ terminal) :
    CadenceHighJitterSchedule (packet.actual offset)
      (cadenceDates packet.actual (offset + 1) count) terminal := by
  induction count generalizing offset with
  | zero => simpa [CadenceHighJitterSchedule] using hend
  | succ count ih =>
    rw [cadenceDates_succ]
    constructor
    · linarith [packet.cadence_actual_gap hJ offset]
    · apply ih
      have hidx : offset + 1 + count = offset + (count + 1) := by omega
      simpa only [hidx] using hend

end KernelR.Hybrid
