import KernelR.HybridSourceProgress

namespace KernelR.Hybrid

/-- The expiry action has a fixed successor and does not consume a queue token. -/
noncomputable def rawExpiryJump {n route} (s : Snapshot n) (i : Fin n) (p : Port) (origin : ℝ)
    (hactive : s.raw i p = some origin) (hdue : s.time = origin + 1) :
    Jump route s (setRaw s i p none) :=
  .rawEnd s i p origin hactive hdue

noncomputable def rawExpiryExecution {n θ route} (s : Snapshot n) (i : Fin n) (p : Port) (origin : ℝ)
    (hactive : s.raw i p = some origin) (hdue : s.time = origin + 1) :
    Execution θ route s (setRaw s i p none) :=
  .cons (.jump (rawExpiryJump s i p origin hactive hdue)) (.nil _)

theorem rawExpiryExecution_no_events {n θ route s i p origin}
    (hactive : s.raw i p = some origin) (hdue : s.time = origin + 1) :
    (@rawExpiryExecution n θ route s i p origin hactive hdue).deliveries = [] ∧
      (@rawExpiryExecution n θ route s i p origin hactive hdue).ledger.emissions = [] :=
  ⟨rfl,rfl⟩

theorem rawExpiry_preserves {n} (s : Snapshot n) (i : Fin n) (p : Port) :
    (setRaw s i p none).pending = s.pending ∧
      (setRaw s i p none).x = s.x ∧ (setRaw s i p none).time = s.time ∧
      (setRaw s i p none).main = s.main ∧ (setRaw s i p none).aux = s.aux ∧
      (setRaw s i p none).raw i p = none := by
  simp [setRaw]

/-- An expiry coincident with the SILENT-to-ERROR guard permits both orders,
including when the expiring raw slot is the same auxiliary slot. -/
theorem raw_expiry_error_orders {n θ route} (s : Snapshot n)
    (i : Fin n) (p : Port) (origin : ℝ) (k : Fin n) (q : Port)
    (hactive : s.raw i p = some origin) (hdue : s.time = origin + 1)
    (hmode : s.aux k q = .silent) (hguard : s.x k (.m q) = 1 / 10) :
    Nonempty (Execution θ route s (setAux (setRaw s i p none) k q .error)) ∧
      Nonempty (Execution θ route s (setRaw (setAux s k q .error) i p none)) := by
  constructor
  · exact ⟨.cons (.jump (rawExpiryJump s i p origin hactive hdue))
      (.cons (.jump (.error _ k q hmode hguard)) (.nil _))⟩
  · exact ⟨.cons (.jump (.error s k q hmode hguard))
      (.cons (.jump (rawExpiryJump _ i p origin hactive hdue)) (.nil _))⟩

theorem raw_expiry_error_same_final {n} (s : Snapshot n)
    (i : Fin n) (p : Port) (k : Fin n) (q : Port) :
    setAux (setRaw s i p none) k q .error = setRaw (setAux s k q .error) i p none := rfl

theorem birth_protocol_remaining_due {born : Snapshot 1}
    (d : Delivery 1) (hd : d ∈ (birthProtocolFirstAfter born).pending) : 8 ≤ d.due := by
  change d ∈ sourceTrain 0 0 8 8 15 ++ sourceTrain 0 0 160 8 16 at hd
  rcases List.mem_append.mp hd with hd | hd
  all_goals
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    dsimp
    have hk : (0 : ℝ) ≤ (k.val : ℝ) := Nat.cast_nonneg _
    linarith

theorem birth_protocol_next_token (born : Snapshot 1) :
    (⟨0,0,8⟩ : Delivery 1) ∈ (birthProtocolFirstAfter born).pending := by
  change (⟨0,0,8⟩ : Delivery 1) ∈ sourceTrain 0 0 8 8 15 ++ sourceTrain 0 0 160 8 16
  rw [sourceTrain_succ]
  simp

/-- The first expiry is strictly before every retained source token. -/
theorem birth_protocol_first_expiry_before_sources {born : Snapshot 1}
    (hs : BirthState born) :
    ∀ d ∈ (birthProtocolFirstAfter born).pending, born.time + 1 < d.due := by
  intro d hd
  rw [hs.1]
  linarith [birth_protocol_remaining_due d hd]

/-- Before source 8, a finite constructed prefix cannot consume any of the
thirty-one retained source occurrences. This does not assume a continuation. -/
theorem Execution.birth_protocol_before_eight_no_arrivals {θ route born u}
    (e : @Execution 1 θ route (birthProtocolFirstAfter born) u)
    (hroute : ∀ i t, route i t = []) (ht : u.time < 8) : e.deliveries = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro d hd
  rcases e.delivery_provenance d hd with hs | ⟨event,he,hr⟩
  · have hl := birth_protocol_remaining_due d hs
    have hu := (e.delivery_time_bounds d hd).2
    linarith
  · rw [hroute] at hr
    contradiction

end KernelR.Hybrid
