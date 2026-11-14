import NetworkTheorem

namespace NetworkStability.AutonomousFeedback.Schedule.PortMemory

inductive Coordinate
  | port0
  | port1
  | recovery
  deriving DecidableEq

def Coordinate.index : Coordinate → Nat
  | .port0 => 0
  | .port1 => 1
  | .recovery => 2

private theorem index_lt (c : Coordinate) : c.index < 3 := by cases c <;> decide

/-- Three independent memory coordinates per cell. Recovery is a separate
write event in this abstraction. -/
structure Address (N : Nat) where
  cell : Fin N
  coordinate : Coordinate
  deriving DecidableEq

def Address.encode (a : Address N) : Fin (3 * N) :=
  ⟨3 * a.cell.val + a.coordinate.index, by
    have := a.cell.isLt
    have := index_lt a.coordinate
    omega⟩

theorem address_encode_injective (a b : Address N) (eq : a.encode = b.encode) : a = b := by
  have val := congrArg Fin.val eq
  change 3 * a.cell.val + a.coordinate.index = 3 * b.cell.val + b.coordinate.index at val
  have ha := index_lt a.coordinate
  have hb := index_lt b.coordinate
  have cell : a.cell = b.cell := Fin.ext (by omega)
  have coord : a.coordinate.index = b.coordinate.index := by
    rw [cell] at val
    omega
  cases a with
  | mk i c =>
    cases b with
    | mk j e =>
      change i = j at cell
      subst j
      cases c <;> cases e <;> simp_all [Coordinate.index]

structure PortModel (N : Nat) (P : Type) where
  target : P → Address N
  bias : P → Int
  drive : P → Nat
  route : P → List P

def PortModel.guarded (M : PortModel N P) : Model (3 * N) P where
  cell := fun p => (M.target p).encode
  bias := M.bias
  drive := M.drive
  route := M.route

/-- One pending occurrence per port, and at most one for the separate
recovery coordinate. This permits one pending occurrence on each port. -/
def PortExclusive (M : PortModel N P) (s : Config (3 * N) P) : Prop :=
  (s.pending.map M.target).Nodup

private theorem nodup_encode {xs : List (Address N)} (h : xs.Nodup) :
    (xs.map Address.encode).Nodup := by
  induction xs with
  | nil => simp
  | cons a tail ih =>
    obtain ⟨no, distinct⟩ := List.nodup_cons.mp h
    apply List.nodup_cons.mpr
    refine ⟨?_, ih distinct⟩
    intro found
    obtain ⟨b, mem, eq⟩ := List.mem_map.mp found
    exact no (address_encode_injective b a eq ▸ mem)

theorem exclusivity_lifts (M : PortModel N P) (s : Config (3 * N) P)
    (h : PortExclusive M s) : Exclusive M.guarded s := by
  simpa only [Exclusive, PortModel.guarded, List.map_map, Function.comp_def] using
    nodup_encode h

theorem distinct_ports_commute (M : PortModel N P) (d : Nat)
    (s : Config (3 * N) P) (p q : P) (rest : List P) (different : M.target p ≠ M.target q) :
    let G := M.guarded
    Equivalent
      (process G d (process G d s p (q :: rest)) q (rest ++ emitted G p (read G d s p)))
      (process G d (process G d s q (p :: rest)) p (rest ++ emitted G q (read G d s q))) := by
  exact different_cells_commute M.guarded d s p q rest
    (fun equal => different (address_encode_injective _ _ equal))

/-- Lift the scalar results to the independent coordinates and retain a
per-physical-cell bound across its two ports and recovery memory. -/
theorem per_port_bounds (Q d B rail : Nat) {N : Nat} {P : Type}
    (M : PortModel N P) (seed : List P) (reserve : LocalReserve Q M.guarded seed)
    (base : Fin (3 * N) → Nat) (initial : ∀ i, base i ≤ B) (headroom : B + d * Q < rail)
    (s : Config (3 * N) P) (path : Path M.guarded d (seedConfig (3 * N) seed) s) :
    SafeMemory Q d B rail base s ∧
    ∀ i : Fin N, s.writes (Address.encode ⟨i, .port0⟩) +
      s.writes (Address.encode ⟨i, .port1⟩) +
      s.writes (Address.encode ⟨i, .recovery⟩) ≤ 3 * Q := by
  have count := reachable_bound Q d reserve path
  refine ⟨⟨RoutedCalendar.total_le Q _ count, fun i => ⟨count i, ?_, ?_, ?_⟩⟩, ?_⟩
  · omega
  · exact Nat.add_le_add (initial i) (Nat.mul_le_mul_left d (count i))
  · exact Nat.lt_of_le_of_lt (Nat.add_le_add (initial i) (Nat.mul_le_mul_left d (count i))) headroom
  · intro i
    have := count (Address.encode ⟨i, .port0⟩)
    have := count (Address.encode ⟨i, .port1⟩)
    have := count (Address.encode ⟨i, .recovery⟩)
    omega

theorem per_port_terminal_unique (Q W eta d : Nat) {N : Nat} {P : Type}
    (M : PortModel N P) (seed : List P) (cert : Certificate Q W eta M.guarded seed)
    (exclusive : ∀ s, Path M.guarded d (seedConfig (3 * N) seed) s → PortExclusive M s)
    {a b : State (3 * N) P} (pa : CertifiedTrace M.guarded d (start (3 * N) seed) a)
    (pb : CertifiedTrace M.guarded d (start (3 * N) seed) b) (ha : a.pending = []) (hb : b.pending = [])
    (base : Fin (3 * N) → Nat) :
    a.writes = b.writes ∧ stored d base a = stored d base b :=
  certified_terminal_memory_unique Q W eta d M.guarded seed cert
    (fun s path => Or.inl (exclusivity_lifts M s (exclusive s path))) pa pb ha hb base

/-- The same fairness theorem applies separately to both gains and recovery. -/
theorem per_port_fair_limit_unique (Q d : Nat) {N : Nat} {P : Type}
    (M : PortModel N P) (seed : List P) (reserve : LocalReserve Q M.guarded seed)
    (exclusive : ∀ s, Path M.guarded d (seedConfig (3 * N) seed) s → PortExclusive M s)
    (a b : Execution M.guarded d seed) (fa : WriteFair a) (fb : WriteFair b) :
    ∃ counts, Stable a counts ∧ Stable b counts := by
  obtain ⟨x, sx⟩ := execution_stabilizes Q d reserve a
  obtain ⟨y, sy⟩ := execution_stabilizes Q d reserve b
  have same := fair_limit_unique M.guarded d seed
    (fun s path => Or.inl (exclusivity_lifts M s (exclusive s path))) a b fa fb sx sy
  exact ⟨x, sx, same.symm ▸ sy⟩

/-- A single cell can have all three independent addresses pending. -/
private def exampleTarget : Coordinate → Address 1 := fun c => ⟨0, c⟩

private def independentFixture : PortModel 1 Coordinate :=
  ⟨exampleTarget, fun _ => -1, fun _ => 0, fun _ => []⟩

theorem both_ports_and_recovery_can_be_pending :
    PortExclusive independentFixture
      (seedConfig 3 [.port0, .port1, .recovery]) ∧
    ¬ ([(0 : Fin 1), 0, 0].Nodup) := by
  unfold PortExclusive
  decide

end NetworkStability.AutonomousFeedback.Schedule.PortMemory
