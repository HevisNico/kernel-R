import KernelR.HybridReverseSourceWire
import KernelR.HybridPortWeakCut
import KernelR.HybridReverseLatencyGeometry
import KernelR.HybridReverseWeakStep

/-! The next actual B source responds while A carries its previous weak
cut. Preparation at the new wire is derived from the two real own roots. -/
namespace KernelR.Hybrid

structure ReverseWeakNextWire (θA θB : Fin 1 → Parameters) (forward backward : ℝ → ℝ)
    (source : Snapshot 2) where
  senderCycle : ShortLearnedCycle θB (reverseSourceLocalB source) 2
  wire : ReverseSourceWire θA θB forward backward source senderCycle
  receiver_prepared : PreparedSection wire.final 0
  receiver_charge_lower : 1 / 10 ≤ wire.final.x 0 .q

theorem reverse_weak_next_wire_exists {θA θB ε forward backward sA C sB}
    (weak : PortWeakCut θA sA 2 C)
    (previous : FirstLearnedFire θB (fun _ _ => []) sB 0 2)
    (source : Snapshot 2)
    (hb : PhysicalBox (extendParameters θA (θB 0)) ε)
    (hf : PhysicalInvariant (extendParameters θA (θB 0)) source) (hv : RawValid source)
    (hsourceWindow : 320 ≤ source.time ∧ source.time ≤ 440)
    (hprojection : reverseSourceLocalA source = weak.cut.state)
    (hpreparedB : PreparedSection source 1) (hqB : source.x 1 .q = 1 / 10)
    (hgainB : 9 / 5 ≤ Real.exp (source.x 1 (.z 2)) ∧ Real.exp (source.x 1 (.z 2)) ≤ 2)
    (hrawB : source.raw 1 2 = some source.time)
    (hotherB : ∀ p, p ≠ 2 → source.raw 1 p = none)
    (hQ : ∀ d ∈ source.pending, source.time + 8 ≤ d.due)
    (hpreviousQ : sB.x 0 .q = 1 / 10)
    (hpreviousGain : source.x 1 (.z 2) = sB.x 0 (.z 2))
    (hsourceGap : source.time = sB.time + 8)
    (hpreviousReceipt : sA.time = previous.final.time + backward previous.final.time)
    (hd : ∀ t, (3 / 10 : ℝ) ≤ backward t ∧ backward t ≤ 2 / 5) :
    Nonempty (ReverseWeakNextWire θA θB forward backward source) := by
  have hbB : PhysicalBox θB ε := by
    refine ⟨hb.1,?_⟩
    intro j p
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact hb.2 1 p
  have hfB : PhysicalInvariant θB (reverseSourceLocalB source) := by
    refine ⟨fun _ => hf.region 1,?_,fun _ => hf.recovery_cap 1,fun _ => hf.reserve 1⟩
    intro j p
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact hf.gain_cap 1 p
  obtain ⟨cycle⟩ := short_learned_cycle_exists hbB (reverseSourceLocalB source) 2 hfB
    (fun _ p origin h => hv 1 p origin h)
    ⟨hpreparedB.ready,hpreparedB.charge,hpreparedB.recovery,hpreparedB.auxiliary⟩
    ⟨hgainB.1,by change Real.exp (source.x 1 (.z 2)) ≤ 11 / 5; linarith [hgainB.2]⟩
    hrawB hotherB (by intro d hd; change d ∈ ([] : List (Delivery 1)) at hd; contradiction)
  have hmain : source.main 0 = .ready := by
    change (reverseSourceLocalA source).main 0 = .ready
    rw [hprojection]
    exact weak.cut_main_ready
  have haux : ∀ p, source.aux 0 p = .ready := by
    intro p
    change (reverseSourceLocalA source).aux 0 p = .ready
    rw [hprojection]
    exact (weak.cut_aux_rest p).1
  have hraw : ∀ p, source.raw 0 p = none := by
    intro p
    change (reverseSourceLocalA source).raw 0 p = none
    rw [hprojection]
    exact weak.cut_raw_none p
  have hcharge : source.x 0 .q < 1 := by
    change (reverseSourceLocalA source).x 0 .q < 1
    rw [hprojection]
    have h := weak.cut.before_guards.1 0
    rw [weak.cut_main_ready] at h
    exact h
  have hm : ∀ p, source.x 0 (.m p) < 1 := by
    intro p
    change (reverseSourceLocalA source).x 0 (.m p) < 1
    rw [hprojection]
    linarith [(weak.cut_aux_rest p).2.2]
  obtain ⟨wire⟩ := reverse_source_wire_exists (forward := forward) source cycle hb hf hv hsourceWindow
    hmain haux hraw hcharge hm hQ hd
  have hgainOld : 9 / 5 ≤ Real.exp (sB.x 0 (.z 2)) ∧ Real.exp (sB.x 0 (.z 2)) ≤ 12 / 5 := by
    rw [← hpreviousGain]
    exact ⟨hgainB.1,by linarith [hgainB.2]⟩
  have hgap := (previous.rest_receipt_gap backward cycle.fire hpreviousQ hqB hgainOld
    hpreviousGain hsourceGap hd).1
  have hfinish : weak.weak.final.time ≤ wire.final.time := by
    rw [weak.weak.date,hpreviousReceipt,wire.date]
    linarith
  have hp : PreparedSection wire.final 0 := by
    apply wire.receiver_prepared
    rw [hprojection]
    exact weak.quiet_after_cut_prepared hfinish 0
  have hq : 1 / 10 ≤ wire.final.x 0 .q := by
    rw [wire.a_values,hprojection]
    exact weak.quiet_after_cut_charge_lower wire.final.time
  exact ⟨⟨cycle,wire,hp,hq⟩⟩

namespace ReverseWeakStep
variable {θA θB forward backward source cycle}
  {r : ReverseSourceWire θA θB forward backward source cycle} {later} (s : ReverseWeakStep r later)

theorem receiver_projection : reverseSourceLocalA s.final = s.receiver.cut.state := by
  have hext {n} (u v : Snapshot n) (ht : u.time = v.time) (hx : u.x = v.x)
      (hm : u.main = v.main) (ha : u.aux = v.aux) (hr : u.raw = v.raw)
      (hp : u.pending = v.pending) : u = v := by
    cases u
    cases v
    simp_all only
  apply hext
  · exact s.date.trans s.receiver.cut.date.symm
  · funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact s.a_values
  · funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact s.a_main
  · funext j p
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact s.a_aux p
  · funext j p
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact s.a_raw p
  · exact s.receiver.cut_pending.symm

/-- Continue a real weak step with the next real B source response. The
strictly future queue bound is supplied from its exact remaining sources. -/
theorem next_wire_exists {ε} (hb : PhysicalBox (extendParameters θA (θB 0)) ε)
    (hwindow : 320 ≤ s.final.time ∧ s.final.time ≤ 440)
    (hgainB : 9 / 5 ≤ Real.exp (source.x 1 (.z 2)) ∧ Real.exp (source.x 1 (.z 2)) ≤ 2)
    (hqB : source.x 1 .q = 1 / 10)
    (hQ : ∀ d ∈ s.final.pending, s.final.time + 8 ≤ d.due)
    (hd : ∀ t, (3 / 10 : ℝ) ≤ backward t ∧ backward t ≤ 2 / 5) :
    Nonempty (ReverseWeakNextWire θA θB forward backward s.final) := by
  have hzg : s.final.x 1 (.z 2) = source.x 1 (.z 2) :=
    (s.b_gains 2).trans (r.gains 1 2)
  have hg : 9 / 5 ≤ Real.exp (s.final.x 1 (.z 2)) ∧ Real.exp (s.final.x 1 (.z 2)) ≤ 2 := by
    rw [hzg]
    exact hgainB
  apply reverse_weak_next_wire_exists s.receiver cycle.fire s.final hb s.physical s.raw_valid
    hwindow s.receiver_projection s.b_prepared s.b_charge hg
    (by rw [s.date]; exact s.raw_active) s.raw_other_b hQ hqB hzg
    s.date
  · exact r.date
  · exact hd

end ReverseWeakStep

end KernelR.Hybrid
