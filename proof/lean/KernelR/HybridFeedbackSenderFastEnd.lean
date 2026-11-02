import KernelR.HybridFeedbackFireProjection
import KernelR.HybridPortFastCompletion

/-! Continue the sender from its actual reciprocal FIRE projection. The
sensor dates and RAW origin come from that same constructed global FIRE. -/
namespace KernelR.Hybrid
namespace FeedbackFirstFire
variable {θ forward backward start}
  {w : FeedbackWeakEntry θ (reciprocalEntryRouter forward backward) start}
  (f : FeedbackFirstFire w)

/-- Construct B's complete local FAST continuation, including real auxiliary
and RAW jumps. Its local empty queue is not a global source or wire queue. -/
theorem sender_fast_end_exists {ε} (hb : PhysicalBox θ ε)
    (hg : Real.exp (w.final.x 1 (.z 2)) ≤ 2) :
    Nonempty (PortFastCompletion f.parametersB (fun _ _ => []) f.localB 2) := by
  refine port_fast_completion_exists (route := fun _ _ => []) (f.localB_box hb)
    f.localB 2 w.final.time f.silentStart f.errorStart f.readyTime
    f.localB_physical f.localB_raw_valid (f.localB_fast 0) (f.localB_silent 0)
    ?_ (f.localB_raw_active 0) ?_ (f.localB_other_rest 0) (f.localB_charge 0)
    ?_ ?_ ?_ f.errorStart_eq f.readyTime_eq ?_ ?_ ?_ ?_
  · intro j p h
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact f.localB_aux_other 0 p (by simpa using h)
  · intro j p h
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact f.localB_raw_other 0 p (by simpa using h)
  · change f.localB.x 0 (.m 2) = (4 / 5 : ℝ) *
      Real.exp (-(θ 1).ls 2 * (f.localB.time - f.silentStart))
    exact f.localB_sensor_clock 0
  · rw [f.localB_clock,w.date]
    constructor <;> linarith [f.window.1,f.window.2]
  · rw [f.localB_clock]
    exact f.silentStart_before_fire.le
  · rw [f.localB_clock]
    exact f.errorStart_after_fire hb
  · rw [w.date]
    exact (f.readyTime_window hb).1
  · rw [f.localB_clock]
    exact f.readyTime_before_fast_end hb hg
  · intro d hd
    rw [f.localB_pending] at hd
    contradiction

end FeedbackFirstFire
end KernelR.Hybrid
