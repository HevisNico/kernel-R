import NativeRingExamples
import NativeRingRefinement

namespace NetworkStability.NativeRing

/-- The launch and relay transmit, then the native return port records one dose. -/
theorem all_strong_two_refines : Refines (allStrongParameters 2) (by decide) :=
  native_ring_refinement 2 _ (allStrong_valid (by decide)) (by decide)

/-- The weak relay learns once and the return port is never admitted. -/
theorem stopping_two_refines : Refines (stoppingParameters 2) (by decide) :=
  native_ring_refinement 2 _ (by decide +kernel) (by decide)

end NetworkStability.NativeRing
