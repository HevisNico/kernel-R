import KernelR.HybridTwoCellFlowProduct

/-! Local queue-neutral guard jumps lift to either cell with a fixed global
queue. FIRE and arrivals are explicitly excluded from this transport. -/
namespace KernelR.Hybrid

@[simp] theorem Snapshot.product_setMain_left (sA sB : Snapshot 1) (Q : List (Delivery 2)) (mode : MainMode) :
    (setMain sA 0 mode).product sB Q = setMain (sA.product sB Q) 0 mode := by
  cases sA
  cases sB
  simp only [Snapshot.product,setMain]
  congr 1
  funext i
  fin_cases i <;> rfl

@[simp] theorem Snapshot.product_setMain_right (sA sB : Snapshot 1) (Q : List (Delivery 2)) (mode : MainMode) :
    sA.product (setMain sB 0 mode) Q = setMain (sA.product sB Q) 1 mode := by
  cases sA
  cases sB
  simp only [Snapshot.product,setMain]
  congr 1
  funext i
  fin_cases i <;> rfl

@[simp] theorem Snapshot.product_setAux_left (sA sB : Snapshot 1) (Q : List (Delivery 2)) (p : Port) (mode : AuxMode) :
    (setAux sA 0 p mode).product sB Q = setAux (sA.product sB Q) 0 p mode := by
  cases sA
  cases sB
  simp only [Snapshot.product,setAux]
  congr 1
  funext i
  fin_cases i <;> rfl

@[simp] theorem Snapshot.product_setAux_right (sA sB : Snapshot 1) (Q : List (Delivery 2)) (p : Port) (mode : AuxMode) :
    sA.product (setAux sB 0 p mode) Q = setAux (sA.product sB Q) 1 p mode := by
  cases sA
  cases sB
  simp only [Snapshot.product,setAux]
  congr 1
  funext i
  fin_cases i <;> rfl

@[simp] theorem Snapshot.product_setRaw_left (sA sB : Snapshot 1) (Q : List (Delivery 2)) (p : Port) (origin : Option ℝ) :
    (setRaw sA 0 p origin).product sB Q = setRaw (sA.product sB Q) 0 p origin := by
  cases sA
  cases sB
  simp only [Snapshot.product,setRaw]
  congr 1
  funext i
  fin_cases i <;> rfl

@[simp] theorem Snapshot.product_setRaw_right (sA sB : Snapshot 1) (Q : List (Delivery 2)) (p : Port) (origin : Option ℝ) :
    sA.product (setRaw sB 0 p origin) Q = setRaw (sA.product sB Q) 1 p origin := by
  cases sA
  cases sB
  simp only [Snapshot.product,setRaw]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- This class contains precisely the guard/expiry jumps with unchanged queue.
It excludes FIRE even when its particular route happens to be empty. -/
def Jump.QueueNeutral {n route s u} (j : @Jump n route s u) : Prop :=
  match j with
  | .fire .. => False
  | .arrive .. => False
  | _ => True

/-- Lift an actual queue-neutral local jump at A, leaving B and Q unchanged. -/
def Jump.product_left {routeA : Router 1} {sA uA : Snapshot 1}
    (j : Jump routeA sA uA) (hn : j.QueueNeutral) (sB : Snapshot 1) (Q : List (Delivery 2))
    (route : Router 2) : Jump route (sA.product sB Q) (uA.product sB Q) := by
  cases j with
  | fire => exact False.elim hn
  | arrive => exact False.elim hn
  | fastEnd i hm hq =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simpa only [Snapshot.product_setMain_left] using Jump.fastEnd (route := route) (sA.product sB Q) 0 hm hq
  | reopen i hm hq =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simpa only [Snapshot.product_setMain_left] using Jump.reopen (route := route) (sA.product sB Q) 0 hm hq
  | mark i p hm hq =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simpa only [Snapshot.product_setAux_left] using Jump.mark (route := route) (sA.product sB Q) 0 p hm hq
  | silent i p hm hq =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simpa only [Snapshot.product_setAux_left] using Jump.silent (route := route) (sA.product sB Q) 0 p hm hq
  | error i p hm hq =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simpa only [Snapshot.product_setAux_left] using Jump.error (route := route) (sA.product sB Q) 0 p hm hq
  | auxReady i p hm hq =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simpa only [Snapshot.product_setAux_left] using Jump.auxReady (route := route) (sA.product sB Q) 0 p hm hq
  | rawEnd i p origin hr ht =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simpa only [Snapshot.product_setRaw_left] using Jump.rawEnd (route := route) (sA.product sB Q) 0 p origin hr ht

/-- Lift an actual queue-neutral jump at B. The shared clock is needed for
RAW expiry; no ordering of simultaneous A/B guards is assumed. -/
def Jump.product_right {routeB : Router 1} {sB uB : Snapshot 1}
    (j : Jump routeB sB uB) (hn : j.QueueNeutral) (sA : Snapshot 1)
    (hclock : sA.time = sB.time) (Q : List (Delivery 2)) (route : Router 2) :
    Jump route (sA.product sB Q) (sA.product uB Q) := by
  cases j with
  | fire => exact False.elim hn
  | arrive => exact False.elim hn
  | fastEnd i hm hq =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simpa only [Snapshot.product_setMain_right] using Jump.fastEnd (route := route) (sA.product sB Q) 1 hm hq
  | reopen i hm hq =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simpa only [Snapshot.product_setMain_right] using Jump.reopen (route := route) (sA.product sB Q) 1 hm hq
  | mark i p hm hq =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simpa only [Snapshot.product_setAux_right] using Jump.mark (route := route) (sA.product sB Q) 1 p hm hq
  | silent i p hm hq =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simpa only [Snapshot.product_setAux_right] using Jump.silent (route := route) (sA.product sB Q) 1 p hm hq
  | error i p hm hq =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simpa only [Snapshot.product_setAux_right] using Jump.error (route := route) (sA.product sB Q) 1 p hm hq
  | auxReady i p hm hq =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simpa only [Snapshot.product_setAux_right] using Jump.auxReady (route := route) (sA.product sB Q) 1 p hm hq
  | rawEnd i p origin hr ht =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simpa only [Snapshot.product_setRaw_right] using Jump.rawEnd (route := route) (sA.product sB Q) 1 p origin hr (hclock.trans ht)

end KernelR.Hybrid
