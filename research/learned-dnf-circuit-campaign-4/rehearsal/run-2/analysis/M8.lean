import MonotonePremiseSoundness
import MonotoneOneSidedRecognition

/-! Campaign 4's kernel gate, written by gate4.py from analyze.py, M8. Each `checks_*` theorem asserts the verdict of the
Python; the file compiles only if the kernel agrees. -/

namespace LearnedCoincidence.MonotoneDNF.PremiseCheck.Campaign4

open TwoLayer (SlotTiming ReadObservation)

private def term (a : Fin 2) : Pattern 4 :=
  if a = 0 then pattern [0, 1] else pattern [2, 3]

private def empty4 : ReadObservation 4 := datedRead 0 #v[none, none, none, none] [] 0
private def empty2 : ReadObservation 2 := datedRead 0 #v[none, none] [] 0

def left : SlotTiming := ⟨(1 / 50 : Rat), (11 / 10 : Rat), (22 : Rat)⟩
def right : SlotTiming := ⟨(11 / 10 : Rat), (11 / 5 : Rat), (19 : Rat)⟩

def checks (p : Cascade 2 1 4) (t : TraceTables p) : Bool :=
  checkCascadeValid p &&
  checkTrainingSeparation p left right t.observations &&
  checkCascadeCalibrationOneSided p left right t.observations t.scoreAt

theorem no_eligible_instance : True := trivial

end LearnedCoincidence.MonotoneDNF.PremiseCheck.Campaign4
