import CircuitNetwork

/-! Written by `predict.py` from CONSTANTS.json with K = 3.0. Not edited by hand.

For each instance: the integers of the model, whether every read of the zero-error run has room for the
error budget of its port, and the writes of that run. Ports in the order a1, a2, b1, b2. -/

namespace NetworkStability.CircuitNetwork.Instances

open AutonomousFeedback

def gap7101 : Fin 4 → Int := fun i => [386750, 364521, 307819, 394609].getD i.val 0
def lo7101 : Fin 4 → Int := fun i => [-12918, -13149, -17124, -14541].getD i.val 0
def hi7101 : Fin 4 → Int := fun i => [13169, 12896, 16735, 14185].getD i.val 0

example : ¬ PortMargins (circuit gap7101) 100000 lo7101 hi7101 224 (start 4 (calendar 8 10 8 10)) := by decide +kernel

example : ∀ i : Fin 4, (run (circuit gap7101) 100000 (fun _ => 0) 224 (start 4 (calendar 8 10 8 10))).writes i =
    [4, 4, 4, 4].getD i.val 0 := by decide +kernel

def gap7102 : Fin 4 → Int := fun i => [236673, 302223, 454446, 275475].getD i.val 0
def lo7102 : Fin 4 → Int := fun i => [-18111, -15293, -22742, -15157].getD i.val 0
def hi7102 : Fin 4 → Int := fun i => [17871, 16468, 22113, 14873].getD i.val 0

example : ¬ PortMargins (circuit gap7102) 100000 lo7102 hi7102 224 (start 4 (calendar 8 10 8 10)) := by decide +kernel

example : ∀ i : Fin 4, (run (circuit gap7102) 100000 (fun _ => 0) 224 (start 4 (calendar 8 10 8 10))).writes i =
    [3, 4, 5, 3].getD i.val 0 := by decide +kernel

def gap7103 : Fin 4 → Int := fun i => [269442, 456663, 221145, 331955].getD i.val 0
def lo7103 : Fin 4 → Int := fun i => [-14350, -22875, -15135, -14405].getD i.val 0
def hi7103 : Fin 4 → Int := fun i => [18778, 22752, 14945, 16068].getD i.val 0

example : PortMargins (circuit gap7103) 100000 lo7103 hi7103 224 (start 4 (calendar 8 10 8 10)) := by decide +kernel

example : ∀ i : Fin 4, (run (circuit gap7103) 100000 (fun _ => 0) 224 (start 4 (calendar 8 10 8 10))).writes i =
    [3, 5, 3, 4].getD i.val 0 := by decide +kernel

end NetworkStability.CircuitNetwork.Instances
