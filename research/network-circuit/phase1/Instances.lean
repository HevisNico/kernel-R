import CircuitNetwork

/-! Written by `predict.py` from CONSTANTS.json. Not edited by hand.

For each instance and each error budget: the integers of the model, whether every read of the zero-error
run has room for the budget of its port, and the writes of that run. Ports in the order a1, a2, b1, b2. -/

namespace NetworkStability.CircuitNetwork.Instances

open AutonomousFeedback

/-! ## With noise, K = 3 -/

def gap7101 : Fin 4 → Int := fun i => [386750, 364521, 307819, 394609].getD i.val 0

example : ∀ i : Fin 4, (run (circuit gap7101) 100000 (fun _ => 0) 224 (start 4 (calendar 8 10 8 10))).writes i =
    [4, 4, 4, 4].getD i.val 0 := by decide +kernel

def lo7101k3 : Fin 4 → Int := fun i => [-21363, -21492, -22746, -21575].getD i.val 0
def hi7101k3 : Fin 4 → Int := fun i => [21614, 21239, 22356, 21218].getD i.val 0

example : ¬ PortMargins (circuit gap7101) 100000 lo7101k3 hi7101k3 224 (start 4 (calendar 8 10 8 10)) := by decide +kernel

def gap7102 : Fin 4 → Int := fun i => [236673, 302223, 454446, 275475].getD i.val 0

example : ∀ i : Fin 4, (run (circuit gap7102) 100000 (fun _ => 0) 224 (start 4 (calendar 8 10 8 10))).writes i =
    [3, 4, 5, 3].getD i.val 0 := by decide +kernel

def lo7102k3 : Fin 4 → Int := fun i => [-24722, -23824, -29219, -23978].getD i.val 0
def hi7102k3 : Fin 4 → Int := fun i => [24483, 24998, 28589, 23693].getD i.val 0

example : ¬ PortMargins (circuit gap7102) 100000 lo7102k3 hi7102k3 224 (start 4 (calendar 8 10 8 10)) := by decide +kernel

def gap7103 : Fin 4 → Int := fun i => [269442, 456663, 221145, 331955].getD i.val 0

example : ∀ i : Fin 4, (run (circuit gap7103) 100000 (fun _ => 0) 224 (start 4 (calendar 8 10 8 10))).writes i =
    [3, 5, 3, 4].getD i.val 0 := by decide +kernel

def lo7103k3 : Fin 4 → Int := fun i => [-30188, -32548, -30879, -30137].getD i.val 0
def hi7103k3 : Fin 4 → Int := fun i => [34616, 32425, 30688, 31799].getD i.val 0

example : ¬ PortMargins (circuit gap7103) 100000 lo7103k3 hi7103k3 224 (start 4 (calendar 8 10 8 10)) := by decide +kernel

/-! ## Without noise -/

def lo7101k0 : Fin 4 → Int := fun i => [-1677, -1693, -2284, -1716].getD i.val 0
def hi7101k0 : Fin 4 → Int := fun i => [1928, 1440, 1894, 1359].getD i.val 0

example : PortMargins (circuit gap7101) 100000 lo7101k0 hi7101k0 224 (start 4 (calendar 8 10 8 10)) := by decide +kernel

def lo7102k0 : Fin 4 → Int := fun i => [-1692, -1694, -2271, -1680].getD i.val 0
def hi7102k0 : Fin 4 → Int := fun i => [1452, 2869, 1641, 1396].getD i.val 0

example : ¬ PortMargins (circuit gap7102) 100000 lo7102k0 hi7102k0 224 (start 4 (calendar 8 10 8 10)) := by decide +kernel

def lo7103k0 : Fin 4 → Int := fun i => [-1698, -1689, -1700, -2260].getD i.val 0
def hi7103k0 : Fin 4 → Int := fun i => [6125, 1566, 1510, 3923].getD i.val 0

example : PortMargins (circuit gap7103) 100000 lo7103k0 hi7103k0 224 (start 4 (calendar 8 10 8 10)) := by decide +kernel

end NetworkStability.CircuitNetwork.Instances
