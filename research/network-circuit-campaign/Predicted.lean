import CircuitNetwork

/-! Written by `predict.py` from CONSTANTS.json. Not edited by hand.

For each instance and each error budget: the integers of the model, whether every read of the zero-error
run has room for the budget of its port, and the writes of that run. Ports in the order a1, a2, b1, b2. -/

namespace NetworkStability.CircuitNetwork.Instances

open AutonomousFeedback

/-! ## Without noise, with the allowance for the simulator -/

def gap7201 : Fin 4 → Int := fun i => [492895, 459765, 454950, 336776].getD i.val 0

example : ∀ i : Fin 4, (run (circuit gap7201) 100000 (fun _ => 0) 224 (start 4 (calendar 8 10 8 10))).writes i =
    [5, 5, 5, 4].getD i.val 0 := by decide +kernel

def lo7201k0 : Fin 4 → Int := fun i => [-5699, -3932, -3924, -5683].getD i.val 0
def hi7201k0 : Fin 4 → Int := fun i => [6163, 3757, 3682, 5636].getD i.val 0

example : PortMargins (circuit gap7201) 100000 lo7201k0 hi7201k0 224 (start 4 (calendar 8 10 8 10)) := by decide +kernel

def gap7202 : Fin 4 → Int := fun i => [277550, 249591, 421315, 402923].getD i.val 0

example : ∀ i : Fin 4, (run (circuit gap7202) 100000 (fun _ => 0) 224 (start 4 (calendar 8 10 8 10))).writes i =
    [3, 3, 5, 5].getD i.val 0 := by decide +kernel

def lo7202k0 : Fin 4 → Int := fun i => [-3895, -3924, -3924, -3909].getD i.val 0
def hi7202k0 : Fin 4 → Int := fun i => [3856, 3691, 3807, 3788].getD i.val 0

example : ¬ PortMargins (circuit gap7202) 100000 lo7202k0 hi7202k0 224 (start 4 (calendar 8 10 8 10)) := by decide +kernel

def gap7203 : Fin 4 → Int := fun i => [493434, 531631, 431488, 256344].getD i.val 0

example : ∀ i : Fin 4, (run (circuit gap7203) 100000 (fun _ => 0) 224 (start 4 (calendar 8 10 8 10))).writes i =
    [5, 6, 5, 3].getD i.val 0 := by decide +kernel

def lo7203k0 : Fin 4 → Int := fun i => [-3928, -3924, -3900, -3926].getD i.val 0
def hi7203k0 : Fin 4 → Int := fun i => [5353, 3012, 4270, 4286].getD i.val 0

example : PortMargins (circuit gap7203) 100000 lo7203k0 hi7203k0 224 (start 4 (calendar 8 10 8 10)) := by decide +kernel

def gap7204 : Fin 4 → Int := fun i => [316259, 368270, 363636, 435052].getD i.val 0

example : ∀ i : Fin 4, (run (circuit gap7204) 100000 (fun _ => 0) 224 (start 4 (calendar 8 10 8 10))).writes i =
    [4, 4, 4, 5].getD i.val 0 := by decide +kernel

def lo7204k0 : Fin 4 → Int := fun i => [-3912, -3886, -3911, -3890].getD i.val 0
def hi7204k0 : Fin 4 → Int := fun i => [3191, 3788, 3657, 3046].getD i.val 0

example : PortMargins (circuit gap7204) 100000 lo7204k0 hi7204k0 224 (start 4 (calendar 8 10 8 10)) := by decide +kernel

def gap7205 : Fin 4 → Int := fun i => [277379, 386238, 474666, 285565].getD i.val 0

example : ∀ i : Fin 4, (run (circuit gap7205) 100000 (fun _ => 0) 224 (start 4 (calendar 8 10 8 10))).writes i =
    [3, 4, 5, 3].getD i.val 0 := by decide +kernel

def lo7205k0 : Fin 4 → Int := fun i => [-3931, -7907, -3916, -3903].getD i.val 0
def hi7205k0 : Fin 4 → Int := fun i => [6633, 9094, 4153, 2795].getD i.val 0

example : PortMargins (circuit gap7205) 100000 lo7205k0 hi7205k0 224 (start 4 (calendar 8 10 8 10)) := by decide +kernel

/-! ## With noise, K = 3 -/

def lo7202k3 : Fin 4 → Int := fun i => [-18626, -22001, -19517, -21771].getD i.val 0
def hi7202k3 : Fin 4 → Int := fun i => [18587, 21769, 19400, 21649].getD i.val 0

example : ¬ PortMargins (circuit gap7202) 100000 lo7202k3 hi7202k3 224 (start 4 (calendar 8 10 8 10)) := by decide +kernel

def lo7203k3 : Fin 4 → Int := fun i => [-24383, -26167, -26912, -25454].getD i.val 0
def hi7203k3 : Fin 4 → Int := fun i => [25808, 25255, 27282, 25814].getD i.val 0

example : ¬ PortMargins (circuit gap7203) 100000 lo7203k3 hi7203k3 224 (start 4 (calendar 8 10 8 10)) := by decide +kernel

def lo7204k3 : Fin 4 → Int := fun i => [-24077, -20699, -19525, -19627].getD i.val 0
def hi7204k3 : Fin 4 → Int := fun i => [23356, 20601, 19271, 18784].getD i.val 0

example : ¬ PortMargins (circuit gap7204) 100000 lo7204k3 hi7204k3 224 (start 4 (calendar 8 10 8 10)) := by decide +kernel

def lo7205k3 : Fin 4 → Int := fun i => [-23318, -21464, -21608, -19196].getD i.val 0
def hi7205k3 : Fin 4 → Int := fun i => [26020, 22651, 21846, 18089].getD i.val 0

example : ¬ PortMargins (circuit gap7205) 100000 lo7205k3 hi7205k3 224 (start 4 (calendar 8 10 8 10)) := by decide +kernel

end NetworkStability.CircuitNetwork.Instances
