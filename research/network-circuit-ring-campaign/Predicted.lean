import RingNetwork

/-! Written by `predicted.py` from the measures of campaign 2. Not edited by hand.

Per measured instance: the gap of each port in units of 1/100000 dose, the writes of the zero-error
queue run of the ring for its laps without noise, and for each port and each budget whether `Own` holds
for its need. Ports in the order a1, b1, c1, a2. -/

namespace NetworkStability.RingNetwork.Predicted

open AutonomousFeedback
open NetworkStability.RingNetwork

/-! ## Instance 7301 -/

def gap7301 : Fin 4 → Int := fun i => [497060, 309379, 359225, 471473].getD i.val 0

example : ∀ i : Fin 4, (run (ring 3 gap7301) 100000 (fun _ => 0) (28 * 4) (start 4 (launches 3 28))).writes i =
    [5, 4, 4, 5].getD i.val 0 := by decide +kernel

def lo7301k0 : Fin 4 → Int := fun i => [-3917, -3912, -4490, -3930].getD i.val 0
def hi7301k0 : Fin 4 → Int := fun i => [3555, 3758, 4242, 3823].getD i.val 0

example : ¬ Own (N := 3) gap7301 100000 lo7301k0 hi7301k0 0 5 := by decide +kernel
example : Own (N := 3) gap7301 100000 lo7301k0 hi7301k0 1 4 := by decide +kernel
example : Own (N := 3) gap7301 100000 lo7301k0 hi7301k0 2 4 := by decide +kernel
example : Own (N := 3) gap7301 100000 lo7301k0 hi7301k0 3 5 := by decide +kernel

def lo7301k3 : Fin 4 → Int := fun i => [-26650, -26540, -27132, -26722].getD i.val 0
def hi7301k3 : Fin 4 → Int := fun i => [26288, 26386, 26884, 26614].getD i.val 0

example : ¬ Own (N := 3) gap7301 100000 lo7301k3 hi7301k3 0 5 := by decide +kernel
example : ¬ Own (N := 3) gap7301 100000 lo7301k3 hi7301k3 1 4 := by decide +kernel
example : Own (N := 3) gap7301 100000 lo7301k3 hi7301k3 2 4 := by decide +kernel
example : Own (N := 3) gap7301 100000 lo7301k3 hi7301k3 3 5 := by decide +kernel

/-! ## Instance 7303 -/

def gap7303 : Fin 4 → Int := fun i => [380718, 310551, 200235, 382039].getD i.val 0

example : ∀ i : Fin 4, (run (ring 3 gap7303) 100000 (fun _ => 0) (25 * 4) (start 4 (launches 3 25))).writes i =
    [4, 4, 3, 4].getD i.val 0 := by decide +kernel

def lo7303k0 : Fin 4 → Int := fun i => [-3919, -3908, -3583, -3919].getD i.val 0
def hi7303k0 : Fin 4 → Int := fun i => [4094, 3591, 3458, 3260].getD i.val 0

example : Own (N := 3) gap7303 100000 lo7303k0 hi7303k0 0 4 := by decide +kernel
example : Own (N := 3) gap7303 100000 lo7303k0 hi7303k0 1 4 := by decide +kernel
example : ¬ Own (N := 3) gap7303 100000 lo7303k0 hi7303k0 2 3 := by decide +kernel
example : Own (N := 3) gap7303 100000 lo7303k0 hi7303k0 3 4 := by decide +kernel

def lo7303k3 : Fin 4 → Int := fun i => [-26570, -26524, -26187, -26632].getD i.val 0
def hi7303k3 : Fin 4 → Int := fun i => [26746, 26207, 26063, 25973].getD i.val 0

example : ¬ Own (N := 3) gap7303 100000 lo7303k3 hi7303k3 0 4 := by decide +kernel
example : ¬ Own (N := 3) gap7303 100000 lo7303k3 hi7303k3 1 4 := by decide +kernel
example : ¬ Own (N := 3) gap7303 100000 lo7303k3 hi7303k3 2 3 := by decide +kernel
example : ¬ Own (N := 3) gap7303 100000 lo7303k3 hi7303k3 3 4 := by decide +kernel

/-! ## Instance 7304 -/

def gap7304 : Fin 4 → Int := fun i => [133261, 345302, 407608, 395835].getD i.val 0

example : ∀ i : Fin 4, (run (ring 3 gap7304) 100000 (fun _ => 0) (25 * 4) (start 4 (launches 3 25))).writes i =
    [2, 4, 5, 4].getD i.val 0 := by decide +kernel

def lo7304k0 : Fin 4 → Int := fun i => [-4441, -3898, -3913, -3922].getD i.val 0
def hi7304k0 : Fin 4 → Int := fun i => [4707, 3130, 2799, 4242].getD i.val 0

example : Own (N := 3) gap7304 100000 lo7304k0 hi7304k0 0 2 := by decide +kernel
example : Own (N := 3) gap7304 100000 lo7304k0 hi7304k0 1 4 := by decide +kernel
example : Own (N := 3) gap7304 100000 lo7304k0 hi7304k0 2 5 := by decide +kernel
example : Own (N := 3) gap7304 100000 lo7304k0 hi7304k0 3 4 := by decide +kernel

def lo7304k3 : Fin 4 → Int := fun i => [-26682, -26463, -26687, -26564].getD i.val 0
def hi7304k3 : Fin 4 → Int := fun i => [26948, 25695, 25574, 26884].getD i.val 0

example : Own (N := 3) gap7304 100000 lo7304k3 hi7304k3 0 2 := by decide +kernel
example : Own (N := 3) gap7304 100000 lo7304k3 hi7304k3 1 4 := by decide +kernel
example : ¬ Own (N := 3) gap7304 100000 lo7304k3 hi7304k3 2 5 := by decide +kernel
example : ¬ Own (N := 3) gap7304 100000 lo7304k3 hi7304k3 3 4 := by decide +kernel

/-! ## Instance 7306 -/

def gap7306 : Fin 4 → Int := fun i => [512286, 348267, 395836, 365216].getD i.val 0

example : ∀ i : Fin 4, (run (ring 3 gap7306) 100000 (fun _ => 0) (28 * 4) (start 4 (launches 3 28))).writes i =
    [6, 4, 4, 4].getD i.val 0 := by decide +kernel

def lo7306k0 : Fin 4 → Int := fun i => [-4506, -3925, -3950, -5656].getD i.val 0
def hi7306k0 : Fin 4 → Int := fun i => [3686, 4157, 6339, 7398].getD i.val 0

example : Own (N := 3) gap7306 100000 lo7306k0 hi7306k0 0 6 := by decide +kernel
example : Own (N := 3) gap7306 100000 lo7306k0 hi7306k0 1 4 := by decide +kernel
example : Own (N := 3) gap7306 100000 lo7306k0 hi7306k0 2 4 := by decide +kernel
example : Own (N := 3) gap7306 100000 lo7306k0 hi7306k0 3 4 := by decide +kernel

def lo7306k3 : Fin 4 → Int := fun i => [-27425, -26621, -26799, -28342].getD i.val 0
def hi7306k3 : Fin 4 → Int := fun i => [26604, 26853, 29189, 30084].getD i.val 0

example : ¬ Own (N := 3) gap7306 100000 lo7306k3 hi7306k3 0 6 := by decide +kernel
example : Own (N := 3) gap7306 100000 lo7306k3 hi7306k3 1 4 := by decide +kernel
example : ¬ Own (N := 3) gap7306 100000 lo7306k3 hi7306k3 2 4 := by decide +kernel
example : Own (N := 3) gap7306 100000 lo7306k3 hi7306k3 3 4 := by decide +kernel

end NetworkStability.RingNetwork.Predicted
