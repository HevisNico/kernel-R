import RingNetwork

/-! Written by `predicted.py` from the measures of campaign 3. Not edited by hand.

Per measured instance: the gap of each port in units of 1/100000 dose, the writes of the zero-error
queue run of the ring for its laps without noise, and for each port and each budget whether `Own` holds
for its need. Ports in the order a1, b1, c1, a2. -/

namespace NetworkStability.RingNetwork.Predicted

open AutonomousFeedback
open NetworkStability.RingNetwork

/-! ## Instance 7401 -/

def gap7401 : Fin 4 → Int := fun i => [284343, 83330, 265885, 386187].getD i.val 0

example : ∀ i : Fin 4, (run (ring 3 gap7401) 100000 (fun _ => 0) (21 * 4) (start 4 (launches 3 21))).writes i =
    [3, 1, 3, 4].getD i.val 0 := by decide +kernel

def lo7401k0 : Fin 4 → Int := fun i => [-3910, -3884, -3903, -7908].getD i.val 0
def hi7401k0 : Fin 4 → Int := fun i => [3918, 7068, 3602, 6867].getD i.val 0

example : Own (N := 3) gap7401 100000 lo7401k0 hi7401k0 0 3 := by decide +kernel
example : Own (N := 3) gap7401 100000 lo7401k0 hi7401k0 1 1 := by decide +kernel
example : Own (N := 3) gap7401 100000 lo7401k0 hi7401k0 2 3 := by decide +kernel
example : Own (N := 3) gap7401 100000 lo7401k0 hi7401k0 3 4 := by decide +kernel

def lo7401k3 : Fin 4 → Int := fun i => [-26482, -26109, -26422, -30447].getD i.val 0
def hi7401k3 : Fin 4 → Int := fun i => [26490, 29294, 26120, 29407].getD i.val 0

example : ¬ Own (N := 3) gap7401 100000 lo7401k3 hi7401k3 0 3 := by decide +kernel
example : ¬ Own (N := 3) gap7401 100000 lo7401k3 hi7401k3 1 1 := by decide +kernel
example : Own (N := 3) gap7401 100000 lo7401k3 hi7401k3 2 3 := by decide +kernel
example : ¬ Own (N := 3) gap7401 100000 lo7401k3 hi7401k3 3 4 := by decide +kernel

/-! ## Instance 7403 -/

def gap7403 : Fin 4 → Int := fun i => [316140, 245079, 264959, 395938].getD i.val 0

example : ∀ i : Fin 4, (run (ring 3 gap7403) 100000 (fun _ => 0) (24 * 4) (start 4 (launches 3 24))).writes i =
    [4, 3, 3, 4].getD i.val 0 := by decide +kernel

def lo7403k0 : Fin 4 → Int := fun i => [-3910, -3903, -3882, -3891].getD i.val 0
def hi7403k0 : Fin 4 → Int := fun i => [3771, 2794, 4401, 7135].getD i.val 0

example : Own (N := 3) gap7403 100000 lo7403k0 hi7403k0 0 4 := by decide +kernel
example : Own (N := 3) gap7403 100000 lo7403k0 hi7403k0 1 3 := by decide +kernel
example : Own (N := 3) gap7403 100000 lo7403k0 hi7403k0 2 3 := by decide +kernel
example : Own (N := 3) gap7403 100000 lo7403k0 hi7403k0 3 4 := by decide +kernel

def lo7403k3 : Fin 4 → Int := fun i => [-26513, -26422, -26251, -26445].getD i.val 0
def hi7403k3 : Fin 4 → Int := fun i => [26374, 25313, 26770, 29689].getD i.val 0

example : ¬ Own (N := 3) gap7403 100000 lo7403k3 hi7403k3 0 4 := by decide +kernel
example : Own (N := 3) gap7403 100000 lo7403k3 hi7403k3 1 3 := by decide +kernel
example : Own (N := 3) gap7403 100000 lo7403k3 hi7403k3 2 3 := by decide +kernel
example : ¬ Own (N := 3) gap7403 100000 lo7403k3 hi7403k3 3 4 := by decide +kernel

/-! ## Instance 7404 -/

def gap7404 : Fin 4 → Int := fun i => [234497, 348863, 283771, 395908].getD i.val 0

example : ∀ i : Fin 4, (run (ring 3 gap7404) 100000 (fun _ => 0) (24 * 4) (start 4 (launches 3 24))).writes i =
    [3, 4, 3, 4].getD i.val 0 := by decide +kernel

def lo7404k0 : Fin 4 → Int := fun i => [-3922, -7987, -5642, -3914].getD i.val 0
def hi7404k0 : Fin 4 → Int := fun i => [3154, 7441, 4805, 3359].getD i.val 0

example : Own (N := 3) gap7404 100000 lo7404k0 hi7404k0 0 3 := by decide +kernel
example : Own (N := 3) gap7404 100000 lo7404k0 hi7404k0 1 4 := by decide +kernel
example : Own (N := 3) gap7404 100000 lo7404k0 hi7404k0 2 3 := by decide +kernel
example : Own (N := 3) gap7404 100000 lo7404k0 hi7404k0 3 4 := by decide +kernel

def lo7404k3 : Fin 4 → Int := fun i => [-26520, -30693, -28190, -26594].getD i.val 0
def hi7404k3 : Fin 4 → Int := fun i => [25752, 30148, 27352, 26040].getD i.val 0

example : Own (N := 3) gap7404 100000 lo7404k3 hi7404k3 0 3 := by decide +kernel
example : Own (N := 3) gap7404 100000 lo7404k3 hi7404k3 1 4 := by decide +kernel
example : ¬ Own (N := 3) gap7404 100000 lo7404k3 hi7404k3 2 3 := by decide +kernel
example : ¬ Own (N := 3) gap7404 100000 lo7404k3 hi7404k3 3 4 := by decide +kernel

/-! ## Instance 7405 -/

def gap7405 : Fin 4 → Int := fun i => [288959, 307021, 323232, 419289].getD i.val 0

example : ∀ i : Fin 4, (run (ring 3 gap7405) 100000 (fun _ => 0) (26 * 4) (start 4 (launches 3 26))).writes i =
    [3, 4, 4, 5].getD i.val 0 := by decide +kernel

def lo7405k0 : Fin 4 → Int := fun i => [-3912, -3906, -3897, -3925].getD i.val 0
def hi7405k0 : Fin 4 → Int := fun i => [4798, 4476, 2791, 3760].getD i.val 0

example : Own (N := 3) gap7405 100000 lo7405k0 hi7405k0 0 3 := by decide +kernel
example : Own (N := 3) gap7405 100000 lo7405k0 hi7405k0 1 4 := by decide +kernel
example : Own (N := 3) gap7405 100000 lo7405k0 hi7405k0 2 4 := by decide +kernel
example : Own (N := 3) gap7405 100000 lo7405k0 hi7405k0 3 5 := by decide +kernel

def lo7405k3 : Fin 4 → Int := fun i => [-26475, -26499, -26454, -26713].getD i.val 0
def hi7405k3 : Fin 4 → Int := fun i => [27362, 27069, 25347, 26549].getD i.val 0

example : ¬ Own (N := 3) gap7405 100000 lo7405k3 hi7405k3 0 3 := by decide +kernel
example : ¬ Own (N := 3) gap7405 100000 lo7405k3 hi7405k3 1 4 := by decide +kernel
example : ¬ Own (N := 3) gap7405 100000 lo7405k3 hi7405k3 2 4 := by decide +kernel
example : ¬ Own (N := 3) gap7405 100000 lo7405k3 hi7405k3 3 5 := by decide +kernel

/-! ## Instance 7406 -/

def gap7406 : Fin 4 → Int := fun i => [348089, 403224, 327523, 466940].getD i.val 0

example : ∀ i : Fin 4, (run (ring 3 gap7406) 100000 (fun _ => 0) (28 * 4) (start 4 (launches 3 28))).writes i =
    [4, 5, 4, 5].getD i.val 0 := by decide +kernel

def lo7406k0 : Fin 4 → Int := fun i => [-3942, -4521, -4461, -3929].getD i.val 0
def hi7406k0 : Fin 4 → Int := fun i => [2951, 7078, 3648, 3851].getD i.val 0

example : Own (N := 3) gap7406 100000 lo7406k0 hi7406k0 0 4 := by decide +kernel
example : ¬ Own (N := 3) gap7406 100000 lo7406k0 hi7406k0 1 5 := by decide +kernel
example : Own (N := 3) gap7406 100000 lo7406k0 hi7406k0 2 4 := by decide +kernel
example : Own (N := 3) gap7406 100000 lo7406k0 hi7406k0 3 5 := by decide +kernel

def lo7406k3 : Fin 4 → Int := fun i => [-26739, -27401, -26946, -26715].getD i.val 0
def hi7406k3 : Fin 4 → Int := fun i => [25748, 29959, 26133, 26637].getD i.val 0

example : Own (N := 3) gap7406 100000 lo7406k3 hi7406k3 0 4 := by decide +kernel
example : ¬ Own (N := 3) gap7406 100000 lo7406k3 hi7406k3 1 5 := by decide +kernel
example : Own (N := 3) gap7406 100000 lo7406k3 hi7406k3 2 4 := by decide +kernel
example : Own (N := 3) gap7406 100000 lo7406k3 hi7406k3 3 5 := by decide +kernel

/-! ## Instance 7407 -/

def gap7407 : Fin 4 → Int := fun i => [503606, 308415, 252090, 332075].getD i.val 0

example : ∀ i : Fin 4, (run (ring 3 gap7407) 100000 (fun _ => 0) (27 * 4) (start 4 (launches 3 27))).writes i =
    [6, 4, 3, 4].getD i.val 0 := by decide +kernel

def lo7407k0 : Fin 4 → Int := fun i => [-3949, -3891, -3901, -3922].getD i.val 0
def hi7407k0 : Fin 4 → Int := fun i => [4240, 3643, 6939, 4596].getD i.val 0

example : ¬ Own (N := 3) gap7407 100000 lo7407k0 hi7407k0 0 6 := by decide +kernel
example : Own (N := 3) gap7407 100000 lo7407k0 hi7407k0 1 4 := by decide +kernel
example : Own (N := 3) gap7407 100000 lo7407k0 hi7407k0 2 3 := by decide +kernel
example : Own (N := 3) gap7407 100000 lo7407k0 hi7407k0 3 4 := by decide +kernel

def lo7407k3 : Fin 4 → Int := fun i => [-26955, -26424, -26408, -26613].getD i.val 0
def hi7407k3 : Fin 4 → Int := fun i => [27246, 26176, 29445, 27287].getD i.val 0

example : ¬ Own (N := 3) gap7407 100000 lo7407k3 hi7407k3 0 6 := by decide +kernel
example : ¬ Own (N := 3) gap7407 100000 lo7407k3 hi7407k3 1 4 := by decide +kernel
example : Own (N := 3) gap7407 100000 lo7407k3 hi7407k3 2 3 := by decide +kernel
example : Own (N := 3) gap7407 100000 lo7407k3 hi7407k3 3 4 := by decide +kernel

/-! ## Instance 7408 -/

def gap7408 : Fin 4 → Int := fun i => [400622, 312817, 419329, 440436].getD i.val 0

example : ∀ i : Fin 4, (run (ring 3 gap7408) 100000 (fun _ => 0) (29 * 4) (start 4 (launches 3 29))).writes i =
    [5, 4, 5, 5].getD i.val 0 := by decide +kernel

def lo7408k0 : Fin 4 → Int := fun i => [-3924, -3895, -3918, -3904].getD i.val 0
def hi7408k0 : Fin 4 → Int := fun i => [2969, 3025, 3168, 4697].getD i.val 0

example : ¬ Own (N := 3) gap7408 100000 lo7408k0 hi7408k0 0 5 := by decide +kernel
example : Own (N := 3) gap7408 100000 lo7408k0 hi7408k0 1 4 := by decide +kernel
example : Own (N := 3) gap7408 100000 lo7408k0 hi7408k0 2 5 := by decide +kernel
example : Own (N := 3) gap7408 100000 lo7408k0 hi7408k0 3 5 := by decide +kernel

def lo7408k3 : Fin 4 → Int := fun i => [-26734, -26463, -26675, -26606].getD i.val 0
def hi7408k3 : Fin 4 → Int := fun i => [25779, 25593, 25925, 27399].getD i.val 0

example : ¬ Own (N := 3) gap7408 100000 lo7408k3 hi7408k3 0 5 := by decide +kernel
example : ¬ Own (N := 3) gap7408 100000 lo7408k3 hi7408k3 1 4 := by decide +kernel
example : ¬ Own (N := 3) gap7408 100000 lo7408k3 hi7408k3 2 5 := by decide +kernel
example : Own (N := 3) gap7408 100000 lo7408k3 hi7408k3 3 5 := by decide +kernel

/-! ## Instance 7409 -/

def gap7409 : Fin 4 → Int := fun i => [435563, 287792, 349142, 496491].getD i.val 0

example : ∀ i : Fin 4, (run (ring 3 gap7409) 100000 (fun _ => 0) (27 * 4) (start 4 (launches 3 27))).writes i =
    [5, 3, 4, 5].getD i.val 0 := by decide +kernel

def lo7409k0 : Fin 4 → Int := fun i => [-3919, -3921, -7943, -4489].getD i.val 0
def hi7409k0 : Fin 4 → Int := fun i => [3241, 3643, 7774, 5421].getD i.val 0

example : Own (N := 3) gap7409 100000 lo7409k0 hi7409k0 0 5 := by decide +kernel
example : Own (N := 3) gap7409 100000 lo7409k0 hi7409k0 1 3 := by decide +kernel
example : Own (N := 3) gap7409 100000 lo7409k0 hi7409k0 2 4 := by decide +kernel
example : ¬ Own (N := 3) gap7409 100000 lo7409k0 hi7409k0 3 5 := by decide +kernel

def lo7409k3 : Fin 4 → Int := fun i => [-26678, -26519, -30526, -27234].getD i.val 0
def hi7409k3 : Fin 4 → Int := fun i => [26001, 26241, 30358, 28166].getD i.val 0

example : Own (N := 3) gap7409 100000 lo7409k3 hi7409k3 0 5 := by decide +kernel
example : ¬ Own (N := 3) gap7409 100000 lo7409k3 hi7409k3 1 3 := by decide +kernel
example : Own (N := 3) gap7409 100000 lo7409k3 hi7409k3 2 4 := by decide +kernel
example : ¬ Own (N := 3) gap7409 100000 lo7409k3 hi7409k3 3 5 := by decide +kernel

/-! ## Instance 7410 -/

def gap7410 : Fin 4 → Int := fun i => [237727, 449375, 295931, 448714].getD i.val 0

example : ∀ i : Fin 4, (run (ring 3 gap7410) 100000 (fun _ => 0) (26 * 4) (start 4 (launches 3 26))).writes i =
    [3, 5, 3, 5].getD i.val 0 := by decide +kernel

def lo7410k0 : Fin 4 → Int := fun i => [-5624, -3930, -3897, -8016].getD i.val 0
def hi7410k0 : Fin 4 → Int := fun i => [5767, 4593, 4157, 8188].getD i.val 0

example : Own (N := 3) gap7410 100000 lo7410k0 hi7410k0 0 3 := by decide +kernel
example : Own (N := 3) gap7410 100000 lo7410k0 hi7410k0 1 5 := by decide +kernel
example : Own (N := 3) gap7410 100000 lo7410k0 hi7410k0 2 3 := by decide +kernel
example : Own (N := 3) gap7410 100000 lo7410k0 hi7410k0 3 5 := by decide +kernel

def lo7410k3 : Fin 4 → Int := fun i => [-28082, -26776, -26387, -30894].getD i.val 0
def hi7410k3 : Fin 4 → Int := fun i => [28225, 27439, 26647, 31066].getD i.val 0

example : Own (N := 3) gap7410 100000 lo7410k3 hi7410k3 0 3 := by decide +kernel
example : Own (N := 3) gap7410 100000 lo7410k3 hi7410k3 1 5 := by decide +kernel
example : ¬ Own (N := 3) gap7410 100000 lo7410k3 hi7410k3 2 3 := by decide +kernel
example : Own (N := 3) gap7410 100000 lo7410k3 hi7410k3 3 5 := by decide +kernel

/-! ## Instance 7411 -/

def gap7411 : Fin 4 → Int := fun i => [361051, 339248, 471652, 411413].getD i.val 0

example : ∀ i : Fin 4, (run (ring 3 gap7411) 100000 (fun _ => 0) (28 * 4) (start 4 (launches 3 28))).writes i =
    [4, 4, 5, 5].getD i.val 0 := by decide +kernel

def lo7411k0 : Fin 4 → Int := fun i => [-3923, -3917, -3910, -3919].getD i.val 0
def hi7411k0 : Fin 4 → Int := fun i => [2809, 3163, 3910, 3732].getD i.val 0

example : Own (N := 3) gap7411 100000 lo7411k0 hi7411k0 0 4 := by decide +kernel
example : Own (N := 3) gap7411 100000 lo7411k0 hi7411k0 1 4 := by decide +kernel
example : Own (N := 3) gap7411 100000 lo7411k0 hi7411k0 2 5 := by decide +kernel
example : Own (N := 3) gap7411 100000 lo7411k0 hi7411k0 3 5 := by decide +kernel

def lo7411k3 : Fin 4 → Int := fun i => [-26630, -26550, -26581, -26646].getD i.val 0
def hi7411k3 : Fin 4 → Int := fun i => [25515, 25796, 26581, 26459].getD i.val 0

example : Own (N := 3) gap7411 100000 lo7411k3 hi7411k3 0 4 := by decide +kernel
example : Own (N := 3) gap7411 100000 lo7411k3 hi7411k3 1 4 := by decide +kernel
example : Own (N := 3) gap7411 100000 lo7411k3 hi7411k3 2 5 := by decide +kernel
example : ¬ Own (N := 3) gap7411 100000 lo7411k3 hi7411k3 3 5 := by decide +kernel

/-! ## Instance 7412 -/

def gap7412 : Fin 4 → Int := fun i => [426724, 454554, 488891, 524184].getD i.val 0

example : ∀ i : Fin 4, (run (ring 3 gap7412) 100000 (fun _ => 0) (31 * 4) (start 4 (launches 3 31))).writes i =
    [5, 5, 5, 6].getD i.val 0 := by decide +kernel

def lo7412k0 : Fin 4 → Int := fun i => [-3893, -4518, -3927, -3911].getD i.val 0
def hi7412k0 : Fin 4 → Int := fun i => [2786, 4652, 2812, 5074].getD i.val 0

example : Own (N := 3) gap7412 100000 lo7412k0 hi7412k0 0 5 := by decide +kernel
example : Own (N := 3) gap7412 100000 lo7412k0 hi7412k0 1 5 := by decide +kernel
example : Own (N := 3) gap7412 100000 lo7412k0 hi7412k0 2 5 := by decide +kernel
example : Own (N := 3) gap7412 100000 lo7412k0 hi7412k0 3 6 := by decide +kernel

def lo7412k3 : Fin 4 → Int := fun i => [-26544, -27391, -26739, -26706].getD i.val 0
def hi7412k3 : Fin 4 → Int := fun i => [25437, 27525, 25623, 27868].getD i.val 0

example : Own (N := 3) gap7412 100000 lo7412k3 hi7412k3 0 5 := by decide +kernel
example : Own (N := 3) gap7412 100000 lo7412k3 hi7412k3 1 5 := by decide +kernel
example : ¬ Own (N := 3) gap7412 100000 lo7412k3 hi7412k3 2 5 := by decide +kernel
example : ¬ Own (N := 3) gap7412 100000 lo7412k3 hi7412k3 3 6 := by decide +kernel

end NetworkStability.RingNetwork.Predicted
