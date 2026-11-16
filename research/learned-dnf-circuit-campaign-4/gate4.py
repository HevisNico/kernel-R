"""Campaign 4: the kernel gate. Writes the Lean file that checks, for each measured instance and each of the two
budgets, `checkCascadeValid`, `checkTrainingSeparation` and `checkCascadeCalibrationOneSided` (the Boolean
checkers of research/learned-coincidence, proved sound and complete at 2e586aa, merged by #178) on the predicted
observation of predicted.py, and asserts the verdict the Python gives: `= true` where it says eligible (K0) or that
all three outputs have room (K3), `= false` elsewhere. The file compiles only if Lean agrees with the Python on
every instance and budget. For each instance that passes under K0, the file also derives with
`two_layer_monotone_recognition_one_sided` that the predicted outputs of the second layer are the cascade's outputs.

  gate4.py lean PREDICTED.json OUT.lean          the gate of the campaign
  gate4.py cases CASES.json OUT.lean             the gate on the cases P0 to P6 (rehearsal)

Python's own verdict on the timing of an observation (`timing_ok`) mirrors the decoder, the route and the separation
of the kernel's checkers; the scores' part of the verdict is predicted.py's room.
"""
from fractions import Fraction as F
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import predicted as P                                   # noqa: E402
from c4 import dnf                                      # noqa: E402

THEORY = HERE.parent / "learned-coincidence"


def r(x):
    x = F(x)
    return f"({x.numerator} : Rat)" if x.denominator == 1 else f"({x.numerator} / {x.denominator} : Rat)"


def read_lean(d):
    arr = ", ".join("none" if a is None else f"some {r(a)}" for a in d["arrivals"])
    em = ", ".join(r(e) for e in d["emissions"])
    return f"datedRead {r(d['start'])} #v[{arr}] [{em}] ({d['value']} : Int)"


def word_of(key):
    """Index of an external pattern (A the most significant bit), as maskIndex."""
    s = set(key) - {"-"}
    return sum(8 >> i for i, x in enumerate("ABCD") if x in s)


def key_of(word):
    return "".join(x for i, x in enumerate("ABCD") if word & (8 >> i)) or "-"


def cascade_lean(name, x, K):
    g, h, d, b = x["guarded"]["gain"], x["guarded"]["help"], x["guarded"]["dose"], x["budgets"][f"K{K}"]
    return f"""def {name} : Cascade 2 1 4 where
  first := {{
    target := term, tests := [],
    initialGain := fun a j => ((#v[#v[{g['a1']}, {g['a2']}, 0, 0], #v[0, 0, {g['b1']}, {g['b2']}]] : Vector (Vector Nat 4) 2).get a).get j,
    help := fun a => (#v[{h['a']}, {h['b']}] : Vector Nat 2).get a, threshold := fun _ => {P.THETA},
    trainingError := fun a => (#v[{b['a']['training']}, {b['b']['training']}] : Vector Nat 2).get a,
    testingError := fun a => (#v[{b['a']['testing']}, {b['b']['testing']}] : Vector Nat 2).get a,
    dose := {d['a']}, maxWrites := {x['Q1']}, rail := {P.RAIL}
  }}
  second := {{
    lines := fun _ _ => true, alwaysFire := fun _ => false,
    initialGain := fun _ j => (#v[{g['c1']}, {g['c2']}] : Vector Nat 2).get j, help := fun _ => {h['c']}, threshold := fun _ => {P.THETA},
    trainingError := fun _ => {b['c']['training']}, testingError := fun _ => {b['c']['testing']},
    dose := {d['c']}, maxWrites := {x['Q2']}, rail := {P.RAIL}
  }}
  delay := fun _ _ => 3 / 2
  heldOut := []                                      -- amendment 1, point 6
"""


def trace_lean(name, cname, o):
    ft = "[" + ", ".join("[" + ", ".join(read_lean(c) for c in row) + "]" for row in o["firstTrain"]) + "]"
    te = "[" + ", ".join("[" + ", ".join(read_lean(c) for c in row) + "]" for row in o["teach"]) + "]"
    st = "[" + ", ".join(read_lean(c) for c in o["secondTrain"]) + "]"
    fx = "[" + ", ".join("[" + ", ".join(read_lean(c) for c in o["firstTest"][key_of(w)]) + "]" for w in range(16)) + "]"
    sx = "[" + ", ".join(read_lean(o["secondTest"][key_of(w)]) for w in range(16)) + "]"
    sc = "[" + ", ".join("#v[" + ", ".join(f"({o['scores'][key_of(w)][m]} : Int)" for m in ("-", "2", "1", "12")) + "]" for w in range(16)) + "]"
    return f"""private def {name}_ft : List (List (ReadObservation 4)) := {ft}
private def {name}_te : List (List (ReadObservation 4)) := {te}
private def {name}_st : List (ReadObservation 2) := {st}
private def {name}_fx : List (List (ReadObservation 4)) := {fx}
private def {name}_sx : List (ReadObservation 2) := {sx}
private def {name}_sc : List (Vector Int 4) := {sc}

def {name} : TraceTables {cname} where
  firstTrain := Vector.ofFn fun r => Vector.ofFn fun a => ({name}_ft.getD r.val []).getD a.val empty4
  teach := Vector.ofFn fun n => Vector.ofFn fun a => ({name}_te.getD n.val []).getD a.val empty4
  secondTrain := Vector.ofFn fun n => {name}_st.getD n.val empty2
  firstTest := Vector.ofFn fun w => Vector.ofFn fun a => ({name}_fx.getD w.val []).getD a.val empty4
  secondTest := Vector.ofFn fun w => Vector.ofFn fun _ => {name}_sx.getD w.val empty2
  scores := Vector.ofFn fun w => Vector.ofFn fun _ => {name}_sc.getD w.val #v[0, 0, 0, 0]
"""


HEADER = """import MonotonePremiseSoundness
import MonotoneOneSidedRecognition

/-! Campaign 4's kernel gate, written by gate4.py from {source}. Each `checks_*` theorem asserts the verdict of the
Python; the file compiles only if the kernel agrees. -/

namespace LearnedCoincidence.MonotoneDNF.PremiseCheck.Campaign4

open TwoLayer (SlotTiming ReadObservation)

private def term (a : Fin 2) : Pattern 4 :=
  if a = 0 then pattern [0, 1] else pattern [2, 3]

private def empty4 : ReadObservation 4 := datedRead 0 #v[none, none, none, none] [] 0
private def empty2 : ReadObservation 2 := datedRead 0 #v[none, none] [] 0

def left : SlotTiming := ⟨{sa}, {da}, {ua}⟩
def right : SlotTiming := ⟨{sc}, {dc}, {uc}⟩

def checks (p : Cascade 2 1 4) (t : TraceTables p) : Bool :=
  checkCascadeValid p &&
  checkTrainingSeparation p left right t.observations &&
  checkCascadeCalibrationOneSided p left right t.observations t.scoreAt

"""


def one(tag, x, K, verdict, derive):
    cn, tn = f"cascade_{tag}_K{K}", f"trace_{tag}_K{K}"
    out = cascade_lean(cn, x, K) + "\n" + trace_lean(tn, cn, x["observation"]) + "\n"
    out += f"""set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks_{tag}_K{K} : checks {cn} {tn} = {'true' if verdict else 'false'} := by decide +kernel
"""
    if verdict and derive:
        out += f"""
/-- The predicted outputs of the second layer follow from the measures by kernel check. -/
theorem outputs_{tag}_K{K} : ∀ x i, ({tn}.observations.secondTest x i).fired = output {cn} i x := by
  have checked := checks_{tag}_K{K}
  unfold checks at checked
  obtain ⟨parameterAndCalendar, calibration⟩ := Bool.and_eq_true_iff.mp checked
  obtain ⟨params, calendar⟩ := Bool.and_eq_true_iff.mp parameterAndCalendar
  exact (two_layer_monotone_recognition_one_sided 2 1 4 {cn}
    (cascade_valid_checker_sound _ _ _ _ params) left right
    {tn}.observations {tn}.scoreAt
    (training_separation_checker_sound _ _ _ _ _ _ _ calendar)
    (cascade_calibration_one_sided_checker_sound _ _ _ _ _ _ _ _ calibration)).2
"""
    return out + "\n"


def header(source):
    return HEADER.format(source=source, sa=r(P.SKEW_A), da=r(P.DEADLINE_A), ua=r(P.DURATION_A), sc=r(P.SKEW_C), dc=r(P.DEADLINE_C), uc=r(P.DURATION_C))


# ------------------------------------------------------------------------------- the Python mirror of the timing

def timing_ok(o, Q1, Q2):
    """The decoder (arrivals within the skew, at most one emission after every arrival and before the deadline),
    the route (every arrival on c is its upstream emission plus 3/2) and the separation of the training slots, on a
    serialized predicted observation."""
    f = lambda s: None if s is None else F(s)

    def decoder(d, skew, deadline):
        start, arr, em = F(d["start"]), [f(a) for a in d["arrivals"]], [F(e) for e in d["emissions"]]
        if any(a is not None and not (start <= a <= start + skew) for a in arr):
            return False
        if len(em) > 1:
            return False
        if em and not (start <= em[0] <= start + deadline and all(a is None or a <= em[0] for a in arr)):
            return False
        return True
    reads1 = [c for row in o["firstTrain"] + o["teach"] for c in row] + [c for k in o["firstTest"] for c in o["firstTest"][k]]
    reads2 = o["secondTrain"] + list(o["secondTest"].values())
    ok = all(decoder(d, P.SKEW_A, P.DEADLINE_A) for d in reads1) and all(decoder(d, P.SKEW_C, P.DEADLINE_C) for d in reads2)
    head = lambda d: F(d["emissions"][0]) if d["emissions"] else None
    for n, row in enumerate(o["teach"]):
        want = [None if head(c) is None else head(c) + F(3, 2) for c in row]
        ok = ok and [f(a) for a in o["secondTrain"][n]["arrivals"]] == want
    for k, row in o["firstTest"].items():
        want = [None if head(c) is None else head(c) + F(3, 2) for c in row]
        ok = ok and [f(a) for a in o["secondTest"][k]["arrivals"]] == want
    starts1 = [F(row[0]["start"]) for row in o["firstTrain"]]
    ok = ok and all(starts1[i] + P.DURATION_A <= starts1[i + 1] for i in range(len(starts1) - 1))
    lessons = [(F(row[0]["start"]), F(o["secondTrain"][n]["start"])) for n, row in enumerate(o["teach"])]
    tests = [F(o["firstTest"][k][0]["start"]) for k in o["firstTest"]] + [F(d["start"]) for d in o["secondTest"].values()]
    later = [s for s, _ in lessons] + [s for _, s in lessons]
    ok = ok and all(starts1[-1] + P.DURATION_A <= s for s in later + tests)
    for n, (a, c) in enumerate(lessons):
        nxt = [s for m, (x, y) in enumerate(lessons) if m > n for s in (x, y)] + tests
        ok = ok and all(a + P.DURATION_A <= s and c + P.DURATION_C <= s for s in nxt)
    return ok


def verdicts(x):
    """The Python's verdict per budget: K0 eligibility, K3 room of all three outputs, each with the timing."""
    t = timing_ok(x["observation"], x["Q1"], x["Q2"])
    return dict(K0=bool(x["eligible"]) and t, K3=all(x["room_at_K3"].values()) and t)


def lean_file(instances, source, derive=True):
    out = header(source)
    for x in instances:
        v = verdicts(x)
        for K in (0, 3):
            out += one(x["tag"], x, K, v[f"K{K}"], derive)
    return out + "end LearnedCoincidence.MonotoneDNF.PremiseCheck.Campaign4\n"


def main():
    what, src, dst = sys.argv[1], Path(sys.argv[2]), Path(sys.argv[3])
    data = json.loads(src.read_text())
    if what == "lean":
        xs = [dict(x, tag=str(x["seed"])) for x in data["instances"] if x.get("measured") and "observation" in x]
    else:
        xs = data["cases"]
    dst.write_text(lean_file(xs, src.name))


if __name__ == "__main__":
    main()
