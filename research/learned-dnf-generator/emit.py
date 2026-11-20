"""The Lean writer of the parameterized kernel gate (GENERATOR_DESIGN.md, 3.2 and 3.3).

`lean_file(specs, verdicts, source)` writes one Lean file for loaded specs (spec.load) of one style and one shape.
Each named budget gets `cascade_<tag>_<K>`, `trace_<tag>_<K>` and

  theorem checks_<tag>_<K> : checks cascade trace = true|false := by decide +kernel

so the file compiles only if Lean's value equals the asserted one. In the generic style, each checker also gets its
own theorem (`valid_`, `separation_`, `calibration_`, named as campaign 5's cases.py `lean_targets`). Where the
asserted conjunction is true and `derive` is set, `outputs_<tag>_<K>` derives the second layer's outputs with
`two_layer_monotone_recognition_one_sided A B M`.

Style "gate4" writes the text of campaign 5's gate4.py; for its shape Cascade 2 1 4 the output is byte-identical
(tests/test_legacy.py). The literal forms are rules on the values, not on the shape: a per-cell field is a `Vector`
table (or, where gate4 does it, `fun _ => v` when constant), so the 2 1 4 case comes out as gate4 writes it.
"""
from fractions import Fraction as F


def r(x):
    """A rational as gate4.r writes it."""
    x = F(x)
    return f"({x.numerator} : Rat)" if x.denominator == 1 else f"({x.numerator} / {x.denominator} : Rat)"


def plain(x):
    """A rational without ascription: `3 / 2`, `0` (gate4 writes the delay so)."""
    x = F(x)
    return f"{x.numerator}" if x.denominator == 1 else f"{x.numerator} / {x.denominator}"


def vec(xs):
    return "#v[" + ", ".join(str(x) for x in xs) + "]"


def bool_lean(b):
    return "true" if b else "false"


def read_lean(d):
    arr = ", ".join("none" if a is None else f"some {r(a)}" for a in d["arrivals"])
    em = ", ".join(r(e) for e in d["emissions"])
    return f"datedRead {r(d['start'])} #v[{arr}] [{em}] ({d['value']} : Int)"


def pattern_lean(x):
    return "pattern [" + ", ".join(str(j) for j in sorted(x)) + "]"


def per_cell(name, xs, n, var="a", const_ok=False):
    """A per-cell Nat field: `fun _ => v` when const_ok and constant, else a Vector table."""
    if const_ok and n > 0 and len(set(xs)) == 1:
        return f"{name} := fun _ => {xs[0]}"
    if n == 0:
        return f"{name} := fun {var} => {var}.elim0"
    return f"{name} := fun {var} => ({vec(xs)} : Vector Nat {n}).get {var}"


def cascade_lean(name, s, K, style):
    A, B, M = s["A"], s["B"], s["M"]
    f, g, b = s["first"], s["second"], s["budgets"][K]
    if A == 0:
        ig1 = "initialGain := fun a _ => a.elim0"
    else:
        ig1 = f"initialGain := fun a j => (({vec(vec(row) for row in f['initialGain'])} : Vector (Vector Nat {M}) {A}).get a).get j"
    first = f"""  first := {{
    target := term, tests := [],
    {ig1},
    {per_cell('help', f['help'], A)}, {per_cell('threshold', f['threshold'], A, const_ok=True)},
    {per_cell('trainingError', b['first']['training'], A)},
    {per_cell('testingError', b['first']['testing'], A)},
    dose := {f['dose']}, maxWrites := {f['maxWrites']}, rail := {f['rail']}
  }}
"""
    if B == 1:
        lines = "fun _ _ => true" if len(g["lines"][0]) == A else (
            f"fun _ j => ({vec(bool_lean(j in g['lines'][0]) for j in range(A))} : Vector Bool {A}).get j" if A else "fun _ j => j.elim0")
        af = f"fun _ => {bool_lean(g['alwaysFire'][0])}"
        ig2 = f"fun _ j => ({vec(g['initialGain'][0])} : Vector Nat {A}).get j" if A else "fun _ j => j.elim0"
        sec = f"""  second := {{
    lines := {lines}, alwaysFire := {af},
    initialGain := {ig2}, help := fun _ => {g['help'][0]}, threshold := fun _ => {g['threshold'][0]},
    trainingError := fun _ => {b['second']['training'][0]}, testingError := fun _ => {b['second']['testing'][0]},
    dose := {g['dose']}, maxWrites := {g['maxWrites']}, rail := {g['rail']}
  }}
"""
    else:
        if all(len(ls) == A for ls in g["lines"]):
            lines = "fun _ _ => true"
        elif A == 0:
            lines = "fun _ j => j.elim0"
        else:
            lines = f"fun i j => (({vec(vec(bool_lean(j in ls) for j in range(A)) for ls in g['lines'])} : Vector (Vector Bool {A}) {B}).get i).get j"
        af = (f"fun _ => {bool_lean(g['alwaysFire'][0])}" if len(set(g["alwaysFire"])) == 1
              else f"fun i => ({vec(bool_lean(x) for x in g['alwaysFire'])} : Vector Bool {B}).get i")
        ig2 = ("fun _ j => j.elim0" if A == 0 else
               f"fun i j => (({vec(vec(row) for row in g['initialGain'])} : Vector (Vector Nat {A}) {B}).get i).get j")
        sec = f"""  second := {{
    lines := {lines}, alwaysFire := {af},
    initialGain := {ig2}, {per_cell('help', g['help'], B, 'i')}, {per_cell('threshold', g['threshold'], B, 'i', const_ok=True)},
    {per_cell('trainingError', b['second']['training'], B, 'i')}, {per_cell('testingError', b['second']['testing'], B, 'i')},
    dose := {g['dose']}, maxWrites := {g['maxWrites']}, rail := {g['rail']}
  }}
"""
    flat = [v for row in s["delay"] for v in row]
    if A == 0 or B == 0:
        delay = "fun _ _ => 0"
    elif len(set(flat)) == 1:
        delay = f"fun _ _ => {plain(flat[0])}"
    else:
        delay = f"fun i a => (({vec(vec(r(v) for v in row) for row in s['delay'])} : Vector (Vector Rat {A}) {B}).get i).get a"
    held = "[" + ", ".join(pattern_lean(x) for x in s["heldOut"]) + "]"
    held_line = f"  heldOut := {held}" + ("                                      -- amendment 1, point 6" if style == "gate4" else "")
    return f"def {name} : Cascade {A} {B} {M} where\n" + first + sec + f"  delay := {delay}\n{held_line}\n"


def empty_name(n):
    return f"empty{n}"


def zeros(n):
    return vec([0] * n)


def trace_lean(name, cname, s):
    A, B, M = s["A"], s["B"], s["M"]
    o = s["observation"]
    rows = lambda t: "[" + ", ".join("[" + ", ".join(read_lean(c) for c in row) + "]" for row in t) + "]"
    flat = lambda t: "[" + ", ".join(read_lean(c) for c in t) + "]"
    eM, eA = empty_name(M), empty_name(A)
    out = f"""private def {name}_ft : List (List (ReadObservation {M})) := {rows(o['firstTrain'])}
private def {name}_te : List (List (ReadObservation {M})) := {rows(o['teach'])}
private def {name}_st : List (ReadObservation {A}) := {flat(o['secondTrain'])}
private def {name}_fx : List (List (ReadObservation {M})) := {rows(o['firstTest'])}
"""
    if B == 1:
        sx = flat([row[0] for row in o["secondTest"]])
        sc = "[" + ", ".join("#v[" + ", ".join(f"({v} : Int)" for v in row[0]) + "]" for row in o["scores"]) + "]"
        out += f"""private def {name}_sx : List (ReadObservation {A}) := {sx}
private def {name}_sc : List (Vector Int {2 ** A}) := {sc}
"""
        st_fx = f"Vector.ofFn fun w => Vector.ofFn fun _ => {name}_sx.getD w.val {eA}"
        st_sc = f"Vector.ofFn fun w => Vector.ofFn fun _ => {name}_sc.getD w.val {zeros(2 ** A)}"
    else:
        sx = rows(o["secondTest"])
        sc = "[" + ", ".join("[" + ", ".join("#v[" + ", ".join(f"({v} : Int)" for v in col) + "]" for col in row) + "]" for row in o["scores"]) + "]"
        out += f"""private def {name}_sx : List (List (ReadObservation {A})) := {sx}
private def {name}_sc : List (List (Vector Int {2 ** A})) := {sc}
"""
        st_fx = f"Vector.ofFn fun w => Vector.ofFn fun i => ({name}_sx.getD w.val []).getD i.val {eA}"
        st_sc = f"Vector.ofFn fun w => Vector.ofFn fun i => ({name}_sc.getD w.val []).getD i.val {zeros(2 ** A)}"
    out += f"""
def {name} : TraceTables {cname} where
  firstTrain := Vector.ofFn fun r => Vector.ofFn fun a => ({name}_ft.getD r.val []).getD a.val {eM}
  teach := Vector.ofFn fun n => Vector.ofFn fun a => ({name}_te.getD n.val []).getD a.val {eM}
  secondTrain := Vector.ofFn fun n => {name}_st.getD n.val {eA}
  firstTest := Vector.ofFn fun w => Vector.ofFn fun a => ({name}_fx.getD w.val []).getD a.val {eM}
  secondTest := {st_fx}
  scores := {st_sc}
"""
    return out


def term_lean(s):
    A, M = s["A"], s["M"]
    ts = s["first"]["terms"]
    if A == 0:
        return f"private def term : Fin 0 → Pattern {M} := Fin.elim0\n"
    if A == 1:
        return f"private def term : Fin 1 → Pattern {M} := fun _ => {pattern_lean(ts[0])}\n"
    body = ""
    for a, t in enumerate(ts[:-1]):
        body += f"if a = {a} then {pattern_lean(t)} else "
    body += pattern_lean(ts[-1])
    return f"private def term (a : Fin {A}) : Pattern {M} :=\n  {body}\n"


def empties(s):
    out = ""
    for n in sorted({s["M"], s["A"]}, reverse=True):
        nones = ", ".join(["none"] * n)
        out += f"private def {empty_name(n)} : ReadObservation {n} := datedRead 0 #v[{nones}] [] 0\n"
    return out


def header(s, source):
    lt, rt = s["timing"]["left"], s["timing"]["right"]
    A, B, M = s["A"], s["B"], s["M"]
    ns = s["lean"]["namespace"]
    if s["lean"]["style"] == "gate4":
        doc = f"""/-! Campaign 4's kernel gate, written by gate4.py from {source}. Each `checks_*` theorem asserts the verdict of the
Python; the file compiles only if the kernel agrees. -/"""
    else:
        doc = f"""/-! A kernel gate written by the parameterized generator (research/learned-dnf-generator/emit.py) from {source}.
Shape `Cascade {A} {B} {M}`. Each `checks_*`, `valid_*`, `separation_*` and `calibration_*` theorem asserts a verdict
by `decide +kernel`; the file compiles only if the kernel agrees with every asserted value. -/"""
    return f"""import MonotonePremiseSoundness
import MonotoneOneSidedRecognition

{doc}

namespace {ns}

open TwoLayer (SlotTiming ReadObservation)

{term_lean(s)}
{empties(s)}
def left : SlotTiming := ⟨{r(lt['skew'])}, {r(lt['deadline'])}, {r(lt['duration'])}⟩
def right : SlotTiming := ⟨{r(rt['skew'])}, {r(rt['deadline'])}, {r(rt['duration'])}⟩

def checks (p : Cascade {A} {B} {M}) (t : TraceTables p) : Bool :=
  checkCascadeValid p &&
  checkTrainingSeparation p left right t.observations &&
  checkCascadeCalibrationOneSided p left right t.observations t.scoreAt

"""


CHECKERS = ("checkCascadeValid", "checkTrainingSeparation", "checkCascadeCalibrationOneSided")


def one(s, K, verdict, per_checker=None):
    """verdict: the asserted conjunction; per_checker: {checker: bool} (generic style)."""
    tag = s["tag"]
    A, B, M = s["A"], s["B"], s["M"]
    cn, tn = f"cascade_{tag}_{K}", f"trace_{tag}_{K}"
    out = cascade_lean(cn, s, K, s["lean"]["style"]) + "\n" + trace_lean(tn, cn, s) + "\n"
    out += f"""set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks_{tag}_{K} : checks {cn} {tn} = {bool_lean(verdict)} := by decide +kernel
"""
    if per_checker is not None:
        b = lambda c: bool_lean(per_checker[c])
        out += f"""
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_{tag}_{K} : checkCascadeValid {cn} = {b(CHECKERS[0])} := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_{tag}_{K} : checkTrainingSeparation {cn} left right {tn}.observations = {b(CHECKERS[1])} := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_{tag}_{K} : checkCascadeCalibrationOneSided {cn} left right {tn}.observations {tn}.scoreAt = {b(CHECKERS[2])} := by decide +kernel
"""
    if verdict and s["lean"]["derive"]:
        out += f"""
/-- The predicted outputs of the second layer follow from the measures by kernel check. -/
theorem outputs_{tag}_{K} : ∀ x i, ({tn}.observations.secondTest x i).fired = output {cn} i x := by
  have checked := checks_{tag}_{K}
  unfold checks at checked
  obtain ⟨parameterAndCalendar, calibration⟩ := Bool.and_eq_true_iff.mp checked
  obtain ⟨params, calendar⟩ := Bool.and_eq_true_iff.mp parameterAndCalendar
  exact (two_layer_monotone_recognition_one_sided {A} {B} {M} {cn}
    (cascade_valid_checker_sound _ _ _ _ params) left right
    {tn}.observations {tn}.scoreAt
    (training_separation_checker_sound _ _ _ _ _ _ _ calendar)
    (cascade_calibration_one_sided_checker_sound _ _ _ _ _ _ _ _ calibration)).2
"""
    return out + "\n"


def lean_file(specs, verdicts, source, per_checker=None, extra=""):
    """specs: loaded specs, all of one style, shape, namespace and timing (they share `term`, `left`, `right`).
    verdicts: {(tag, K): bool}; per_checker: {(tag, K): {checker: bool}} or None. extra: Lean text before `end`."""
    s0 = specs[0]
    for s in specs[1:]:
        for k in ("A", "B", "M", "timing"):
            assert s[k] == s0[k], f"one file holds one shape and one timing: {k}"
        assert s["first"]["terms"] == s0["first"]["terms"] and s["lean"]["namespace"] == s0["lean"]["namespace"]
        assert s["lean"]["style"] == s0["lean"]["style"]
    out = header(s0, source)
    for s in specs:
        for K in s["budgets"]:
            pc = None if per_checker is None else per_checker[(s["tag"], K)]
            out += one(s, K, verdicts[(s["tag"], K)], pc)
    return out + extra + f"end {s0['lean']['namespace']}\n"
