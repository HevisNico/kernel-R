"""The Lean writer of the layered kernel gate (LAYERED_GENERATOR_DESIGN.md, section 4).

`lean_file(specs, verdicts, source)` writes one Lean file for loaded specs (lspec.load). For each spec, with suffix
T = its tag, it writes:

  timing_T_k, node_T_k_i, layer_T_k (k = 1..L), circuit_T     the cascade, `.layer (.layer .input t1 n1) t2 n2`
  empty_T_k, rt_T_*, reps_T_k, reads_T_k, train_T_k, test_T     the traces, as list tables read through `getD`
  theorem valid_T       : checkLayeredValid circuit_T = v                        := by decide +kernel
  theorem separation_T  : checkLayeredSeparation circuit_T train_T test_T = v   := by decide +kernel
  theorem training_T    : checkLayeredTrainingCalibration circuit_T train_T = v := by decide +kernel
  theorem reads_T       : checkLayeredReadCalibration circuit_T train_T test_T = v := by decide +kernel
  theorem checks_T      : (the four, &&) = v       by rewriting with the four theorems
  theorem outputs_T     (all four true)            layered_monotone_recognition_one_sided through the soundness lemmas
  theorem function_T    (all four true, a function given): (patterns M).all (predict x 0 == f x) = true

So the file compiles only if Lean's value of every checker equals the asserted one.
"""
from fractions import Fraction as F
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from emit import r, read_lean, pattern_lean, vec, bool_lean  # noqa: E402

CHECKERS = ("checkLayeredValid", "checkLayeredSeparation", "checkLayeredTrainingCalibration", "checkLayeredReadCalibration")
SHORT = dict(zip(CHECKERS, ("valid", "separation", "training", "reads")))
OPT = "set_option maxRecDepth 100000 in\nset_option maxHeartbeats 0 in\n"


def width_below(s, k):
    """The width of layer k - 1 (layer 0 = the M inputs)."""
    return s["M"] if k == 1 else s["widths"][k - 2]


def layer_name(s, k):
    return "(Cascade.input : Cascade {} 0 {})".format(s["M"], s["M"]) if k == 0 else f"layer_{s['tag']}_{k}"


def node_lean(s, k, i, n):
    T, M, W0 = s["tag"], s["M"], width_below(s, k)
    src = vec("none" if j is None else f"some {j}" for j in n["source"])
    dl = vec(r(v) for v in n["delay"])
    st = vec(pattern_lean(x) for x in n["stimulus"])
    cell = (f"{{ gate := .{n['gate']}, initialGain := fun a => ({vec(n['initialGain'])} : Vector Nat 2).get a, "
            f"help := {n['help']}, threshold := {n['threshold']}, trainError := {n['trainError']}, testError := {n['testError']}, "
            f"dose := {n['dose']}, maxWrites := {n['maxWrites']}, rail := {n['rail']} }}")
    return f"""def cell_{T}_{k}_{i} : Cell := {cell}

def node_{T}_{k}_{i} : Node {M} {W0} where
  cell := cell_{T}_{k}_{i}
  source := fun a => ({src} : Vector (Option (Fin {W0})) 2).get a
  delay := fun a => ({dl} : Vector Rat 2).get a
  stimulus := fun g => ({st} : Vector (Pattern {M}) 2).get g
"""


def cascade_lean(s):
    T, M = s["tag"], s["M"]
    out = ""
    for k, lay in enumerate(s["layers"], start=1):
        t = lay["timing"]
        out += f"def timing_{T}_{k} : SlotTiming := ⟨{r(t['skew'])}, {r(t['deadline'])}, {r(t['duration'])}⟩\n\n"
        for i, n in enumerate(lay["nodes"]):
            out += node_lean(s, k, i, n) + "\n"
        W, W0 = s["widths"][k - 1], width_below(s, k)
        lower = ".input" if k == 1 else f"layer_{T}_{k - 1}"
        nodes = vec(f"node_{T}_{k}_{i}" for i in range(W))
        out += f"def layer_{T}_{k} : Cascade {M} {k} {W} :=\n  .layer {lower} timing_{T}_{k} fun i => ({nodes} : Vector (Node {M} {W0}) {W}).get i\n\n"
    out += f"def circuit_{T} : Cascade {M} {len(s['layers'])} {s['widths'][-1]} := layer_{T}_{len(s['layers'])}\n\n"
    return out


def rt_term(s, rt, k):
    """A ReadTrace of layers 1..k as a Lean term (expected type ReadTrace layer_T_k)."""
    M = s["M"]
    if k == 0:
        arr = vec("none" if a is None else f"some {r(a)}" for a in rt["arrivals"])
        return f"(fun j => ({arr} : Vector (Option Rat) {M}).get j)"
    W = s["widths"][k - 1]
    cells = rt["layers"][k - 1]
    reads = vec(read_lean(c["read"]) for c in cells)
    scores = vec(vec(f"({v} : Int)" for v in c["scores"]) for c in cells)
    return (f"⟨{rt_term(s, rt, k - 1)},\n    fun i => ({reads} : Vector (ReadObservation 2) {W}).get i,\n"
            f"    fun i y => (({scores} : Vector (Vector Int (2 ^ 2)) {W}).get i).get (maskIndex y)⟩")


def traces_lean(s):
    T, M, L = s["tag"], s["M"], len(s["layers"])
    out = f"private def empty_{T}_0 : ReadTrace {layer_name(s, 0)} := fun _ => none\n"
    for k in range(1, L + 1):
        out += f"private def empty_{T}_{k} : ReadTrace layer_{T}_{k} := ⟨empty_{T}_{k - 1}, fun _ => er2, fun _ _ => 0⟩\n"
    out += "\n"
    # lessons: one def per replay
    for k, lay in enumerate(s["layers"], start=1):
        names = []
        for i, groups in enumerate(s["training"][k - 1]):
            gn = []
            for g, rounds in enumerate(groups):
                rn = []
                for q, x in enumerate(rounds):
                    nm = f"rt_{T}_L{k}_{i}_{g}_{q}"
                    out += f"private def {nm} : ReadTrace {layer_name(s, k - 1)} :=\n  {rt_term(s, x['replay'], k - 1)}\n\n"
                    rn.append(nm)
                gn.append(rn)
            names.append(gn)
        lists = "[" + ", ".join("[" + ", ".join("[" + ", ".join(rn) + "]" for rn in gn) + "]" for gn in names) + "]"
        reads = "[" + ", ".join("[" + ", ".join("[" + ", ".join(read_lean(x["read"]) for x in rounds) + "]" for rounds in groups) + "]"
                               for groups in s["training"][k - 1]) + "]"
        out += f"private def reps_{T}_{k} : List (List (List (ReadTrace {layer_name(s, k - 1)}))) := {lists}\n\n"
        out += f"private def cellreads_{T}_{k} : List (List (List (ReadObservation 2))) := {reads}\n\n"
        lower_train = "()" if k == 1 else f"train_{T}_{k - 1}"
        out += (f"def train_{T}_{k} : TrainingTrace layer_{T}_{k} :=\n"
                f"  ⟨{lower_train},\n"
                f"   fun i g r => ((reps_{T}_{k}.getD i.val []).getD g.val []).getD r empty_{T}_{k - 1},\n"
                f"   fun i g r => ((cellreads_{T}_{k}.getD i.val []).getD g.val []).getD r er2⟩\n\n")
    tests = []
    for w, rt in enumerate(s["tests"]):
        nm = f"rtest_{T}_{w}"
        out += f"private def {nm} : ReadTrace circuit_{T} :=\n  {rt_term(s, rt, L)}\n\n"
        tests.append(nm)
    out += f"private def tests_{T} : List (ReadTrace circuit_{T}) := [{', '.join(tests)}]\n\n"
    out += f"def test_{T} (x : Pattern {M}) : ReadTrace circuit_{T} := tests_{T}.getD (maskIndex x).val empty_{T}_{L}\n\n"
    return out


def theorems_lean(s, pc):
    T, M, L, N = s["tag"], s["M"], len(s["layers"]), s["widths"][-1]
    c, tr, te = f"circuit_{T}", f"train_{T}_{L}", f"test_{T}"
    stmt = {CHECKERS[0]: f"checkLayeredValid {c}", CHECKERS[1]: f"checkLayeredSeparation {c} {tr} {te}",
            CHECKERS[2]: f"checkLayeredTrainingCalibration {c} {tr}", CHECKERS[3]: f"checkLayeredReadCalibration {c} {tr} {te}"}
    out = ""
    for ch in CHECKERS:
        out += OPT + f"theorem {SHORT[ch]}_{T} : {stmt[ch]} = {bool_lean(pc[ch])} := by decide +kernel\n\n"
    conj = all(pc.values())
    out += (f"theorem checks_{T} : ({' && '.join(stmt[ch] for ch in CHECKERS)}) = {bool_lean(conj)} := by\n"
            f"  rw [{', '.join(f'{SHORT[ch]}_{T}' for ch in CHECKERS)}] <;> rfl\n\n")
    if conj and s["lean"]["derive"]:
        out += (f"/-- The layered recognition theorem on this trace, from the four kernel-checked checkers. -/\n"
                f"theorem outputs_{T} : {c}.Trained {tr} ∧ ∀ x, observed {c} ({te} x) = {c}.predict x :=\n"
                f"  layered_monotone_recognition_one_sided {M} {L} {N} {c}\n"
                f"    (layered_valid_checker_sound {M} {L} {N} _ valid_{T}) {tr} {te}\n"
                f"    (layered_separation_checker_sound {M} {L} {N} _ _ _ separation_{T})\n"
                f"    (layered_training_calibration_checker_sound {M} {L} {N} _ _ training_{T})\n"
                f"    (layered_read_calibration_checker_sound {M} {L} {N} _ _ _ reads_{T})\n\n")
        if s.get("function"):
            out += OPT + (f"theorem function_{T} : ((patterns {M}).all fun x => {c}.predict x 0 == ({s['function']})) = true := by\n"
                          f"  decide +kernel\n\n")
    return out


def header(namespace, source):
    return f"""import LayeredMonotoneCheckerProofs
import LayeredMonotoneRecognition

/-! A layered kernel gate written by research/learned-dnf-generator/layered/lemit.py from {source}.
Each `valid_*`, `separation_*`, `training_*` and `reads_*` theorem asserts a checker's value by `decide +kernel`;
the file compiles only if the kernel agrees with every asserted value. -/

namespace {namespace}

open TwoLayer (ReadObservation SlotTiming)
open MonotoneDNF.PremiseCheck (datedRead patterns maskIndex)

private def er2 : ReadObservation 2 := datedRead 0 #v[none, none] [] 0

"""


def lean_file(specs, per_checker, source):
    """specs: loaded specs of one namespace; per_checker: {tag: {checker: bool}}."""
    ns = specs[0]["lean"]["namespace"]
    assert all(s["lean"]["namespace"] == ns for s in specs)
    out = header(ns, source)
    for s in specs:
        out += f"/-! ## {s['tag']} -/\n\n" + cascade_lean(s) + traces_lean(s) + theorems_lean(s, per_checker[s["tag"]])
    return out + f"end {ns}\n"
