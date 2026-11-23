"""M4: the Lean file of one calibrated instance at one K (K0 or K3), and its check by decide +kernel.

New file (lean.py, pushed, is not modified; its helpers q, opt, lst, bl are imported). The file defines:
  the cascade with the FITTED cells of fit.py at that K (gains, help, dose, trainError, testError, maxWrites), the
  design timing, wiring and stimuli;
  the measured test traces and training trace WITH SCORES: every read's measuredScore is its mapped Z, and every
  cell's reference scores (`scoreAt`) are the mapped Z of the four masks at the same slot (scores.py);
  `build`, a trace constructor from data rows (no proof obligation).
Theorems, each stating the library checker's value as computed by the Python mirror (fit.py and measure.py), so the
file compiles only if the kernel agrees:
  checkLayeredValid; checkLayeredTrainingCalibration; at every input pattern `Checker.oneRead` (the read calibration
  at that pattern, sound by `one_read_checker_sound` of lean/LayeredReadCheckAt.lean). The front-end law and the
  timing chain are checked by lean.py's file of the same run (lnet.py lean), not repeated here.
When all of these are true, the recognition theorem is applied, not compared: `layered_recognition_at` gives
`circuit.Trained train` and `observed = circuit.predict (lines y)`, and `circuit.predict` is checked to be the
expected function.

  leancal.py SPEC OUT     writes OUT/Cal<TAG>K0.lean and OUT/Cal<TAG>K3.lean, OUT/leancal.json
"""
from fractions import Fraction as F
import json
from pathlib import Path
import subprocess
import os
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import fit as fitmod  # noqa: E402
import lean as L  # noqa: E402
import measure as measmod  # noqa: E402
import scores as scoremod  # noqa: E402
import spec as specmod  # noqa: E402

CFG = json.loads((HERE / "config.json").read_text())
q, opt, lst, bl = L.q, L.opt, L.lst, L.bl


def mask_index(ports):
    """Lean's maskIdx: bit 0 = Lean port 0 = circuit port 1."""
    return (1 if 1 in ports else 0) + (2 if 2 in ports else 0)


class Scorer:
    """Z of a cell's read at a slot, for any mask, from the record's u (scores.py's mapping)."""

    def __init__(self, s, rec, fitres):
        self.rec = rec
        self.an = {c["cell"]: dict(d=c["anchors"]["d"], g={int(k): v for k, v in c["anchors"]["g"].items()})
                   for c in fitres["cells"] if c["measured"]}
        sc = rec["scans"]
        self.D = {k: F(v) for k, v in sc["D"].items()}
        self.u0 = sc["u0"]

    def table(self, slot_idx, c):
        sl = self.rec["slots"][slot_idx]
        an = self.an[c]
        w = {p: (F(self.u0[c][p - 1]) - F(sl["u"][c][p - 1])) / self.D[f"{c}/{p}"] for p in (1, 2) if f"{c}/{p}" in self.D}
        out = []
        for ports in ((), (1,), (2,), (1, 2)):
            out.append(scoremod.score(an, w, list(ports)) if all(p in w for p in ports) else 0)
        return out


def read_lit(r, Z):
    return f"⟨{q(r['start'])}, arr2 ({opt(r['arrivals'][0])}) ({opt(r['arrivals'][1])}), {lst(q(t) for t in r['emissions'])}, {Z}⟩"


def rows_lit(meas, scorer, slot_idx, sl, top):
    """Layer rows of a slot, top layer first, each read with its score table."""
    tr = meas.trace(sl, top)
    out = []
    for k, row in enumerate(tr, start=1):
        cells = []
        for i, r in enumerate(row):
            c = f"c{k}_{i}"
            tab = scorer.table(slot_idx, c)
            ports = [p for p in (1, 2) if r["arrivals"][p - 1] is not None]
            cells.append(f"({read_lit(r, tab[mask_index(ports)])}, {lst(str(z) for z in tab)})")
        out.append(lst(cells))
    return lst(reversed(out)), tr


def emit(s, rec, fitres, K, mirror):
    meas = measmod.Measure(s, CFG, rec)
    scorer = Scorer(s, rec, fitres)
    tim, Ly = meas.tim, meas.L
    m, M, T = s["m"], s["lines"], s["tag"]
    cells = {c["cell"]: c for c in fitres["cells"]}
    lessons, maxw = meas.lessons()
    o = ["import LayeredWitnessSupport", "import LayeredMonotoneCheckerProofs", "import LayeredReadCheckAt", "",
         f"/-! Calibrated instance {T} ({s['function']}), seed {rec['seed']}, at {K}: research/layered-networks/leancal.py. -/",
         "", f"namespace LearnedCoincidence.Layered.Cal{T}{K}", "",
         "open TwoLayer (ReadObservation SlotTiming)", "open MonotoneDNF.PremiseCheck (patterns)",
         "open MonotoneDNF (InverterTiming rails)", "", "set_option maxRecDepth 100000", "set_option maxHeartbeats 0",
         "set_option linter.unusedVariables false", ""]
    widths = [M] + [len(n) for n in s["layers"]]
    for k, nodes in enumerate(s["layers"], start=1):
        o.append(f"def timing{k} : SlotTiming := ⟨{q(tim['skew'][k])}, {q(tim['deadline'][k])}, {q(tim['duration'][k])}⟩")
        for i, n in enumerate(nodes):
            p = cells[f"c{k}_{i}"]["lean_cell"][K]
            src = n["source"]
            sv = lambda a: "none" if src[a] is None else f"some {src[a]}"
            stim = [("pattern " + lst(str(j) for j in sorted(x))) if x is not None else "pattern []" for x in n["stimulus"]]
            o.append(f"def cell{k}_{i} : Cell := {{ gate := .{n['gate']}, initialGain := fun a => if a.val = 0 then "
                     f"{p['gain'][1]} else {p['gain'][2]}, help := {p['help']}, threshold := {p['threshold']}, "
                     f"trainError := {p['trainError']}, testError := {p['testError']}, dose := {p['dose']}, "
                     f"maxWrites := {p['maxWrites']}, rail := {p['rail']} }}")
            o.append(f"def node{k}_{i} : Node {M} {widths[k - 1]} := ⟨cell{k}_{i}, fun a => if a.val = 0 then {sv(0)} else {sv(1)}, "
                     f"fun _ => {q(tim['delta'])}, fun g => if g.val = 0 then {stim[0]} else {stim[1]}⟩")
        lower = f"(Cascade.input : Cascade {M} 0 {M})" if k == 1 else f"layer{k - 1}"
        sel = " else ".join(f"if i.val = {i} then node{k}_{i}" for i in range(len(nodes) - 1))
        body = f"{sel} else node{k}_{len(nodes) - 1}" if len(nodes) > 1 else f"node{k}_0"
        o += [f"def layer{k} : Cascade {M} {k} {len(nodes)} := .layer {lower} timing{k} fun i => {body}", ""]
    o += [f"def circuit := layer{Ly}", ""]
    o += ["def blankRead : ReadObservation 2 := ⟨0, fun _ => none, [], 0⟩",
          "def blankInv : ReadObservation 1 := ⟨0, fun _ => none, [], 0⟩",
          "def arr2 (a b : Option Rat) : Fin 2 → Option Rat := fun j => if j.val = 0 then a else b",
          "def maskIdx (y : Pattern 2) : Nat := (if y 0 then 1 else 0) + (if y 1 then 2 else 0)", "",
          "/-- A trace constructor from data rows (top layer first; each read with its four reference scores) and the",
          "line arrivals. No proof obligation. -/",
          "def build : (c : Cascade M L N) → List (List (ReadObservation 2 × List Int)) → List (Option Rat) → ReadTrace c",
          "  | .input, _, ext => fun j => ext.getD j.val none",
          "  | .layer lower _ _, rows, ext => ⟨build lower rows.tail ext,",
          "      fun i => ((rows.headD []).getD i.val (blankRead, [])).1,",
          "      fun i y => (((rows.headD []).getD i.val (blankRead, [])).2).getD (maskIdx y) 0⟩", ""]
    tests = meas.tests()
    o.append("def testData : Nat → List (List (ReadObservation 2 × List Int)) × List (Option Rat)")
    for kk, t in enumerate(tests):
        idx = rec["tests"][kk]
        rows, _ = rows_lit(meas, scorer, idx, t, Ly)
        o.append(f"  | {kk} => ({rows}, {lst(opt(x) for x in meas.lines(t))})")
    o += ["  | _ => ([], [])", "def test (k : Nat) : ReadTrace circuit := build circuit (testData k).1 (testData k).2",
          f"def code (y : Pattern {m}) : Nat := (List.finRange {m}).foldl (fun acc j => acc + if y j then 2 ^ j.val else 0) 0",
          "def expect : Nat → Bool"]
    o += [f"  | {kk} => {bl(v)}" for kk, v in enumerate(s["expect"])] + ["  | _ => false"]
    o.append(f"def lines (y : Pattern {m}) : Pattern {M} := " + ("rails y" if s["front"] else "y"))
    o.append("")
    o.append("def lessonRow : Nat → Nat → Nat → Nat → List (List (ReadObservation 2 × List Int)) × List (Option Rat) × ReadObservation 2")
    for (k, i, g, r), sl in sorted(lessons.items()):
        idx = next(x["slot"] for x in rec["lessons"] if (x["layer"], x["cell"], x["group"], x["round"]) == (k, i, g, r))
        tr = meas.trace(sl, k)
        rows_below, _ = rows_lit(meas, scorer, idx, sl, k - 1) if k > 1 else ("[]", None)
        tab = scorer.table(idx, f"c{k}_{i}")
        rd = tr[-1][i]
        ports = [p for p in (1, 2) if rd["arrivals"][p - 1] is not None]
        o.append(f"  | {k}, {i}, {g}, {r} => ({rows_below}, {lst(opt(x) for x in meas.lines(sl))}, {read_lit(rd, tab[mask_index(ports)])})")
    o += ["  | _, _, _, _ => ([], [], blankRead)",
          "def buildTrain : (c : Cascade M L N) → TrainingTrace c",
          "  | .input => ()",
          "  | .layer (L := L) lower _ _ => ⟨buildTrain lower,",
          "      fun i g r => build lower (lessonRow (L + 1) i.val g.val r).1 (lessonRow (L + 1) i.val g.val r).2.1,",
          "      fun i g r => (lessonRow (L + 1) i.val g.val r).2.2⟩",
          "def train : TrainingTrace circuit := buildTrain circuit", ""]
    pats = f"(patterns {m}).all fun y =>"
    o += [f"theorem valid_check : checkLayeredValid circuit = {bl(mirror['valid'])} := by decide +kernel",
          f"theorem training_check : checkLayeredTrainingCalibration circuit train = {bl(mirror['training'])} := by decide +kernel",
          f"theorem reads_check : ({pats} Checker.oneRead circuit train (lines y) (test (code y))) = {bl(mirror['reads'])} := by decide +kernel",
          f"theorem predicted_check : ({pats} circuit.predict (lines y) 0 == expect (code y)) = true := by decide +kernel"]
    if mirror["valid"] and mirror["training"] and mirror["reads"]:
        o += ["", f"private theorem every_pattern {{P : Pattern {m} → Bool}} (h : (patterns {m}).all P = true) (y : Pattern {m}) :",
              "    P y = true := List.all_eq_true.mp h y (MonotoneDNF.patterns_complete y)", "",
              "/-- The recognition theorem on the measured instance: the cascade is trained, and at every input pattern",
              "the observed output is the expected function. Applied, not compared. -/",
              f"theorem computes (y : Pattern {m}) :",
              "    circuit.Trained train ∧ observed circuit (test (code y)) 0 = expect (code y) := by",
              "  have valid := layered_valid_checker_sound _ _ _ _ valid_check",
              "  have training := layered_training_calibration_checker_sound _ _ _ _ _ training_check",
              "  have reads := one_read_checker_sound (every_pattern reads_check y)",
              "  obtain ⟨trained, decided⟩ := layered_recognition_at _ _ _ circuit valid train training (lines y) _ reads",
              "  refine ⟨trained, ?_⟩",
              "  rw [decided]",
              "  exact beq_iff_eq.mp (every_pattern predicted_check y)"]
    o += ["", f"end LearnedCoincidence.Layered.Cal{T}{K}", ""]
    return "\n".join(o)


def mirror_values(s, rec, fitres, K):
    """The Python values of the three calibration checkers at K (fit.py's clauses with measure.py's timing)."""
    meas = measmod.Measure(s, CFG, rec)
    rep = meas.report()[0]
    timing_tests = all(rep["summary"]["tests"].get(k, True) for k in ("decoder", "window", "routed", "scheduled"))
    timing_lessons = all(rep["summary"]["lessons"].get(k, True) for k in ("decoder", "window", "routed", "scheduled"))
    cells = fitres["cells"]
    v = all(c["measured"] and c["verdicts"][K]["valid"] for c in cells)
    tr = all(c["measured"] and c["verdicts"][K]["training_calibration"] and c["verdicts"][K]["read_calibration"]
             for c in cells) and timing_lessons and timing_tests
    rd = all(c["measured"] and c["verdicts"][K]["read_calibration"] for c in cells) and timing_tests
    return dict(valid=v, training=tr, reads=rd)


def build_extra(build):
    env = dict(os.environ, LEAN_PATH=str(build))
    src = HERE / "lean" / "LayeredReadCheckAt.lean"
    ol = build / "LayeredReadCheckAt.olean"
    if not ol.exists() or ol.stat().st_mtime < src.stat().st_mtime:
        p = subprocess.run(["lean", "-DwarningAsError=true", "-o", str(ol), str(src)], cwd=src.parent, env=env,
                           capture_output=True, text=True, timeout=3600)
        if p.returncode:
            raise RuntimeError(p.stdout[-3000:] + p.stderr[-3000:])


def main(spec_path, out):
    out = Path(out).resolve()
    s = specmod.load(spec_path)
    import records
    rec = records.load(out)
    fitres = fitmod.instance_fit(s, rec)
    if not all(c["measured"] for c in fitres["cells"]):
        res = dict(emitted=False, why=[f"{c['cell']}: {c['why_not_measured']}" for c in fitres["cells"] if not c["measured"]])
        (out / "leancal.json").write_text(json.dumps(res, indent=1) + "\n")
        print(json.dumps(res, indent=1))
        return False
    build = HERE / "build"
    L.build_modules(CFG, build)
    build_extra(build)
    res = dict(emitted=True, files={})
    for K in ("K0", "K3"):
        mv = mirror_values(s, rec, fitres, K)
        path = out / f"Cal{s['tag']}{K}.lean"
        path.write_text(emit(s, rec, fitres, K, mv))
        r = L.check(CFG, path, build)
        res["files"][K] = dict(file=path.name, mirror=mv, recognition_theorem=all(mv.values()), **r)
        if r["accepted"]:
            res["files"][K].pop("output")
    (out / "leancal.json").write_text(json.dumps(res, indent=1) + "\n")
    print(json.dumps(res, indent=1))
    return all(f["accepted"] for f in res["files"].values())


if __name__ == "__main__":
    sys.exit(0 if main(sys.argv[1], sys.argv[2]) else 1)
