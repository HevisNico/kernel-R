"""The calibrated Lean file of an instance WITH an inverter front end, closed by `layered_inverters_chained`.

New file (leancal.py and lean.py stay as pushed; the record is loaded with records2.py, repeat rule v2; leancal.emit gives the calibrated cascade, the scored traces and
the calibration checkers). Added here, for a spec with a front end:
  the design schedule `sched T`, the measured intrinsic delays `dmin`, `dmax`, the external width `w`,
  `lhigh k = layerSkew circuit k + dmax k`, the front timing `front` (config.json `timing`), the test dates `testT`,
  the measured inverter reads `testInv` and the external pulses `testExt`;
  theorems stating the mirror's values (measure.py) of, at every input pattern:
    checkChainDates (sched (testT k)) (latencyLow dmin) (latencyHigh w lhigh) circuit,
    checkLayeredFront front (testT k) (testExt k y) (testInvs k) circuit (test k),
    checkScheduled (sched (testT k)) circuit (test k), checkLatencies dmin lhigh circuit (test k),
    and that the external pulses realise y;
  front_fit: sched T 0 = T + front.emitEarly, front.window <= w, front.emitLate - front.emitEarly <= w.
When every value is true, `computes`: the cascade is trained, and at every pattern the arrival windows hold and the
observed output is the expected function, by `layered_inverters_chained` (the latency chain from the front end), with
`circuit.Trained train` from `layered_recognition_at`.

  leancal2.py SPEC OUT     writes OUT/Cal<TAG>K0.lean, OUT/Cal<TAG>K3.lean, OUT/leancal2.json
"""
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import fit as fitmod  # noqa: E402
import lean as L  # noqa: E402
import leancal  # noqa: E402
import measure as measmod  # noqa: E402
import spec as specmod  # noqa: E402

CFG = leancal.CFG
q, opt, lst, bl = L.q, L.opt, L.lst, L.bl


def front_values(s, rec):
    meas = measmod.Measure(s, CFG, rec)
    rep, dmin, dmax, _, _ = meas.report()
    t = rep["tests"]
    allt = lambda key: all(x[key] for x in t)
    return meas, dmin, dmax, dict(chain=rep["summary"]["chain"], front=allt("front"), scheduled=allt("scheduled"),
                                  latency=allt("latency"), realised=allt("realised"))


def emit(s, rec, fitres, K, mirror):
    base = leancal.emit(s, rec, fitres, K, mirror)
    T = s["tag"]
    cut = base.find("\nprivate theorem every_pattern")
    end = base.rfind(f"\nend LearnedCoincidence.Layered.Cal{T}{K}")
    head = base[:cut] if cut >= 0 else base[:end]
    meas, dmin, dmax, fv = front_values(s, rec)
    tim, Ly, m = meas.tim, meas.L, s["m"]
    off = " else ".join(f"if k = {k} then {q(v)}" for k, v in sorted(tim["offset"].items()) if k < Ly) + \
        f" else {q(tim['offset'][Ly])}"
    lim = lambda d: " else ".join(f"if k = {k} then {q(d[k])}" for k in range(1, Ly)) + (" else " if Ly > 1 else "") + q(d[Ly])
    tests = meas.tests()
    o = [head.rstrip(), "",
         "/-! The front end and the latency chain (measure.py's timing, config.json's design constants). -/", "",
         f"def sched (T : Rat) : Nat → Rat := fun k => T + ({off})",
         f"def dmin : Nat → Rat := fun k => {lim(dmin)}",
         f"def dmax : Nat → Rat := fun k => {lim(dmax)}",
         f"def w : Rat := {q(tim['w'])}",
         "def lhigh : Nat → Rat := fun k => layerSkew circuit k + dmax k",
         f"def front : InverterTiming := ⟨{q(tim['inverter_window'])}, {q(tim['emit_early'])}, {q(tim['emit_late'])}⟩",
         "def testT : Nat → Rat"]
    o += [f"  | {k} => {q(meas.d(t['T']))}" for k, t in enumerate(tests)] + ["  | _ => 0"]
    o.append("def testInv : Nat → List (ReadObservation 1)")
    o += [f"  | {k} => {lst(L.read1(v) for v in meas.inverters(t))}" for k, t in enumerate(tests)] + ["  | _ => []"]
    o += [f"def testExt (k : Nat) (y : Pattern {m}) : Fin {m} → Option Rat := fun j => if y j then some (testT k) else none",
          f"def testInvs (k : Nat) : Fin {m} → ReadObservation 1 := fun j => (testInv k).getD j.val blankInv", ""]
    pats = f"(patterns {m}).all fun y => let k := code y;"
    front_ok = fv["chain"] and fv["front"] and fv["scheduled"] and fv["latency"]
    o += [f"theorem front_check : ({pats} checkChainDates (sched (testT k)) (latencyLow dmin) (latencyHigh w lhigh) circuit && "
          "checkLayeredFront front (testT k) (testExt k y) (testInvs k) circuit (test k) && "
          f"checkScheduled (sched (testT k)) circuit (test k) && checkLatencies dmin lhigh circuit (test k)) = {bl(front_ok)} := by decide +kernel",
          f"theorem realised_check : ({pats} (List.finRange {m}).all fun j => (testExt k y j).isSome == y j) = {bl(fv['realised'])} := by decide +kernel",
          "theorem front_fit : (∀ T, sched T 0 = T + front.emitEarly) ∧ front.window ≤ w ∧ front.emitLate - front.emitEarly ≤ w := by",
          "  refine ⟨fun T => ?_, by decide +kernel, by decide +kernel⟩",
          "  simp [sched, front]"]
    all_true = mirror["valid"] and mirror["training"] and mirror["reads"] and front_ok and fv["realised"]
    if all_true:
        o += ["", f"private theorem every_pattern {{P : Pattern {m} → Bool}} (h : (patterns {m}).all P = true) (y : Pattern {m}) :",
              "    P y = true := List.all_eq_true.mp h y (MonotoneDNF.patterns_complete y)", "",
              "/-- The recognition theorem on the measured instance, through its inverters: the cascade is trained, and at",
              "every input pattern the arrival windows hold and the observed output is the expected function. The latency",
              "chain starts at the front end (`layered_inverters_chained`). Applied, not compared. -/",
              f"theorem computes (y : Pattern {m}) : circuit.Trained train ∧",
              "    ArrivalWindows circuit (test (code y)) ∧ observed circuit (test (code y)) 0 = expect (code y) := by",
              "  have valid := layered_valid_checker_sound _ _ _ _ valid_check",
              "  have training := layered_training_calibration_checker_sound _ _ _ _ _ training_check",
              "  have cal := one_read_checker_sound (every_pattern reads_check y)",
              "  have trained := (layered_recognition_at _ _ _ circuit valid train training (lines y) _ cal).1",
              "  have reads := (read_calibration_iff circuit train (lines y) (test (code y))).mp cal",
              "  have premises := every_pattern front_check y",
              "  simp only [Bool.and_eq_true] at premises",
              "  obtain ⟨⟨⟨dates, frontOk⟩, scheduled⟩, latency⟩ := premises",
              f"  have realised : ∀ j, (testExt (code y) y j).isSome = y j := fun j =>",
              "    beq_iff_eq.mp (List.all_eq_true.mp (every_pattern realised_check y) j (List.mem_finRange j))",
              "  obtain ⟨first, windowFits, spreadFits⟩ := front_fit",
              "  obtain ⟨windows, decisions⟩ := layered_inverters_chained _ _ _ circuit valid train training",
              "    front (testT (code y)) (testExt (code y) y) (testInvs (code y)) y (test (code y))",
              "    (sched (testT (code y))) dmin lhigh w (first _) windowFits spreadFits",
              "    (chain_dates_checker_sound _ _ _ _ _ _ _ dates) realised",
              "    (layered_front_checker_sound frontOk) reads.2.1",
              "    (scheduled_checker_sound scheduled) (latencies_checker_sound latency)",
              "  refine ⟨trained, windows, ?_⟩",
              "  rw [decisions]",
              "  exact beq_iff_eq.mp (every_pattern predicted_check y)"]
    o += ["", f"end LearnedCoincidence.Layered.Cal{T}{K}", ""]
    text = "\n".join(o)
    imports = "import LayeredWitnessSupport\nimport LayeredMonotoneCheckerProofs\nimport LayeredReadCheckAt\n"
    assert text.startswith(imports)
    text = imports + "import LayeredInverters\nimport LayeredChainChecks\nimport LayeredIntrinsic\n" + text[len(imports):]
    return text, dict(fv, all_true=all_true)


def main(spec_path, out):
    out = Path(out).resolve()
    s = specmod.load(spec_path)
    if not s["front"]:
        raise SystemExit("leancal2.py is for a spec with a front end; use leancal.py")
    import records2
    rec = records2.load(out)                            # repeat rule v2
    fitres = fitmod.instance_fit(s, rec)
    if not all(c["measured"] for c in fitres["cells"]):
        res = dict(emitted=False, why=[f"{c['cell']}: {c['why_not_measured']}" for c in fitres["cells"] if not c["measured"]])
        (out / "leancal2.json").write_text(json.dumps(res, indent=1) + "\n")
        print(json.dumps(res, indent=1))
        return False
    build = HERE / "build"
    L.build_modules(CFG, build)
    leancal.build_extra(build)
    res = dict(emitted=True, files={})
    for K in ("K0", "K3"):
        mv = leancal.mirror_values(s, rec, fitres, K)
        path = out / f"Cal{s['tag']}{K}.lean"
        text, fv = emit(s, rec, fitres, K, mv)
        path.write_text(text)
        r = L.check(CFG, path, build)
        res["files"][K] = dict(file=path.name, mirror=mv, front=fv, recognition_theorem=fv["all_true"], **r)
        if r["accepted"]:
            res["files"][K].pop("output")
    (out / "leancal2.json").write_text(json.dumps(res, indent=1) + "\n")
    print(json.dumps(res, indent=1))
    return all(f["accepted"] for f in res["files"].values())


if __name__ == "__main__":
    sys.exit(0 if main(sys.argv[1], sys.argv[2]) else 1)
