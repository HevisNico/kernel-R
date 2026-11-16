"""Campaign 4: mutation test of the Python mirror of the three kernel checkers (cases.py), asked by the independent
review after amendment 2. Each mutation is P0 of cases.py (CALIBRATION.json of #172 only, no campaign data) with one
hand-made change of its serialized numbers (nothing recomputed), meant to make exactly one kind of condition false.
The test passes when, under beta_0, the mirror's failing conditions are all of that kind (at least one), and Lean,
deciding the three checkers separately, gives the mirror's verdict per checker (the Lean file asserts it, so it
compiles only if they agree).

  mirror_mutations.py OUT.json OUT.lean      writes the mutated cases and the Lean file; prints the result

The mutations (r: a read; s: its start; Q1 = 6; the need is 4; test slot "-" is the first, after the last lesson):

  guarded margin    a's trainingError under beta_0 + 5 (the last silence has room +4); residuals only get easier
  residual          firstTest A, cell a (silent single): measured score + 10 000, still below theta
  emission window   firstTrain 4, cell a (its first FIRE): emission at s + 6/5, past the deadline 11/10
  one emission      firstTrain 4, cell a: its emission doubled
  v <= t            secondTest AB (line a alone): s moved 1/2 earlier, emission at the arrival - 1/4
  skew              firstTest A, cell a: arrival of A at s + 1/10, past the skew 1/50
  route             secondTrain 0 (line a, silent): arrival + 1/100, within the skew
  separation        firstTrain 1, cell a (silent): s 1/100 earlier, its arrivals unchanged (within the skew 1/50)
  submask           secondTest ABCD: measured score and scoreAt(both lines) set to line a alone's score - 1
  anchor            secondTest ABCD: scoreAt(line a alone) set to 50 000, below theta (so no submask condition)
  scoreAt = value   secondTest ABCD: scoreAt(both lines) + 1, measured score unchanged
  FIRE bit          secondTest "-" (no arrival, empty score): an emission at s + 1/2
"""
from fractions import Fraction as F
import copy
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import cases                                            # noqa: E402
import gate4                                            # noqa: E402

KIND = {
    "margin": "guarded margin", "residual": "residual", "window": "decoder: emission within the deadline",
    "single": "decoder: at most one emission", "vt": "decoder: v <= t", "skew": "decoder: arrival within the skew",
    "route": "route", "separation": "separation", "submask": "submask comparison", "anchor": "anchor",
    "scoreat": "measured score = scoreAt(input)", "firebit": "decoder: FIRE bit is the threshold comparison",
}


def mutations(p0):
    o0 = p0["observation"]
    out = {}

    def new():
        return copy.deepcopy(p0)

    x = new()
    x["budgets"]["K0"]["a"]["training"] += 5
    out["margin"] = x

    x = new()
    x["observation"]["firstTest"]["A"][0]["value"] += 10000
    assert x["observation"]["firstTest"]["A"][0]["value"] < cases.P.THETA
    out["residual"] = x

    x = new()
    r = x["observation"]["firstTrain"][4][0]
    assert r["emissions"]
    r["emissions"] = [str(F(r["start"]) + F(6, 5))]
    out["window"] = x

    x = new()
    r = x["observation"]["firstTrain"][4][0]
    r["emissions"] = r["emissions"] * 2
    out["single"] = x

    x = new()
    r = x["observation"]["secondTest"]["AB"]
    v = F(r["arrivals"][0])
    assert r["arrivals"][1] is None and r["emissions"]
    r["start"] = str(F(r["start"]) - F(1, 2))
    r["emissions"] = [str(v - F(1, 4))]
    out["vt"] = x

    x = new()
    r = x["observation"]["firstTest"]["A"][0]
    r["arrivals"][0] = str(F(r["start"]) + F(1, 10))
    out["skew"] = x

    x = new()
    r = x["observation"]["secondTrain"][0]
    assert not r["emissions"]
    r["arrivals"][0] = str(F(r["arrivals"][0]) + F(1, 100))
    out["route"] = x

    x = new()
    r = x["observation"]["firstTrain"][1][0]
    assert not r["emissions"]
    r["start"] = str(F(r["start"]) - F(1, 100))
    out["separation"] = x

    x = new()
    z = o0["scores"]["ABCD"]["1"] - 1
    assert z >= cases.P.THETA
    x["observation"]["scores"]["ABCD"]["12"] = z
    x["observation"]["secondTest"]["ABCD"]["value"] = z
    out["submask"] = x

    x = new()
    x["observation"]["scores"]["ABCD"]["1"] = 50000
    out["anchor"] = x

    x = new()
    x["observation"]["scores"]["ABCD"]["12"] += 1
    out["scoreat"] = x

    x = new()
    r = x["observation"]["secondTest"]["-"]
    assert not any(r["arrivals"]) and not r["emissions"]
    r["emissions"] = [str(F(r["start"]) + F(1, 2))]
    out["firebit"] = x
    return out


def lean_file(muts, verdicts):
    out = gate4.header("mirror_mutations.py")
    for name, x in muts.items():
        tag = f"M_{name}"
        cn, tn = f"cascade_{tag}", f"trace_{tag}"
        out += gate4.cascade_lean(cn, x, 0) + "\n" + gate4.trace_lean(tn, cn, x["observation"]) + "\n"
        v = verdicts[name]
        b = lambda c: "true" if v[c] else "false"
        for th, stmt, c in ((f"valid_{tag}", f"checkCascadeValid {cn}", cases.VALID),
                            (f"separation_{tag}", f"checkTrainingSeparation {cn} left right {tn}.observations", cases.SEP),
                            (f"calibration_{tag}", f"checkCascadeCalibrationOneSided {cn} left right {tn}.observations {tn}.scoreAt", cases.CAL)):
            out += f"set_option maxRecDepth 100000 in\nset_option maxHeartbeats 0 in\ntheorem {th} : {stmt} = {b(c)} := by decide +kernel\n\n"
    return out + "end LearnedCoincidence.MonotoneDNF.PremiseCheck.Campaign4\n"


def main():
    p0 = next(x for x in cases.build() if x["tag"] == "P0")
    assert all(ok for *_, ok in cases.conditions(p0, 0))
    muts = mutations(p0)
    verdicts, passed = {}, True
    for name, x in muts.items():
        conds = cases.conditions(x, 0)
        fails = [c for c in conds if not c[3]]
        verdicts[name] = cases.per_checker(conds)
        ok = bool(fails) and all(kind.startswith(KIND[name]) for _, kind, _, _ in fails)
        passed &= ok
        print(f"{name}: {'only its kind' if ok else 'NOT ONLY ITS KIND'}; " + ", ".join(f"{c}={'T' if verdicts[name][c] else 'F'}" for c in cases.CHECKERS))
        for ch, kind, where, _ in fails:
            print(f"    FAIL {ch}: {kind}: {where}")
    Path(sys.argv[1]).write_text(json.dumps(dict(source="P0 of cases.py", mutations=muts), indent=1, default=str))
    Path(sys.argv[2]).write_text(lean_file(muts, verdicts))
    print("mirror mutation test:", "passed" if passed else "FAILED")


if __name__ == "__main__":
    main()
