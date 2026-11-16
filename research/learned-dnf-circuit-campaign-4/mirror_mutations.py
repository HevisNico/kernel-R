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

Added at the independent review's request before the freeze: the parameter conditions, and the second layer of the
kinds that exist in both layers.

  rail              layer 1's rail set to its largest guarded gain at the need (the check is gain < rail)
  delay             the routing delay set to -1/100; every arrival on c moved with it (upstream emission - 1/100), and
                    each read of c with an arrival starts at its first arrival, so that the route and the decoder
                    still hold
  need in range     layer 1's maxWrites set to 3, below the need 4 (the trace keeps its first 4 training rows)
  timing valid      c's timing set to skew 11/10, deadline 19, duration 19 (deadline >= duration); held by
                    checkThresholdRead, so by checkCascadeCalibrationOneSided
  residual (c)      secondTrain 0 (line a, silent): measured score + 1 000, still below theta
  emission window (c)  secondTest AB: emission at s + 23/10, past the deadline 11/5
  skew (c)          secondTest AB: s moved 6/5 earlier, so its arrival is past the skew 11/10

Not constructible alone, with the reason:
  reachable         with both lines selected it fails only when one layer-1 target contains the other: that changes
                    `term`, so every layer-1 read
  FIRE bit (layer 1)  every layer-1 read is routed to c (teach, firstTest) or counted (firstTrain, observedCount): an
                    emission change moves a route or a count, and a score across theta moves the residual past its
                    budget (the last silence of a: |theta - G| = 781 against 777)
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
    "rail": "rail", "delay": "delay nonnegative", "maxwrites": "need in 1..maxWrites", "timing": "timing valid",
    "residual2": "residual", "window2": "decoder: emission within the deadline", "skew2": "decoder: arrival within the skew",
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

    x = new()
    g, n = x["guarded"], x["needs"]
    x["rail1"] = max(g["gain"][f"{c}{p}"] + g["dose"][c] * n[c] for c in "ab" for p in (1, 2))
    out["rail"] = x

    x = new()
    o = x["observation"]
    d = F(-1, 100)
    x["delay"] = str(d)
    for nn, r in enumerate(o["secondTrain"]):
        row = o["teach"][nn]
        r["arrivals"] = [None if v is None else str(F(row[j]["emissions"][0]) + d) for j, v in enumerate(r["arrivals"])]
        r["start"] = str(min(F(v) for v in r["arrivals"] if v is not None))
    for k, r in o["secondTest"].items():
        row = o["firstTest"][k]
        r["arrivals"] = [None if v is None else str(F(row[j]["emissions"][0]) + d) for j, v in enumerate(r["arrivals"])]
        got = [F(v) for v in r["arrivals"] if v is not None]
        if got:
            r["start"] = str(min(got))
    out["delay"] = x

    x = new()
    assert x["needs"]["a"] == 4 and x["Q1"] == 6
    x["Q1"] = 3
    out["maxwrites"] = x

    x = new()
    x["timing2"] = ["11/10", "19", "19"]
    out["timing"] = x

    x = new()
    r = x["observation"]["secondTrain"][0]
    assert not r["emissions"]
    r["value"] += 1000
    assert r["value"] < cases.P.THETA
    out["residual2"] = x

    x = new()
    r = x["observation"]["secondTest"]["AB"]
    r["emissions"] = [str(F(r["start"]) + F(23, 10))]
    out["window2"] = x

    x = new()
    r = x["observation"]["secondTest"]["AB"]
    r["start"] = str(F(r["start"]) - F(6, 5))
    out["skew2"] = x
    return out


def lean_file(muts, verdicts):
    out = gate4.header("mirror_mutations.py")
    for name, x in muts.items():
        tag = f"M_{name}"
        cn, tn = f"cascade_{tag}", f"trace_{tag}"
        cascade = gate4.cascade_lean(cn, x, 0)
        right = "right"
        if "rail1" in x:
            i = cascade.index(f"rail := {cases.P.RAIL}")
            cascade = cascade[:i] + f"rail := {x['rail1']}" + cascade[i + len(f"rail := {cases.P.RAIL}"):]
        if "delay" in x:
            old = "delay := fun _ _ => 3 / 2"
            assert cascade.count(old) == 1
            cascade = cascade.replace(old, f"delay := fun _ _ => {gate4.r(F(x['delay']))}")
        if "timing2" in x:
            right = f"right_{tag}"
            out += f"def {right} : SlotTiming := ⟨{', '.join(gate4.r(F(v)) for v in x['timing2'])}⟩\n\n"
        out += cascade + "\n" + gate4.trace_lean(tn, cn, x["observation"]) + "\n"
        v = verdicts[name]
        b = lambda c: "true" if v[c] else "false"
        for th, stmt, c in ((f"valid_{tag}", f"checkCascadeValid {cn}", cases.VALID),
                            (f"separation_{tag}", f"checkTrainingSeparation {cn} left {right} {tn}.observations", cases.SEP),
                            (f"calibration_{tag}", f"checkCascadeCalibrationOneSided {cn} left {right} {tn}.observations {tn}.scoreAt", cases.CAL)):
            out += f"set_option maxRecDepth 100000 in\nset_option maxHeartbeats 0 in\ntheorem {th} : {stmt} = {b(c)} := by decide +kernel\n\n"
    return out + "end LearnedCoincidence.MonotoneDNF.PremiseCheck.Campaign4\n"


def main():
    print(cases.c4.require_pinned())
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
