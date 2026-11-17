"""Campaign 5, pre-run of the gate cases (draft PREDICTION.md, section 7.4), before PREDICTION.md is pushed.

  cases5.py OUT.json OUT_TARGETS.lean GATE_MODULE    writes the cases and the targets file; prints every condition that fails

Built from campaign 4's frozen case builder (cases.py, predicted.py, gate4.py and c4.py of 093995b, copied
unchanged into this folder), with the only input CALIBRATION.json of #172 (commit 49684af): nominal data, no
campaign data. What changes against campaign 4's cases.py:

  P0   the nominal table with b's guard-on latency + 1/10 unit on every read that has a latency (every stage and
       mask), so that a and b are not the same cell; everything recomputed by the frozen prediction code
  P1   as in campaign 4, on this P0
  P1p  the score of a's pair read at stage 3 set to s1*, the largest integer in [Z, theta - 1] for which the frozen
       code gives the instance eligible (every integer of the interval tried; the set found is printed)
  P2   as in campaign 4, on this P0
  P2p  the score of a's pair read at stage 4 set to s2*, the least integer in [theta, Z] for which the frozen code
       gives the instance eligible (idem)
  P3   as in campaign 4, on this P0 (the aligned pair changed; the test pair's score is the lower of the two)
  P3p  c's aligned and 0.3-late pairs at stage min(n1, n2) both set to max(Z_1, Z_2) + c's testingError under
       beta_0 (Z_j: line j alone at its stage n_j, from P0's table)
  P4   the emission of c's test read on ABCD placed at the midpoint of its two arrivals (now 1/10 apart in P0)
  P4p  the same emission placed at its last arrival
  P5   as in campaign 4, on this P0
  P5p  in the same test slot, a's firstTest emission and the arrival of line a on c moved together, 1/10 later
  P6   as in campaign 4, on this P0 (the first test slot)
  P6p  the start of a's firstTest read in the second test slot of the calendar moved 1/100 earlier

The checker mirror, the Python gate and the Lean targets are campaign 4's (cases.Mirror, gate4.verdicts,
cases.lean_targets), unchanged.
"""
from fractions import Fraction as F
import copy
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import c4                                               # noqa: E402
import predicted as P                                   # noqa: E402
import gate4                                            # noqa: E402
import cases as C4                                      # noqa: E402
from c4 import dnf                                      # noqa: E402

SHIFT_B = F(1, 10)


def base():
    t, dose = C4.nominal()
    for key, v in t.items():
        if key[0] == "b" and v["latency"] is not None:
            v["latency"] = P.exact(v["latency"]) + SHIFT_B
    return t, dose


def eligible(t, dose):
    try:
        x = P.instance(None, t, dose, [], c4.DECISION5)
    except (AssertionError, ValueError):
        return None
    return x if x.get("eligible") else None


def scan(t0, dose, key, lo, hi):
    ok = []
    for s in range(lo, hi + 1):
        t = copy.deepcopy(t0)
        t[key]["Z"] = s
        C4.fire_bits(t, key)
        if eligible(t, dose):
            ok.append(s)
    return ok


def runs(xs):
    out = []
    for s in xs:
        if out and s == out[-1][1] + 1:
            out[-1][1] = s
        else:
            out.append([s, s])
    return out


def with_score(t0, dose, key, s):
    t = copy.deepcopy(t0)
    t[key]["Z"] = s
    C4.fire_bits(t, key)
    return C4.predict(t, dose)


def build():
    t0, dose = base()
    p0 = C4.predict(t0, dose)
    n = p0["needs"]
    out = [dict(p0, tag="P0", change="nominal table, b's guard-on latency + 1/10 on every read")]
    notes = {}

    k1 = ("a", 3, "both")
    out.append(dict(with_score(t0, dose, k1, P.THETA - 1), tag="P1", change="pair of a at stage 3: Z = theta - 1"))
    z = t0[k1]["Z"]
    ok = scan(t0, dose, k1, z, P.THETA - 1)
    notes["P1p"] = dict(interval=[z, P.THETA - 1], eligible_runs=runs(ok))
    s1 = max(ok) if ok else z
    out.append(dict(with_score(t0, dose, k1, s1), tag="P1p", change=f"pair of a at stage 3: Z = s1* = {s1} (P0: {z})"))

    k2 = ("a", 4, "both")
    out.append(dict(with_score(t0, dose, k2, P.THETA), tag="P2", change="pair of a at stage 4: Z = theta"))
    z = t0[k2]["Z"]
    ok = scan(t0, dose, k2, P.THETA, z)
    notes["P2p"] = dict(interval=[P.THETA, z], eligible_runs=runs(ok))
    s2 = min(ok) if ok else z
    out.append(dict(with_score(t0, dose, k2, s2), tag="P2p", change=f"pair of a at stage 4: Z = s2* = {s2} (P0: {z})"))

    lo = min(n["c1"], n["c2"])
    t = copy.deepcopy(t0)
    t[("c", lo, "both")]["Z"] = t0[("c", n["c1"], "port 1")]["Z"] - 1
    C4.fire_bits(t, ("c", lo, "both"))
    out.append(dict(C4.predict(t, dose), tag="P3", change=f"aligned pair of c at stage {lo}: Z = line a alone at stage {n['c1']} minus 1"))

    zmax = max(t0[("c", n["c1"], "port 1")]["Z"], t0[("c", n["c2"], "port 2")]["Z"])
    v = zmax + p0["budgets"]["K0"]["c"]["testing"]
    t = copy.deepcopy(t0)
    for r in ("both", P.SKEWED):
        t[("c", lo, r)]["Z"] = v
        C4.fire_bits(t, ("c", lo, r))
    out.append(dict(C4.predict(t, dose), tag="P3p", change=f"aligned and 0.3-late pairs of c at stage {lo}: Z = max(Z_1, Z_2) + testingError = {v}"))

    x = copy.deepcopy(p0)
    d = x["observation"]["secondTest"]["ABCD"]
    a1, a2 = sorted(F(v) for v in d["arrivals"])
    notes["P4"] = dict(arrivals=[str(a1), str(a2)], emission_P0=d["emissions"])
    assert a2 - a1 == SHIFT_B, (a1, a2)
    d["emissions"] = [str((a1 + a2) / 2)]
    out.append(dict(x, tag="P4", change=f"emission of c's test read on ABCD at the midpoint {(a1 + a2) / 2} of its arrivals {a1} and {a2}"))
    x = copy.deepcopy(p0)
    x["observation"]["secondTest"]["ABCD"]["emissions"] = [str(a2)]
    out.append(dict(x, tag="P4p", change=f"emission of c's test read on ABCD at its last arrival {a2}"))

    x = copy.deepcopy(p0)
    o = x["observation"]
    k = C4.first_slot(o, lambda k: o["firstTest"][k][0]["emissions"])
    o["secondTest"][k]["arrivals"][0] = str(F(o["secondTest"][k]["arrivals"][0]) + F(1, 10))
    out.append(dict(x, tag="P5", change=f"arrival of line a on c in test slot {k} moved 1/10 later"))
    x = copy.deepcopy(p0)
    o = x["observation"]
    o["firstTest"][k][0]["emissions"] = [str(F(e) + F(1, 10)) for e in o["firstTest"][k][0]["emissions"]]
    o["secondTest"][k]["arrivals"][0] = str(F(o["secondTest"][k]["arrivals"][0]) + F(1, 10))
    out.append(dict(x, tag="P5p", change=f"emission of a and arrival of line a on c in test slot {k} moved together 1/10 later"))

    order = [("".join(sorted(p)) or "-") for p in dnf.patterns()]
    x = copy.deepcopy(p0)
    d = x["observation"]["firstTest"][order[0]][0]
    d["start"] = str(F(d["start"]) - F(1, 100))
    out.append(dict(x, tag="P6", change=f"start of a's firstTest read in test slot {order[0]} (the first) moved 1/100 earlier"))
    x = copy.deepcopy(p0)
    d = x["observation"]["firstTest"][order[1]][0]
    d["start"] = str(F(d["start"]) - F(1, 100))
    out.append(dict(x, tag="P6p", change=f"start of a's firstTest read in test slot {order[1]} (the second) moved 1/100 earlier"))
    return out, notes


def main():
    print(c4.require_pinned())
    cases, notes = build()
    Path(sys.argv[1]).write_text(json.dumps(dict(source="CALIBRATION.json, #172, 49684af; campaign 5 pre-run", notes=notes, cases=cases), indent=1, default=str))
    print("notes: " + json.dumps(notes, default=str))
    verdicts = {}
    for x in cases:
        g = gate4.verdicts(x)
        for K in (0, 3):
            conds = C4.conditions(x, K)
            v = C4.per_checker(conds)
            verdicts[(x["tag"], K)] = v
            fails = [c for c in conds if not c[3]]
            print(f"{x['tag']} K{K}: eligible {x.get('eligible')}; gate {'yes' if g[f'K{K}'] else 'no'}; mirror "
                  + ", ".join(f"{c}={'T' if v[c] else 'F'}" for c in C4.CHECKERS)
                  + f"; {len(conds)} conditions, {len(fails)} failing" + (f" | {x['change']}" if K == 0 else ""))
            for ch, kind, where, _ in fails:
                print(f"    FAIL {ch}: {kind}: {where}")
    Path(sys.argv[2]).write_text(C4.lean_targets(cases, verdicts, sys.argv[3]))


if __name__ == "__main__":
    main()
