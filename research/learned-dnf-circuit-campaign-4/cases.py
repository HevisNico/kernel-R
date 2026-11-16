"""Campaign 4: the cases P0 to P6 of the kernel gate (PREDICTION.md, The gate on "no" cases; amendment 1), built
from phase 0's CALIBRATION.json only (#172, commit 49684af), with no campaign data.

  cases.py OUT.json            writes {"cases": [...]} for gate4.py cases, and prints the Python verdicts

P0's table (amendment 1, section 8, item 5): a and b are the nominal cell at amplitude 0.49, c at amplitude 1; Z the
file's four decimals in integer units; the latency the file's; c's 0.3-late pair equal to its aligned pair; the dose
of a port at stage k the difference of the stored voltages of stages k and k + 1 (stage 7: that of stage 6), as the
file gives them for port 1, for both ports. The noisy budget uses the constants of decision 5 (the rehearsal has no
validated value). Each of P1 to P6 is P0 with the single change of the table of PREDICTION.md:

  P1  the pair read of a at stage 3, Z set to theta - 1                       a measure; everything recomputed
  P2  the pair read of a at stage 4, Z set to theta                           a measure; everything recomputed
  P3  c's aligned pair at stage min(n1, n2), Z set to c's line a alone at n1, minus 1
                                                                              a measure; everything recomputed
  P4  the emission of c's test read on ABCD moved to the midpoint of its two arrivals     the observation
  P5  the arrival of line a on c, in the first test slot where a fires, moved 1/10 later  the observation
  P6  the start of a's firstTest read in the first test slot, moved 1/100 earlier         the observation

Choices the table leaves open, fixed here before any verdict was computed: P3 changes the aligned pair (the 0.3-late
copy is taken from P0's table; the test pair's score is the lower of the two, so it is the changed value either way).
P4's "between" is the midpoint. P5 and P6 use the first test slot of the calendar (dnf.patterns order) that fits.
P6's 1/100 is below the layer-1 skew bound 1/50, so the arrivals stay within the skew and only the separation from
the previous slot (the last lesson) changes; TrainingSeparation does not order test slots among themselves.
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
from c4 import dnf                                      # noqa: E402

CALIBRATION = HERE.parent / "learned-dnf-circuit" / "CALIBRATION.json"
AMPLITUDE = dict(a="049", b="049", c="10")


def nominal():
    d = json.loads(CALIBRATION.read_text())
    t, dose = {}, {}
    for c in c4.CELLS:
        rows = sorted(d["amplitudes"][AMPLITUDE[c]]["table"], key=lambda r: r["stage"])
        assert [r["stage"] for r in rows] == list(range(c4.STAGES))
        for row in rows:
            k = row["stage"]
            for name in P.READS:
                m = row[name]
                z = P.zint(m["Z"])
                assert m["fire"] == (z >= P.THETA), (c, k, name)
                t[(c, k, name)] = dict(Z=z, fire=m["fire"], latency=m["latency"])
            if c == "c":
                t[(c, k, P.SKEWED)] = dict(t[(c, k, "both")])
        u = [r["u_mV"] for r in rows]
        for k in range(c4.STAGES):
            mv = u[k] - u[k + 1] if k + 1 < c4.STAGES else u[k - 1] - u[k]
            for p in (1, 2):
                dose[(c, p, k)] = mv
    return t, dose


def predict(t, dose):
    x = P.instance(None, t, dose, [], c4.DECISION5)
    assert x.get("eligible") is not None and "observation" in x, x.get("why_not_eligible")
    return x


def fire_bits(t, key):
    t[key]["fire"] = t[key]["Z"] >= P.THETA


def first_slot(o, test):
    return next(k for k in (("".join(sorted(x)) or "-") for x in dnf.patterns()) if test(k))


def build():
    t0, dose = nominal()
    p0 = predict(t0, dose)
    n = p0["needs"]
    cases = [dict(p0, tag="P0", change="none")]

    t = copy.deepcopy(t0)
    t[("a", 3, "both")]["Z"] = P.THETA - 1
    fire_bits(t, ("a", 3, "both"))
    cases.append(dict(predict(t, dose), tag="P1", change="pair of a at stage 3: Z = theta - 1"))

    t = copy.deepcopy(t0)
    t[("a", 4, "both")]["Z"] = P.THETA
    fire_bits(t, ("a", 4, "both"))
    cases.append(dict(predict(t, dose), tag="P2", change="pair of a at stage 4: Z = theta"))

    t = copy.deepcopy(t0)
    lo = min(n["c1"], n["c2"])
    t[("c", lo, "both")]["Z"] = t0[("c", n["c1"], "port 1")]["Z"] - 1
    fire_bits(t, ("c", lo, "both"))
    cases.append(dict(predict(t, dose), tag="P3", change=f"aligned pair of c at stage {lo}: Z = line a alone at stage {n['c1']} minus 1"))

    x = copy.deepcopy(p0)
    d = x["observation"]["secondTest"]["ABCD"]
    a1, a2 = (F(v) for v in d["arrivals"])
    d["emissions"] = [str((a1 + a2) / 2)]
    cases.append(dict(x, tag="P4", change=f"emission of c's test read on ABCD moved to the midpoint of its arrivals {a1} and {a2}"))

    x = copy.deepcopy(p0)
    o = x["observation"]
    k = first_slot(o, lambda k: o["firstTest"][k][0]["emissions"])
    d = o["secondTest"][k]
    d["arrivals"][0] = str(F(d["arrivals"][0]) + F(1, 10))
    cases.append(dict(x, tag="P5", change=f"arrival of line a on c in test slot {k} moved 1/10 later"))

    x = copy.deepcopy(p0)
    o = x["observation"]
    k = first_slot(o, lambda k: True)
    d = o["firstTest"][k][0]
    d["start"] = str(F(d["start"]) - F(1, 100))
    cases.append(dict(x, tag="P6", change=f"start of a's firstTest read in test slot {k} (the first) moved 1/100 earlier"))
    return cases


def main():
    cases = build()
    Path(sys.argv[1]).write_text(json.dumps(dict(source="CALIBRATION.json, #172, 49684af", cases=cases), indent=1, default=str))
    for x in cases:
        v = gate4.verdicts(x)
        print(x["tag"], "K0", "yes" if v["K0"] else "no", "K3", "yes" if v["K3"] else "no", "|", x["change"])


if __name__ == "__main__":
    main()
