"""Development only, arithmetic: the expected compute E of a campaign of I instances at twice the dose and reltol 1e-5,
by campaign 6's own function report6.expected_E (its stopping rule: stages split within the kit's bound, E the sum over
stages and machines of sum / 4 + 3/4 max). No simulation.

  c7_E.py REPO BATCH2X_REPORT.json OUT.json

Measures: the mean wall time of each kind in the batch at twice the dose (BATCH2X_REPORT.json), as the rule says.
Network runs: campaign 6 fixed 718, 132 and 1 400 s for the unchanged dose at 1e-4. Here report6.NET is replaced, for
the time of a call, by estimates: the nominal cell's quiet run (492 s) and noisy runs (mean 842 s, 816 to 870 s) at
twice the dose and 1e-4 (steps C and D), times a slow-down for 1e-5, with or without campaign 6's margins for a
mismatched cell (1.25 on the quiet run, 734 / 485 on a noisy run). No network run exists at 1e-5, none on a mismatched
cell at twice the dose, and no untrained run at twice the dose (132 s is campaign 6's figure): estimates, not measures.
The frozen file is not edited.
"""
from fractions import Fraction as F
import json
import math
from pathlib import Path
import sys
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))
import dosedev2

QUIET_2X, NOISY_2X, UNTRAINED = F(492), F(842), F(132)
MISMATCH_QUIET, MISMATCH_NOISY = F(125, 100), F(734, 485)

if __name__ == "__main__":
    repo, rep, out = sys.argv[1], json.loads(Path(sys.argv[2]).read_text()), Path(sys.argv[3])
    dosedev2.repo_paths(repo)
    import report6
    means = {k: F(str(v)) for k, v in rep["wall_times"]["mean_wall_s_of_complete_runs"].items()}
    one = sum(means[k] * n for k, n in report6.KINDS)
    rows = []
    for label, k in (("network on ceil(k_all3 I / 10) instances", rep["summary"]["k_all3"]), ("network on ceil(k_elig I / 10) instances", rep["summary"]["k_elig"])):
        for slow in (F(1), F(14, 10), F(21, 10)):
            for margin in (False, True):
                net = dict(quiet=QUIET_2X * slow * (MISMATCH_QUIET if margin else 1), untrained=UNTRAINED * slow,
                           noisy=NOISY_2X * slow * (MISMATCH_NOISY if margin else 1))
                for I in (15, 10, 8, 6, 5):
                    with mock.patch.object(report6, "NET", net):
                        try:
                            E, stages = report6.expected_E(I, k, means)
                        except ValueError as e:
                            E, stages = None, str(e)
                    rows.append(dict(network=label, k=k, I=I, network_instances=math.ceil(F(k * I, 10)), slow_down=float(slow), mismatch_margin=margin,
                                     net_s={a: round(float(b)) for a, b in net.items()}, E_s=None if E is None else round(float(E)), stages=stages,
                                     within_bound=None if E is None else E <= report6.E_MAX))
    # the measures alone: the network at zero cost
    alone = {}
    for I in (15, 10, 8, 6, 5):
        with mock.patch.object(report6, "NET", dict(quiet=F(0), untrained=F(0), noisy=F(0))):
            E, stages = report6.expected_E(I, 1, means)
        alone[I] = round(float(E))
    res = dict(what="estimates of E by campaign 6's function; network costs are not measured at 1e-5", bound_E_s=report6.E_MAX, bound_I=report6.I_MAX,
               means_s={k: round(float(v), 1) for k, v in means.items()}, measures_of_one_instance_s=round(float(one)), measures_alone_E_s=alone, rows=rows)
    out.write_text(json.dumps(res, indent=1) + "\n")
    print("means", res["means_s"], "one instance", res["measures_of_one_instance_s"])
    print("measures alone:", alone)
    for r in rows:
        if r["I"] in (15, 10):
            print(r["k"], r["I"], r["network_instances"], r["slow_down"], r["mismatch_margin"], r["net_s"], r["E_s"], r["stages"], r["within_bound"])
    print("largest I within the bound, per case:")
    for label, k in (("k_all3", rep["summary"]["k_all3"]), ("k_elig", rep["summary"]["k_elig"])):
        for slow in (F(1), F(14, 10), F(21, 10)):
            for margin in (False, True):
                net = dict(quiet=QUIET_2X * slow * (MISMATCH_QUIET if margin else 1), untrained=UNTRAINED * slow, noisy=NOISY_2X * slow * (MISMATCH_NOISY if margin else 1))
                best = None
                for I in range(1, 41):
                    with mock.patch.object(report6, "NET", net):
                        try:
                            E, _ = report6.expected_E(I, k, means)
                        except ValueError:
                            continue
                    if E <= report6.E_MAX:
                        best = (I, round(float(E)))
                print(" ", label, float(slow), margin, best)
