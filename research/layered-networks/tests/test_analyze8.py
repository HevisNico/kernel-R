"""Tests of analyze8.py's D4 rule (no simulation). Run with the pinned environment: python -B tests/test_analyze8.py

The rule is tried on synthetic rows, with the audited lines and the regate given:
- no audited instance, or D4* <= 0.005: nothing is regated, nothing changes;
- D4* > 0.005: every unaudited instance with a prediction is regated, and only those whose gate fails at a counted
  level are premise_flagged_D4 there;
- a refuted level keeps its refutation and its count, and only carries the flag; the group verdicts are recounted;
- one real regate of a sealed instance (dev/dryrun_b/ANDOR3_9805, its record unaudited) through d4_section.
"""
import json
from fractions import Fraction as F
from pathlib import Path
import sys
import tempfile

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import analyze8 as A8  # noqa: E402


def inst(root, name, audited):
    d = Path(root) / name / "D"
    d.mkdir(parents=True)
    src = "this run's solo scans" if audited else "calibration.json d4_stage"
    (d / "fit_d.json").write_text(json.dumps(dict(cells=[dict(cell="c1_0", budgets=dict(K0=dict(D4_source=src)))])))
    (d / "prediction.json").write_text("{}")
    return d.parent


def rows(names, refuted=()):
    return [dict(machine="machine_1", instance=n, group="ANDOR3", K0=dict(counted=True, refuted=n in refuted),
                 K3=dict(counted=False)) for n in names]


def run(values, fails, refuted=()):
    with tempfile.TemporaryDirectory() as d:
        names = ["ANDOR3_1", "ANDOR3_2", "ANDOR3_3", "ANDOR3_4"]
        dirs = {n: inst(d, n, n == "ANDOR3_1") for n in names}
        lines = lambda D: {"c1_0": {0: F(values)}} if D.parent.name == "ANDOR3_1" else {}
        calls = []

        def regate(spec, i, star):
            calls.append((Path(i).name, star))
            ok = Path(i).name not in fails
            return dict(reproduces_sealed=True, sealed={}, regated={}, gate_holds_K0=ok, gate_holds_K3=True,
                        newly_failing_K0={} if ok else {"c2_0": ["x"]}, newly_failing_K3={})
        rs = rows(names, refuted)
        sec, flags = A8.d4_section(rs, lambda r: dirs[r["instance"]], lambda r: "spec", regate=regate, lines=lines)
        res = dict(instances=rs, thresholds=dict(K0=dict(ANDOR3=3), K3=dict(ANDOR3=3)),
                   groups=dict(ANDOR3=dict(K0={}, K3={})), family={})
        A8.apply_flags(res, flags)
        return sec["groups"]["ANDOR3"], calls, res


def test_no_change_at_or_under_frozen():
    for v in ("0.004", "0.005"):
        g, calls, res = run(v, fails={"ANDOR3_2"})
        assert not g["exceeds"] and not calls and not g["premise_flagged_D4"]["K0"]
        assert res["groups"]["ANDOR3"]["K0"]["counted"] == 4 and res["groups"]["ANDOR3"]["K0"]["verdict"] == "established"
        assert g["lines"][0]["above_frozen"] is False


def test_exceeding_flags_only_failing_counted():
    g, calls, res = run("0.0138", fails={"ANDOR3_2", "ANDOR3_3"})
    assert g["exceeds"] and g["D4_star"] == "69/5000"
    assert sorted(c[0] for c in calls) == ["ANDOR3_2", "ANDOR3_3", "ANDOR3_4"]      # the audited one is not regated
    assert all(c[1] == F("0.0138") for c in calls)
    assert g["premise_flagged_D4"]["K0"] == ["ANDOR3_2", "ANDOR3_3"]
    k0 = res["groups"]["ANDOR3"]["K0"]
    assert k0["counted"] == 2 and k0["premise_flagged_D4"] == ["ANDOR3_2", "ANDOR3_3"]
    assert k0["verdict"] == "held on 2 instances, not established"


def test_refutation_is_never_removed():
    g, calls, res = run("0.0138", fails={"ANDOR3_2"}, refuted={"ANDOR3_2"})
    r2 = next(r for r in res["instances"] if r["instance"] == "ANDOR3_2")
    assert r2["K0"]["refuted"] and r2["K0"]["counted"] and r2["K0"]["premise_flagged_D4"]
    assert res["groups"]["ANDOR3"]["K0"]["verdict"] == "refuted"


def test_real_regate_through_the_section():
    inst_dir = HERE / "dev/dryrun_b/ANDOR3_9805"
    with tempfile.TemporaryDirectory() as d:
        aud = inst(d, "ANDOR3_1", True)
        r = [dict(machine="machine_1", instance="ANDOR3_1", group="ANDOR3", K0=dict(counted=True), K3={}),
             dict(machine="machine_1", instance="ANDOR3_9805", group="ANDOR3", K0=dict(counted=True), K3={})]
        dirs = {"ANDOR3_1": aud, "ANDOR3_9805": inst_dir}
        lines = lambda D: {"c3_0": {0: F("0.0138")}} if D.parent.name == "ANDOR3_1" else {}
        sec, flags = A8.d4_section(r, lambda x: dirs[x["instance"]], lambda x: HERE / "specs/andor3.json", lines=lines)
    g = sec["groups"]["ANDOR3"]
    assert g["premise_flagged_D4"]["K0"] == ["ANDOR3_9805"] and g["regated"][0]["reproduces_sealed"]


if __name__ == "__main__":
    n = 0
    for k, f in list(globals().items()):
        if k.startswith("test_"):
            f()
            n += 1
            print("ok", k)
    print(f"{n} tests passed")
