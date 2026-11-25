"""noise4: the C5 inverter's K3 budget at the injected (measured) noise level. Development only. New file: noise3.py,
the gate (research/inverter-instances invinst/gate.py) and research/circuit/noise.json stay as they are.

The owner's decision: budget the inverter's K3 room at the measured injected noise, each sigma at the larger of two
measures (NOT1 9801, noise seeds 98011 and 98014: the comparator's total vnzm rms, and the sd of the mirror charge over
a window of length D). The constants are in noise4_budget.json. The R cells are unchanged.

  noise4.py check                 the budget file against both noise_sources.json, and its allowance as gate.py rounds it
  noise4.py room [COMMIT]         the dev inverters' K3 room under the noise.json allowance and under noise4's

`room` regates, in Python only, with the gate's own mirror of the Lean premises (gate.premises, gate.measures,
gate.best_early, gate.design, read from research/inverter-instances at COMMIT, default d599300), every dev inverter
whose measures are stored there:
- the 60 instances of dev_lot (values in SUMMARY.json; eligibility, the observation and the state bound in
  REGATE_SINGLE_SOURCE_SUMMARY.json, which do not depend on the allowance);
- the two in-network inverters of indeck_smoke_9803 (GATE_9803_n0.json, GATE_9803_n1.json).
Under the noise.json allowance it must reproduce the stored K3 verdicts and margins; the noise4 allowance then only
changes k (delta, eta). Nothing is simulated; no Lean file is compiled (the kernel agreed with the mirror on all 60).
"""
import json
import math
from fractions import Fraction as F
from pathlib import Path
import subprocess
import sys
import types

HERE = Path(__file__).resolve().parent
BUDGET = json.loads((HERE / "noise4_budget.json").read_text())
INV = "research/circuit/inverter/instances"


def up(x, den=1000000):
    return F(math.ceil(x * den), den)


def allowance(K=None):
    """noise4's K3 allowance (delta, eta) in x, rounded up as gate.allowance rounds."""
    K = BUDGET["K3_sigmas"] if K is None else K
    return dict(delta=up(K * BUDGET["sigma_delta"]["sigma_delta_x"]), eta=up(K * BUDGET["sigma_eta"]["sigma_eta_x"]))


def check():
    b, ok = BUDGET, len(BUDGET["measures"]) >= 2
    for m in b["measures"]:                                # each measure equals its noise_sources.json
        s = json.loads((HERE / m["sources"]).read_text())["n0"]
        ok &= (s["nzm_rms_uV"] == m["comparator_total_rms_uV"] and s["all_windows_charge_x"]["sd"] == m["sigma_eta_x"]
               and abs(s["nzm_rms_uV"] * 1e-6 / b["vunit_V"] - m["sigma_delta_x"]) < 1e-15)
    ok &= b["sigma_delta"]["sigma_delta_x"] == max(m["sigma_delta_x"] for m in b["measures"])   # the larger
    ok &= b["sigma_delta"]["comparator_total_rms_uV"] == max(m["comparator_total_rms_uV"] for m in b["measures"])
    ok &= b["sigma_eta"]["sigma_eta_x"] == max(m["sigma_eta_x"] for m in b["measures"])
    k = allowance()
    ok &= k == {n: F(v) for n, v in b["allowance_K3"].items()}
    old = dict(delta=up(3 * s["model_total_uV"] * 1e-6 / b["vunit_V"]), eta=up(3 * s["model_sigma_q_x"]))
    ok &= old == {n: F(v) for n, v in b["allowance_K3_noise_json"].items()}
    print(json.dumps(dict(noise4=b["allowance_K3"], noise_json=b["allowance_K3_noise_json"],
                          ratio=dict(delta=float(k["delta"] / old["delta"]), eta=float(k["eta"] / old["eta"]))), indent=1))
    print("BUDGET FILE CONSISTENT" if ok else "BUDGET FILE INCONSISTENT")
    return ok


def show(commit, path):
    return subprocess.run(["git", "show", f"{commit}:{path}"], capture_output=True, text=True, check=True,
                          cwd=HERE).stdout


def gate_module(commit):
    """The gate's mirror functions, from its pushed source (its allowance() is not used)."""
    m = types.ModuleType("gate_at_commit")
    m.__file__ = str(HERE / "gate_at_commit.py")
    exec(compile(show(commit, f"{INV}/invinst/gate.py"), f"{commit}:{INV}/invinst/gate.py", "exec"), m.__dict__)
    return m


def verdict(g, d, base, k, t, grid):
    ms = dict(base, early=g.best_early(d, base, k, t, grid))
    v, mg = g.premises(d, ms, k, t)
    return v, {n: float(x) for n, x in mg.items()}


def room(commit="d599300"):
    g = gate_module(commit)
    cfg = json.loads(show(commit, f"{INV}/config.json"))
    d, grid = g.design(cfg), F(cfg["gate"]["early_grid"])
    t = {n: F(v) for n, v in cfg["gate"]["timing"].items()}
    k_old = {n: F(v) for n, v in BUDGET["allowance_K3_noise_json"].items()}
    k_new = allowance()
    summ = {r["seed"]: r for r in json.loads(show(commit, f"{INV}/dev_lot/SUMMARY.json"))["rows"]}
    reg = json.loads(show(commit, f"{INV}/dev_lot/REGATE_SINGLE_SOURCE_SUMMARY.json"))["rows"]
    rows, reproduced = [], True
    for r in reg:
        x = dict(summ[r["seed"]]["values"])
        x["leak_above"], x["leak_below"] = {"rate": x["leak_above"]}, {"rate": x["leak_below"]}
        base = g.measures(cfg, x)
        v0, m0 = verdict(g, d, base, k_old, t, grid)
        v1, m1 = verdict(g, d, base, k_new, t, grid)
        same = v0["Premises"] == r["kernel"]["K3"] and all(abs(m0[n] - r["margins"]["K3"][n]) < 1e-12 for n in m0)
        reproduced &= same
        rows.append(dict(inverter=f"dev_lot {r['seed']}", eligible_K0=r["eligible_K0"],
                         room_noise_json=r["eligible_K0"] and v0["Premises"], room_noise4=r["eligible_K0"] and v1["Premises"],
                         failing_noise4=[p for p, b in v1.items() if not b], reproduced=same,
                         margins_noise4=m1, margins_noise_json=m0))
    for j in ("n0", "n1"):
        G = json.loads(show(commit, f"{INV}/indeck_smoke_9803/GATE_9803_{j}.json"))
        base = {n: F(v) for n, v in G["measures"]["K0"].items() if n != "early"}
        obs = G["eligible_K0"]
        v0, m0 = verdict(g, d, base, k_old, t, grid)
        v1, m1 = verdict(g, d, base, k_new, t, grid)
        same = v0["Premises"] == G["kernel"]["K3"] and all(abs(m0[n] - G["margins"]["K3"][n]) < 1e-12 for n in m0)
        reproduced &= same
        rows.append(dict(inverter=f"XOR3 9803 {j} (in network)", eligible_K0=obs, room_noise_json=obs and v0["Premises"],
                         room_noise4=obs and v1["Premises"], failing_noise4=[p for p, b in v1.items() if not b],
                         reproduced=same, margins_noise4=m1, margins_noise_json=m0))
    lot = [r for r in rows if r["inverter"].startswith("dev_lot")]
    res = dict(gate_commit=commit, allowance_noise_json=BUDGET["allowance_K3_noise_json"],
               allowance_noise4=BUDGET["allowance_K3"], reproduced_stored_K3=reproduced,
               dev_lot=dict(n=len(lot), eligible_K0=sum(r["eligible_K0"] for r in lot),
                            room_noise_json=sum(r["room_noise_json"] for r in lot),
                            room_noise4=sum(r["room_noise4"] for r in lot),
                            lost=[r["inverter"] for r in lot if r["room_noise_json"] and not r["room_noise4"]],
                            min_silence_margin_noise4=min(r["margins_noise4"]["silence_margin"] for r in lot if r["eligible_K0"]),
                            min_firing_margin_noise4=min(r["margins_noise4"]["firing_margin"] for r in lot if r["eligible_K0"])),
               in_network={r["inverter"]: dict(room_noise_json=r["room_noise_json"], room_noise4=r["room_noise4"],
                                               margins_noise4=r["margins_noise4"]) for r in rows if "network" in r["inverter"]},
               rows=rows)
    (HERE / "dev/noise4").mkdir(parents=True, exist_ok=True)
    (HERE / "dev/noise4/room.json").write_text(json.dumps(res, indent=1) + "\n")
    print(json.dumps({k: v for k, v in res.items() if k != "rows"}, indent=1))
    print("STORED K3 VERDICTS REPRODUCED" if reproduced else "STORED K3 VERDICTS NOT REPRODUCED")
    return reproduced


if __name__ == "__main__":
    a = sys.argv[1:]
    if a and a[0] == "check":
        sys.exit(0 if check() else 1)
    if a and a[0] == "room":
        sys.exit(0 if room(*a[1:2]) else 1)
    print(__doc__)
    sys.exit(2)
