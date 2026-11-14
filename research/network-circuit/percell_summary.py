"""From the per-cell runs to the numbers the network expectation uses. No simulation is run.

  percell_summary.py DATA          -> PERCELL.json   (DATA: folder of the runs of percell.py, outside the repository)

Reserves are in mV, counted from the service threshold of the port in the capacitor coordinate
(stored node minus summing node): a read fires when the reserve, plus what recent pulses left, is
positive. The latency of an isolated read against the reserve comes from the qualification
(`../sky130-supervisor-closure/QUALIFICATION.json`, same cell, same junction areas, reads 11 units apart).
"""
import json
import math
from pathlib import Path
import sys

import numpy as np

HERE = Path(__file__).resolve().parent


def main():
    data = Path(sys.argv[1])
    load = lambda name: json.loads((data / name / "result.json").read_text())
    out = dict(scope="one nominal cell alone: typical corner, 27 C, junction areas of stage J, no noise; exploratory", ports={}, files={})
    for name in ("train-8", "train-22", "thr-1", "thr-2", "history"):
        r = load(name)
        out["files"][name] = dict(raw_sha256=r["raw_sha256"], deck_sha256=r["deck_sha256"], pulses=len(r["pulses"]))
    doses = [p["step_mV"] for name in ("train-8", "train-22") for p in load(name)["pulses"] if not p["fire"]]
    dose = float(np.mean(doses))
    for port in (1, 2):
        reads = [p for p in load(f"thr-{port}")["pulses"] if p["kind"] == "read"]
        good = [(p[f"u{port}_before_V"], p["latency"]) for p in reads if p["fire"] and p["latency"] <= 1.0]
        us = max(good)[0]
        bad = min(p[f"u{port}_before_V"] for p in reads if not (p["fire"] and p["latency"] <= 1.0) and p[f"u{port}_before_V"] > us)
        gap = (reads[0][f"u{port}_before_V"] - us) * 1e3
        need = math.ceil(gap / dose)
        out["ports"][str(port)] = dict(threshold_u_mV=us * 1e3, bracket_uV=(bad - us) * 1e6, preset_u_mV=reads[0][f"u{port}_before_V"] * 1e3, gap_mV=gap,
                                       gap_doses=gap / dose, need=need, silence_room_mV=gap - (need - 1) * dose, fire_room_mV=need * dose - gap,
                                       latency_at_threshold=max(good)[1],
                                       isolated_latency_by_reserve=sorted([(us - u) * 1e3, l] for u, l in good))
    t22, t8 = load("train-22")["pulses"], load("train-8")["pulses"]
    out["dose_mV"] = dict(mean=dose, smallest=min(doses), largest=max(doses), count=len(doses))
    out["trains"] = {name: dict(word="".join("F" if p["fire"] else "s" for p in rows), latencies=[p["latency"] for p in rows if p["fire"]],
                                main_charge_at_start=[p["main_charge_at_start"] for p in rows]) for name, rows in (("22 units apart", t22), ("8 units apart", t8))}
    out["phases_units"] = dict(error_phase=[min(p["error_phase_units"][0] for p in t22 if p["error_phase_units"]), max(p["error_phase_units"][1] for p in t22 if p["error_phase_units"])],
                               protected_until_isolated=[p["protected_until_units"] for p in t22 if p["fire"]],
                               protected_until_8_apart=[p["protected_until_units"] for p in t8 if p["fire"]])
    q = json.loads((HERE.parent / "sky130-supervisor-closure" / "QUALIFICATION.json").read_text())
    pts = sorted(set((x[0], x[1]) for s in q["reads_map"]["tt27"]["single"] for x in s))
    rs, ls = np.array([a for a, _ in pts]), np.array([b for _, b in pts])
    order = np.argsort(ls)
    us1 = out["ports"]["1"]["threshold_u_mV"]
    rows, pulses = [], load("history")["pulses"]
    for i, p in enumerate(pulses):
        if p.get("role") != "test":
            continue
        reserve = us1 - p["u1_before_V"] * 1e3
        row = dict(gap_units=p["gap_units"], earlier_pulse="FIRE" if pulses[i - 1]["fire"] else "silent", reserve_mV=reserve,
                   protected_at_arrival=p["protected_at_start"], fire=p["fire"], latency=p["latency"], write=p["writes1"], step_mV=p["step_mV"],
                   residual_charge=p["main_charge_at_start"] - 0.1)
        if p["fire"] and not p["protected_at_start"]:
            row["isolated_latency_at_that_reserve"] = float(np.interp(reserve, rs, ls))
            row["help_mV"] = float(np.interp(p["latency"], ls[order], rs[order])) - reserve
        rows.append(row)
    out["after_an_earlier_pulse_on_the_other_port"] = rows
    helped = [r for r in rows if "help_mV" in r]
    out["help_mV_per_unit_of_residual_charge"] = float(sum(r["help_mV"] * r["residual_charge"] for r in helped) / sum(r["residual_charge"] ** 2 for r in helped))
    (HERE / "PERCELL.json").write_text(json.dumps(out, indent=1) + "\n")
    print(json.dumps({k: v for k, v in out.items() if k not in ("after_an_earlier_pulse_on_the_other_port", "files")}, indent=1)[:2500])


if __name__ == "__main__":
    main()
