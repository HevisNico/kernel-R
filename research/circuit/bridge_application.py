"""Where the simulated circuit stands against `needAlong_of_circuit_tolerances`.

Reads the pushed results of bridge_check/ and the historical table need_budget_ports.csv.
Writes BRIDGE_APPLICATION.md and bridge_ports.csv. Computes no new estimate: every number
comes from a file named in the table. No simulation is run.
"""
import csv
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
B = ROOT / "bridge_check"


def main():
    local = json.loads((B / "local_summary.json").read_text())
    level = json.loads((B / "level_summary.json").read_text())
    with (B / "rest_samples.csv").open(newline="") as fh:
        rest = list(csv.DictReader(fh))
    with (ROOT / "need_budget_ports.csv").open(newline="") as fh:
        ports = list(csv.DictReader(fh))
    fit = next(f for f in local["local_fit"] if f["temperature_C"] == 27)
    win, ev = local["windows"], local["events"]
    nom, quiet = win["nominal_200ns_retry1"]["silent"], win["mm2064_quiet_retry1"]["silent"]
    noisy = [win[n]["silent"] for n in ("mm2064_noise_1_retry1", "mm2064_noise_2_retry1")]
    big = lambda key: max(x[key]["max"] for x in noisy)
    q = [float(r["q"]) for r in rest]
    inside = sum(r["literal_inside"] == "True" for r in rest)
    e_nom = nom["handoff_local"]["max"] + nom["increment_error_bound_local"]["max"]
    b_nom = nom["residual_log_gain_local"]["max"] + nom["sensor_tolerance_local"]["max"] + e_nom
    level0 = [0.1 + float(p["trip_proxy"]) / 0.5 for p in ports if p["trip_proxy"]]
    firing_on = sum(g["firing_steering"] != [[0, 0]] for g in win.values())
    cap_quiet = max(win[n]["firing"]["capacitor_log_gain_local"]["max"] for n in ("nominal_200ns_retry1", "nominal_100ns_retry1", "mm2064_quiet_retry1"))
    cap_noisy = max(win[n]["firing"]["capacitor_log_gain_local"]["max"] for n in ("mm2064_noise_1_retry1", "mm2064_noise_2_retry1"))
    cell = {(p["run"], p["port"]): p for p in level["ports"]}

    H = [  # hypothesis, class, bound, source
        ("`scale`: `0 <= k`, with `k = beta / Cf`", "verified",
         f"`beta` = {fit['beta_per_V']:.3f} per V at 27 °C; all {fit['secants']} adjacent-grid secants of the nine DC curves are negative",
         "`bridge_check/local_summary.json`. Nominal devices, finite grid"),
        ("`fire`, `fire0`: `19/20 <= level`, `level0`", "verified for `level0`; for `level`, on cell 2064 only",
         f"`level0` from {min(level0):.4f} to {max(level0):.4f} over the 200 ports; smallest level at a FIRE in the replays of cell 2064: {level['smallest_level']:.5f}",
         "`need_budget_ports.csv`, `bridge_check/level_summary.json`"),
        ("`windows`: integral charge balances of the sensor and of the storage capacitor", "supported",
         "holds for the two ideal capacitors of the netlist; the device capacitances on the same nodes are counted in the residual",
         "`cell.spice`, `bridge_check/GAIN_PROTOCOL.md`"),
        ("`residual`: transferred-charge error, `k * eta`", "supported",
         f"{nom['residual_log_gain_local']['max']:.2e} on the nominal replays, {quiet['residual_log_gain_local']['max']:.2e} on cell 2064 without noise, {big('residual_log_gain_local'):.2e} with noise",
         "`bridge_check/window_samples.csv`. Five replays; not measured on the 100 original runs"),
        ("`sensorTol`: sensor-dose error `sigma`", "supported",
         f"{nom['sensor_tolerance_local']['max']:.2e} nominal, {quiet['sensor_tolerance_local']['max']:.2e} on cell 2064 without noise, {big('sensor_tolerance_local'):.2e} with noise, around `beta * (Cs/Cf) * 0.1` = {fit['nominal_dose']:.5f}",
         "`bridge_check/window_samples.csv`. Five replays"),
        ("`handoff`: linkage error `e`, window to read-to-read increment", "supported",
         f"{nom['handoff_local']['max']:.2e} not explained by the window, plus {nom['increment_error_bound_local']['max']:.2e} of local calibration (`epsilon` = {fit['epsilon_per_V']:.3f} per V times the step): "
         f"{e_nom:.2e} on the nominal replays. With noise the first term is {big('handoff_local'):.2e}, a sample of one draw",
         "`bridge_check/window_samples.csv`, Lean `ChargeWindow.local_slope_step`. Piecewise-linear DC curves of nominal devices"),
        ("`stepPos`: the gain does not fall at a write", "supported",
         f"every read-to-read increment of a silent pulse is positive in the five replays ({sum(w['silent_increments_positive'] for w in win.values())} of {sum(w['silent']['increment_local']['n'] for w in win.values())}); "
         "all 824 silent steps of the stored voltage are positive in the 100 original runs; `epsilon < beta`",
         "`bridge_check/local_summary.json`, `lean/README.md`. A voltage proxy for the original runs"),
        ("`gain`: start distance `a` to the centre of need `m`", "to measure",
         "only the peak-based proxy `a_proxy` exists. It assumes the ideal gain-to-swing relation and uses the outcomes of the same run",
         "`need_budget_ports.csv`, `NEED_BUDGET.md`"),
        ("`levelTol`: threshold error `ell`", "supported for cell 2064, to measure for the 99 others",
         f"`ell_static` = {level['ell_static']:.5f}, measured on the replay of cell 2064 without noise; `ell_dynamic` = {level['ell_dynamic']:.5f}, a statistic of two noisy replays, not certified for the original trajectory",
         "`bridge_check/level_summary.json`, `bridge_check/LEVEL_PROTOCOL.md`"),
        ("`room`: `a + m*(k*eta + sigma + e) + (20/17)*ell + 1/8000 < d0/2`", "to measure",
         f"on the nominal replays `k*eta + sigma + e` = {b_nom:.2e} per write, against `d0/2` = {fit['nominal_dose'] / 2:.4f}. The historical table uses another `b`, the spread of peak ratios, and `ell = 0`",
         "this file, `need_budget_ports.csv`"),
        ("Rest band: main charge in `[0.1, 0.1001]` before each pulse", "verified on the replays, supported for the original runs",
         f"{inside} of {len(rest)} pre-pulse states inside, `q` from {min(q):.8f} to {max(q):.8f}, the two noisy replays included",
         "`bridge_check/rest_samples.csv`"),
        ("FIRE of the circuit is one event per read", "verified on the replays",
         f"the protection latch rises at most once per period; the raw comparator has {ev['nominal_200ns_retry1']['comparator_transitions_per_fire_period'][0]} transitions in a period with a FIRE, "
         f"all within 3 ns of a latch transition, none inside an ERROR window",
         "`bridge_check/latch_events.csv`, `bridge_check/LOCAL_RESULTS.md`"),
        ("A silent pulse writes once, a firing pulse writes nothing", "verified on the available data",
         f"steering switch turned on once per silent window and on {firing_on} firing windows of the replays; capacitor change on a firing window at most {cap_quiet:.1e} in log-gain without noise, {cap_noisy:.1e} with noise; "
         "0 of 3 526 firing pulses steer in the original campaign",
         "`bridge_check/local_summary.json`, `VERDICTS.md`, `COMPLEMENT.md`"),
        ("Scalar read equation: the main charge is the gain times one pulse shape, with a FIRE at a fixed level", "to measure",
         f"not established. The slope of the gain law moves by up to {fit['epsilon_per_V'] / fit['beta_per_V']:.1%} with the input current and the drain voltage, and the level at a FIRE moves with the read",
         "`bridge_check/local_summary.json`, `bridge_check/level_samples.csv`"),
        ("The original noisy trajectory of each of the 100 runs", "out of reach",
         "no waveform of the original runs was kept, and the seed of a run does not reproduce its noise",
         "`COMPLEMENT.md`"),
        ("Every future pulse under any noise; the transistor netlist as a kernel execution", "out of reach",
         "a finite simulation gives sample values, not uniform bounds", "`lean/README.md`"),
    ]

    rows, briefs = [], {}
    for p in ports:
        key = (p["run"], int(p["port"]))
        own = cell.get(key)
        reasons = ["no waveform of this run: eta, sigma, e and the rest state are not bounded on its trajectory",
                   "a and d0 are peak-based proxies, and the gain law is calibrated on nominal devices only"]
        brief = ["no waveform", "proxies"]
        if own is None:
            reasons.append("ell is not measured for this cell: no replay without noise")
            brief.append("ell not measured")
        else:
            reasons.append(f"ell_static measured on the cell: room = {own['room_with_ell_static']:+.6f}, not positive")
            brief.append("ell_static: room not positive")
        if p["proxy_passes"] == "False":
            reasons.append("historical room, with ell = 0, is not positive")
            brief.append("historical room not positive")
        elif p["proxy_passes"] == "":
            reasons.append("historical room not evaluable: no dose-dispersion sample")
            brief.append("historical room not evaluable")
        briefs[key] = "; ".join(brief)
        rows.append(dict(run=p["run"], port=p["port"], observed_silent=p["observed_silent"], m=p["ceiling_count"], count_agrees=p["count_agrees"],
                         room_historical_ell_0=p["room_proxy"],
                         room_with_ell_static="" if own is None else f"{own['room_with_ell_static']:.12g}",
                         room_with_ell_static_and_dynamic="" if own is None else f"{own['room_with_ell']:.12g}",
                         in_certified_domain="no", reason="; ".join(reasons)))
    with (ROOT / "bridge_ports.csv").open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(rows[0]), lineterminator="\n")
        w.writeheader(); w.writerows(rows)

    agree = sum(r["count_agrees"] == "True" for r in rows)
    p1 = cell[("mc_2064", 1)]
    L = ["# The circuit against the need theorem", "",
         "Written by `bridge_application.py` from the pushed results. Theorem: `needAlong_of_circuit_tolerances` in",
         "[`lean/CircuitNeed.lean`](lean/CircuitNeed.lean), the variant of `needAlong_of_circuit_residual` with `sigma` and `e`.", "",
         "## Summary", "",
         "1. **Certified:** the theorem, the lemma `ChargeWindow.local_slope_step` that bounds the calibration error by `epsilon` times the step, "
         "and their audits: no `sorry`, no project axiom, seven negative controls rejected.",
         f"2. **Verified on the five replays:** the rest band ({inside} of {len(rest)} states), one FIRE of the latch per read, one write per silent pulse and none on a firing pulse.",
         f"3. **Supported, on the replays only:** `k*eta`, `sigma` and `e`. On the nominal replays their sum is {b_nom:.1e} per write, a quarter of `d0/2`; with noise `e` is larger and is a statistic.",
         f"4. **Not certified:** no port of the 100 cells is in the certified domain. 0 of {len(rows)}: the original trajectories have no waveform, `a` and `d0` are proxies, and `ell` is measured for one cell.",
         f"5. **`mc_2064`, port 1:** historical room {p1['room_historical_ell_0']:+.6f} with `ell = 0`; {p1['room_with_ell_static']:+.6f} with `ell_static` measured on the cell. "
         f"Its count stays {p1['observed_silent']} against `m` = {p1['m']}, and its historical status is not changed. The three replays of its mismatch seed give 4.", "",
         "## Hypotheses", "",
         "Verified: established on the available data. Supported: measured on a finite set of replays, on nominal devices, or through a proxy. "
         "To measure: no measure exists for the ports in question. Out of reach: cannot come from a finite simulation.", "",
         "| Hypothesis | Class | Bound | Source and limit |", "|---|---|---|---|"]
    L += [f"| {a} | {b} | {c} | {d} |" for a, b, c, d in H]
    L += ["", "## The 200 ports", "",
          f"In the certified domain: **0 of {len(rows)}**. The observed count equals `m` on {agree} ports and differs on {len(rows) - agree}; "
          "a count that agrees outside the certified domain is an observation, not a consequence of the theorem.", "",
          "Reasons, with the ports they apply to:", "",
          f"- no waveform of the original run, so `eta`, `sigma`, `e` and the rest state are not bounded on its trajectory: {len(rows)} ports;",
          f"- `a` and `d0` are peak-based proxies, and the gain law is calibrated on nominal devices only: {len(rows)} ports;",
          f"- `ell` is not measured for the cell: {sum(1 for r in rows if not r['room_with_ell_static'])} ports;",
          f"- `ell_static` measured on the cell and room not positive: {sum(1 for r in rows if r['room_with_ell_static'])} ports, those of `mc_2064`;",
          f"- historical room not positive even with `ell = 0`: {sum(p['proxy_passes'] == 'False' for p in ports)} ports; not evaluable: {sum(p['proxy_passes'] == '' for p in ports)}.", "",
          "The full table is [`bridge_ports.csv`](bridge_ports.csv). The historical columns are those of [`need_budget_ports.csv`](need_budget_ports.csv), unchanged.", "",
          "| Run | Port | Observed | m | Agrees | Historical room, `ell = 0` | Room with `ell_static` | In the certified domain | Reason |", "|---|---|---|---|---|---|---|---|---|"]
    for r in rows:
        why = briefs[(r["run"], int(r["port"]))]
        hist = "—" if r["room_historical_ell_0"] == "" else f"{float(r['room_historical_ell_0']):+.5f}"
        stat = "—" if r["room_with_ell_static"] == "" else f"{float(r['room_with_ell_static']):+.5f}"
        L.append(f"| `{r['run']}` | {r['port']} | {r['observed_silent']} | {r['m']} | {'yes' if r['count_agrees'] == 'True' else 'no'} | {hist} | {stat} | no | {why} |")
    L.append("")
    (ROOT / "BRIDGE_APPLICATION.md").write_text("\n".join(L))
    print("\n".join(L[:9 + len(H) + 12]))


if __name__ == "__main__":
    main()
