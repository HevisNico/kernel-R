"""The one analysis of campaign 3: words of the runs of the ring from their waveforms, against PREDICTED.json. It is the
analysis of campaign 2, with N-own' and N-word' added on the words' of amendment 2 (`write'`), and M7.

  analyze.py OUT_DIR PREDICTED.json --measures EVIDENCE... --runs EVIDENCE...

EVIDENCE are the folders written by `launch.py collect`: those of the measures (small files are enough) and those
of the network runs (with their waveforms). Written in OUT_DIR: RESULTS.json and REPORT.md, as generated.

It follows PREDICTION.md and decides nothing: the eligible instances, the needs, the ports with own room and room up
to them, the laps, the zero-error words and the control instance are read in PREDICTED.json, which was committed
before the network runs. It checks first that PREDICTED.json and Predicted.lean are what `predicted.py` gives from
the evidence of the measures, and that the runs found are the runs it lists. If they are not, every claim is "not
established".
"""
import argparse
import json
from pathlib import Path
import statistics
import sys
import tempfile

HERE = Path(__file__).resolve().parent
NET = HERE.parent / "network-circuit"
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(NET))
sys.path.insert(0, str(NET / "phase1"))
import measure
import net
import plan
import predicted
import router

PORTS = plan.PORTS
UNUSED = plan.UNUSED
TOLERANCE_MV = 0.01
WRITE_PRIME_S = 1e-6           # write': the write signal stays above 0.9 V for at least 1 us
SEPARATION = 16
NOT = "not established"


def letter(tr, o):
    """The letter of one pulse, as PREDICTION.md defines the word of a port."""
    if o.get("refused"):
        return "r"
    if not o["delivered"]:
        return "x"
    c, q, date = o["cell"], o["port"], o["date_s"]
    if tr.at(f"v(x{c}.p)", date - 1e-9) > 0.9:
        return "-"
    fires = len(tr.crossings(f"v(x{c}.p)", date, date + net.TU + 2e-6))
    writes = len(tr.crossings(f"v(x{c}.x{q}.si)", date, date + net.CYCLE))
    return "F" if (fires, writes) == (1, 0) else "s" if (fires, writes) == (0, 1) else "?"


def write_crossings(tr, o):
    """Every rising crossing of 0.9 V by the write signal of the port of a delivered pulse inside its cycle, with the
    time it stays above 0.9 V: to the next falling crossing, wherever it falls (to the end of the waveform if none)."""
    c, q, date = o["cell"], o["port"], o["date_s"]
    name = f"v(x{c}.x{q}.si)"
    out = []
    for rise in tr.crossings(name, date, date + net.CYCLE):
        falls = tr.crossings(name, rise, float(tr.t[-1]) + 1e-12, rising=False)
        out.append(dict(rise_units=(rise - date) / net.TU, width_s=(falls[0] if falls else float(tr.t[-1])) - rise))
    return out


def letter_prime(tr, o):
    """The letter of one pulse in the word' of amendment 2: as `letter`, with write' in place of write."""
    if o.get("refused"):
        return "r"
    if not o["delivered"]:
        return "x"
    c, date = o["cell"], o["date_s"]
    if tr.at(f"v(x{c}.p)", date - 1e-9) > 0.9:
        return "-"
    fires = len(tr.crossings(f"v(x{c}.p)", date, date + net.TU + 2e-6))
    writes = sum(x["width_s"] >= WRITE_PRIME_S for x in write_crossings(tr, o))
    return "F" if (fires, writes) == (1, 0) else "s" if (fires, writes) == (0, 1) else "?"


def lap(date_s, period):
    """floor(d / P) + 1, with d the start of the pulse in units after date 0."""
    return int(((date_s - router.ORIGIN) / net.TU) // period) + 1


def network(evidence, doses, guarded):
    """Everything the analysis takes from one run of the ring."""
    result = json.loads((evidence / "result.json").read_text())
    record = json.loads((evidence / "record.json").read_text())
    tr = measure.Trace(evidence / "trace.raw")
    P = result["calendar"]["period"]
    occurrences = sorted(result["occurrences"], key=lambda o: o["date_s"])
    words, words_prime, short_writes, own, latencies, moves, laps = {}, {}, {}, {}, {}, [], {}
    for name in PORTS + UNUSED:
        c, q = name[0], int(name[1])
        mine = [o for o in occurrences if f"{o['cell']}{o['port']}" == name]
        letters = [letter(tr, o) for o in mine]
        words[name] = "".join(letters)
        words_prime[name] = "".join(letter_prime(tr, o) for o in mine)
        short_writes[name] = [dict(pulse=i + 1, **x) for i, o in enumerate(mine) if o["delivered"] for x in write_crossings(tr, o) if x["width_s"] < WRITE_PRIME_S]
        own[name] = "".join("r" if o.get("refused") else "x" if not o["delivered"] else "-" if o["protected_at_start"] else
                            "F" if o["fire"] and o[f"writes{q}"] == 0 else "s" if not o["fire"] and o[f"writes{q}"] == 1 else "?" for o in mine)
        latencies[name] = [(tr.crossings(f"v(x{c}.p)", o["date_s"], o["date_s"] + net.TU + 2e-6)[0] - o["date_s"]) / net.TU for o, x in zip(mine, letters) if x == "F"]
        laps[name] = dict(first_pulse=lap(mine[0]["date_s"], P) if mine else None, writes=[lap(o["date_s"], P) for o, x in zip(mine, letters) if x == "s"])
        u = lambda lo, hi: tr.u(c, q, lo, hi) * 1e3
        previous = None
        for o, x in zip(mine, letters):
            if not o["delivered"]:
                continue
            before, after = u(o["date_s"] - 30e-6, o["date_s"] - 2e-6), u(o["date_s"] + net.CYCLE - 30e-6, o["date_s"] + net.CYCLE - 2e-6)
            if previous is not None:
                moves.append(dict(port=name, what="between two of its pulses", mV=before - previous))
            if x == "s":
                moves.append(dict(port=name, what="an s against its measured dose", mV=(before - after) - doses[name]))
            else:
                moves.append(dict(port=name, what="across a pulse " + x, mV=before - after))
            previous = after
    dates = {c: sorted(o["date_s"] for o in occurrences if o["cell"] == c and o["delivered"]) for c in result["cells"]}
    separation = min([(b - a) / net.TU for d in dates.values() for a, b in zip(d, d[1:])] or [float("inf")])
    by_id = {o["id"]: o for o in occurrences}
    launch = [f for f in result["fires"] if f["cell"] == "a" and any(f"{by_id[i]['cell']}{by_id[i]['port']}" == "a1" for i in f["during"])]
    back = [f for f in result["fires"] if f["cell"] == "a" and any(f"{by_id[i]['cell']}{by_id[i]['port']}" == "a2" for i in f["during"])]
    worst = max(moves, key=lambda m: abs(m["mV"])) if moves else dict(port=None, what="no pulse", mV=0.0)
    H = dict(guard_refuses_no_pulse=not any(o.get("refused") for o in occurrences),
             no_pulse_on_a_protected_cell=not any("-" in w for w in words.values()),
             every_pulse_delivered=all(o["delivered"] for o in occurrences),
             nothing_left_in_the_queue=not result["still_queued_at_the_horizon"],
             launch_fires_carried_to_b1_and_return_fires_nowhere=all([e["cell"], e["port"]] == ["b", 1] for f in launch for e in f["routed"]) and
             all(len(f["routed"]) == 1 for f in launch) and not any(f["routed"] for f in back),
             stored_voltages_move_by_doses_only=abs(worst["mV"]) <= TOLERANCE_MV,
             waveform_reaches_the_horizon=bool(record["reached_its_last_date"]))
    if guarded:
        H["pulses_of_a_cell_16_units_apart"] = separation >= SEPARATION - 1e-9
    initial = {p: result["initial_u_V"][p] * 1e3 for p in PORTS + UNUSED}
    final = {p: result["final_u_V"][p] * 1e3 for p in PORTS + UNUSED}
    P4 = {p: dict(initial_mV=initial[p], final_mV=final[p], predicted_mV=initial[p] - words[p].count("s") * doses[p], pulses=len(words[p]),
                  allowance_mV=(2 * len(words[p]) + 1) * TOLERANCE_MV) for p in PORTS}
    for p in PORTS:
        P4[p]["holds"] = abs(P4[p]["final_mV"] - P4[p]["predicted_mV"]) <= P4[p]["allowance_mV"]
    for p in UNUSED:
        P4[p] = dict(initial_mV=initial[p], final_mV=final[p], allowance_mV=TOLERANCE_MV, holds=abs(final[p] - initial[p]) <= TOLERANCE_MV)
    return dict(words=words, words_prime=words_prime, writes_that_are_not_write_prime=short_writes, record_is_the_waveform=words == own, pulse_laps=laps, freeze_lap=max([x for p in PORTS for x in laps[p]["writes"]] or [0]),
                fires=len(result["fires"]), launch_fires=len(launch), return_fires=len(back), least_separation_units=separation,
                largest_move_not_a_dose_mV=worst, H=H, P4=P4, latencies=latencies, wall_s=result["wall_s"], guard_units=result["guard_units"],
                calendar=result["calendar"]["name"], noise_fingerprint=record["noise_fingerprint"])


def n_own(word, need):
    """None if the port received fewer than `need` pulses (the port-run does not count); else whether its word is
    exactly `need` letters s followed only by letters F."""
    if len(word) < need:
        return None
    return word == "s" * need + "F" * (len(word) - need)


def verdict(rows, good):
    return NOT if not rows else "holds" if all(good(r) for r in rows) else "fails"


def analyse(P, measure_folders, run_folders, **setup):
    """`setup` is empty for the campaign; the rehearsal gives the arguments of `predicted.build` that it used."""
    out = dict(what="analysis of campaign 2, generated by analyze.py; see PREDICTION.md")
    # 1. the predictions are those of the measures, and the runs are those of the predictions
    with tempfile.TemporaryDirectory() as tmp:
        predicted.build(tmp, [str(x) for x in measure_folders], **setup)
        out["predictions_are_those_of_the_measures"] = json.loads((Path(tmp) / "PREDICTED.json").read_text()) == P
        out["lean_file_is_that_of_the_measures"] = (Path(tmp) / "Predicted.lean").read_text() == predicted.lean(P["instances"], P["measured_instances"])
    trusted = out["predictions_are_those_of_the_measures"]
    planned = P["network_runs"]
    found = predicted.gather(run_folders, planned)
    out["runs_not_in_the_predictions"] = sorted({r["id"] for f in map(Path, run_folders) for r in json.loads((f / "STATE.json").read_text())["records"]} - {r["id"] for r in planned})
    measured_runs = predicted.gather(measure_folders, setup.get("runs") or plan.measure_runs(setup.get("which")))
    out["measure_runs"] = {k: v[0] for k, v in measured_runs.items()}
    out["network_runs"] = {k: v[0] for k, v in found.items()}
    out["removed_for_the_budget"] = [r["id"] for r in P["removed_for_the_budget"]]
    # 2. every network run that counts
    runs = {}
    for r in planned:
        status, evidence = found[r["id"]]
        if status == "complete":
            runs[r["id"]] = dict(r, **network(evidence, P["instances"][str(r["seed"])]["doses_mV"], guarded=bool(r["guard"])))
    out["runs"] = runs
    by = lambda seed, scenario: [x for x in runs.values() if str(x["seed"]) == seed and x["scenario"] == scenario]
    # 3. the primary claim: P1 and P2; H and P4 reported with it
    tested, not_tested, rows = [], [], []
    for seed in P["eligible_instances"]:
        quiet = by(seed, "quiet")
        if not quiet:
            not_tested.append(seed)
            continue
        I, x = P["instances"][seed], quiet[0]
        expected = I["zero_error_words"]["quiet"]
        S = [sum(I["need"][q] for q in PORTS[:k + 1]) for k in range(len(PORTS))]
        first = {p: (S[k - 1] if k else 0) + 1 for k, p in enumerate(PORTS)}
        tested.append(seed)
        rows.append(dict(instance=seed, run=x["id"], laps=I["laps"]["quiet"], predicted=expected, observed={p: x["words"][p] for p in PORTS},
                         ports_that_differ=[p for p in PORTS if x["words"][p] != expected[p]],
                         freeze_lap=dict(predicted=S[-1], observed=x["freeze_lap"]),
                         first_pulse_lap=dict(predicted=first, observed={p: x["pulse_laps"][p]["first_pulse"] for p in PORTS}),
                         pulses_on_unused_ports={p: x["words"][p] for p in UNUSED if x["words"][p]},
                         H=x["H"], P4=x["P4"], least_separation_units=x["least_separation_units"], largest_move_not_a_dose_mV=x["largest_move_not_a_dose_mV"],
                         record_is_the_waveform=x["record_is_the_waveform"]))
    for row in rows:
        row["P1"] = not row["ports_that_differ"]
        row["P2"] = row["freeze_lap"]["predicted"] == row["freeze_lap"]["observed"] and row["first_pulse_lap"]["predicted"] == row["first_pulse_lap"]["observed"]
    out["primary"] = dict(verdict=verdict(rows, lambda r: r["P1"] and r["P2"]) if trusted else NOT, eligible_instances=P["eligible_instances"],
                          tested=tested, not_tested=not_tested, rows=rows)
    out["H"] = dict(verdict=verdict(rows, lambda r: all(r["H"].values())) if trusted else NOT)
    out["P4"] = dict(verdict=verdict(rows, lambda r: all(v["holds"] for v in r["P4"].values())) if trusted else NOT)
    # 4. the claim under noise, after the noisy runs that share a fingerprint
    duplicates, kept = [], []
    for seed in P["measured_instances"]:
        seen = {}
        for x in by(seed, "noisy"):
            if x["noise_fingerprint"] in seen:
                duplicates.append(dict(instance=seed, run=x["id"], same_noise_as=seen[x["noise_fingerprint"]]))
            else:
                seen[x["noise_fingerprint"]] = x["id"]
                kept.append(x)
    out["noisy_runs_with_the_noise_of_an_earlier_run"] = duplicates
    own_rows, word_rows, short, m1, m2, m5, m7 = [], [], [], [], [], [], []
    own_prime, word_prime, short_prime = [], [], []
    for x in kept:
        seed = str(x["seed"])
        I = P["instances"][seed]
        B = I["budgets"]["noisy_k3"]
        quiet = by(seed, "quiet")
        for p in PORTS:
            w, need, zero = x["words"][p], I["need"][p], I["zero_error_words"]["noisy"][p]
            wp = x["words_prime"][p]
            m7.append(dict(instance=seed, run=x["id"], port=p, word=w, word_prime=wp, differ=w != wp, writes_that_are_not_write_prime=x["writes_that_are_not_write_prime"][p]))
            if B["own_room"][p]:
                okp = n_own(wp, need)
                if okp is None:
                    short_prime.append(dict(instance=seed, run=x["id"], port=p, need=need, observed=wp))
                else:
                    own_prime.append(dict(instance=seed, run=x["id"], port=p, need=need, observed=wp, holds=okp))
            if B["room_up_to_it"][p]:
                word_prime.append(dict(instance=seed, run=x["id"], port=p, zero_error_word=zero, observed=wp, holds=wp == zero))
            if B["own_room"][p]:
                ok = n_own(w, need)
                if ok is None:
                    short.append(dict(instance=seed, run=x["id"], port=p, need=need, observed=w))
                else:
                    own_rows.append(dict(instance=seed, run=x["id"], port=p, need=need, observed=w, holds=ok))
            else:
                m1.append(dict(instance=seed, run=x["id"], port=p, zero_error_word=zero, observed=w, same_word=w == zero, same_writes=w.count("s") == zero.count("s")))
            if B["room_up_to_it"][p]:
                word_rows.append(dict(instance=seed, run=x["id"], port=p, zero_error_word=zero, observed=w, holds=w == zero))
            elif B["own_room"][p]:
                m2.append(dict(instance=seed, run=x["id"], port=p, zero_error_word=zero, observed=w, same_word=w == zero))
            lat = x["latencies"][p]
            shaped = lambda word: word.count("s") == need and word == "s" * need + "F" * (len(word) - need)
            if quiet and len(lat) >= 3 and shaped(w) and shaped(quiet[0]["words"][p]) and quiet[0]["latencies"][p]:
                slope = I["constants"][p]["train_18_quiet"]["slope_per_mV"]
                m5.append(dict(instance=seed, run=x["id"], port=p, fires=len(lat), offset_mV=(statistics.median(quiet[0]["latencies"][p]) - statistics.mean(lat)) / slope,
                               within_sd_mV=statistics.stdev(lat) / slope))
    out["N_own"] = dict(verdict=verdict(own_rows, lambda r: r["holds"]) if trusted else NOT, port_runs=len(own_rows),
                        port_runs_with_fewer_than_need_pulses=len(short), rows=own_rows, not_counted=short)
    out["N_word"] = dict(verdict=verdict(word_rows, lambda r: r["holds"]) if trusted else NOT, port_runs=len(word_rows), rows=word_rows)
    out["N_own_prime"] = dict(verdict=verdict(own_prime, lambda r: r["holds"]) if trusted else NOT, port_runs=len(own_prime),
                              port_runs_with_fewer_than_need_pulses=len(short_prime), rows=own_prime, not_counted=short_prime)
    out["N_word_prime"] = dict(verdict=verdict(word_prime, lambda r: r["holds"]) if trusted else NOT, port_runs=len(word_prime), rows=word_prime)
    out["M7"] = m7
    # 5. the negative control
    control = P["control_instance"]
    rows = by(control, "control") if control else []
    if rows:
        x, I = rows[0], P["instances"][control]
        expected, need = I["zero_error_words"]["quiet"], I["need"]["a2"]
        w = x["words"]["a2"]
        earlier = "F" in w and w.index("F") < need and set(w[:w.index("F")]) <= {"s"}
        out["C"] = dict(verdict=("holds" if earlier else "fails") if trusted else NOT, instance=control, run=x["id"], need_of_a2=need,
                        zero_error_words=expected, observed={p: x["words"][p] for p in PORTS}, ports_that_differ=[p for p in PORTS if x["words"][p] != expected[p]],
                        pulses_on_a_protected_cell=sum(v.count("-") for v in x["words"].values()), least_separation_units=x["least_separation_units"])
    else:
        out["C"] = dict(verdict=NOT, instance=control, why="no control instance" if control is None else "its run does not count")
    # 6. declared comparisons
    out["M1"], out["M2"], out["M5"] = m1, m2, m5
    out["M3"] = [dict(instance=seed, run=x["id"], zero_error_words=P["instances"][seed]["zero_error_words"]["quiet"], observed={p: x["words"][p] for p in PORTS},
                      own_room={p: P["instances"][seed]["budgets"]["noise_free"]["own_room"][p] for p in PORTS},
                      room_up_to_it={p: P["instances"][seed]["budgets"]["noise_free"]["room_up_to_it"][p] for p in PORTS},
                      same_word={p: x["words"][p] == P["instances"][seed]["zero_error_words"]["quiet"][p] for p in PORTS})
                 for seed in P["measured_instances"] if seed not in P["eligible_instances"] for x in by(seed, "quiet")]
    nominal = lambda L: dict(zip(PORTS, predicted.ring.zero_error([4] * len(PORTS), L)["words"]))
    out["M4"] = dict(eligible={seed: sum(P["instances"][seed]["zero_error_words"]["quiet"][p] != nominal(P["instances"][seed]["laps"]["quiet"])[p] for p in PORTS)
                               for seed in P["eligible_instances"]},
                     quiet_runs={x["id"]: dict(eligible=str(x["seed"]) in P["eligible_instances"],
                                               ports_that_differ_from_the_nominal_word=sum(x["words"][p] != nominal(x["laps"])[p] for p in PORTS))
                                 for x in runs.values() if x["scenario"] == "quiet"})
    out["M6"] = [dict(run=x["id"], scenario=x["scenario"], eligible=str(x["seed"]) in P["eligible_instances"], H=x["H"], P4={p: v["holds"] for p, v in x["P4"].items()})
                 for x in runs.values() if x["scenario"] == "noisy" or (x["scenario"] == "quiet" and str(x["seed"]) not in P["eligible_instances"])]
    return out


def report(R, P):
    yes = lambda b: "yes" if b else "no"
    L = ["# Periodic ring of R cells, campaign 3: report", "", "Generated by `analyze.py` from the evidence of the two machines. Not edited.", ""]
    L += ["## Checks before any count", "",
          f"- PREDICTED.json is what `predicted.py` gives from the evidence of the measures: **{'yes' if R['predictions_are_those_of_the_measures'] else 'NO: every claim is not established'}**.",
          f"- Predicted.lean is what `predicted.py` gives from them: {yes(R['lean_file_is_that_of_the_measures'])}.",
          f"- Network runs outside the list of PREDICTED.json: {R['runs_not_in_the_predictions'] or 'none'}.",
          f"- Noisy runs removed for the budget before the launch: {R['removed_for_the_budget'] or 'none'}.",
          f"- Measure runs that do not count: {sorted(k for k, v in R['measure_runs'].items() if v != 'complete') or 'none'}.",
          f"- Network runs that do not count (missing runs): {sorted(k + ': ' + v for k, v in R['network_runs'].items() if v != 'complete') or 'none'}.",
          f"- Noisy runs with the noise of an earlier run: {R['noisy_runs_with_the_noise_of_an_earlier_run'] or 'none'}.", ""]
    L += ["## Instances", "", "| Instance | Machine | Measured | Needs a1, b1, c1, a2 | Eligible | Own room at K = 3 | Room up to it at K = 3 | Laps |", "|---|---|---|---|---|---|---|---|"]
    for seed, I in P["instances"].items():
        if I["measured"]:
            B = I["budgets"]["noisy_k3"]
            L.append(f"| {seed} | {P['machine_of_each_instance'].get(seed, '-')} | yes | {', '.join(str(I['need'][p]) for p in PORTS)} | {yes(I['eligible'])} | "
                     f"{', '.join(p for p in PORTS if B['own_room'][p]) or 'none'} | {', '.join(p for p in PORTS if B['room_up_to_it'][p]) or 'none'} | "
                     f"{I['laps']['quiet']} / {I['laps']['noisy']} |")
        else:
            L.append(f"| {seed} | {P['machine_of_each_instance'].get(seed, '-')} | no: {json.dumps(I['why'])} | - | - | - | - | - |")
    p1 = R["primary"]
    L += ["", f"Control instance: {P['control_instance']}.", "", "## Primary claim: P1 and P2", "",
          f"**{p1['verdict']}.** Eligible instances: {p1['eligible_instances'] or 'none'}; tested: {p1['tested'] or 'none'}; not tested: {p1['not_tested'] or 'none'}.", ""]
    if p1["rows"]:
        L += ["| Instance | Port | Predicted | Observed | |", "|---|---|---|---|---|"]
        for row in p1["rows"]:
            L += [f"| {row['instance']} | `{p}` | `{row['predicted'][p]}` | `{row['observed'][p]}` | {'differs' if p in row['ports_that_differ'] else 'same'} |" for p in PORTS]
        L += ["", "| Instance | Lap of the freeze, predicted / observed | First pulse of a1, b1, c1, a2: predicted / observed | P2 |", "|---|---|---|---|"]
        for row in p1["rows"]:
            f = row["first_pulse_lap"]
            L.append(f"| {row['instance']} | {row['freeze_lap']['predicted']} / {row['freeze_lap']['observed']} | "
                     f"{', '.join(str(f['predicted'][p]) for p in PORTS)} / {', '.join(str(f['observed'][p]) for p in PORTS)} | {'holds' if row['P2'] else 'fails'} |")
        L.append("")
    L += [f"**H, the hypotheses observed: {R['H']['verdict']}.** **P4, final stored values: {R['P4']['verdict']}.** Neither refutes P1 or P2.", ""]
    if p1["rows"]:
        L += ["| Instance | Hypotheses that do not hold | Closest pulses on a cell, units | Largest move that is not a dose, mV | Ports where P4 fails |", "|---|---|---|---|---|"]
        for row in p1["rows"]:
            m = row["largest_move_not_a_dose_mV"]
            L.append(f"| {row['instance']} | {[k for k, v in row['H'].items() if not v] or 'none'} | {row['least_separation_units']:.2f} | {m['mV']:+.4f} ({m['port']}, {m['what']}) | "
                     f"{[p for p, v in row['P4'].items() if not v['holds']] or 'none'} |")
        L.append("")
    L += ["## The claim under noise, per port, at K = 3", ""]
    o, w = R["N_own"], R["N_word"]
    L += [f"**N-own: {o['verdict']}**, on {o['port_runs']} port-runs; {o['port_runs_with_fewer_than_need_pulses']} port-runs with fewer than `need` pulses do not count.", ""]
    if o["rows"]:
        L += ["| Instance | Run | Port | Need | Observed | |", "|---|---|---|---|---|---|"]
        L += [f"| {r['instance']} | {r['run']} | `{r['port']}` | {r['need']} | `{r['observed']}` | {'holds' if r['holds'] else 'fails'} |" for r in o["rows"]]
        L.append("")
    L += [f"**N-word: {w['verdict']}**, on {w['port_runs']} port-runs.", ""]
    if w["rows"]:
        L += ["| Instance | Run | Port | Zero-error word | Observed | |", "|---|---|---|---|---|---|"]
        L += [f"| {r['instance']} | {r['run']} | `{r['port']}` | `{r['zero_error_word']}` | `{r['observed']}` | {'holds' if r['holds'] else 'fails'} |" for r in w["rows"]]
        L.append("")
    op, wq = R["N_own_prime"], R["N_word_prime"]
    L += ["### With write' (amendment 2), in addition to N-own and N-word, never instead; campaign 3 only, never pooled", "",
          f"**N-own': {op['verdict']}**, on {op['port_runs']} port-runs; {op['port_runs_with_fewer_than_need_pulses']} port-runs with fewer than `need` pulses do not count.", ""]
    if op["rows"]:
        L += ["| Instance | Run | Port | Need | Observed (word') | |", "|---|---|---|---|---|---|"]
        L += [f"| {r['instance']} | {r['run']} | `{r['port']}` | {r['need']} | `{r['observed']}` | {'holds' if r['holds'] else 'fails'} |" for r in op["rows"]]
        L.append("")
    L += [f"**N-word': {wq['verdict']}**, on {wq['port_runs']} port-runs.", ""]
    if wq["rows"]:
        L += ["| Instance | Run | Port | Zero-error word | Observed (word') | |", "|---|---|---|---|---|---|"]
        L += [f"| {r['instance']} | {r['run']} | `{r['port']}` | `{r['zero_error_word']}` | `{r['observed']}` | {'holds' if r['holds'] else 'fails'} |" for r in wq["rows"]]
        L.append("")
    c = R["C"]
    L += ["## Negative control", "", f"**C: {c['verdict']}.** Instance: {c['instance']}." + ("" if "observed" in c else " " + c["why"] + "."), ""]
    if "observed" in c:
        L += ["| Port | Zero-error word | Observed, return 8 units after the launch | |", "|---|---|---|---|"]
        L += [f"| `{p}` | `{c['zero_error_words'][p]}` | `{c['observed'][p]}` | {'differs' if p in c['ports_that_differ'] else 'same'} |" for p in PORTS]
        L += ["", f"Pulses on a protected cell: {c['pulses_on_a_protected_cell']}. Closest pulses on a cell: {c['least_separation_units']:.2f} units.", ""]
    L += ["## Declared comparisons, not claims", ""]
    count = lambda rows, key: f"{sum(r[key] for r in rows)} of {len(rows)}"
    L += [f"- **M1**, ports without own room at K = 3, noisy runs: {count(R['M1'], 'same_word')} port-runs with the zero-error word, {count(R['M1'], 'same_writes')} with its writes.",
          f"- **M2**, ports with own room but not room up to them at K = 3, noisy runs: {count(R['M2'], 'same_word')} port-runs with the zero-error word."]
    m3 = [(r["same_word"][p]) for r in R["M3"] for p in PORTS]
    L.append(f"- **M3**, runs without noise of the instances that are not eligible: {sum(m3)} of {len(m3)} ports with the zero-error word.")
    L.append(f"- **M4**, the nominal predictor (need 4 everywhere): ports whose zero-error word differs from the nominal word, per eligible instance: {R['M4']['eligible'] or 'none'}; "
             f"ports of each run without noise whose word differs from it: {dict((k, v['ports_that_differ_from_the_nominal_word']) for k, v in R['M4']['quiet_runs'].items()) or 'none'}.")
    if R["M4"]["eligible"] and not any(R["M4"]["eligible"].values()):
        L.append("  P1 cannot tell the measured predictor from the nominal one on these instances.")
    if R["M5"]:
        offsets = [x["offset_mV"] for x in R["M5"]]
        L.append(f"- **M5**, {len(offsets)} port-runs: run offsets {statistics.mean(v * v for v in offsets) ** 0.5:.3f} mV rms (fixed: 0.090), "
                 f"scatter within a run {statistics.mean(x['within_sd_mV'] ** 2 for x in R['M5']) ** 0.5:.3f} mV rms (fixed: 0.064).")
    else:
        L.append("- **M5**: no port-run to compare.")
    L.append(f"- **M6**, H and P4 on the other runs: {sum(all(r['H'].values()) for r in R['M6'])} of {len(R['M6'])} runs with every hypothesis, "
             f"{sum(all(r['P4'].values()) for r in R['M6'])} of {len(R['M6'])} with P4 on every port.")
    differ = [r for r in R["M7"] if r["differ"]]
    shorts = [dict(run=r["run"], port=r["port"], **x) for r in R["M7"] for x in r["writes_that_are_not_write_prime"]]
    L.append(f"- **M7**, word against word' in the noisy runs: {len(differ)} of {len(R['M7'])} port-runs differ" + (": " + ", ".join(f"{r['run']} `{r['port']}` `{r['word']}` / `{r['word_prime']}`" for r in differ) if differ else "") + "; "
             + (f"{len(shorts)} writes that are not write': " + ", ".join(f"{x['run']} `{x['port']}` pulse {x['pulse']} at {x['rise_units']:.4f} units, {x['width_s'] * 1e9:.1f} ns" for x in shorts) if shorts else "no write that is not a write'") + ".")
    L += ["", "## Runs", "", "| Run | Scenario | Laps | Words a1, b1, c1, a2 | FIRE | Closest pulses, units | Wall, s |", "|---|---|---|---|---|---|---|"]
    for x in R["runs"].values():
        L.append(f"| {x['id']} | {x['scenario']} | {x['laps']} | " + ", ".join(f"`{x['words'][p]}`" for p in PORTS) +
                 f" | {x['fires']} | {x['least_separation_units']:.2f} | {x['wall_s']:.0f} |")
    return "\n".join(L) + "\n"


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("out", type=Path)
    p.add_argument("predicted", type=Path)
    p.add_argument("--measures", type=Path, nargs="+", required=True)
    p.add_argument("--runs", type=Path, nargs="+", required=True)
    a = p.parse_args()
    P = json.loads(a.predicted.read_text())
    R = analyse(P, a.measures, a.runs)
    (a.out / "RESULTS.json").write_text(json.dumps(R, indent=1) + "\n")
    (a.out / "REPORT.md").write_text(report(R, P))
    print(json.dumps({k: R[k]["verdict"] for k in ("primary", "H", "P4", "N_own", "N_word", "N_own_prime", "N_word_prime", "C")}))


if __name__ == "__main__":
    main()
