"""The constants of the model for each instance, from MEASURES.json alone. Phase 1, exploratory.

  constants.py MEASURES.json CONSTANTS.json

Voltages are in mV across the storage capacitor (`u`: stored node minus summing node). A more negative `u` is a
higher gain. Per port:

  preset        `u` before the first pulse
  threshold     the middle of the bracket between the weakest state that fired and the strongest that stayed
                silent, among reads at least 22 units after the previous pulse of the cell
  dose          the mean step of a silent read
  gap           preset minus threshold, also in doses; `need` is the number of doses that crosses it
  slope         latency per mV at the trained state, from the isolated reads of the scan
  help_16       what a FIRE 16 units earlier adds to a read, over what a pulse 22 units earlier adds: the gain
                of latency, divided by the slope
  help_18       the same at 18 units, from the train without noise: after a silent read, and after a FIRE
  noise         of a read, as an equivalent `u`, from the noisy trains that gave the word of the train without
                noise, each in its own simulator process:
                  within a run   scatter of the FIRE latency about the mean of its run, divided by the slope;
                  run offsets    for each run, (FIRE latency without noise - mean FIRE latency of the run) / slope

Per instance:
  noise_between_runs_mV   root mean square of the run offsets of its four ports: what one run adds to every read
                          of a port, the same for the whole run (see NOISE.md)
  dose_noise_sd_mV        root mean square of (dose in a noisy train - dose of the port without noise)
"""
import json
from pathlib import Path
import statistics
import sys

HELP_22_NOMINAL = 0.015         # mV, phase 0, nominal cell: what a pulse 22 units earlier adds over a long silence


def secant(points, u):
    """Slope of latency against u at `u`, from the two measured points around it (or the two nearest)."""
    points = sorted(set(points))
    merged = []
    for p in points:                                      # one point per stored state: reads at one state repeat within 2 uV
        if merged and p[0] - merged[-1][0][0] < 0.02:
            merged[-1].append(p)
        else:
            merged.append([p])
    points = [(statistics.mean(x[0] for x in g), statistics.mean(x[1] for x in g)) for g in merged]
    assert len(points) >= 2
    i = min(max(sum(1 for p in points if p[0] <= u), 1), len(points) - 1)
    (u0, l0), (u1, l1) = points[i - 1], points[i]
    return (l1 - l0) / (u1 - u0)


def port(name, scan, quiet, noisy):
    P = scan["pulses"]
    isolated = [p for p in P if p["kind"] in ("read", "reference")]
    fired = [(p["u_before_mV"], p["latency"]) for p in isolated if p["fire"]]
    silent = [p["u_before_mV"] for p in isolated if not p["fire"]]
    doses = [p["step_mV"] for p in P if not p["fire"]]
    lo, hi = max(u for u, _ in fired), min(silent)
    assert lo < hi
    dose, threshold, preset = statistics.mean(doses), (lo + hi) / 2, P[0]["u_before_mV"]
    gap = preset - threshold
    need = next(n for n in range(1, 40) if n * dose > gap)
    reference = next(p for p in P if p["kind"] == "reference")
    after16 = next(p for p in P if p["kind"] == "16 units after a FIRE")
    trained = reference["u_before_mV"]
    slope = secant(fired, trained)
    r = dict(preset_mV=preset, threshold_mV=threshold, bracket_half_mV=(hi - lo) / 2, dose_mV=dose, dose_spread_mV=max(doses) - min(doses),
             gap_mV=gap, gap_doses=gap / dose, need=need, room_last_silence_mV=gap - (need - 1) * dose, room_first_fire_mV=need * dose - gap,
             trained_mV=trained, latency_isolated=reference["latency"], slope_per_mV=slope,
             help_16_mV=(reference["latency"] - after16["latency"]) / slope,
             latency_range=[min(l for _, l in fired), max(l for _, l in fired)],
             protected_until_units=max(p["protected_until_units"] for p in P if p["fire"]),
             error_phase_units=[min(p["error_phase_units"][0] for p in P if p.get("error_phase_units")), max(p["error_phase_units"][1] for p in P if p.get("error_phase_units"))])
    T = quiet
    word = "".join("F" if p["fire"] else "s" for p in T)
    first = word.index("F")
    assert word == "s" * first + "F" * (len(word) - first) and len(word) - first >= 2
    level = T[first]["u_before_mV"]
    here = secant(fired, level)
    base = reference["latency"] + (level - trained) * here               # isolated latency at this stored state
    later = [p["latency"] for p in T[first + 1:]]
    r["train_18_quiet"] = dict(word=word, writes=first, state_mV=level, slope_per_mV=here, latency_first_fire=T[first]["latency"],
                               latency_later=statistics.median(later), later_range=[min(later), max(later)])
    r["help_18_after_silent_mV"] = (base - T[first]["latency"]) / here
    r["help_18_after_fire_mV"] = (base - statistics.median(later)) / here
    runs, offsets, squares, count, doses = [], [], 0.0, 0, []
    for run in noisy:
        N = run["ports"][name]
        noisy_word = "".join("F" if p["fire"] else "s" for p in N)
        doses += [p["step_mV"] for p in N if not p["fire"]]
        lat = [p["latency"] for p in N if p["fire"]]
        same = noisy_word == "s" * first + "F" * (len(noisy_word) - first) and len(lat) >= 3
        entry = dict(run=run["run"], word=noisy_word, same_word_as_without_noise=same)
        if same:
            mean = statistics.mean(lat)
            entry.update(fires=len(lat), offset_mV=(statistics.median(later) - mean) / here, within_sd_mV=statistics.stdev(lat) / here)
            offsets.append(entry["offset_mV"])
            squares += sum((x - mean) ** 2 for x in lat) / here ** 2
            count += len(lat) - 1
        runs.append(entry)
    r["noisy_trains"] = runs
    r["noisy_doses_mV"] = doses
    r["noise_run_offsets_mV"] = offsets
    if count >= 8:
        r["noise_within_run_mV"] = (squares / count) ** 0.5
    return r


def instance(I):
    """The constants of one instance from its entry of MEASURES.json."""
    ports = {name: port(name, scan, I["quiet_train"]["ports"][name], I["noisy_trains"]) for name, scan in I["scans"].items()}
    deviations = [x - p["dose_mV"] for p in ports.values() for x in p["noisy_doses_mV"]]
    offsets = [x for p in ports.values() for x in p["noise_run_offsets_mV"]]
    out = dict(section=I["section"], seed=I["seed"], ports=ports,
               protected_until_units=max(p["protected_until_units"] for p in ports.values()),
               noisy_trains=len(I["noisy_trains"]), run_offsets=len(offsets),
               dose_noise_sd_mV=statistics.mean(x * x for x in deviations) ** 0.5, noisy_doses=len(deviations))
    if len(offsets) >= 8:
        out["noise_between_runs_mV"] = statistics.mean(x * x for x in offsets) ** 0.5
    return out


def main():
    M = json.loads(Path(sys.argv[1]).read_text())
    out = {seed: instance(I) for seed, I in M["instances"].items()}
    Path(sys.argv[2]).write_text(json.dumps(dict(what="constants of the guarded model per instance; see constants.py", help_22_nominal_mV=HELP_22_NOMINAL,
                                                 instances=out), indent=1) + "\n")


if __name__ == "__main__":
    main()
