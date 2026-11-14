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
  noise         standard deviation of a read, as an equivalent `u`: scatter of the FIRE latency in the noisy train
                at one stored state, divided by the slope there

Per instance, `dose_noise_sd_mV`: root mean square of (dose in the noisy train - dose of the port without noise),
over the silent reads of its four ports.
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


def port(scan, trains):
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
    quiet = trains.get("quiet")
    if quiet:
        T = quiet
        word = "".join("F" if p["fire"] else "s" for p in T)
        first = next((i for i, p in enumerate(T) if p["fire"]), None)
        r["train_18_quiet"] = dict(word=word, writes=word.count("s"))
        if first is not None and first + 1 < len(T) and all(p["fire"] for p in T[first:]):
            level = T[first]["u_before_mV"]
            here = secant(fired, level)
            base = reference["latency"] + (level - trained) * here       # isolated latency at this stored state
            later = [p["latency"] for p in T[first + 1:]]
            r["train_18_quiet"].update(state_mV=level, latency_first_fire=T[first]["latency"], latency_later=statistics.median(later),
                                       later_range=[min(later), max(later)])
            r["help_18_after_silent_mV"] = (base - T[first]["latency"]) / here
            r["help_18_after_fire_mV"] = (base - statistics.median(later)) / here
    noisy = trains.get("noise")
    if noisy:
        T = noisy
        word = "".join("F" if p["fire"] else "s" for p in T)
        steps = [p["step_mV"] for p in T if not p["fire"]]
        groups = {}
        for i, p in enumerate(T):
            if p["fire"]:
                groups.setdefault(word[:i].count("s"), []).append(p)
        writes, G = max(groups.items(), key=lambda kv: len(kv[1])) if groups else (None, [])
        r["train_18_noise"] = dict(word=word, writes=word.count("s"), doses_mV=steps)
        if len(G) >= 8:
            level = statistics.mean(p["u_before_mV"] for p in G)
            here = secant(fired, level)
            lat = [p["latency"] for p in G]
            r["train_18_noise"].update(fires_at_one_state=len(G), writes_at_that_state=writes, state_mV=level, slope_per_mV=here,
                                       latency_mean=statistics.mean(lat), latency_sd=statistics.stdev(lat),
                                       state_sd_mV=statistics.stdev(p["u_before_mV"] for p in G))
            r["noise_sd_mV"] = statistics.stdev(lat) / here
    return r


def main():
    M = json.loads(Path(sys.argv[1]).read_text())
    out = {}
    for seed, I in M["instances"].items():
        trains = I["trains"]
        ports = {name: port(scan, {mode: t["ports"][name] for mode, t in trains.items()}) for name, scan in I["scans"].items()}
        deviations = [x - p["dose_mV"] for p in ports.values() for x in p.get("train_18_noise", {}).get("doses_mV", [])]
        out[seed] = dict(section=I["section"], seed=I["seed"], ports=ports,
                         protected_until_units=max(p["protected_until_units"] for p in ports.values()))
        if deviations:                                    # one number per instance: a port has three to five noisy doses only
            out[seed].update(dose_noise_sd_mV=statistics.mean(x * x for x in deviations) ** 0.5, noisy_doses=len(deviations))
    Path(sys.argv[2]).write_text(json.dumps(dict(what="constants of the guarded model per instance; see constants.py", help_22_nominal_mV=HELP_22_NOMINAL,
                                                 instances=out), indent=1) + "\n")


if __name__ == "__main__":
    main()
