"""Reads the complement (complement.py) against the campaign. Writes COMPLEMENT.md.

1. The nominal run, run again without the option rel: identical to the campaign or not.
2. The runs replayed with the same seeds: does the seed of a run reproduce it?
3. Prediction P2 on the replays, where a latency is printed from the start of its pulse.
   The verdict of the campaign stays in VERDICTS.md; this one is shown next to it.
"""
import csv, math, os, shutil, statistics, sys, tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import analyze
from complement import AGAIN, REPEATED

TU, TPER, T0 = 20e-6, 440e-6, 4.1e-6
DASH = "—"


def rows(path):
    if not os.path.exists(path):
        return None
    with open(path, newline="") as fh:
        return list(csv.DictReader(fh))


def expected_largest(pairs, n):
    """Largest correlation expected among `pairs` independent pairs of n values (Fisher transform, extreme of a normal sample)."""
    u = math.sqrt(2 * math.log(pairs))
    return math.tanh((u - (math.log(math.log(pairs)) + math.log(4 * math.pi)) / (2 * u)) / math.sqrt(n - 3))


def verdicts_with(folder, names):
    """The verdicts of the analysis when the runs `names` are taken from `folder` and all the others from the campaign."""
    with tempfile.TemporaryDirectory() as tmp:
        for f in os.listdir("results"):
            if f.endswith(".csv"):
                shutil.copy(f"results/{f}", tmp)
        for n in names:
            if os.path.exists(f"{tmp}/{n}.csv"):
                os.remove(f"{tmp}/{n}.csv")
            if os.path.exists(f"{folder}/{n}.csv"):
                shutil.copy(f"{folder}/{n}.csv", tmp)
        c, R, S, X = analyze.analyse(tmp)
    return {v["id"]: v for v in R.v}, S


def main(out="COMPLEMENT.md"):
    L = ["# Complement to the campaign", "",
         "Run after the campaign by `complement.py` and read by `compare.py`. Nothing here is a prediction, and nothing here replaces a verdict.", ""]

    # 1. the option rel changes nothing when it is off
    L += ["## The runner without the new option", ""]
    L.append("The option `rel` was added to `run.py` after the campaign. Runs without noise are run again without it. "
             "They must give the result of the campaign exactly: if they did not, something else than the noise would vary from one run to the next.")
    L.append("")
    checks = sorted(f[:-4] for f in os.listdir("results_check") if f.endswith(".csv")) if os.path.isdir("results_check") else []
    if not checks:
        L.append("Not evaluable: no run was run again.")
    for n in checks:
        if not os.path.exists(f"results/{n}.csv"):
            L.append(f"- `{n}`: not evaluable, no result in the campaign.")
            continue
        same = open(f"results/{n}.csv", "rb").read() == open(f"results_check/{n}.csv", "rb").read()
        L.append(f"- `{n}`: " + ("identical byte for byte to the result of the campaign." if same else "DIFFERS from the result of the campaign."))
    L.append("")

    # 2. the replays: does the seed of a run reproduce it?
    L += ["## Runs replayed with the same seeds", "",
          "Same netlist, same options, same seeds. The only change is that each time is printed from the start of its pulse.", ""]
    n_runs = n_pulses = same_v = 0
    reproduced = False
    bad_fire, missing, dv, dlat = [], [], [], []
    joint, swing = {}, {}
    for name in AGAIN:
        c, r = rows(f"results/{name}.csv"), rows(f"results_rel/{name}.csv")
        if c is None or r is None or len(c) != len(r):
            missing.append(name)
            continue
        n_runs += 1
        for x, y in zip(c, r):
            n_pulses += 1
            k = int(x["pulse"])
            if x["fired"] != y["fired"]:
                bad_fire.append(f"{name} pulse {k}")
            elif x["fired"] == "1":
                dlat.append(abs(float(x["fire_latency"]) - float(y["fire_latency"])))
            same_v += x["vmem1"] == y["vmem1"] and x["vmem2"] == y["vmem2"]
            dv += [1e3 * (float(x["vmem1"]) - float(y["vmem1"])), 1e3 * (float(x["vmem2"]) - float(y["vmem2"]))]
            if x["port"] == "0" and name.startswith("nz_"):
                joint[name] = (float(x["fire_latency"]) if x["fired"] == "1" else None, float(y["fire_latency"]) if y["fired"] == "1" else None)
        if name.startswith("mc_"):          # the swing of the main capacitor at the first pulse of each port: the start gain of the port
            first = lambda rr, q: next((1.25 - float(x["vq_min"]) for x in rr if x["port"] == q), None)
            swing[name] = [(first(c, q), first(r, q)) for q in ("1", "2")]
    if missing:
        L.append(f"Not evaluable for {len(missing)} of {len(AGAIN)} runs, result missing or of another length: {', '.join(missing)}.")
        L.append("")
    if n_runs:
        rms = math.sqrt(sum(d * d for d in dv) / len(dv))
        L += [f"- Runs compared: {n_runs}, {n_pulses} pulses.",
              f"- FIRE or silence differs on {len(bad_fire)} of {n_pulses} pulses" + (": " + "; ".join(bad_fire[:8]) if bad_fire else "") + ".",
              f"- The two stored voltages are identical on {same_v} of {n_pulses} pulses. Their difference between the campaign and the replay has an rms of {rms:.3f} mV.",
              f"- FIRE latency, on the pulses that fire in both: largest difference {max(dlat):.4f} unit." if dlat else "- No pulse fires in both.", ""]
        reproduced = same_v == n_pulses and not bad_fire
        if reproduced:
            L += ["**The replays reproduce the campaign.**", ""]
        else:
            L += ["**The replays do not reproduce the campaign.** With the same seed a run draws another noise sample: "
                  "the stored voltages differ by an amount of the size of the read noise. The seed of a run does not set its noise.", ""]
        pairs = [p for v in swing.values() for p in v if None not in p]
        allc = []
        for path in sorted(os.listdir("results")) if os.path.isdir("results") else []:
            if path.startswith("mc_") and path.endswith(".csv"):
                rr = rows("results/" + path)
                allc += [1.25 - float(x["vq_min"]) for x in rr if x["pulse"] in ("0", "10")]
        if pairs and len(allc) > 2:
            L += [f"The mismatch sample is another matter. The swing of the main capacitor at the first pulse of a port measures the start gain of that port. "
                  f"Over the {len(pairs)} ports of the replayed mismatch runs it differs by at most {1e3 * max(abs(a - b) for a, b in pairs):.2f} mV between the campaign and the replay. "
                  f"Between the {len(allc)} ports of the campaign it has a sigma of {1e3 * statistics.stdev(allc):.2f} mV.", ""]
            alone = []
            for d in ("results", "results_rel"):
                for n in AGAIN:
                    rr = rows(f"{d}/{n}.csv") if n.startswith("nz_") else None
                    if rr:
                        alone += [1.25 - float(x["vq_min"]) for x in rr if x["pulse"] in ("0", "10")]
            if len(alone) > 2:
                L += [f"Noise alone moves this swing: over the noise runs without mismatch it has a sigma of {1e3 * statistics.stdev(alone):.2f} mV. "
                      "The mismatch sample of a run is therefore reproduced by its seed, within what the noise allows to see.", ""]
        L += ["The four mismatch runs of this list (cells 2061 to 2064) are those that were being computed when the campaign was stopped by a time "
              "limit and resumed. They had written nothing when they were stopped, so the campaign holds one result for each, and the stop "
              "itself gives nothing to compare.", ""]

    # 3. the noise series, sample by sample
    L += ["## The 20 noise runs, sample by sample", "",
          "In the campaign a joint read is printed to 0.0005 unit, 10 ns. In the replays it is printed to 0.00001 unit or better. "
          + ("The replays reproduce the campaign, so they are the same sample read more finely." if reproduced else
             "A replay draws another noise sample, so each set of replays is another sample of 20 runs, not the same sample read more finely."), "",
          "P1 to P5 are judged again on each sample, as written. The verdicts of the campaign are those of `VERDICTS.md`; the others are shown next to them.", ""]
    nz = [n for n in AGAIN if n.startswith("nz_")]
    samples = [("Campaign", "results")] + [(f"Replay {i}", d) for i, d in enumerate(("results_rel", "results_rel2", "results_rel3"), 1)
                                           if os.path.isdir(d) and all(os.path.exists(f"{d}/{n}.csv") for n in nz)]
    if not os.path.isdir("results"):
        L.append("Not evaluable: no result of the campaign.")
    else:
        L += ["| Sample | Sigma of the joint read | Range of the joint read | Sigma of a port at rest | P1 | P2 | P3 | P4 | P5 |", "|---|---|---|---|---|---|---|---|---|"]
        sig, fine, held = [], [], {p: 0 for p in ("P1", "P2", "P3", "P4", "P5")}
        for label, d in samples:
            v, S = verdicts_with(d, nz)
            z = S.get("noise", {})
            j = z.get("joint") or []
            sig.append(z.get("joint_sigma"))
            for p in held:
                held[p] += v[p]["status"] == analyze.HOLDS
            if d != "results":
                fine += j
            L.append(f"| {label} | {analyze.fm(z.get('joint_sigma'), '.5f')} | {analyze.span(j, '.5f')} | {analyze.fm(z.get('idle_sigma_mV'), '.3f')} mV | "
                     + " | ".join(v[p]["status"] for p in ("P1", "P2", "P3", "P4", "P5")) + " |")
        sig = [s for s in sig if s]
        L.append("")
        L.append(f"- Of {len(samples)} samples: " + ", ".join(f"{p} holds on {k}" for p, k in held.items()) + ".")
        if len(sig) >= 2:
            L.append(f"- Over the {len(sig)} samples the sigma of the joint read goes from {min(sig):.5f} to {max(sig):.5f}, a ratio of {max(sig) / min(sig):.1f}.")
            L.append(f"- If the joint reads followed a normal law, a sigma measured on 20 runs would be uncertain by about {100 / math.sqrt(38):.0f}%. "
                     f"Resampling the 20 runs of the campaign gives a wider interval: see the intervals in `VERDICTS.md`.")
        if len(fine) >= 3:
            L.append(f"- The {len(fine)} joint reads of the replays together: sigma {statistics.stdev(fine):.5f}, from {min(fine):.5f} to {max(fine):.5f}.")
    L.append("")

    # 3b. the two noisy refresh runs, repeated
    L += ["## The two noisy refresh runs, repeated", "",
          "The campaign has one run of each. They are run again four times each, with the same options. P14 and P17 are judged again on each run, as written.", ""]
    for name, pid, title in (("refresh_none_nz", "P14", "No leak, with noise, 150 pulses (P14: at most one relapse)"),
                             ("refresh_lk11_nz", "P17", "0.1 TΩ, with noise, 150 pulses (P17: relapses 17 to 28 periods apart, never two silent pulses in a row, band within 1.6 dose)")):
        L += [f"### {title}", "", f"| Sample | Relapses | Distances between relapses | Band in doses | {pid} |", "|---|---|---|---|---|"]
        gaps, bands, nrel = [], [], []
        for label, d in [("Campaign", "results")] + [(f"Repeat {i}", f"results_rep{i}") for i in range(1, 5)]:
            if not os.path.exists(f"{d}/{name}.csv"):
                L.append(f"| {label} | {DASH} | {DASH} | {DASH} | not evaluable: run missing |")
                continue
            v, S = verdicts_with(d, [name])
            r = S.get("refresh", {}).get(name[8:], {})
            gaps += r.get("gaps") or []
            nrel.append(len(r.get("relapses") or []))
            if r.get("band") is not None:
                bands.append(r["band"])
            L.append(f"| {label} | {len(r.get('relapses') or [])} | {', '.join(str(g) for g in r.get('gaps') or []) or DASH} | {analyze.fm(r.get('band'), '.2f')} | {v[pid]['status']} |")
        L.append("")
        if len(bands) >= 2:
            L.append(f"Over {len(bands)} runs: {min(nrel)} to {max(nrel)} relapses, band from {min(bands):.2f} to {max(bands):.2f} dose"
                     + (f", distances from {min(gaps)} to {max(gaps)} periods, mean {statistics.mean(gaps):.1f}." if gaps else "."))
            L.append("")

    # 3c. the charge really received by each integrator
    L += ["## The charge received by the integrator", "",
          "P10 checks the steering command. Here the current itself is measured: an ammeter of 0 V between the steering switch and the "
          "summing node of each integrator, integrated over each whole period (`gate_current.py`). "
          "A charge of 40.4 fC on the feedback capacitor of 30 pF is one dose, 1.3465 mV.", ""]
    gate = sorted(f[:-4] for f in os.listdir("results_gate") if f.endswith(".csv")) if os.path.isdir("results_gate") else []
    if not gate:
        L.append("Not evaluable: no run.")
    else:
        L += ["Charges in fC. For a pulse on both ports, both integrators are counted.", "",
              "| Run | Silent pulses | Charge on a silent pulse | Firing pulses | Charge on a firing pulse: mean | largest in size | Periods at rest | Charge at rest: mean |",
              "|---|---|---|---|---|---|---|---|"]
        worst, steps_f, steps_r = {False: [], True: []}, [], []
        for n in gate:
            rr = rows(f"results_gate/{n}.csv")
            sil, fir, rest = [], [], []
            noisy = n.startswith(("mc_", "nz_"))
            for x in rr:
                q, s = (None, float(x["charge1_fC"]), float(x["charge2_fC"])), (None, float(x["step1_mV"]), float(x["step2_mV"]))
                for port in (1, 2):
                    if x["port"] in (str(port), "0"):
                        (fir if x["fired"] == "1" else sil).append(q[port])
                        if x["fired"] == "1" and not noisy:
                            steps_f.append(s[port])
                    else:
                        rest.append(q[port])
                        if not noisy:
                            steps_r.append(s[port])
            worst[noisy] += [abs(q) for q in fir]
            m = lambda v, spec=".4f": format(statistics.mean(v), spec) if v else DASH
            L.append(f"| `{n}` | {len(sil)} | " + (f"{min(sil):.2f} to {max(sil):.2f}" if sil else DASH) + f" | {len(fir)} | {m(fir)} | "
                     + (f"{max(abs(q) for q in fir):.4f}" if fir else DASH) + f" | {len(rest)} | {m(rest)} |")
        L.append("")
        for noisy, label in ((False, "without noise"), (True, "with mismatch and noise")):
            if worst[noisy]:
                L.append(f"- Largest charge received by an integrator on a firing pulse, runs {label}: {max(worst[noisy]):.4f} fC, "
                         f"{100 * max(worst[noisy]) / 40.395:.2f}% of a dose, over {len(worst[noisy])} firing pulses.")
        L += [
              "- The current of the ammeter alternates in sign from one time point to the next, an effect of trapezoidal integration. "
              "It limits this measure: the same effect spreads the charge of a silent pulse around one dose, and more so with noise.",
              "- The stored voltage integrates the same current exactly. In these runs it is averaged from the time points, without the rounding "
              "to 1 µV of the campaign. The solver resolves a voltage to 0.1 µV."]
        if steps_f and steps_r:
            L.append(f"- In the runs without noise, the mean change of the stored voltage over a period, toward a higher gain, is "
                     f"{1e3 * statistics.mean(steps_f):+.2f} µV on a firing pulse and {1e3 * statistics.mean(steps_r):+.2f} µV for a port at rest. "
                     f"A dose is 1346.5 µV.")
    L.append("")

    # 4. are the noise samples of the campaign independent of each other?
    L += ["## Do two runs of the campaign share a noise sample?", "",
          "If two runs had the same noise sample, the changes of the stored voltage of their ports at rest would be the same. "
          "For every pair of noisy cell runs of the campaign, the correlation of these 20 changes is computed. "
          "This diagnostic can show a shared sample. It cannot prove that the samples are independent.", ""]
    idle = {}
    for path in sorted(os.listdir("results")) if os.path.isdir("results") else []:
        if path.startswith(("nz_", "mc_")) and path.endswith(".csv"):
            rr = rows("results/" + path)
            idle[path[:-4]] = [float(x["step2_mV"]) for x in rr if x["port"] == "1"] + [float(x["step1_mV"]) for x in rr if x["port"] == "2"]
    idle = {k: v for k, v in idle.items() if len(v) == 20 and statistics.pstdev(v) > 0}
    if len(idle) < 2:
        L.append("Not evaluable: fewer than two noisy cell runs.")
    else:
        names = sorted(idle)
        cs = [(statistics.correlation(idle[a], idle[b]), a, b) for i, a in enumerate(names) for b in names[i + 1:]]
        top = max(cs)
        L += [f"- {len(names)} runs, {len(cs)} pairs.",
              f"- Largest correlation: {top[0]:.2f}, between `{top[1]}` and `{top[2]}`. Pairs above 0.9: {sum(1 for x in cs if x[0] > 0.9)}.",
              f"- For independent samples of 20 values the largest of {len(cs)} correlations is expected near {expected_largest(len(cs), 20):.2f}.",
              "- No sign of a noise sample used twice in this diagnostic." if top[0] < 0.9 else "- A pair of runs is correlated as a shared noise sample would be."]
    L.append("")
    with open(out, "w") as fh:
        fh.write("\n".join(L))
    print("\n".join(L))


if __name__ == "__main__":
    main(*sys.argv[1:2])
