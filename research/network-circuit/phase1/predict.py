"""From the constants of an instance to its predicted learned state. Phase 1, exploratory: no network has been run
on any of the instances.

  predict.py CONSTANTS.json PREDICTED.json Instances.lean [K]

For each instance and the calendar `calendars.reciprocal(18)`:

1. the calendar is checked to keep two pulses of one cell at least 16 units apart whatever the latencies;
2. each port gets its integers: gap, and the bounds [lo, hi] of its read error, in units of 1/100000 of its dose.
   The error budget, in mV, is
       hi = + (largest help measured at 16 or 18 units) + K x noise + (half bracket of the threshold)
       lo = - (help at 22 units, 0.015 mV)             - K x noise - (half bracket of the threshold)
   since the threshold was measured with reads 22 units after a pulse. `noise` adds in quadrature the noise of a
   read of the port and that of the doses written before it: sqrt(read^2 + need x dose^2);
3. the zero-error run of the model gives the word of each port (s: silent and one dose, F: FIRE), its writes, the
   FIRE of each cell and the pulses on each wire;
4. every read is checked for room. If all have room, the instance is covered by `circuit_predicted`: the run with
   errors is the zero-error run. If not, every read without room is taken both ways, and a port is
     - **predicted** when all its own reads have room and it receives the same pulses in every case: its word is known;
     - **learned state predicted** when all its own reads have room but the number of pulses it receives depends
       on a port without room: its writes are known, its number of FIRE is not;
     - **no prediction** when one of its own reads has no room.

`Instances.lean` restates step 4 for the Lean kernel: the margins hold, or they do not, and the writes of the
zero-error run.
"""
import json
import math
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import calendars
import model

D = model.D
CELL_OF = dict(a1="a", a2="a", b1="b", b2="b")


def noise(p, dose_sd):
    return math.sqrt(p["noise_sd_mV"] ** 2 + p["need"] * dose_sd ** 2)


def budget(p, k, help_22, dose_sd):
    """(lo, hi) of the read error of a port, in mV. None without the measures of both trains."""
    if "noise_sd_mV" not in p or "help_18_after_fire_mV" not in p or dose_sd is None:
        return None
    helps = [p["help_16_mV"], p["help_18_after_silent_mV"], p["help_18_after_fire_mV"]]
    spread = k * noise(p, dose_sd) + p["bracket_half_mV"]
    return -(help_22 + spread), max(0.0, *helps) + spread


def integers(ports, k, help_22, dose_sd):
    gap, lo, hi = {}, {}, {}
    for name, p in ports.items():
        b = budget(p, k, help_22, dose_sd)
        gap[name] = round(p["gap_doses"] * D)
        lo[name], hi[name] = math.floor(b[0] / p["dose_mV"] * D), math.ceil(b[1] / p["dose_mV"] * D)
    return gap, lo, hi


def predict(instance, k, help_22, calendar):
    ports, dose_sd = instance["ports"], instance.get("dose_noise_sd_mV")
    if any(budget(p, k, help_22, dose_sd) is None for p in ports.values()):
        return dict(k=k, verdict="no prediction: a port lacks the measures of a train")
    counts = calendars.counts(calendar)
    pending, n = model.seed(*counts), model.steps(*counts)
    gap, lo, hi = integers(ports, k, help_22, dose_sd)
    cases = model.outcomes(gap, lo, hi, pending, n)
    nominal, writes, left = model.run(gap, pending, n)
    assert not left and (tuple(writes[p] for p in model.PORTS), tuple(model.word(nominal, p).count("F") for p in model.PORTS)) in cases
    dated_words, dated_writes = model.dated_run(gap, calendar)          # the order of the dates gives the same run, port by port
    assert dated_writes == writes and all(dated_words[p] == model.word(nominal, p) for p in model.PORTS)
    out = dict(k=k, calendar=calendar["name"], counts=dict(zip(("a0", "a1", "b0", "b1"), counts)), steps=n,
               separation_units=calendars.separation(calendar), hypotheses_hold_by_construction=calendars.holds_by_construction(calendar),
               gap=gap, lo=lo, hi=hi, all_reads_have_room=len(cases) == 1, terminal_states=len(cases), ports={})
    for i, name in enumerate(model.PORTS):
        mine = [(score, fire) for _, _, port, score, fire in nominal if port == name]
        rooms = [model.room(score, lo[name], hi[name]) for score, _ in mine]
        own = all(model.has_room(score, lo[name], hi[name]) for score, _ in mine)
        w, f = sorted({c[0][i] for c in cases}), sorted({c[1][i] for c in cases})
        pulses = sorted({c[0][i] + c[1][i] for c in cases})
        mv = ports[name]["dose_mV"] / D
        sd = noise(ports[name], dose_sd)
        out["ports"][name] = dict(
            verdict="no prediction" if not own else "predicted" if len(pulses) == 1 else "learned state predicted",
            zero_error_word=model.word(nominal, name), writes=w, fires=f, pulses=pulses,
            budget_mV=[lo[name] * mv, hi[name] * mv], noise_sd_mV=sd,
            margin_of_the_last_silence_mV=min(-score for score, fire in mine if not fire) * mv,
            margin_of_the_first_fire_mV=min([score for score, fire in mine if fire], default=float("nan")) * mv,
            least_room_mV=min(rooms) * mv, least_room_in_noise_sd=min(rooms) * mv / sd + k)
    for cell in ("a", "b"):
        out[f"fires_of_{cell}"] = sorted({sum(c[1][i] for i, p in enumerate(model.PORTS) if CELL_OF[p] == cell) for c in cases})
    out["nominal_writes"] = writes
    return out


def lean(predictions, k):
    lines = ["import CircuitNetwork", "",
             f"/-! Written by `predict.py` from CONSTANTS.json with K = {k}. Not edited by hand.", "",
             "For each instance: the integers of the model, whether every read of the zero-error run has room for the",
             "error budget of its port, and the writes of that run. Ports in the order a1, a2, b1, b2. -/", "",
             "namespace NetworkStability.CircuitNetwork.Instances", "", "open AutonomousFeedback", ""]
    for seed, r in predictions.items():
        if "gap" not in r:
            continue
        c = r["counts"]
        cal = f"(start 4 (calendar {c['a0']} {c['a1']} {c['b0']} {c['b1']}))"
        for what in ("gap", "lo", "hi"):
            values = ", ".join(str(r[what][p]) for p in model.PORTS)
            lines += [f"def {what}{seed} : Fin 4 → Int := fun i => [{values}].getD i.val 0"]
        writes = ", ".join(str(r["nominal_writes"][p]) for p in model.PORTS)
        claim = f"PortMargins (circuit gap{seed}) {D} lo{seed} hi{seed} {r['steps']} {cal}"
        lines += ["", f"example : {claim if r['all_reads_have_room'] else '¬ ' + claim} := by decide +kernel", "",
                  f"example : ∀ i : Fin 4, (run (circuit gap{seed}) {D} (fun _ => 0) {r['steps']} {cal}).writes i =",
                  f"    [{writes}].getD i.val 0 := by decide +kernel", ""]
    return "\n".join(lines + ["end NetworkStability.CircuitNetwork.Instances", ""])


def main():
    C = json.loads(Path(sys.argv[1]).read_text())
    k = float(sys.argv[4]) if len(sys.argv) > 4 else 3.0
    calendar = calendars.reciprocal(18)
    out = {seed: predict(I, k, C["help_22_nominal_mV"], calendar) for seed, I in C["instances"].items()}
    sweep = {seed: {str(kk): {name: p["verdict"] for name, p in predict(I, kk, C["help_22_nominal_mV"], calendar).get("ports", {}).items()}
                    for kk in (2.0, 3.0, 4.0)} for seed, I in C["instances"].items()}
    Path(sys.argv[2]).write_text(json.dumps(dict(what="predicted learned state per instance; see predict.py. No network run exists for these instances.",
                                                 k=k, instances=out, verdicts_by_k=sweep), indent=1) + "\n")
    Path(sys.argv[3]).write_text(lean(out, k))


if __name__ == "__main__":
    main()
