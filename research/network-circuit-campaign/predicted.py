"""From the collected evidence of the measures to PREDICTED.json: which instances are measured, their constants,
the two budgets, which instances are eligible, the zero-error words, the control instance and the network runs.

  predicted.py OUT_DIR EVIDENCE...

EVIDENCE are the folders written by `launch.py collect` for the measures of the two machines (their small files,
as committed, are enough: no waveform is read). Written in OUT_DIR, all without a date so that anyone gets the
same bytes: MEASURES.json, CONSTANTS.json, PREDICTED.json and Predicted.lean, which restates the margins for the
Lean kernel (`check.sh`). PREDICTED.json is the protocol of the network runs: it is committed and pushed before
any of them, and the launcher is bound to its SHA-256.

Everything is decided by PREDICTION.md; the scripts of ../network-circuit/phase1 do the arithmetic.
"""
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
NET = HERE.parent / "network-circuit"
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(NET / "phase1"))
import calendars
import collect
import constants
import model
import plan
import predict

K = 3.0
ALLOWANCE_MV = 0.030            # for the simulator itself, on each side of the noise-free budget
HELP_22_MV = constants.HELP_22_NOMINAL


def gather(folders, runs):
    """The measure runs found in the evidence: {run id: (status, folder of its evidence or None)}. A run counts when
    the launcher recorded it complete and its own record says that it reached its last date."""
    found = {}
    for folder in map(Path, folders):
        state = json.loads((folder / "STATE.json").read_text())
        for record in state["records"]:
            status = record["status"]
            evidence = folder / record["id"] / "evidence"
            if status == "complete":
                own = json.loads((evidence / "record.json").read_text())
                if not own["reached_its_last_date"]:
                    status = "complete for the launcher, but its record says that it did not reach its last date"
            assert record["id"] not in found, "a run in two evidence folders: " + record["id"]
            found[record["id"]] = (status, evidence)
    return {r["id"]: found.get(r["id"], ("never started", None)) for r in runs}


def measures(found, runs, section):
    """MEASURES.json in the format of ../network-circuit/phase1/collect.py, for the instances whose runs all count."""
    out, missing = {}, {}
    for seed in sorted({r["seed"] for r in runs}, key=str):
        mine = [r for r in runs if r["seed"] == seed]
        bad = {r["id"]: found[r["id"]][0] for r in mine if found[r["id"]][0] != "complete"}
        if bad:
            missing[str(seed)] = bad
            continue
        read = lambda r: json.loads((found[r["id"]][1] / "result.json").read_text())

        def train(r):
            x = read(r)
            assert x["deck"] == dict(section=section, noise=bool(r["noise"])) and not x["calendar"]["edges"] and not x["still_queued_at_the_horizon"]
            assert all(o["delivered"] for o in x["occurrences"])
            return dict(run=r["id"], ports={name: [collect.pulse(o, name[1]) for o in x["occurrences"] if f"{o['cell']}{o['port']}" == name] for name in plan.PORTS},
                        calendar=x["calendar"]["name"], fires=len(x["fires"]), wall_s=x["wall_s"], simulated_s=x["calendar"]["horizon"] * 20e-6,
                        deck_sha256=x["deck_sha256"], raw_sha256=x["raw_sha256"])

        scans = {}
        for r in mine:
            if r["kind"] == "scan":
                x = read(r)
                assert (x["section"], x["cell"] + str(x["port"])) == (section, r["port"])
                scans[r["port"]] = dict(pulses=[collect.pulse(o, r["port"][1]) for o in x["pulses"]], other_cell=x["idle"], wall_s=x["wall_s"],
                                        deck_sha256=x["deck_sha256"], raw_sha256=x["raw_sha256"])
        quiet = [train(r) for r in mine if r["kind"] == "train" and not r["noise"]]
        assert len(quiet) == 1 and sorted(scans) == plan.PORTS
        out[str(seed)] = dict(section=section, seed=seed, scans={p: scans[p] for p in plan.PORTS}, quiet_train=quiet[0],
                              noisy_trains=[train(r) for r in mine if r["kind"] == "train" and r["noise"]])
    return out, missing


def predictions(M, missing, seeds):
    """Constants and predictions of every instance, and the plan of the network runs. `seeds` gives the order."""
    C, instances, seeds = {}, {}, [str(s) for s in seeds]
    quiet_calendar = calendars.reciprocal(18)
    assert calendars.holds_by_construction(quiet_calendar) and calendars.counts(quiet_calendar) == (8, 10, 8, 10)
    for seed in seeds:
        if seed in missing:
            instances[seed] = dict(measured=False, why=dict(missing_runs=missing[seed]))
            continue
        try:
            C[seed] = constants.instance(M[seed])
        except Exception as error:                      # the measures do not give the constants of the four ports
            instances[seed] = dict(measured=False, why=dict(constants=type(error).__name__ + ": " + str(error)[:300]))
            continue
        without = predict.predict(C[seed], 0.0, HELP_22_MV, quiet_calendar, allowance=ALLOWANCE_MV)
        noisy = predict.predict(C[seed], K, HELP_22_MV, quiet_calendar)
        instances[seed] = dict(measured=True, eligible=without["all_reads_have_room"],
                               zero_error_words={p: without["ports"][p]["zero_error_word"] for p in model.PORTS},
                               writes={p: without["nominal_writes"][p] for p in model.PORTS},
                               least_margin_of_a_last_silence_mV=min(C[seed]["ports"][p]["room_last_silence_mV"] for p in model.PORTS),
                               doses_mV={p: C[seed]["ports"][p]["dose_mV"] for p in model.PORTS},
                               noise_free=without, noisy_k3=noisy, full_room_at_k3=bool(noisy.get("all_reads_have_room")))
    measured = [s for s in seeds if instances[s]["measured"]]
    eligible = [s for s in measured if instances[s]["eligible"]]
    control = min(eligible, key=lambda s: (instances[s]["least_margin_of_a_last_silence_mV"], seeds.index(s))) if eligible else None
    return C, instances, measured, eligible, control


def build(out, folders, which=None, section=None, runs=None, network=None):
    """The whole step. The defaults are the campaign; the rehearsal gives its own instance, section and runs."""
    which = plan.instances() if which is None else which
    section = plan.SECTION if section is None else section
    runs = plan.measure_runs(which) if runs is None else runs
    M, missing = measures(gather(folders, runs), runs, section)
    C, instances, measured, eligible, control = predictions(M, missing, [i["seed"] for i in which])
    seed_of = {str(i["seed"]): i["seed"] for i in which}
    planned = (plan.network_runs if network is None else network)([seed_of[s] for s in measured], None if control is None else seed_of[control], which)
    write(Path(out), M, C, instances, measured, eligible, control, planned, {str(i["seed"]): i["machine"] for i in which})


def main(argv):
    build(argv[1], argv[2:])


def write(out, M, C, instances, measured, eligible, control, network, machines):
    dump = lambda name, value: (out / name).write_text(json.dumps(value, indent=1, allow_nan=False) + "\n")
    dump("MEASURES.json", dict(what="per-port measures of the instances of the campaign; see predicted.py", instances=M))
    dump("CONSTANTS.json", dict(what="constants of the guarded model per measured instance; see predicted.py", help_22_nominal_mV=HELP_22_MV, instances=C))
    dump("PREDICTED.json", dict(
        what="predictions of the network campaign, written from the per-cell measures before any network run; see PREDICTION.md and predicted.py",
        k=K, allowance_for_the_simulator_mV=ALLOWANCE_MV, help_22_mV=HELP_22_MV, calendar=calendars.reciprocal(18)["name"], control_calendar=calendars.reciprocal(8)["name"],
        machine_of_each_instance=machines, measured_instances=measured, eligible_instances=eligible, control_instance=control,
        instances=instances, network_runs=network))
    sets = [("k0", "Without noise, with the allowance for the simulator", {s: instances[s]["noise_free"] for s in measured}),
            ("k3", "With noise, K = 3", {s: instances[s]["noisy_k3"] for s in measured})]
    (out / "Predicted.lean").write_text(predict.lean(sets))


if __name__ == "__main__":
    main(sys.argv)
