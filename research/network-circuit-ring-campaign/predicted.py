"""From the collected evidence of the measures to PREDICTED.json: which instances are measured, their constants,
the integers of the two budgets, the need of each port, which ports have own room and room up to them, which
instances are eligible, their laps and zero-error words, the control instance and the network runs.

  predicted.py OUT_DIR EVIDENCE...

EVIDENCE are the folders written by `launch.py collect` for the measures of the two machines (their small files,
as committed, are enough: no waveform is read). Written in OUT_DIR, all without a date so that anyone gets the
same bytes: MEASURES.json, PREDICTED.json and Predicted.lean, which restates, port by port, `Own` or its negation
for the Lean kernel (`check.sh`), with the writes of the zero-error run of the ring. PREDICTED.json is the protocol
of the network runs: committed and pushed before any of them, with the launcher bound to its SHA-256.

Everything is decided by PREDICTION.md; `constants.port` of ../network-circuit/phase1 does the measures.
"""
import json
import math
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
NET = HERE.parent / "network-circuit"
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent / "network-circuit-ring"))
sys.path.insert(0, str(NET / "phase1"))
import collect
import constants
import plan
import ring

D = 100000                                              # one dose, in units of the score
K = 3.0
ALLOWANCE_MV = 0.030                                    # for the simulator itself, on each side of the noise-free budget
HELP_22_MV = constants.HELP_22_NOMINAL                  # 0.015
FIXED_NOISE_MV = dict(between_runs=0.090, within_run=0.064, dose=0.009)
PORTS = plan.PORTS


def gather(folders, runs):
    """The runs found in the evidence: {run id: (status, folder of its evidence or None)}. A run counts when the
    launcher recorded it complete and its own record says that it reached its last date."""
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
    """MEASURES.json: per instance whose five runs all count, the pulses of the scan of each port and of its train."""
    out, missing = {}, {}
    for seed in sorted({r["seed"] for r in runs}, key=str):
        mine = [r for r in runs if r["seed"] == seed]
        bad = {r["id"]: found[r["id"]][0] for r in mine if found[r["id"]][0] != "complete"}
        if bad:
            missing[str(seed)] = bad
            continue
        read = lambda r: json.loads((found[r["id"]][1] / "result.json").read_text())
        scans, trains = {}, []
        for r in mine:
            x = read(r)
            if r["kind"] == "scan":
                assert (x["section"], x["cell"] + str(x["port"])) == (section, r["port"])
                scans[r["port"]] = dict(pulses=[collect.pulse(o, r["port"][1]) for o in x["pulses"]], other_cell=x["idle"], wall_s=x["wall_s"],
                                        deck_sha256=x["deck_sha256"], raw_sha256=x["raw_sha256"])
            else:
                assert x["deck"] == dict(section=section, noise=False) and not x["calendar"]["edges"] and not x["still_queued_at_the_horizon"]
                assert all(o["delivered"] for o in x["occurrences"])
                trains.append(dict(run=r["id"], ports={p: [collect.pulse(o, p[1]) for o in x["occurrences"] if f"{o['cell']}{o['port']}" == p] for p in PORTS},
                                   calendar=x["calendar"]["name"], fires=len(x["fires"]), wall_s=x["wall_s"], simulated_s=x["calendar"]["horizon"] * 20e-6,
                                   deck_sha256=x["deck_sha256"], raw_sha256=x["raw_sha256"]))
        assert len(trains) == 1 and sorted(scans) == sorted(PORTS)
        out[str(seed)] = dict(section=section, seed=seed, scans={p: scans[p] for p in PORTS}, quiet_train=trains[0])
    return out, missing


def need_of(gap):
    """The least n >= 0 with n x D >= gap."""
    return max(0, -(-gap // D))


def budget_mV(p, need, noisy):
    """(lo, hi) of the read error of a port, in mV: the noise-free budget, or the noisy budget at K = 3 with the
    fixed noise constants."""
    helps = max(0.0, p["help_16_mV"], p["help_18_after_silent_mV"], p["help_18_after_fire_mV"])
    if noisy:
        f = FIXED_NOISE_MV
        spread = K * math.sqrt(f["within_run"] ** 2 + f["between_runs"] ** 2 + need * f["dose"] ** 2) + p["bracket_half_mV"]
    else:
        spread = ALLOWANCE_MV + p["bracket_half_mV"]
    return -(HELP_22_MV + spread), helps + spread


def score(gap, w):
    return -gap + D * w


def own(gap, lo, hi, need):
    """`Own gap D lo hi k need` of RingNetwork.lean."""
    return all(score(gap, w) < 0 and score(gap, w) + hi < 0 for w in range(need)) and score(gap, need) >= 0 and score(gap, need) + lo >= 0


def least_room(gap, lo, hi, need):
    """The least distance, in units, from a decision change over the reads of `Own`: > 0 for a silent read, >= 0 for
    the FIRE."""
    return min([-(score(gap, w) + hi) for w in range(need)] + [score(gap, need) + lo])


def instance(C):
    """Integers, budgets, room and words of one measured instance, from the constants of its four ports."""
    gap = {p: round(C[p]["gap_doses"] * D) for p in PORTS}
    need = {p: need_of(gap[p]) for p in PORTS}
    out = dict(gap=gap, need=need, budgets={})
    for name, noisy in (("noise_free", False), ("noisy_k3", True)):
        lo, hi, mv = {}, {}, {}
        for p in PORTS:
            b = budget_mV(C[p], need[p], noisy)
            lo[p], hi[p] = math.floor(b[0] / C[p]["dose_mV"] * D), math.ceil(b[1] / C[p]["dose_mV"] * D)
            mv[p] = list(b)
        has = {p: own(gap[p], lo[p], hi[p], need[p]) for p in PORTS}
        upto = {p: all(has[q] for q in PORTS[:i + 1]) for i, p in enumerate(PORTS)}
        out["budgets"][name] = dict(lo=lo, hi=hi, budget_mV=mv, own_room=has, room_up_to_it=upto,
                                    least_room_mV={p: least_room(gap[p], lo[p], hi[p], need[p]) * C[p]["dose_mV"] / D for p in PORTS})
    needs = [need[p] for p in PORTS]
    L, L2 = plan.laps(needs)
    words = lambda n: dict(zip(PORTS, ring.zero_error(needs, n)["words"]))
    out.update(eligible=all(out["budgets"]["noise_free"]["own_room"].values()), laps=dict(quiet=L, noisy=L2),
               zero_error_words=dict(quiet=words(L), noisy=words(L2)), freeze_lap=ring.zero_error(needs, L)["freeze_lap"],
               writes={p: min(need[p], len(w)) for p, w in words(L).items()},
               margin_of_the_last_silence_mV={p: (gap[p] - (need[p] - 1) * D) * C[p]["dose_mV"] / D if need[p] >= 1 else None for p in PORTS},
               doses_mV={p: C[p]["dose_mV"] for p in PORTS})
    return out


def predictions(M, missing, seeds):
    """Constants and predictions of every instance. `seeds` gives the order."""
    instances, seeds = {}, [str(s) for s in seeds]
    for seed in seeds:
        if seed in missing:
            instances[seed] = dict(measured=False, why=dict(missing_runs=missing[seed]))
            continue
        try:
            C = {p: constants.port(p, M[seed]["scans"][p], M[seed]["quiet_train"]["ports"][p], []) for p in PORTS}
        except Exception as error:                      # the measures do not give the constants of the four ports
            instances[seed] = dict(measured=False, why=dict(constants=type(error).__name__ + ": " + str(error)[:300]))
            continue
        instances[seed] = dict(measured=True, constants=C, **instance(C))
    measured = [s for s in seeds if instances[s]["measured"]]
    eligible = [s for s in measured if instances[s]["eligible"]]
    candidates = [s for s in eligible if instances[s]["need"]["a2"] >= 1]
    control = min(candidates, key=lambda s: (instances[s]["margin_of_the_last_silence_mV"]["a2"], seeds.index(s))) if candidates else None
    return instances, measured, eligible, control


def lean(instances, measured):
    """Predicted.lean: per measured instance, its gaps, the writes of the zero-error queue run for its quiet laps, and
    per port and budget `Own` or its negation, checked by the kernel."""
    lines = ["import RingNetwork", "",
             "/-! Written by `predicted.py` from the measures of campaign 2. Not edited by hand.", "",
             "Per measured instance: the gap of each port in units of 1/100000 dose, the writes of the zero-error",
             "queue run of the ring for its laps without noise, and for each port and each budget whether `Own` holds",
             "for its need. Ports in the order a1, b1, c1, a2. -/", "",
             "namespace NetworkStability.RingNetwork.Predicted", "", "open AutonomousFeedback", "open NetworkStability.RingNetwork", ""]
    values = lambda d: ", ".join(str(d[p]) for p in PORTS)
    for seed in measured:
        I = instances[seed]
        L = I["laps"]["quiet"]
        lines += [f"/-! ## Instance {seed} -/", "",
                  f"def gap{seed} : Fin 4 → Int := fun i => [{values(I['gap'])}].getD i.val 0", "",
                  f"example : ∀ i : Fin 4, (run (ring 3 gap{seed}) {D} (fun _ => 0) ({L} * 4) (start 4 (launches 3 {L}))).writes i =",
                  f"    [{values(I['writes'])}].getD i.val 0 := by decide +kernel", ""]
        for name, suffix in (("noise_free", "k0"), ("noisy_k3", "k3")):
            B = I["budgets"][name]
            lines += [f"def lo{seed}{suffix} : Fin 4 → Int := fun i => [{values(B['lo'])}].getD i.val 0",
                      f"def hi{seed}{suffix} : Fin 4 → Int := fun i => [{values(B['hi'])}].getD i.val 0", ""]
            for k, p in enumerate(PORTS):
                claim = f"Own (N := 3) gap{seed} {D} lo{seed}{suffix} hi{seed}{suffix} {k} {I['need'][p]}"
                lines += [f"example : {claim if B['own_room'][p] else '¬ ' + claim} := by decide +kernel"]
            lines.append("")
    return "\n".join(lines + ["end NetworkStability.RingNetwork.Predicted", ""])


def build(out, folders, which=None, section=None, runs=None, network=None):
    """The whole step. The defaults are the campaign; the rehearsal gives its own instance, section and runs."""
    which = plan.instances() if which is None else which
    section = plan.SECTION if section is None else section
    runs = plan.measure_runs(which) if runs is None else runs
    M, missing = measures(gather(folders, runs), runs, section)
    instances, measured, eligible, control = predictions(M, missing, [i["seed"] for i in which])
    seed_of = {str(i["seed"]): i["seed"] for i in which}
    needs = {seed_of[s]: [instances[s]["need"][p] for p in PORTS] for s in measured}
    network, removed = (plan.network_runs if network is None else network)(needs, None if control is None else seed_of[control], which)
    write(Path(out), M, instances, measured, eligible, control, network, removed, {str(i["seed"]): i["machine"] for i in which})


def write(out, M, instances, measured, eligible, control, network, removed, machines):
    dump = lambda name, value: (out / name).write_text(json.dumps(value, indent=1, allow_nan=False) + "\n")
    dump("MEASURES.json", dict(what="per-port measures of the instances of campaign 2; see predicted.py", instances=M))
    dump("PREDICTED.json", dict(
        what="predictions of campaign 2, the periodic ring of three cells, written from the per-port measures before any network run; see PREDICTION.md and predicted.py",
        ports=PORTS, k=K, allowance_for_the_simulator_mV=ALLOWANCE_MV, help_22_mV=HELP_22_MV, fixed_noise_mV=FIXED_NOISE_MV, dose_units=D,
        calendar=ring.ring(plan.N, 1)["name"].split(",")[0], period_units=ring.period(plan.N), control_period_units=ring.control(plan.N, 1)["period"],
        machine_of_each_instance=machines, measured_instances=measured, eligible_instances=eligible, control_instance=control,
        instances=instances, network_runs=network, removed_for_the_budget=removed,
        kit_bound_s=dict(plan.caps(network), total=sum(plan.caps(network).values()))))
    (out / "Predicted.lean").write_text(lean(instances, measured))


def main(argv):
    build(argv[1], argv[2:])


if __name__ == "__main__":
    main(sys.argv)
