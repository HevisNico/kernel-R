"""What fits in 4 h on two machines at N = 3: the cost of the campaign from the wall times of the rehearsal.
Phase 0, design only.

  cost.py REHEARSAL.json > COST.json

**The plan that is sized.** Six instances of the ring of 3 cells, three per machine. Per instance: one scan per
port (4), one train without noise, then either three noisy trains (noise measured on the instance) or none (noise
constants fixed beforehand); one run without noise; `R` noisy runs. One control run, on one machine.

**The model of the wall time.** With four simulations at a time on a machine, a run of the bench costs

    wall = cells x (A x simulated ms + B x pulses) x (NOISE if the run has noise)

`A` and `B` are fitted on two rehearsal runs of the ring that have the same pulses and different lengths (the run
inside the timing condition and the first control); `NOISE` is the ratio of the noisy run to the quiet one. The
other rehearsal runs are not used for the fit: `model_against_the_rehearsal` says how far the model is from each.
A scan costs what the rehearsal measured.

**The laps.** A run without noise has `sum of the predicted needs + 10` laps: ten laps after the predicted freeze.
A noisy run has that, or `sum + SHORT_TAIL` laps when it is shortened. The expected case takes the needs of
campaign 1 (20 ports: 3 to 6 doses, 4.3 on average); the limits are computed for `CAP` doses per port on average
(20 for the four ports; campaign 1 had at most 19).

**Two ways of counting 4 h.**
  - `kit_budget_s`: as campaign 1 counted. Each run has a limit of `MARGIN` times its wall time at the cap, rounded
    up to 10 s; a stage on a machine costs the sum of (limit + 10 s) divided by four, plus the largest
    (limit + 10 s); the two stages on the two machines must add up to at most 14 400 s. This is what the campaign
    costs if every run takes its whole limit. Campaign 1 was sized at 13 862 s this way and used 109 minutes.
  - `expected_machine_s`: the expected wall time of the two machines. A stage on a machine is taken as the sum of
    the expected times divided by four, plus three quarters of the largest (the bound of a greedy schedule on four
    processors). The same formula gives 128 minutes for campaign 1, which used 109.

**The rates** are those of campaign 1, on its 20 measured ports: 23 of 24 scans gave a threshold; 19 of 20 ports had
room for the noise-free budget; 16 of 20 had their noise measures, and 10 of these 16 had room for the budget at
K = 3; with the fixed noise constants of `FIXED_NOISE_MV`, 10 of the 20 would have had room at K = 3.
"""
import json
import math
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import ring

N = 3
INSTANCES = (3, 3)              # per machine
MARGIN = 1.3
JOBS = 4
BUDGET_S = 14400
MEAN_NEED, CAP = 4.3, 5
TRAIN_READS = 10
NOISY_TRAINS = 3
SHORT_TAIL = 3
SCAN_OK, QUIET_ROOM = 23 / 24, 19 / 20
NOISE_MEASURED, K3_ROOM_MEASURED, K3_ROOM_FIXED = 16 / 20, 10 / 16, 10 / 20
FIXED_NOISE_MV = dict(between_runs=0.090, within_run=0.064, dose=0.009)


def fit(R):
    a, b = R["runs"]["ring-3-quiet"], R["runs"]["ring-3-control-10-units"]
    pa, pb = sum(map(len, a["words"].values())), sum(map(len, b["words"].values()))
    assert pa == pb and a["n"] == b["n"] == N
    A = (a["wall_s"] - b["wall_s"]) / (N * (a["simulated_ms"] - b["simulated_ms"]))
    B = (a["wall_s"] / N - A * a["simulated_ms"]) / pa
    return dict(A_s_per_cell_ms=A, B_s_per_cell_pulse=B, noise=R["runs"]["ring-3-noise"]["wall_s"] / a["wall_s"],
                scan_s=R["runs"]["scan-3-a1"]["total_wall_s"])


def wall(F, ms, pulses, noise=False):
    return N * (F["A_s_per_cell_ms"] * ms + F["B_s_per_cell_pulse"] * pulses) * (F["noise"] if noise else 1)


def ring_run(F, need, tail=10, noise=False, control=False):
    """Expected wall time of a run of the ring whose ports need `need` doses on average (a real number)."""
    laps = math.ceil(need * (N + 1)) + tail
    pulses = (N + 1) * laps - need * N * (N + 1) / 2
    calendar = ring.control(N, laps) if control else ring.ring(N, laps)
    return wall(F, calendar["horizon"] * 0.02, pulses, noise)


def train(F, noise=False):
    calendar = ring.train(N, TRAIN_READS)
    return wall(F, calendar["horizon"] * 0.02, len(calendar["sources"]), noise)


def limit(seconds):
    return 10 * math.ceil(MARGIN * seconds / 10)


def kit(limits):
    return sum(x + 10 for x in limits) / JOBS + max(x + 10 for x in limits)


def greedy(times):
    return sum(times) / JOBS + (1 - 1 / JOBS) * max(times)


def kinds(F):
    """Each kind of run: expected wall time, wall time at the cap, limit."""
    out = dict(scan=(F["scan_s"], F["scan_s"]), quiet_train=(train(F), train(F)), noisy_train=(train(F, True), train(F, True)),
               quiet_run=(ring_run(F, MEAN_NEED), ring_run(F, CAP)), control_run=(ring_run(F, MEAN_NEED, control=True), ring_run(F, CAP, control=True)),
               noisy_run=(ring_run(F, MEAN_NEED, noise=True), ring_run(F, CAP, noise=True)),
               short_noisy_run=(ring_run(F, MEAN_NEED, SHORT_TAIL, True), ring_run(F, CAP, SHORT_TAIL, True)))
    return {k: dict(expected_s=round(e), at_the_cap_s=round(c), limit_s=limit(c)) for k, (e, c) in out.items()}


def option(K, name, noise_measures, noisy_runs, short):
    """`noise_measures` is "instance" (three noisy trains per instance) or "fixed" (none). `noisy_runs` per instance."""
    noisy = "short_noisy_run" if short else "noisy_run"
    kit_total = expected_total = 0.0
    stages = []
    for m, count in enumerate(INSTANCES):
        measures = (["scan"] * (N + 1) + ["quiet_train"] + ["noisy_train"] * (NOISY_TRAINS if noise_measures == "instance" else 0)) * count
        runs = ["quiet_run"] * count + ["control_run"] * (m == 0) + [noisy] * (noisy_runs * count)
        for stage in (measures, runs):
            k, e = kit([K[x]["limit_s"] for x in stage]), greedy([K[x]["expected_s"] for x in stage])
            stages.append(dict(machine="ab"[m], runs=len(stage), kit_budget_s=round(k), expected_machine_s=round(e)))
            kit_total, expected_total = kit_total + k, expected_total + e
    instances = sum(INSTANCES)
    measured = instances * SCAN_OK ** (N + 1)
    eligible = instances * (SCAN_OK * QUIET_ROOM) ** (N + 1)
    with_budget, room = (measured * NOISE_MEASURED, K3_ROOM_MEASURED) if noise_measures == "instance" else (measured, K3_ROOM_FIXED)
    own, upto = with_budget * (N + 1) * room, with_budget * sum(room ** (k + 1) for k in range(N + 1))
    return dict(option=name, noise_measures=noise_measures, noisy_runs_per_instance=noisy_runs,
                laps_after_the_freeze_in_noisy_runs=(SHORT_TAIL if short else 10) if noisy_runs else None, stages=stages,
                kit_budget_s=round(kit_total), within_4h_by_the_kit_budget=kit_total <= BUDGET_S,
                expected_machine_s=round(expected_total), expected_machine_min=round(expected_total / 60), within_4h_expected=expected_total <= BUDGET_S,
                network_stage_kit_budget_s=sum(s["kit_budget_s"] for s in stages[1::2]),
                expected_measured_instances=round(measured, 2), expected_eligible_instances=round(eligible, 2),
                expected_noisy_runs=round(measured * noisy_runs, 1),
                expected_ports_with_own_room=round(own, 1), expected_ports_with_room_up_to_them=round(upto, 1),
                expected_port_runs_own_room=round(own * noisy_runs, 1), expected_port_runs_room_up_to_them=round(upto * noisy_runs, 1))


def options(K):
    out, k = [], 0
    for noise_measures in ("instance", "fixed"):
        for noisy_runs, short in ((0, False), (1, True), (1, False), (2, True), (2, False), (3, True), (3, False), (4, True)):
            k += 1
            out.append(option(K, f"{'I' if noise_measures == 'instance' else 'F'}{noisy_runs}{'s' if short and noisy_runs else ''}", noise_measures, noisy_runs, short))
    return out


def against(F, R):
    out = {}
    for name, r in R["runs"].items():
        if name.startswith("ring-3"):
            pulses = sum(map(len, r["words"].values()))
            out[name] = dict(measured_s=round(r["wall_s"]), model_s=round(wall(F, r["simulated_ms"], pulses, r["noise"])), pulses=pulses)
        elif name.startswith("train-3"):
            out[name] = dict(measured_s=round(r["total_wall_s"]), model_s=round(train(F, name.endswith("noise"))))
    return out


def campaign_1():
    """The second way of counting, applied to campaign 1 with its own wall times (REPORT of campaign 1: scans 143 to
    243 s, quiet trains 307 to 347, noisy trains 394 to 470, quiet runs 401 to 482, control 368, noisy runs 497 to 646)."""
    mid = lambda a, b: (a + b) / 2
    measures = [mid(143, 243)] * 12 + [mid(307, 347)] * 3 + [mid(394, 470)] * 9
    runs = [mid(401, 482)] * 3 + [mid(497, 646)] * 6
    return dict(formula_min=round((2 * greedy(measures) + greedy(runs + [368]) + greedy(runs)) / 60), used_min=109, kit_budget_s=13862)


def build(R):
    F = fit(R)
    K = kinds(F)
    return dict(what="cost of campaign 2 at N = 3 from the rehearsal; see cost.py", n=N, instances_per_machine=list(INSTANCES), margin=MARGIN, jobs=JOBS,
                budget_s=BUDGET_S, mean_need=MEAN_NEED, cap_need=CAP, laps=dict(expected=math.ceil(MEAN_NEED * (N + 1)) + 10, cap=CAP * (N + 1) + 10, period_units=ring.period(N)),
                rates=dict(scan_ok=SCAN_OK, quiet_room=QUIET_ROOM, noise_measured=NOISE_MEASURED, k3_room_measured=K3_ROOM_MEASURED, k3_room_fixed=K3_ROOM_FIXED),
                fixed_noise_mV=FIXED_NOISE_MV, fit=F, model_against_the_rehearsal=against(F, R), runs=K, campaign_1_by_the_second_count=campaign_1(), options=options(K))


if __name__ == "__main__":
    print(json.dumps(build(json.loads(Path(sys.argv[1]).read_text())), indent=1))
