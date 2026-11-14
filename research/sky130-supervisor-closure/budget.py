"""What fits in four hours on two machines, from the wall times measured in the qualification. No simulation is run.

  budget.py          -> BUDGET.json
  budget.py --check  compares with the committed file instead of writing it

The times are those of the noisy confirmation sequences, four at a time on one cloud container of four
processors — the conditions of the registered campaign. A sequence simulates the slots before its
entry (two idle slots and the preparation), two slots per service and one last slot. Its whole wall
time is divided by that number of slots; the largest ratio is the cost of a slot, and the longest
preparation seen is charged to every run: estimate = cost of a slot x (longest preparation + 2 x
services + 1). The bound of the launch kit is, for each machine,
sum(timeout + 10 s) / jobs + max(timeout + 10 s).
"""
import json
import math
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
BUDGET_S = 14400
JOBS = 4
RESERVE = 1.5                    # time limit of a run = RESERVE x its estimate
CLEANUP_S = 10


def table(q):
    noisy = [s for s in q["confirmation"].values() if s["noise"]]
    assert noisy, "no noisy confirmation sequence"
    slots = lambda s: s["entered_at_slot"] + 2 * s["services"] + 1
    per_slot = max(s["wall_s"] / slots(s) for s in noisy)
    preparation = max(s["entered_at_slot"] for s in noisy)
    rows = []
    for services in (12, 18, 24, 36):
        estimate = math.ceil(per_slot * (preparation + 2 * services + 1))
        timeout = math.ceil(RESERVE * estimate)
        n = 0                                        # runs per machine: the largest number whose bound fits half the budget
        while ((n + 1) * (timeout + CLEANUP_S)) / JOBS + (timeout + CLEANUP_S) <= BUDGET_S / 2:
            n += 1
        rows.append(dict(services_per_run=services, estimate_s=estimate, timeout_s=timeout, runs_per_machine=n, runs=2 * n, services=2 * n * services,
                         bound_per_machine_s=n * (timeout + CLEANUP_S) / JOBS + (timeout + CLEANUP_S), expected_wall_per_machine_s=n * estimate / JOBS))
    quiet = [s for s in q["confirmation"].values() if not s["noise"]]
    mean = lambda rows: sum(s["wall_s"] / slots(s) for s in rows) / len(rows)
    return dict(budget_s=BUDGET_S, machines=2, jobs=JOBS, reserve_factor=RESERVE, cleanup_allowance_s=CLEANUP_S,
                measured_on=dict(sequences=len(noisy), services_each=sorted({s["services"] for s in noisy}),
                                 wall_s=[min(s["wall_s"] for s in noisy), max(s["wall_s"] for s in noisy)]),
                seconds_per_slot=per_slot, longest_preparation_slots=preparation, mean_seconds_per_slot=mean(noisy),
                quiet_mean_seconds_per_slot=mean(quiet), noise_timing_factor=mean(noisy) / mean(quiet),
                packings=rows)


def main():
    result = table(json.loads((HERE / "QUALIFICATION.json").read_text()))
    target = HERE / "BUDGET.json"
    if "--check" in sys.argv:
        assert json.loads(target.read_text()) == result
        print("PASS: the committed budget recomputed")
    else:
        target.write_text(json.dumps(result, indent=1) + "\n")
    print(json.dumps(result, indent=1))


if __name__ == "__main__":
    main()
