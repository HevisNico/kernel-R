"""The learned monotone DNF (A and B) or (C and D) on three circuit cells: its calendar, its routing, its predictor,
its timing checks and its cost. Phase 0, design only: nothing here has been run on a cell with mismatch.

Cells and ports (the cell of `../circuit/cell.spice` has two ports):

    cell a (layer 1)   port 1 = input A, port 2 = input B      learns A and B by joint training
    cell b (layer 1)   port 1 = input C, port 2 = input D      learns C and D by joint training
    cell c (layer 2)   port 1 = line from a, port 2 = line b    learns the OR, each line trained in isolation

External inputs are pulses of amplitude AMP_AND (0.49) on the ports of layer 1, every active input of a slot at the
same date. A FIRE of a or b rising within the decision window of a routed slot sends one pulse of amplitude AMP_OR
(1.0) to its port of c, WIRE units after the FIRE. A cell writes only when its slot enables it; otherwise its dose
current is off (the read-only gate of `gate.py`). Dates in time units of 20 us, as everywhere in the bench.
"""
import itertools
import math

INPUTS = dict(A=("a", 1), B=("a", 2), C=("b", 1), D=("b", 2))
LINES = {"a": ("c", 1), "b": ("c", 2)}
AMP_AND, AMP_OR = 0.49, 1.0
SLOT = 22                       # units between two slots: every read is an isolated read, as in the calibration
WINDOW = 1.1                    # a FIRE counts when it rises within one unit and 2 us of the start of its read
WIRE = 1.5                      # units from a FIRE of layer 1 to its pulse on cell c
LATENCY = (0.0, 1.06)           # FIRE latencies seen on the bench (campaigns 1 to 3, all reads)
SNAP = 0.02                     # a pulse starts at most 0.4 us after its nominal date
GATE_LEAD = 3                   # units before a slot at which the write gates of that slot are set, cells at rest
SEPARATION = 16                 # least distance between the starts of two pulses on one cell, in the hypotheses
SETTLE = 12                     # units simulated after the last slot
EXTRA = 3                       # presentations after the predicted stop, to see the stop hold


def truth(x):
    """(A and B) or (C and D) on a set of active inputs."""
    return ({"A", "B"} <= x) or ({"C", "D"} <= x)


def patterns():
    """The 16 test patterns, in binary order of DCBA."""
    return [frozenset(n for i, n in enumerate("ABCD") if m >> i & 1) for m in range(16)]


def calendar(need_a, need_b, need_c1, need_c2, control=None):
    """The slots of one network run. `need_*` are the predicted needs; each stage gives EXTRA presentations after the
    predicted stop. `control` is None (the campaign run), "untrained" (the 16 tests only, on the preset state) or
    "skew" (the campaign run, then the two training targets with their second input 2 units late).
    A slot: (date, stage, external inputs {name: offset}, cells that may write, routed?)."""
    out, t = [], 0
    if control != "untrained":
        for r in range(max(need_a, need_b) + EXTRA):                      # stage 1: layer 1, both cells in one slot
            out.append(dict(date=t, stage="layer 1", round=r + 1, inputs=dict(A=0, B=0, C=0, D=0), writes=("a", "b"), routed=False))
            t += SLOT
        for r in range(max(need_c1, need_c2) + EXTRA):                    # stage 2: the two lines of c, each alone
            for line, pair in (("a", ("A", "B")), ("b", ("C", "D"))):
                out.append(dict(date=t, stage="layer 2", round=r + 1, line=line, inputs={n: 0 for n in pair}, writes=("c",), routed=True))
                t += SLOT
    for x in patterns():                                                   # stage 3: the 16 tests, read-only
        out.append(dict(date=t, stage="test", pattern="".join(sorted(x)) or "-", inputs={n: 0 for n in sorted(x)}, writes=(), routed=True))
        t += SLOT
    if control == "skew":
        for pair in (("A", "B"), ("C", "D")):
            out.append(dict(date=t, stage="skew control", pattern="".join(pair), inputs={pair[0]: 0, pair[1]: 2}, writes=(), routed=True))
            t += SLOT
    return out


def pulses(slots):
    """Every pulse a calendar can produce, as (cell, port, earliest start, latest start, kind), whichever cells fire."""
    out = []
    for s in slots:
        for n, off in s["inputs"].items():
            c, p = INPUTS[n]
            out.append((c, p, s["date"] + off, s["date"] + off + SNAP, "input"))
        if s["routed"]:
            for src, (c, p) in LINES.items():
                if any(INPUTS[n][0] == src for n in s["inputs"]):
                    first = s["date"] + min(o for n, o in s["inputs"].items() if INPUTS[n][0] == src)
                    last = s["date"] + max(o for n, o in s["inputs"].items() if INPUTS[n][0] == src)
                    out.append((c, p, first + LATENCY[0] + WIRE, last + SNAP + LATENCY[1] + WIRE + SNAP, "line"))
    return out


def separation(slots):
    """Per cell, the least distance between the latest start of a pulse and the earliest start of the next pulse of
    the same cell in a later slot. Pulses of one slot on one cell are the joint read, at one date (or the skew)."""
    out = {}
    for cell in "abc":
        mine = sorted((lo, hi) for c, _, lo, hi, _ in pulses(slots) if c == cell)
        groups = []
        for lo, hi in mine:
            if groups and lo - groups[-1][1] < SEPARATION and lo - groups[-1][0] < SLOT / 2:
                groups[-1] = (groups[-1][0], max(groups[-1][1], hi))
            else:
                groups.append((lo, hi))
        out[cell] = min(b[0] - a[1] for a, b in zip(groups, groups[1:])) if len(groups) > 1 else math.inf
    return out


def settled(slots):
    """Every slot is over before the next one starts: the last pulse of a slot, plus its cycle of 6 units and a FIRE
    protection of at most 6.5 units, ends before the gates of the next slot are set."""
    worst = max(hi for c, p, lo, hi, kind in pulses(slots[:1]) + pulses(slots)) if slots else 0
    per_slot = max(max(hi for _, _, _, hi, _ in pulses([s])) - s["date"] for s in slots if s["inputs"])
    return per_slot + 6.5 < SLOT - GATE_LEAD, per_slot, worst


def zero_error(need_a, need_b, need_c1, need_c2, control=None):
    """The run of the guarded model with zero read error: per cell and port, its word in the run (s: a silent read and
    one dose, F: a FIRE, . : a read-only read), the outputs on each test pattern."""
    slots = calendar(need_a, need_b, need_c1, need_c2, control)
    writes = dict(a=0, b=0, c1=0, c2=0)
    need = dict(a=need_a, b=need_b, c1=need_c1, c2=need_c2)
    trained = control != "untrained"
    words = dict(a="", b="", c1="", c2="")
    tests = {}
    for s in slots:
        fire = {}
        for cell in "ab":
            if any(INPUTS[n][0] == cell for n in s["inputs"]):
                both = all(INPUTS[n][0] != cell or True for n in s["inputs"]) and sum(INPUTS[n][0] == cell for n in s["inputs"]) == 2
                coincident = both and len({o for n, o in s["inputs"].items() if INPUTS[n][0] == cell}) == 1
                f = coincident and writes[cell] >= need[cell]
                fire[cell] = f
                if s["stage"] == "layer 1":
                    words[cell] += "F" if f else "s"
                    if not f:
                        writes[cell] += 1
        if s["routed"]:
            arrived = [LINES[x][1] for x in "ab" if fire.get(x)]
            fc = any(writes[f"c{p}"] >= need[f"c{p}"] for p in arrived)
            if s["stage"] == "layer 2":
                p = LINES[s["line"]][1]
                if arrived:
                    words[f"c{p}"] += "F" if fc else "s"
                    if not fc:
                        writes[f"c{p}"] += 1
            else:
                tests[s["pattern"]] = dict(a=bool(fire.get("a")), b=bool(fire.get("b")), c=bool(fc and arrived))
    return dict(words=words, writes=writes, tests=tests, slots=len(slots), trained=trained)


def nominal():
    """The nominal predictor: every cell nominal, a need of 4 for each joint pair of layer 1 (amplitude 0.49) and for
    each line of c (amplitude 1), from the calibration of phase 0."""
    return zero_error(4, 4, 4, 4)


# The cost of a run: the model of phase 0 of the ring (`../network-circuit-ring/cost.py`), fitted on decks of three
# cells, four runs at a time: wall = 3 x (3.7746 s x simulated ms + 3.9820 s x pulses), x 1.3861 with noise. On the
# decks of one cell of this phase 0 it is about twice the measured wall (125 to 152 s against 258 s): a prudent bound.
A_MS, B_PULSE, NOISE = 3.7746, 3.9820, 1.3861


def cost(ms, n_pulses, noise=False, cells=3):
    return cells * (A_MS * ms + B_PULSE * n_pulses) * (NOISE if noise else 1.0)


def run_pulses(slots, need=(4, 4, 4, 4)):
    """Pulses delivered in a run with the zero-error decisions."""
    z = zero_error(*need)
    n = sum(len(s["inputs"]) for s in slots)
    n += sum(1 for s in slots if s["stage"] == "layer 2")                  # the isolated line arrives in each slot
    n += sum(t["a"] + t["b"] for t in z["tests"].values())
    return n


def calibration_cost(stages=7):
    """The calibration deck of an instance: at each stage, the empty read, port 1, port 2 and both, on the three cells
    at once (a and b at AMP_AND, c at AMP_OR), then a clock-only dose on both ports of each cell: 18 pulses."""
    ms = stages * 5 * SLOT * 0.02
    return cost(ms, 18 * stages)


def sizing(budget_s=14400, machines=2, jobs=4, measured=0.92):
    """Instances that fit in the expected machine time (the count of campaigns 2 and 3: per stage and machine, the sum
    of the expected times / jobs + 3/4 of the largest), for 0 to 3 noisy runs per measured instance."""
    slots = calendar(4, 4, 4, 4)
    ms = (slots[-1]["date"] + SLOT + SETTLE) * 0.02
    quiet, noisy = cost(ms, run_pulses(slots)), cost(ms, run_pulses(slots), noise=True)
    untrained = calendar(4, 4, 4, 4, "untrained")
    control = cost((untrained[-1]["date"] + SLOT + SETTLE) * 0.02, run_pulses(untrained))
    cal = calibration_cost()
    out = {}
    for r in range(4):
        per = 2 * cal / jobs + measured * (quiet + r * noisy) / jobs
        tails = machines * 0.75 * cal + machines * 0.75 * (noisy if r else quiet)
        n = int((budget_s - tails - control / jobs) // per)
        out[r] = dict(instances=n, per_instance_s=round(per), tails_s=round(tails))
    return dict(calibration_deck_s=round(cal), quiet_run_s=round(quiet), noisy_run_s=round(noisy), untrained_control_s=round(control),
                network_slots=len(slots), network_ms=round(ms, 2), network_pulses=run_pulses(slots), by_noisy_runs=out)


if __name__ == "__main__":
    import json
    z = nominal()
    print(json.dumps(dict(words=z["words"], outputs={k: v["c"] for k, v in z["tests"].items()},
                          all_tests_right=all(v["c"] == truth(set(k) - {"-"}) for k, v in z["tests"].items()),
                          untrained={k: v["c"] for k, v in zero_error(4, 4, 4, 4, "untrained")["tests"].items()},
                          separation=separation(calendar(4, 4, 4, 4, "skew")), settled=settled(calendar(4, 4, 4, 4, "skew"))[:2],
                          sizing=sizing()), indent=1))
