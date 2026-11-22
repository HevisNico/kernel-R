"""Development only: the plan and the runner of one network run of a member of the step-1 family (X1, X2, F4, F2, F3;
F1 as the regression anchor). New code. It edits no frozen file and runs no simulation by itself: only `network_run`
(the runner) starts ngspice, through the frozen session4.play, and nothing in this folder calls it.

The calendar of a run is the calendar that the frozen prediction code (research/function-family/dev/family_predict.py,
sha256 00b6a516..., research/function-family-dev at 0c003fbf) used to date each observation (family_predict.observation):

  layer 1   max(needs of the layer-1 cells) + EXTRA slots; stimulus the union of the terms; every layer-1 cell writes;
            not routed;
  layer 2   max(needs of c's lines) + EXTRA rounds, one slot per line in the order a, b; stimulus that line's term;
            only c writes; routed;
  tests     the 2^M patterns in family_predict.patterns(inputs) order; read-only; routed;
  "skew"    after the tests, one slot per pair term, its second input 2 units late (no slot for a unary term);
  "untrained"  the tests only.

Slots are dnf.SLOT (22) units apart from 0. Every constant comes from dnf and c4, unchanged. For F1 the calendar is
dnf.calendar and the plan is plans4.network, key for key (test_family_net.F1Regression).

  family_net.py plan  REPO MEMBER NEEDS CONTROL [CELL=PORT ...]     prints the plan's summary; runs nothing
        NEEDS: the member's needs in needs_keys order, comma-separated (F1: a,b,c1,c2; X1: a,c1); CONTROL skew |
        untrained | none; CELL=PORT the unary port of each unary cell (a=1, b=2, ...)
  family_net.py check REPO SEED MEMBER STAGE KIND ROUND PREDICTED    whether the run belongs to its stage; runs nothing
  family_net.py run   REPO OUT ID SEED MEMBER STAGE KIND ROUND PREDICTED NGSPICE PDK      one network run
        STAGE Q | N1 | N2 | N3 | rehearsal (PREDICTION.md 7); KIND quiet (no noise, with the skew slots) | untrained |
        noisy; ROUND 0 without noise, n in stage Nn, the table's n in the rehearsal; PREDICTED the prediction record
        (PREDICTION.md 3), from which the needs, the unary ports, eligibility and room are read.

The campaign's rules (PREDICTION.md 4, 7 and 8): seeds 8501 to 8515 in stages Q and N1 to N3, each run of the member
DRAW.json gives its seed; 8303 and 8306 only in the stage "rehearsal"; noise seed 10 S + n (n = 1 to 3), and in the
rehearsal the table of section 7 exactly. A network run only on an eligible instance; a noisy run only where every cell
has room at K = 3; the untrained run of a member only on its first eligible instance in seed order.

PYTHONPATH: FUP dev, PREP dev, research/function-family/dev (as topup.py's), then this folder.
"""
import json
from pathlib import Path
import resource
import sys
import time

import family_predict as fp                     # MEMBERS, wiring, kinds, patterns, LINE_PORT: imported, never copied

MEMBERS = fp.MEMBERS
wiring = fp.wiring
MAX_NEED = 7                                    # the needs refused above (the brief; dosedev2.network's bound)
CONTROLS = (None, "skew", "untrained")
SKEW_LATE = 2                                   # dnf.calendar's skew: the second input 2 units late (dnf has no name for it)


def require_debug():
    if not __debug__:
        raise SystemExit("refused: not with python -O (or PYTHONOPTIMIZE): the guards are asserts")


def paths(repo):
    """The frozen modules' folders, as topup.paths: dosedev2.repo_paths (C5, NC, DNF, circuit, C6 batch and campaign6)."""
    import batch2x                              # noqa: F401  (PREP dev)
    import dosedev2
    dosedev2.repo_paths(repo)


# ------------------------------------------------------------------------------------------------ the arguments

def layer1(member):
    return tuple(fp.kinds(member))


def needs_keys(member):
    """The member's needs, in order: its layer-1 cells, then c's lines c1 (line a) and c2 (line b)."""
    L1 = layer1(member)
    return L1 + tuple(f"c{fp.LINE_PORT[c]}" for c in L1)


def check_member(member):
    require_debug()
    assert member in MEMBERS, f"refused: {member!r} is not a member ({', '.join(MEMBERS)})"
    return member


def check_ports(member, unary_ports):
    """{cell: port} for exactly the member's unary cells, each port 1 or 2."""
    check_member(member)
    unary = sorted(c for c, k in fp.kinds(member).items() if k == "unary")
    ports = dict(unary_ports or {})
    for c, p in ports.items():
        assert c in unary, (f"refused: {member} has no unary cell {c!r}" if unary else f"refused: {member} has no unary cell; no unary port is given")
        assert p in (1, 2) and isinstance(p, int) and not isinstance(p, bool), f"refused: the unary port of {c} is 1 or 2, not {p!r}"
    missing = [c for c in unary if c not in ports]
    assert not missing, f"refused: no unary port for {missing}"
    return ports


def published_ports(predictions, seed, member):
    """The unary ports of (seed, member) as published in topup-verdict/PREDICTIONS.json (TOPUP_RULES.md 1), read from
    `instances[].members[member].unary_ports` only; nothing else of the file is read."""
    check_member(member)
    rows = [x for x in json.loads(Path(predictions).read_text())["instances"] if x["seed"] == int(seed)]
    assert len(rows) == 1, f"refused: seed {seed} is published {len(rows)} times, not once"
    assert member in rows[0]["members"], f"refused: no published row for {member} of {seed}"
    ports = rows[0]["members"][member]["unary_ports"]
    return check_ports(member, ports)


def check_needs(member, needs):
    """needs: {key: int} with exactly needs_keys(member), or a sequence in that order. Each from 0 to MAX_NEED."""
    keys = needs_keys(member)
    if not isinstance(needs, dict):
        needs = list(needs)
        assert len(needs) == len(keys), f"refused: {member} has {len(keys)} needs {keys}, not {len(needs)}"
        needs = dict(zip(keys, needs))
    assert set(needs) == set(keys), f"refused: {member}'s needs are {keys}, not {sorted(needs)}"
    for k in keys:
        v = needs[k]
        assert isinstance(v, int) and not isinstance(v, bool), f"refused: need {k} is not an integer: {v!r}"
        assert 0 <= v <= MAX_NEED, f"refused: need {k} = {v}: above {MAX_NEED} (or negative)"
    return {k: needs[k] for k in keys}


def check_control(control):
    assert control in CONTROLS, f"refused: control is skew, untrained or none, not {control!r}"
    return control


# ------------------------------------------------------------------------------------------------ the calendar

def calendar(member, needs, control=None):
    """dnf.calendar generalised by the member's terms. A slot: dict(date, stage, round | line | pattern, inputs {name:
    offset}, writes, routed), in dnf.calendar's form and key order."""
    from c4 import dnf
    check_member(member)
    needs = check_needs(member, needs)
    check_control(control)
    spec = MEMBERS[member]
    L1 = layer1(member)
    terms = spec["terms"]
    union = [n for n in spec["inputs"] if any(n in terms[c] for c in L1)]
    out, t = [], 0
    if control != "untrained":
        for r in range(max(needs[c] for c in L1) + dnf.EXTRA):
            out.append(dict(date=t, stage="layer 1", round=r + 1, inputs={n: 0 for n in union}, writes=L1, routed=False))
            t += dnf.SLOT
        for r in range(max(needs[f"c{fp.LINE_PORT[c]}"] for c in L1) + dnf.EXTRA):
            for line in L1:
                out.append(dict(date=t, stage="layer 2", round=r + 1, line=line, inputs={n: 0 for n in terms[line]}, writes=("c",), routed=True))
                t += dnf.SLOT
    for x in fp.patterns(spec["inputs"]):
        out.append(dict(date=t, stage="test", pattern="".join(sorted(x)) or "-", inputs={n: 0 for n in sorted(x)}, writes=(), routed=True))
        t += dnf.SLOT
    if control == "skew":
        for c in L1:
            pair = terms[c]
            if len(pair) == 2:
                out.append(dict(date=t, stage="skew control", pattern="".join(pair), inputs={pair[0]: 0, pair[1]: SKEW_LATE}, writes=(), routed=True))
                t += dnf.SLOT
    return out


# ------------------------------------------------------------------------------------------------ the plan

def amplitude(member, cell):
    """A pair cell's inputs at c4.AMP_AND (0.49); a unary cell's input at c4.AMP_OR (1.0)."""
    import c4
    return c4.AMP_AND if fp.kinds(member)[cell] == "pair" else c4.AMP_OR


def network(member, needs, unary_ports, control=None):
    """plans4.network generalised: the plan of a network run of `member` and its slots. One source per wiring entry of
    each active input; gates plans4.gates(writes) at date - GATE_LEAD; one edge per layer-1 cell with an input in a
    routed slot, to c's port LINE_PORT[cell], delay WIRE, gate (first input, + WINDOW), amplitude AMP_OR."""
    import c4
    import plans4
    from c4 import dnf
    check_member(member)
    ports = check_ports(member, unary_ports)
    slots = calendar(member, needs, control)
    wire = wiring(member, ports)
    L1 = layer1(member)
    amp = {c: amplitude(member, c) for c in L1}
    plan = dict(cells=list(c4.CELLS), gates=[], sources=[], edges=[])
    for s in slots:
        plan["gates"].append((s["date"] - c4.GATE_LEAD, plans4.gates(s["writes"])))
        for n, off in s["inputs"].items():
            for c in L1:
                if n in wire[c]:
                    plan["sources"].append((s["date"] + off, c, wire[c][n], amp[c]))
        if s["routed"]:
            for src in L1:
                offs = [o for n, o in s["inputs"].items() if n in wire[src]]
                if offs:
                    lo = s["date"] + min(offs)
                    p = fp.LINE_PORT[src]
                    plan["edges"].append(dict(name=f"{src}->c{p}@{s['date']}", source=src, cell="c", port=p, delay=c4.WIRE,
                                              gate=(lo, lo + c4.WINDOW), amp=c4.AMP_OR))
    plan["horizon"] = slots[-1]["date"] + dnf.SLOT + dnf.SETTLE
    return plan, slots


# ------------------------------------------------------------------------------------------------ hypotheses H, generic

def pulses(member, unary_ports, slots):
    """dnf.pulses read through the member's wiring: (cell, port, earliest start, latest start, kind)."""
    from c4 import dnf
    wire = wiring(member, check_ports(member, unary_ports))
    L1 = layer1(member)
    out = []
    for s in slots:
        for n, off in s["inputs"].items():
            for c in L1:
                if n in wire[c]:
                    out.append((c, wire[c][n], s["date"] + off, s["date"] + off + dnf.SNAP, "input"))
        if s["routed"]:
            for src in L1:
                offs = [o for n, o in s["inputs"].items() if n in wire[src]]
                if offs:
                    first, last = s["date"] + min(offs), s["date"] + max(offs)
                    out.append(("c", fp.LINE_PORT[src], first + dnf.LATENCY[0] + dnf.WIRE,
                                last + dnf.SNAP + dnf.LATENCY[1] + dnf.WIRE + dnf.SNAP, "line"))
    return out


def separation(member, unary_ports, slots):
    """dnf.separation on the generic pulses (the same grouping)."""
    import math
    from c4 import dnf
    ps = pulses(member, unary_ports, slots)
    out = {}
    for cell in "abc":
        mine = sorted((lo, hi) for c, _, lo, hi, _ in ps if c == cell)
        groups = []
        for lo, hi in mine:
            if groups and lo - groups[-1][1] < dnf.SEPARATION and lo - groups[-1][0] < dnf.SLOT / 2:
                groups[-1] = (groups[-1][0], max(groups[-1][1], hi))
            else:
                groups.append((lo, hi))
        out[cell] = min(b[0] - a[1] for a, b in zip(groups, groups[1:])) if len(groups) > 1 else math.inf
    return out


def settled(member, unary_ports, slots):
    """dnf.settled on the generic pulses: (every slot over before the next slot's gates, the longest slot)."""
    from c4 import dnf
    per_slot = max(max(hi for _, _, _, hi, _ in pulses(member, unary_ports, [s])) - s["date"] for s in slots if s["inputs"])
    return per_slot + 6.5 < dnf.SLOT - dnf.GATE_LEAD, per_slot


# ------------------------------------------------------------------------------------------------ the campaign's rules

CAMPAIGN_DIR = Path(__file__).resolve().parent.parent       # research/function-family-campaign
PROTOCOL = CAMPAIGN_DIR / "PREDICTION.md"
PROTOCOL_SHA256 = "5f9cdfe652c10535d66507324fd5554319e7d2340d127726ad98fb206253de4a"   # at 385c33bf
DRAW = CAMPAIGN_DIR / "DRAW.json"
DRAW_SHA256 = "5c2adb110b0b3fca5f62786a0d03b7a4762211082f1c523c8c07de1181a5df4b"       # at 385c33bf
CAMPAIGN_SEEDS = tuple(range(8501, 8516))                    # PREDICTION.md 1
REHEARSAL_SEEDS = (8303, 8306)                               # PREDICTION.md 7, R-N
STAGES = ("Q", "N1", "N2", "N3", "rehearsal")                # PREDICTION.md 7; "rehearsal" is R-N, the explicit mode
KINDS = ("quiet", "untrained", "noisy")
REHEARSAL_NOISE = {                                          # PREDICTION.md 7: (seed, member, n) -> 10 S + n, exactly
    **{(8303, "F2", n): 83030 + n for n in (1, 2, 3, 4)}, (8303, "X1", 5): 83035, (8303, "X2", 6): 83036,
    **{(8306, "F2", n): 83060 + n for n in (1, 2, 3, 4)}, (8306, "F4", 5): 83065, (8306, "F3", 6): 83066,
}


def sha256_file(path):
    import hashlib
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def protocol_check():
    """The governing protocol is PREDICTION.md at its pushed SHA-256 (campaign 6's safeguard (i), by hash)."""
    got = sha256_file(PROTOCOL)
    assert got == PROTOCOL_SHA256, f"refused: PREDICTION.md has SHA-256 {got}, not the pushed {PROTOCOL_SHA256}"
    return got


def draw():
    """{seed: member} of DRAW.json at its pushed SHA-256."""
    got = sha256_file(DRAW)
    assert got == DRAW_SHA256, f"refused: DRAW.json has SHA-256 {got}, not the pushed {DRAW_SHA256}"
    return {int(s): m for s, m in json.loads(DRAW.read_text())["draw"].items()}


def guard_seed(text, stage):
    """The seed of a run, or a refusal before anything is written: 8501 to 8515 in the stages Q, N1, N2, N3; 8303 and
    8306 in the stage "rehearsal" only; everything else refused."""
    assert stage in STAGES, f"refused: stage {stage!r} is not one of {STAGES}"
    assert str(text) != "none", "refused: the nominal cell has no network run in this campaign"
    seed = int(text)
    assert str(seed) == str(text), f"refused: {text!r} is not a seed"
    if stage == "rehearsal":
        assert seed in REHEARSAL_SEEDS, f"refused: the rehearsal runs on 8303 and 8306 only, not {seed}"
    else:
        assert seed in CAMPAIGN_SEEDS, f"refused: stage {stage} runs on 8501 to 8515 only, not {seed}"
    return seed


def noise_seed(seed, member, rnd, stage):
    """Campaign: 10 S + n, n = 1 to 3 (PREDICTION.md 4). Rehearsal: the table of PREDICTION.md 7, exactly."""
    if stage == "rehearsal":
        key = (seed, member, rnd)
        assert key in REHEARSAL_NOISE, f"refused: no rehearsal noise seed for {member} round {rnd} on {seed}"
        return REHEARSAL_NOISE[key]
    assert seed in CAMPAIGN_SEEDS and rnd in (1, 2, 3), f"refused: a campaign noise seed is 10 S + n with n from 1 to 3, not {rnd}"
    return 10 * seed + rnd


def run_of(stage, kind, rnd):
    """(control, noise) of a run of `kind` in `stage`, or a refusal: Q holds the runs without noise (with the skew
    slots) and the untrained runs; N<n> the noisy runs of round n; the rehearsal all three kinds."""
    assert stage in STAGES, f"refused: stage {stage!r} is not one of {STAGES}"
    assert kind in KINDS, f"refused: kind {kind!r} is not one of {KINDS}"
    if kind in ("quiet", "untrained"):
        assert stage in ("Q", "rehearsal"), f"refused: a {kind} run belongs to stage Q, not {stage}"
        assert rnd == 0, "refused: a run without noise has round 0"
        return ("skew" if kind == "quiet" else "untrained"), "none"
    assert stage != "Q", "refused: a noisy run does not belong to stage Q"
    if stage != "rehearsal":
        assert stage == f"N{rnd}", f"refused: round {rnd} does not belong to stage {stage}"
    return None, "injected"


def read_predicted(path):
    """PREDICTED.json in family_predict.py's output shape: {"instances": [{"seed", "members": {member: row}}]}.
    Returns {seed: {member: row}}; a seed listed twice is refused."""
    out = {}
    for x in json.loads(Path(path).read_text())["instances"]:
        s = int(x["seed"])
        assert s not in out, f"refused: seed {s} is listed twice in the prediction record"
        out[s] = x["members"]
    return out


def kernel(row):
    """The kernel's verdicts {K0, K3} of a row, or None; refuses a row whose summary flags disagree with them."""
    k = (row.get("gate") or {}).get("kernel")
    if not k:
        return None
    assert isinstance(k.get("K0"), bool) and isinstance(k.get("K3"), bool), f"refused: the kernel's verdicts are not booleans: {k}"
    if "gate_K0" in row:
        assert row["gate_K0"] == k["K0"], "refused: gate_K0 disagrees with the kernel's K0"
    if "room_K3" in row:
        assert row["room_K3"] == k["K3"], "refused: room_K3 disagrees with the kernel's K3"
    return k


def eligible(row):
    """PREDICTION.md 3: measured, and the kernel's checks hold at K = 0."""
    k = kernel(row)
    return row.get("measured") is True and row.get("eligible_needs") is not False and bool(k) and k["K0"]


def room(row):
    """PREDICTION.md 3 and 4: every cell has room, the kernel's checks at K = 3 (on an eligible row)."""
    return eligible(row) and kernel(row)["K3"]


def admit(stage, kind, rnd, seed, member, predicted, members_of=None):
    """Whether the run belongs to its stage, from the prediction record; refuses otherwise. Returns dict(control,
    noise, round, noise_id, needs, unary_ports, row). members_of: {seed: member} (DRAW.json; campaign stages only)."""
    check_member(member)
    control, noise = run_of(stage, kind, rnd)
    if stage != "rehearsal":
        members_of = draw() if members_of is None else members_of
        assert members_of.get(seed) == member, f"refused: {seed} is drawn for {members_of.get(seed)}, not {member}"
    assert seed in predicted and member in predicted[seed], f"refused: no row for {member} of {seed} in the prediction record"
    row = predicted[seed][member]
    assert row.get("member", member) == member and int(row.get("seed", seed)) == seed, "refused: the row names another member or seed"
    assert eligible(row), f"refused: {member} of {seed} is not eligible (PREDICTION.md 3): no network run"
    if noise == "injected":
        assert room(row), f"refused: {member} of {seed} has no room at K = 3 for every cell: no noisy run"
    if kind == "untrained" and stage != "rehearsal":
        first = None
        for s in sorted(x for x, m in members_of.items() if m == member):
            assert s in predicted and member in predicted[s], f"refused: no row for {member} of {s}: its first eligible instance is undecided"
            if eligible(predicted[s][member]):
                first = s
                break
        assert first == seed, f"refused: {member}'s untrained run is on its first eligible instance, {first}, not {seed}"
    ports = check_ports(member, row.get("unary_ports") or {})
    needs = check_needs(member, row["needs"])
    L1 = layer1(member)
    for q, keys in (("Q1", L1), ("Q2", needs_keys(member)[len(L1):])):
        if q in row:
            assert row[q] == max(needs[k] for k in keys) + 2, f"refused: the row's {q} is not max(needs) + 2"
    noise_id = noise_seed(seed, member, rnd, stage) if noise == "injected" else None
    return dict(control=control, noise=noise, round=rnd if noise == "injected" else None, noise_id=noise_id, needs=needs, unary_ports=ports)


# ------------------------------------------------------------------------------------------------ the runner

def network_run(repo, out, rid, seed_text, member, stage, kind, rnd, predicted, ngspice, pdk, members_of=None):
    """One network run of the campaign (stages Q, N1 to N3) or of the rehearsal R-N. Every check is made before
    anything is written: the protocol's SHA-256, the stage, the seed, the draw, the record's eligibility and room,
    the noise seed. The needs and the unary ports are the prediction record's; nothing else chooses them."""
    require_debug()
    paths(repo)
    import dosedev2
    out = Path(out)
    dosedev2.outside(repo, out)
    proto = protocol_check()
    seed = guard_seed(seed_text, stage)
    pred_sha = sha256_file(predicted)
    a = admit(stage, kind, rnd, seed, member, read_predicted(predicted), members_of)
    head = dict(stage=dict(name=stage, kind=kind, protocol_sha256=proto, predicted_sha256=pred_sha,
                           draw_sha256=DRAW_SHA256 if stage != "rehearsal" else None))
    return play_run(repo, out, rid, seed, member, a["unary_ports"], a["needs"], a["control"], a["noise_id"], rnd, ngspice, pdk, head)


def play_run(repo, out, rid, seed, member, unary_ports, needs, control, noise_id, rnd, ngspice, pdk, head):
    """campaign6/net6.py network()'s body, with MEMBER and UNARY_PORTS, at the 2x design point (dosedev_tol.tolerance and
    dosedev2.window(batch2x.PARAMS), as topup.py applies it). The same frozen functions in the same order (the plan,
    noisemodel.shim, net.deck, session4.play, run4.trnoise_fingerprint); the same deck; net6's record keys in its
    order, its `stage` as head["stage"] and `campaign6` replaced by `family`; then member, wiring, unary_ports and
    dosedev. Called by network_run after its checks, and by the tests."""
    require_debug()
    paths(repo)
    import batch2x
    import c4
    import dosedev2
    import dosedev_tol
    import noisemodel
    import run4
    import session4
    from session4 import net
    began = time.time()
    out = Path(out)
    dosedev2.outside(repo, out)
    check_member(member)
    ports = check_ports(member, unary_ports)
    needs = check_needs(member, needs)
    check_control(control)
    assert (noise_id is None) == (rnd == 0), "a noisy run has a round and a noise seed, a run without noise neither"
    print(c4.require_pinned())
    section = c4.SECTION
    rec = dict(id=rid, kind="network", section=section, seed=seed, stage=head["stage"])     # net6's (run4.run's) order
    plan, slots = network(member, needs, ports, control)
    shim, seen = None, []
    with dosedev_tol.tolerance(), dosedev2.window(batch2x.PARAMS, seen):
        if noise_id is not None:
            out.mkdir(parents=True, exist_ok=True)
            shim, shim_info = noisemodel.shim(out)
            text = net.deck(cells=c4.CELLS, section=section, noise=True)
            info = dict(model="injected", noise_seed=noise_id, imposed_process_number=noise_id, shim=shim_info)
        else:
            text = net.deck(cells=c4.CELLS, section=section)
            info = dict(model="none")
        changed = {k: v for k, v in seen[0]["parameters_changed"].items() if v["old"] != v["new"]}
        assert changed == dict(vhi=dict(old="0.6", new="0.7"), reltol=dict(old="1e-4", new="1e-5")), f"refused: not the 2x design point: {changed}"
        rec.update(needs=list(needs.values()), control=control, round=rnd if noise_id is not None else None, slots=len(slots))
        result, tr = session4.play(out / "evidence", plan, text, Path(ngspice), Path(pdk), seed=seed, guard_off=False, noise_id=noise_id, shim=shim)
    (out / "evidence" / "pdk").unlink()
    reached = bool(tr.t[-1] >= result["horizon_s"] - 1e-9)
    mark = run4.trnoise_fingerprint(tr, c4.CELLS)
    if shim is not None:
        Path(shim).unlink()
    ev = out / "evidence"
    rec.update(noise=info, reached_its_last_date=reached, horizon_s=result["horizon_s"], waveform_ends_s=result["waveform_ends_s"],
               points=result["points"], files={x: run4.sha(ev / x) for x in ("input.spice", "session.log", "trace.raw", "result.json")})
    rec.update(noise_fingerprint=mark, wall_s=time.time() - began,
               peak_rss_MB=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss / 1024)
    rec["family"] = dict(campaign="function-family-campaign", protocol_sha256=head["stage"].get("protocol_sha256"), instance=seed,
                         member=member, kind="network", stage=head["stage"].get("name"), interpreter=c4.interpreter())
    rec.update(member=member, wiring=wiring(member, ports), unary_ports=ports,
               dosedev=dict(what=f"network run of {member} at the 2x design point", needs=needs, decks=seen))
    (out / "noise.sha256").write_text(mark + "\n")
    (out / "record.json").write_text(json.dumps(rec, indent=1) + "\n")
    assert rec["reached_its_last_date"], "the waveform ends before the last date of the run"
    return rec


# ------------------------------------------------------------------------------------------------ command line

def parse_ports(items):
    out = {}
    for x in items:
        c, _, p = x.partition("=")
        assert c and p.isdigit() and c not in out, f"refused: {x!r} is not CELL=PORT (or given twice)"
        out[c] = int(p)
    return out


def main(argv=None):
    require_debug()
    a = sys.argv[1:] if argv is None else argv
    cmd = a[0] if a else None
    if cmd == "plan":
        repo, member, needs, control, *ports = a[1:]
        paths(repo)
        plan, slots = network(member, [int(x) for x in needs.split(",")], parse_ports(ports), None if control == "none" else control)
        print(json.dumps(dict(member=member, slots=len(slots), sources=len(plan["sources"]), edges=len(plan["edges"]),
                              horizon=plan["horizon"]), indent=1))
    elif cmd == "check":
        repo, seed, member, stage, kind, rnd, predicted = a[1:]
        paths(repo)
        protocol_check()
        s = guard_seed(seed, stage)
        x = admit(stage, kind, int(rnd), s, member, read_predicted(predicted))
        print(json.dumps(dict(seed=s, member=member, stage=stage, kind=kind, **x)))
    elif cmd == "run":
        repo, out, rid, seed, member, stage, kind, rnd, predicted, ngspice, pdk = a[1:]
        rec = network_run(repo, out, rid, seed, member, stage, kind, int(rnd), predicted, ngspice, pdk)
        print(json.dumps(dict(id=rec["id"], reached_its_last_date=rec["reached_its_last_date"], wall_s=round(rec["wall_s"]))))
    else:
        raise SystemExit(__doc__)


if __name__ == "__main__":
    main()
