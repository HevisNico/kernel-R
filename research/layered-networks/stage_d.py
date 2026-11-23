"""Stage D of the campaign plan (CAMPAIGN_PLAN_DRAFT.md §2, step 2): the per-cell measures of one instance, made
BEFORE any network run, and the prediction they give. Development only; nothing here is frozen.

  stage_d.py run     SPEC OUT SEED [overlay=FILE|overlay=none] [inverters=FILE|inverters=assumed] [solo=1]
                     one stage-D session (OUT/record.json), then `predict`
  stage_d.py predict SPEC OUT [inverters=FILE|inverters=assumed]
                     the fit, the verdicts and the prediction from OUT/record.json (no simulation): OUT/fit_d.json,
                     OUT/prediction.json (canonical bytes), OUT/cost_d.json
  stage_d.py seal    SEALDIR OUT [OUT ...]     the sealed prediction record (seal.py)
  stage_d.py verify  SEALDIR                   its SHA256SUMS checked

The method is campaign (a)'s (research/function-family-campaign-impl 920413ec, campaign_predict.py): per-cell measures
in their own session of the same deck and mismatch seed, the gates applied, and the predicted words and outputs
"read off the observation" of that session; stage N is then compared with them directly (compare_d.py).

**The session.** instrument.CalNetwork (the deck of instrument.deck_text: the design point, the junction areas, one
leak node per port), the same mismatch seed as the network run, and with `overlay=` the config overlay of lcal2.py
(default config_inverter_c5.json; `overlay=none` is config.json as pushed, the deck of the dev/cal5_* records). No
routing: every R cell is driven alone by ideal pulses on its own ports, at its gate's amplitude, at T + delta of its
slot; the inverters are idle. The cells are driven in the same slots (one cell's pulses never reach another cell), so
the D4 bound applies to the scans as in the in-situ runs (d4_stage, or `solo=1` for the run's own solo scans: the
plan's D4 audit). Three phases, in the family's order (every cell's groups in order, g0 then g1):
1. **Training ascent from the preset.** Each cell takes its groups' lessons, write gate open, from s = 0; a silent
   lesson writes one dose (the cell's own write); a group stops after `hold` FIREs in a row or `max_rounds` rounds
   (config.json `calendar`, as the network's training). Its letters are the stage-D word of that (cell, group).
2. **Mask reads at the settled state**, read-only: one read per non-empty mask of the gate (both {1}, {2}, {1,2};
   copy {1}; either {1}, {2}, {1,2}). They give the cell's observed table, and the read calibration of fit.py.
3. **Scans**: instrument.scan_all unchanged (bisection from the ascent's bracket, both-direction repeats); the record
   is loaded with records2.py (repeat rule v2).

**The fit and the gates**: fit.cell_fit unchanged, on a per-cell view of the record (that cell's reads only), so its
lessons are its own and the mask reads are its test reads. Eligible at K0: every cell measured with its K0 verdict
(Cell.Valid with the budgets, the stage-D word equal to the model's stop, the training and read calibrations) and,
with a front end, every inverter's K0 gate. Room at K3: the same at K3.

**The inverter gate** comes from the inverter kit (research/inverter-instances), as a JSON file `inverters=FILE`:
{"inverters": {"n0": {"K0": bool, "K3": bool, ...}, ...}, ...} (interface proposed to the kit's session; to be
confirmed). Without it, an instance with a front end has no prediction ("inverter gate not measured").
`inverters=assumed` is for development validation only: the gate is taken as holding at K0 and K3, and the
prediction record says so in `inverter_gate.source`.

**The prediction** (only when eligible at K0; it applies to noisy runs only with room at K3):
- every training word, `need` letters `s` then `hold` letters `F`, per (layer, cell, group): the stage-D word;
- every cell's FIRE bit and the output on every input pattern: the cells' observed tables composed through the
  layers, the inverters firing exactly on the absent inputs (their gate);
- both cells silent in any shift slot.
"""
import copy
import hashlib
import json
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import deck as deckmod  # noqa: E402
import fit as fitmod  # noqa: E402
import instrument  # noqa: E402
import records2  # noqa: E402
import run as runmod  # noqa: E402
import scores as scoremod  # noqa: E402
import spec as specmod  # noqa: E402

CAL = instrument.CAL
FORMAT = "layered-stage-d-prediction/1"
# the package files whose bytes make the prediction (their sha256 goes into the record)
CODE = ("stage_d.py", "instrument.py", "fit.py", "scores.py", "records.py", "records2.py", "deck.py", "run.py",
        "session.py", "spec.py", "calibration.json", "config.json")


def sha256_bytes(b):
    return hashlib.sha256(b).hexdigest()


def sha256_file(p):
    return sha256_bytes(Path(p).read_bytes())


def canon(obj):
    """Canonical bytes: fit.js (Fractions as strings), sorted keys, no spaces, ASCII, one trailing newline."""
    return (json.dumps(fitmod.js(obj), sort_keys=True, separators=(",", ":"), ensure_ascii=True) + "\n").encode()


def config(overlay):
    if overlay in (None, "none"):
        cfg = json.loads((HERE / "config.json").read_text())
        return cfg, dict(file="none")
    import lcal2
    cfg, ov = lcal2.config(overlay)
    return cfg, dict(file=overlay, sha256=sha256_file(HERE / overlay))


def cell_names(s):
    return [(f"c{k}_{i}", k, i, n["gate"]) for k, nodes in enumerate(s["layers"], start=1) for i, n in enumerate(nodes)]


def group_ports(gate, g):
    return tuple(p for p in (1, 2) if specmod.GROUP_MASK[gate][g][p - 1])


def read_masks(gate):
    return [m for m in fitmod.MASKS[gate] if m]


# ------------------------------------------------------------------------------------------------ the session

class StageDNetwork(instrument.CalNetwork):
    """CalNetwork with one more slot kind: ideal pulses on chosen ports of chosen cells, no routing."""

    def drive(self, kind, todo, writing, info):
        """todo: {cell: ports}; writing: the cells whose ports are ungated (their dose source on). Pulses at the
        slot's T + delta (on the noise grid), at the gate's amplitude. A FIRE is a latch rise through 0.9 V within the
        watch window (run.Network's rule); its emission is the launch date minus delta, as the router records it."""
        cal = self.cfg["calendar"]
        T = self.next_T
        self.next_T = self.snap(T + self.slot_ns)
        self.ses.run((T - self.ns(cal["gate_lead_tu"])) * 1e-9)
        u = self.measure_u()
        self.gate_ports({(c, p) for c in writing for p in deckmod.PORTS})
        date = self.snap(T + self.delta)
        reads, watch = {}, {}
        for c, ports in todo.items():
            k, i = (int(x) for x in c[1:].split("_"))
            arr = [None, None]
            for p in ports:
                self.pulse(c, p, date, self.cfg["stimulus"]["amp"][self.gate_of(c)])
                arr[p - 1] = date
            reads[c] = dict(layer=k, index=i, start=date, arrivals=arr, latch=None, emission=None, second=None)
            watch[f"x{c}.p"] = c
        end = (T + self.ns(cal["watch_tu"])) * 1e-9
        live = dict(watch)
        while live:
            t = self.ses.run(end, list(live))
            if t >= end - 1e-12:
                break
            for node in list(live):
                if self.ses.last(f"v({node})") > 0.9:
                    c = live.pop(node)
                    lt = self.ses.rise(node, (date - 1000) * 1e-9)
                    assert lt is not None, node
                    lt = round(lt * 1e9)
                    reads[c].update(latch=lt, emission=self.snap(lt + self.delta) - self.delta)
        gap = CAL.get("same_edge_ns", 1000)
        for node, c in watch.items():
            r = reads[c]
            if r["latch"] is not None:
                two = self.ses.rise(node, (r["latch"] + gap) * 1e-9)
                r["second"] = None if two is None else round(two * 1e9)
        rec = dict(kind=kind, T=T, info=info, lines=[], inv=[], u=u,
                   reads=sorted(reads.values(), key=lambda r: (r["layer"], r["index"])))
        self.slots.append(rec)
        return rec


def training(net, s, cfg, log):
    """Phase 1: every cell's lessons from the preset, in parallel slots, its groups in order."""
    calc = cfg["calendar"]
    st = {c: dict(layer=k, idx=i, gate=g, g=0, ng=specmod.GROUPS[g], r=0, run=0, word="") for c, k, i, g in cell_names(s)}
    lessons, words = [], {}
    while any(x["g"] < x["ng"] for x in st.values()):
        todo = {c: group_ports(x["gate"], x["g"]) for c, x in st.items() if x["g"] < x["ng"]}
        rec = net.drive("lesson", todo, set(todo), dict(stage="D", groups={c: st[c]["g"] for c in todo}))
        idx = len(net.slots) - 1
        for r in rec["reads"]:
            c = f"c{r['layer']}_{r['index']}"
            x = st[c]
            f = r["emission"] is not None
            lessons.append(dict(layer=x["layer"], cell=x["idx"], group=x["g"], round=x["r"], slot=idx))
            x["word"] += "F" if f else "s"
            x["run"] = x["run"] + 1 if f else 0
            x["r"] += 1
            if x["run"] >= calc["hold"] or x["r"] >= calc["max_rounds"]:
                words[f"{x['layer']}/{x['idx']}/{x['g']}"] = x["word"]
                log(f"stage D lesson {c} group {x['g']}: {x['word']}")
                x.update(g=x["g"] + 1, r=0, run=0, word="")
    return lessons, words


def mask_reads(net, s, log):
    """Phase 2: one read-only read per non-empty mask, every cell in the same slots."""
    masks = {c: read_masks(g) for c, _, _, g in cell_names(s)}
    tests = []
    for j in range(max(len(m) for m in masks.values())):
        todo = {c: m[j] for c, m in masks.items() if j < len(m)}
        rec = net.drive("test", todo, set(), dict(stage="D", masks={c: list(m) for c, m in todo.items()}))
        tests.append(len(net.slots) - 1)
        got = []
        for r in rec["reads"]:
            c = f"c{r['layer']}_{r['index']}"
            got.append(f"{c}{list(todo[c])}={'F' if r['emission'] is not None else 's'}")
        log("stage D mask reads: " + ", ".join(got))
    return tests


def run_stage_d(s, cfg, out, seed, log=print, solo=False):
    out = Path(out)
    t_start = time.time()
    net = StageDNetwork(s, cfg, out, seed)
    net.ses.cmd("echo ready")
    t_setup, c_setup = time.time() - t_start, runmod.cpu_of(net.ses.p.pid)
    status, lessons, words, tests, scans, u_end = "done", [], {}, [], None, None
    t_train = t_test = 0.0
    c_train = c_test = None
    try:
        t0 = time.time()
        lessons, words = training(net, s, cfg, log)
        t_train, c_train = time.time() - t0, runmod.cpu_of(net.ses.p.pid)
        tests = mask_reads(net, s, log)
        t_test, c_test = time.time() - t0 - t_train, runmod.cpu_of(net.ses.p.pid)
        partial = dict(slots=net.slots, lessons=lessons)
        scans = instrument.scan_all(net, partial, log, solo=solo)
        u_end = partial["u_end"]
    except Exception as e:                                  # reported, never retried
        status = f"failed: {e}"
        log(status)
    finally:
        simulated = net.ses.now
        c_end = runmod.cpu_of(net.ses.p.pid)
        net.ses.close()
    record = dict(stage="D", tag=s["tag"], seed=seed, status=status, cells=net.cells, inverters=net.invs,
                  cost=dict(wall_setup_s=t_setup, wall_train_s=t_train, wall_test_s=t_test,
                            wall_scan_s=None if scans is None else scans["wall_s"],
                            cpu_setup_s=c_setup, cpu_train_s=c_train, cpu_test_s=c_test, cpu_end_s=c_end,
                            simulated_s=simulated, lesson_slots=len({x["slot"] for x in lessons}),
                            test_slots=len(tests), scan_slots=None if scans is None else scans["slots"],
                            solo_scan_slots=None if scans is None or "solo" not in scans else scans["solo"]["slots"]),
                  words=words, lessons=lessons, tests=tests, slots=net.slots, u_end=u_end, scans=scans)
    (out / "record.json").write_text(json.dumps(record, indent=1, default=str) + "\n")
    return record


# ------------------------------------------------------------------------------------------------ the prediction

def cell_view(rec, c, layer):
    """The record as cell c alone sees it: only its reads in every slot, and every lesson slot labelled with its layer
    (so that fit.cell_fit takes its lessons as its own training and no other cell's lesson as a replay read)."""
    v = dict(rec)
    v["slots"] = []
    for sl in rec["slots"]:
        sl = dict(sl)
        if "reads" in sl:
            sl["reads"] = [r for r in sl["reads"] if f"c{r['layer']}_{r['index']}" == c]
        if sl["kind"] == "lesson":
            sl["info"] = dict(sl.get("info") or {}, layer=layer)
        v["slots"].append(sl)
    return v


def observed_table(rec, c):
    """{mask: fired} from the stage-D mask reads of cell c."""
    out = {}
    for idx in rec["tests"]:
        for r in rec["slots"][idx]["reads"]:
            if f"c{r['layer']}_{r['index']}" == c:
                out[tuple(p for p in (1, 2) if r["arrivals"][p - 1] is not None)] = r["emission"] is not None
    return out


def compose(s, tables):
    """Every cell's FIRE bit and the output on every input pattern: the tables composed through the layers. With a
    front end the rails are spec.rails (each inverter fires exactly on its absent input: its gate). A cell with no
    arrival is silent; a mask missing from a table is None (unknown) and makes everything above it unknown."""
    cells, outputs = {}, {}
    for x in specmod.patterns(s["m"]):
        below, bits = specmod.rails(s, x), {}
        for k, nodes in enumerate(s["layers"], start=1):
            now = []
            for i, n in enumerate(nodes):
                src = [None if n["source"][a] is None else below[n["source"][a]] for a in range(2)]
                if any(b is None for a, b in enumerate(src) if n["source"][a] is not None):
                    f = None
                else:
                    mask = tuple(p for p in (1, 2) if src[p - 1])
                    f = False if not mask else tables[f"c{k}_{i}"].get(mask)
                bits[f"c{k}_{i}"] = f
                now.append(f)
            below = tuple(now)
        key = str(specmod.code(x))
        cells[key], outputs[key] = bits, below[-1]
    return cells, outputs


def inverter_gate(s, arg):
    """The inverter gate of the instance: {source, inverters, K0, K3, why}."""
    if not s["front"]:
        return dict(source="no front end", inverters={}, K0=True, K3=True, why=[])
    names = [f"n{j}" for j in range(s["m"])]
    if arg == "assumed":
        return dict(source="assumed, not measured (development validation only)",
                    inverters={n: dict(K0=True, K3=True) for n in names}, K0=True, K3=True, why=[])
    if arg is None or not Path(arg).exists():
        return dict(source="missing", inverters={}, K0=False, K3=False, why=["inverter gate not measured"])
    g = json.loads(Path(arg).read_text())
    inv = g.get("inverters", {})
    why = [f"{n}: no gate" for n in names if n not in inv]
    why += [f"{n}: K0 fails" for n in names if n in inv and not inv[n].get("K0")]
    whyK3 = [f"{n}: K3 fails" for n in names if n in inv and not inv[n].get("K3")]
    return dict(source=dict(file=Path(arg).name, sha256=sha256_file(arg), kit_commit=g.get("kit_commit")),
                inverters={n: dict(K0=bool(inv.get(n, {}).get("K0")), K3=bool(inv.get(n, {}).get("K3"))) for n in names},
                K0=not why, K3=not why and not whyK3, why=why + whyK3)


def record_core(rec):
    """The record without its cost and wall-time fields (record.cost, scans.wall_s, scans.solo.wall_s): what a second
    machine must reproduce byte for byte, and what the prediction's record_core_sha256 hashes."""
    core = {k: v for k, v in rec.items() if k != "cost"}
    if core.get("scans"):
        core["scans"] = {k: v for k, v in core["scans"].items() if k != "wall_s"}
        if core["scans"].get("solo"):
            core["scans"]["solo"] = {k: v for k, v in core["scans"]["solo"].items() if k != "wall_s"}
    return core


def predict(spec_path, out, inverters=None):
    s = specmod.load(spec_path)
    out = Path(out)
    rec = records2.load(out)
    ov = json.loads((out / "overlay_d.json").read_text()) if (out / "overlay_d.json").exists() else dict(file="?")
    cells, tables = [], {}
    if rec["status"] == "done":
        for c, k, i, gate in cell_names(s):
            view = cell_view(rec, c, k)
            ro = scoremod.readout(s, view)
            cf = fitmod.cell_fit(s, view, ro, c, k, i)
            cells.append(cf)
            tables[c] = observed_table(rec, c)
    inv = inverter_gate(s, inverters)
    measured = rec["status"] == "done" and all(c["measured"] for c in cells)
    elig = measured and all(c["verdicts"]["K0"]["ok"] for c in cells) and inv["K0"]
    room = elig and all(c["verdicts"]["K3"]["ok"] for c in cells) and inv["K3"]
    hold = json.loads((HERE / "config.json").read_text())["calendar"]["hold"]
    summary = []
    for c in cells:
        row = dict(cell=c["cell"], gate=c["gate"], measured=c["measured"], why_not_measured=c["why_not_measured"])
        if c["measured"]:
            row.update(need=c["need"], maxWrites=c["maxWrites"], epsilon=c["epsilon"], anchors=c["anchors"],
                       guarded=c["guarded"], lean_cell=c["lean_cell"],
                       K0=dict(ok=c["verdicts"]["K0"]["ok"], failing=c["verdicts"]["K0"]["failing"]),
                       K3=dict(ok=c["verdicts"]["K3"]["ok"], failing=c["verdicts"]["K3"]["failing"]))
        summary.append(row)
    words = dict(rec["words"])
    pcells, pouts = compose(s, tables) if tables else ({}, {})
    prediction = None
    if elig:
        for c in cells:                                    # the word is the model's: need letters s, then hold F
            k, i = (int(x) for x in c["cell"][1:].split("_"))
            for g, nd in c["need"].items():
                assert words[f"{k}/{i}/{g}"] == "s" * nd + "F" * hold, (c["cell"], g, words[f"{k}/{i}/{g}"])
        assert all(v is not None for v in pouts.values())
        skew = sorted(c["cell"] for c in cells if c["gate"] == "both")
        prediction = dict(words=words, outputs=pouts, cells=pcells, skew_silent=skew,
                          output_equals_function=all(pouts[str(specmod.code(x))] == e
                                                     for x, e in zip(specmod.patterns(s["m"]), s["expect"])))
    core = record_core(rec)
    pred = dict(format=FORMAT, tag=s["tag"], seed=rec["seed"], status=rec["status"],
                spec=dict(file=Path(spec_path).name, sha256=sha256_file(spec_path)), overlay=ov,
                code={f: sha256_file(HERE / f) for f in CODE},
                record_core_sha256=sha256_bytes(canon(core)), repeat_rule_v2=rec.get("repeat_rule_v2", []),
                same_edge_drops=rec.get("same_edge_drops", []),
                inverter_gate=inv, cells=summary, measured=measured, eligible_K0=elig, room_K3=room,
                applies=dict(noiseless=elig, noisy=room), prediction=prediction,
                stage_d_observed_not_a_prediction=dict(words=words, tables={c: {"".join(map(str, m)): f for m, f in t.items()}
                                                                             for c, t in tables.items()}))
    (out / "prediction.json").write_bytes(canon(pred))
    (out / "fit_d.json").write_text(json.dumps(fitmod.js(dict(cells=cells)), indent=1) + "\n")
    cost = rec["cost"]
    cpu = cost.get("cpu_end_s")
    (out / "cost_d.json").write_text(json.dumps(dict(cost=cost, cpu_min=None if cpu is None else cpu / 60), indent=1) + "\n")
    return pred


# ------------------------------------------------------------------------------------------------ commands

def flags(args):
    return dict(a.split("=", 1) for a in args)


def cmd_run(spec_path, out, seed, *rest):
    f = flags(rest)
    cfg, ov = config(f.get("overlay", "config_inverter_c5.json"))
    Path(out).mkdir(parents=True, exist_ok=True)
    (Path(out) / "overlay_d.json").write_bytes(canon(ov))
    r = run_stage_d(specmod.load(spec_path), cfg, out, int(seed), solo=f.get("solo") == "1")
    print(json.dumps(dict(status=r["status"], cost=r["cost"], words=r["words"]), indent=1))
    p = predict(spec_path, out, f.get("inverters"))
    print(json.dumps(dict(eligible_K0=p["eligible_K0"], room_K3=p["room_K3"], prediction=p["prediction"]), indent=1))
    return r["status"] == "done"


def cmd_predict(spec_path, out, *rest):
    p = predict(spec_path, out, flags(rest).get("inverters"))
    print(json.dumps(dict(eligible_K0=p["eligible_K0"], room_K3=p["room_K3"], cells=p["cells"],
                          prediction=p["prediction"]), indent=1, default=str))


if __name__ == "__main__":
    cmd, *a = sys.argv[1:] or ["help"]
    if cmd == "run":
        sys.exit(0 if cmd_run(*a) else 1)
    elif cmd == "predict":
        cmd_predict(*a)
    elif cmd in ("seal", "verify"):
        import seal
        sys.exit(0 if getattr(seal, cmd)(*a) else 1)
    else:
        sys.exit(__doc__)
