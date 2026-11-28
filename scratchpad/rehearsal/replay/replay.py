"""Rehearsal 1, TASK 3: the replay of the third symbol on the isolated stage-D deck (REPLAY_CRITERIA_2026-11-27.md).
A reconstruction made after the fact; exploratory; changes no verdict.

  replay.py FREEZE_TREE INSTANCE_DIR CASE OUTDIR          CASE: 1 | 2 | 3

FREEZE_TREE is a clean clone of research/layered-campaign-freeze at 5d02acce (the code that ran stage D in rehearsal 1);
INSTANCE_DIR the published instance folder (its D/record.json, D/input.spice). Stage D is run as stage_d.py runs it
(StageDNetwork, the instance's seed, overlay config_inverter_c5.json), lesson slots 0, 1 and 2 only. The preset and
the first two lesson slots are exactly stage D's. In slot 2 (the third read) ONLY the two input dates of the two cells
under study change, measured from the slot's T; the other cells keep stage D's 2.4/2.4 us. The run goes on to the end
of slot 2's watch window. Saved, besides stage D's own vectors: x1/x2 vs and vrefsn, vq and vrefmn of the two cells.
Writes OUTDIR/replay.json and OUTDIR/replay.raw (binary)."""
import json
import sys
from pathlib import Path

TREE, INST, CASE, OUT = Path(sys.argv[1]), Path(sys.argv[2]), sys.argv[3], Path(sys.argv[4])
L = TREE / "research" / "layered-networks"
sys.path.insert(0, str(L))
import stage_d        # noqa: E402
import spec as specmod  # noqa: E402

TAG_CELLS = {"XOR3_27735": ("c1_0", "c1_1"), "XOR3_88529": ("c1_1", "c1_0")}     # (refuted, witness)
NET_ORDER_US = {"c1_0": (11.2, 12.8), "c1_1": (12.8, 11.2)}                        # port 1, port 2 (the criteria)
CASES = {"1": lambda c: (2.4, 2.4), "2": lambda c: (12.0, 12.0), "3": lambda c: NET_ORDER_US[c]}

inst = INST.name
seed = int(inst.split("_")[1])
cells = TAG_CELLS[inst]
recD = json.loads((INST / "D" / "record.json").read_text())
spec = specmod.load(L / "specs" / "xor3.json")
cfg, _ = stage_d.config("config_inverter_c5.json")
OUT.mkdir(parents=True, exist_ok=True)
times = {c: CASES[CASE](c) for c in cells}


class Replay(stage_d.StageDNetwork):
    def drive(self, kind, todo, writing, info):
        """stage_d.StageDNetwork.drive, with per-port dates for the two cells in slot 2 only."""
        cal = self.cfg["calendar"]
        T = self.next_T
        self.next_T = self.snap(T + self.slot_ns)
        self.ses.run((T - self.ns(cal["gate_lead_tu"])) * 1e-9)
        u = self.measure_u()
        self.gate_ports({(c, p) for c in writing for p in stage_d.deckmod.PORTS})
        date = self.snap(T + self.delta)
        k_slot = len(self.slots)
        reads, watch = {}, {}
        for c, ports in todo.items():
            k, i = (int(x) for x in c[1:].split("_"))
            arr = [None, None]
            for p in ports:
                d = date
                if k_slot == 2 and c in times:
                    d = self.snap(T + round(times[c][p - 1] * 1000))
                    assert d == T + round(times[c][p - 1] * 1000), "a replay date off the noise grid"
                self.pulse(c, p, d, self.cfg["stimulus"]["amp"][self.gate_of(c)])
                arr[p - 1] = d
            reads[c] = dict(layer=k, index=i, start=min(a for a in arr if a is not None), arrivals=arr, latch=None,
                            emission=None, second=None)
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
                    lt = self.ses.rise(node, (reads[c]["start"] - 1000) * 1e-9)
                    assert lt is not None, node
                    lt = round(lt * 1e9)
                    reads[c].update(latch=lt, emission=self.snap(lt + self.delta) - self.delta)
        if self.ses.now < end - 1e-12:
            self.ses.run(end)                                # the whole decision window, fired or not
        rec = dict(kind=kind, T=T, info=info, lines=[], inv=[], u=u,
                   reads=sorted(reads.values(), key=lambda r: (r["layer"], r["index"])))
        self.slots.append(rec)
        return rec


net = Replay(spec, cfg, OUT, seed)
extra = [f"x{c}.{n}" for c in cells for n in ("x1.vs", "x1.vrefsn", "x2.vs", "x2.vrefsn", "vq", "vrefmn")]
net.ses.saved = net.ses.saved + extra
deck_sha = stage_d.sha256_file(OUT / "input.spice")
pub_sha = stage_d.sha256_file(INST / "D" / "input.spice")
calc = cfg["calendar"]
st = {c: dict(layer=k, idx=i, gate=g, g=0, ng=specmod.GROUPS[g], r=0, run=0, word="") for c, k, i, g in stage_d.cell_names(spec)}
try:
    while len(net.slots) < 3:                                # stage_d.training's loop, three lesson slots
        todo = {c: stage_d.group_ports(x["gate"], x["g"]) for c, x in st.items() if x["g"] < x["ng"]}
        rec = net.drive("lesson", todo, set(todo), dict(stage="D", groups={c: st[c]["g"] for c in todo}))
        for r in rec["reads"]:
            x = st[f"c{r['layer']}_{r['index']}"]
            f = r["emission"] is not None
            x["word"] += "F" if f else "s"
            x["run"] = x["run"] + 1 if f else 0
            x["r"] += 1
            if x["run"] >= calc["hold"] or x["r"] >= calc["max_rounds"]:
                x.update(g=x["g"] + 1, r=0, run=0, word="")
    net.ses.cmd("set filetype=binary")
    net.ses.cmd("write replay.raw " + " ".join(f"v({v})" for v in net.ses.saved))
    status = "done"
except Exception as e:
    status = f"failed: {e!r}"
finally:
    net.ses.close()
(OUT / "replay.json").write_text(json.dumps(dict(instance=inst, case=CASE, cells=dict(refuted=cells[0], witness=cells[1]),
                                                 times_us=times, deck_sha256=deck_sha, published_deck_sha256=pub_sha,
                                                 deck_identical=deck_sha == pub_sha, status=status, slots=net.slots,
                                                 stage_D_slots=recD["slots"][:3]), indent=1) + "\n")
print(status, deck_sha == pub_sha)
