"""Campaign 6's measure runners (PREDICTION.md 2), as the launch kit starts them. New code; the batch's measurement
code is unchanged and is called under campaign 6's seed guard (c6.guard_seed), never through its own command lines.

  meas6.py cal  STAGE_FILE OUT INSTANCE on|off NGSPICE PDK                batch6.cal: one of campaign 5's calibration decks
  meas6.py scan STAGE_FILE OUT INSTANCE CELL KIND INPUTS NGSPICE PDK      one scan, both-lines check or one-sided set

INSTANCE is the seed ("7801"), or "none-a" / "none-b" for the two nominal instances of the measure rehearsal. Every run
first checks its stage file (safeguard i, c6.stage_check) and then its seed (c6.guard_seed), before any deck.

`scan` reads its doses (and, for a one-sided set, its bound W + h) from INPUTS, a frozen file the stage's manifest
binds by its SHA-256 (inputs6.py writes it from the earlier stages' evidence). It then runs `scan_main`, which is
scan6.main copied verbatim but for its first line (its arguments) and three lines (test_campaign6.Copies shows them):
  - the seed guard is c6.guard_seed (with the checked stage and the run's folder), not batch6.guard_seed;
  - the record's header is c6.run_header (with the stage check and the machine that ran it), not batch6.run_header;
  - after the simulator closes, the run writes noise.sha256, the fingerprint of the deck's transient-noise sources
    (campaign 5's run4.trnoise_fingerprint), which the kit requires of every registered run. New behaviour, declared.
`cal` calls batch6.cal (unchanged) after the stage check and the guard. batch6.cal's record keeps its own `batch` key,
batch6.run_header's development-batch label (machine None for 7801 to 7805), since that code is unchanged; `cal` then
sets the record's `stage` to the stage check (batch6.cal writes None there, as run4 does outside a stage) and adds one
key, `campaign6`, the campaign's header (c6.run_header).
"""
from fractions import Fraction as F
import json
from pathlib import Path
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import c6                                               # noqa: E402  (sets the paths of the batch and of campaign 5)
import batch6                                           # noqa: E402
import c4                                               # noqa: E402
import run4                                             # noqa: E402  (campaign 5, frozen: trnoise_fingerprint)
from scan6 import Driver, MOVING, READS, kinds_of, scan, trip_level, sha     # noqa: E402,F401


def cal(stage_file, out, instance, guard, ngspice, pdk):
    st = c6.stage_check(stage_file)
    seed = c6.guard_seed(c6.seed_text(instance), st["stage"], out)
    assert guard in ("on", "off")
    rec = batch6.cal(Path(out), seed, guard, Path(ngspice), Path(pdk))
    rec["stage"] = st
    rec["campaign6"] = c6.run_header(instance, None, f"cal-{guard}", st, out)
    (Path(out) / "record.json").write_text(json.dumps(rec, indent=1) + "\n")
    return rec


def scan_args(out, instance, cell, kind, inputs, ngspice, pdk):
    """scan_main's arguments from the frozen inputs file: the doses of the instance's cell (V) and, for a one-sided set,
    its bound. Refuses an instance the inputs mark as not to be run (its earlier runs failed)."""
    data = json.loads(Path(inputs).read_text())
    seed_text = c6.seed_text(instance)
    x = data["instances"][instance]
    assert "why_not" not in x, f"refused: {instance} is not to be run in {data['stage']}: {x.get('why_not')}"
    dv = x["D_V"][cell]
    if kind == "bothfire":
        return [out, seed_text, cell, "bothfire", *dv, ngspice, pdk]
    if kind == "onesided":
        b = x["bounds"][cell]
        return [out, seed_text, cell, "onesided", b, b, *dv, ngspice, pdk]
    return [out, seed_text, cell, kind, str(c6.DELTA), *dv, ngspice, pdk]


def scan_main(argv, stage, instance):
    a = sys.argv[1:] if argv is None else argv
    batch6.require_debug()
    began = time.time()
    out, seed_text, cell, kind = Path(a[0]), a[1], a[2], a[3]
    seed = c6.guard_seed(seed_text, stage["stage"], out)
    print(c4.require_pinned())
    assert cell in c4.CELLS, cell
    ev = out / "evidence"
    if kind == "reach":
        assert seed is None, "the reach-only read is for the nominal cell (MAPPING_U.md 5), never a seed of the batch"
        s_target, d1, d2, ngspice, pdk = F(a[4]), a[5], a[6], a[7], a[8]
        D = {"1": d1, "2": d2}
        drv = Driver(ev, seed, cell, MOVING["reach"], {1: d1, 2: d2}, Path(ngspice), Path(pdk))
        ok = True
        try:
            drv.move(s_target)
        except RuntimeError as e:
            ok = False
            res_why = str(e)
        target = drv.target(s_target)
        res = dict(kind="reach", s=str(s_target), reached=ok, target_V={str(p): target[p] for p in (1, 2)},
                   u_V={str(p): drv.u[p] for p in (1, 2)}, decides="nothing (MAPPING_U.md 5)")
        if ok:                                   # one read of port 1 alone there, recorded, as a one-sided set reads
            res["port1_alone_fired"] = bool(drv.slot("read", READS["port1"], s_target=str(s_target), label="reach: port 1 alone"))
        else:
            res["why"] = res_why
    elif kind == "bothfire":
        assert cell == "c", "the both-lines FIRE check is for c"
        d1, d2, ngspice, pdk = a[4:8]
        D = {"1": d1, "2": d2}
        drv = Driver(ev, seed, cell, MOVING["bothfire"], {1: d1, 2: d2}, Path(ngspice), Path(pdk))
        fired = bool(drv.read_at(0, READS["both"], "both lines at the preset"))
        res = dict(kind="bothfire", fired=fired)
    elif kind == "onesided":
        assert cell in ("a", "b"), "a one-sided set is for the ports alone of layer 1"
        s1, s2, d1, d2, ngspice, pdk = a[4:10]
        D = {"1": d1, "2": d2}
        drv = Driver(ev, seed, cell, MOVING["onesided"], {1: d1, 2: d2}, Path(ngspice), Path(pdk))
        order = sorted(((F(s1), 1), (F(s2), 2)))
        res = dict(kind="onesided", bounds={"1": str(F(s1)), "2": str(F(s2))}, silent={})
        for s_value, p in order:
            res["silent"][str(p)] = not drv.read_at(s_value, READS[f"port{p}"], f"one-sided port {p}")
        res["all_silent"] = all(res["silent"].values())
    else:
        assert kind in kinds_of(cell), (cell, kind)
        delta, d1, d2, ngspice, pdk = F(a[4]), a[5], a[6], a[7], a[8]
        D = {"1": d1, "2": d2}
        assert delta in batch6.DELTAS, f"the ascent step is 1/4 (B) or 1/2 (C), not {delta}"
        drv = Driver(ev, seed, cell, MOVING[kind], {1: d1, 2: d2}, Path(ngspice), Path(pdk))
        res = dict(kind=kind, delta=str(delta), **scan(drv, kind, delta))
    tr = drv.close()
    (out / "noise.sha256").write_text(run4.trnoise_fingerprint(tr, c4.CELLS) + "\n")
    if res.get("consistent"):
        res["L"] = trip_level(tr, drv, res)
    (ev / "pdk").unlink()
    rec = dict(c6.run_header(instance, cell, kind, stage, out), D_V=D,
               u0_V={str(p): v for p, v in drv.u0.items()}, reads=drv.reads, slots=len(drv.events), result=res,
               files={x: sha(ev / x) for x in ("input.spice", "session.log", "trace.raw")}, wall_s=time.time() - began)
    (ev / "events.json").write_text(json.dumps(drv.events) + "\n")
    rec["files"]["events.json"] = sha(ev / "events.json")
    (out / "record.json").write_text(json.dumps(rec, indent=1) + "\n")
    print(json.dumps(dict(cell=cell, kind=kind, reads=len(drv.reads), wall_s=round(rec["wall_s"]), result={k: v for k, v in res.items() if k != "states"})))
    return rec



def main(argv=None):
    a = sys.argv[1:] if argv is None else argv
    c6.require_debug()
    if a[0] == "cal":
        stage_file, out, instance, guard, ngspice, pdk = a[1:7]
        rec = cal(stage_file, out, instance, guard, ngspice, pdk)
        print(json.dumps(dict(id=rec["id"], reached_its_last_date=rec["reached_its_last_date"], wall_s=round(rec["wall_s"]))))
    elif a[0] == "scan":
        stage_file, out, instance, cell, kind, inputs, ngspice, pdk = a[1:9]
        st = c6.stage_check(stage_file)
        c6.guard_seed(c6.seed_text(instance), st["stage"], out)       # before the inputs are read
        scan_main(scan_args(out, instance, cell, kind, inputs, ngspice, pdk), st, instance)
    else:
        raise SystemExit(__doc__)


if __name__ == "__main__":
    main()
