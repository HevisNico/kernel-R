"""Campaign 6: the frozen inputs of the measure stages M2 and M3 (and of RM2 and RM3), from the collected evidence of the
stages before them. New code. Each file is written by this code alone, pushed before its stage's manifest, and bound by
that manifest's SHA-256; the runners read nothing else.

  inputs6.py M2 OUT.json STAGE_DIR...     the doses of every instance whose two calibration decks count
  inputs6.py M3 OUT.json INPUTS_M2.json STAGE_DIR...   with the bound W + h of each one-sided set (both pair scans consistent)

The rules are the batch's (schedule6.command, BATCH_SPEC.md v10): the doses come from predict6.table and
predict6.doses_V on the two decks, in volts, as `repr(float(mV) / 1000)`; a one-sided set needs both pair scans of its
instance complete with a consistent bracket, and its bound is predict6.layer1_bounds over them (MAPPING_U.md 2). An
instance whose inputs fail is written with `why_not`, and its runs of the stage are not in the manifest (stages6).
"""
from fractions import Fraction as F
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import c6                                               # noqa: E402
import predict6                                         # noqa: E402  (the batch's code, unchanged)


def records(*dirs):
    """Every run record of the kit in the collected stage folders: id -> the kit's record, with the run's folder."""
    out = {}
    for d in dirs:
        for st in Path(d).rglob("STATE.json"):
            for r in json.loads(st.read_text())["records"]:
                out[r["id"]] = dict(r, folder=str(st.parent / r["id"]))
    return out


def complete(rec):
    """A run counts when the kit recorded it complete, its own record exists, and, when the record has the key,
    it reached its last date (a calibration deck or a network run; a scan's record has no such key)."""
    if rec is None or rec.get("status") != "complete":
        return False
    own = Path(rec["folder"]) / "record.json"
    return own.exists() and json.loads(own.read_text()).get("reached_its_last_date", True) is True


def instances(stage):
    """The instances of a measure stage, as `<machine>-<seed>`: the campaign's five, or the nominal cell on each machine."""
    if stage.startswith("RM"):
        return ["a-none", "b-none"]
    return [f"{c6.MACHINE_OF[s]}-{s}" for s in c6.SEEDS]


def m2_inputs(stage, dirs):
    recs = records(*dirs)
    out = {}
    for inst in instances(stage):
        on, off = recs.get(f"{inst}-cal-on"), recs.get(f"{inst}-cal-off")
        if not (complete(on) and complete(off)):
            out[inst] = dict(why_not="a calibration deck did not complete")
            continue
        t, dose, bad = predict6.table(on["folder"], off["folder"])
        if bad:
            out[inst] = dict(why_not="the calibration decks are not usable: " + "; ".join(bad[:3]))
            continue
        D = predict6.doses_V(dose)
        out[inst] = dict(D_V={c: [repr(float(D[(c, p)]) / 1000) for p in (1, 2)] for c in ("a", "b", "c")})
    return dict(stage=stage, instances=out)


def m3_inputs(stage, m2, dirs):
    recs = records(*dirs)
    out = {}
    for inst, x in m2["instances"].items():
        if "why_not" in x:
            out[inst] = dict(why_not=x["why_not"])
            continue
        S, h, why = {}, {}, None
        for c in ("a", "b"):
            r = recs.get(f"{inst}-scan-{c}-pair")
            if not complete(r):
                why = f"the pair scan of {c} did not complete"
                break
            res = json.loads((Path(r["folder"]) / "record.json").read_text())["result"]
            if not res.get("consistent"):
                why = f"the pair scan of {c} has no consistent bracket"
                break
            S[c], h[c] = F(res["s_star"]), F(res["half_bracket"])
        if why:
            out[inst] = dict(why_not=why)
            continue
        b = predict6.layer1_bounds(S, h)
        out[inst] = dict(D_V=x["D_V"], bounds={c: str(b[c]) for c in ("a", "b")})
    return dict(stage=stage, instances=out)


def main(argv=None):
    a = sys.argv[1:] if argv is None else argv
    c6.require_debug()
    if a[0] in ("M2", "RM2"):
        data = m2_inputs(a[0], a[2:])
    elif a[0] in ("M3", "RM3"):
        data = m3_inputs(a[0], json.loads(Path(a[2]).read_text()), a[3:])
    else:
        raise SystemExit(__doc__)
    Path(a[1]).write_text(json.dumps(data, indent=1, sort_keys=True) + "\n")
    print(json.dumps({k: ("why_not" not in v) for k, v in data["instances"].items()}))


if __name__ == "__main__":
    main()
