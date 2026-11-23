"""Loading an instrumented record, with one rule applied (development only).

Same-edge rule: a "second rise" of a protection latch less than `same_edge_ns` (calibration.json, 1 us) after its
first rise is the same rising edge crossing 0.9 V twice, not a second emission. It is dropped, and every drop is
listed in rec["same_edge_drops"]. In the records of 2026-11-23 it occurs once per ANDOR3 run, with a gap of 0 ns
(rounded); the next real FIRE of a latch cannot come before its protection ends (several time units).
New runs re-measure the second rise from 1 us after the first (instrument.CalNetwork.slot), so the rule is a no-op
on them.
"""
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
CAL = json.loads((HERE / "calibration.json").read_text())


def clean(rec):
    gap = CAL.get("same_edge_ns", 1000)
    drops = []
    for i, sl in enumerate(rec["slots"]):
        for r in sl.get("reads", []):
            if r.get("second") is not None and r.get("latch") is not None and r["second"] - r["latch"] < gap:
                drops.append(dict(slot=i, layer=r["layer"], index=r["index"], latch=r["latch"], second=r["second"]))
                r["second"] = None
        for j, v in enumerate(sl.get("inv", [])):
            if v.get("second") is not None and v.get("latch") is not None and v["second"] - v["latch"] < gap:
                drops.append(dict(slot=i, inverter=j, latch=v["latch"], second=v["second"]))
                v["second"] = None
    rec["same_edge_drops"] = drops
    return rec


def load(outdir):
    return clean(json.loads((Path(outdir) / "record.json").read_text()))
