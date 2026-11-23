"""Each inverter's behaviour in the network (200 ns maximum step) against its stand-alone measure. Development only.

For every slot of a record that drives the front end (lessons and tests; the scans do not use it), per inverter:
whether the input pulse was present, whether the inverter fired, its latch delay (first 0.9 V rise of its latch -
start, tu: the stand-alone lot's "emission") and its routed emission delay (the launch on the router's 0.4 us grid,
the date the Lean front checks).
  absent input -> it must fire, once, with its delay in the front's (emitEarly, emitLate] = config.json timing;
  present input -> it must stay silent.
The stand-alone reference is the instance package's measure of the same design (C5): research/inverter-instances,
lot 2 at reltol 1e-4 (dev_lot_2/RESULT_2.md: emission 0.5033-0.5245 tu over 60 instances, silence and firing 60/60)
and, when pushed, the lot re-measured at this deck's directives (RESULT_LOT2_NETOPTS.md). The network instance is a
different mismatch draw from any stand-alone instance, so the comparison is against the lot's range.

  invcompare.py SPEC OUT     writes OUT/invcompare.json
"""
from fractions import Fraction as F
import json
from pathlib import Path
import statistics
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import measure as measmod  # noqa: E402
import records  # noqa: E402
import spec as specmod  # noqa: E402

CFG = json.loads((HERE / "config.json").read_text())
STANDALONE = dict(source="research/inverter-instances c5c06e00 dev_lot_2/RESULT_2.md (C5, reltol 1e-4, max step 5 ns)",
                  emission_tu=[0.5033, 0.5146, 0.5245], silence="60/60", firing="60/60",
                  dates="(2/5, 13/20] (gate.timing)")


def main(spec_path, out):
    s = specmod.load(spec_path)
    rec = records.load(out)
    meas = measmod.Measure(s, CFG, rec)
    tim = meas.tim
    e, l = tim["emit_early"], tim["emit_late"]
    per = {}
    for sl in meas.slots:
        if not sl.get("inv"):
            continue
        for j, v in enumerate(meas.inverters(sl)):
            p = per.setdefault(f"n{j}", dict(absent=0, fired_when_absent=0, twice=0, present=0, silent_when_present=0,
                                             delays=[], out_of_dates=[]))
            present = v["arrival"] is not None
            if present:
                p["present"] += 1
                p["silent_when_present"] += not v["emissions"]
            else:
                p["absent"] += 1
                if v["emissions"]:
                    p["fired_when_absent"] += 1
                    p["twice"] += len(v["emissions"]) > 1
                    dl = v["emissions"][0] - v["start"]
                    p["delays"].append(dl)
                    p.setdefault("latch", []).append(v["latch"] - v["start"])
                    if not (e < dl <= l):
                        p["out_of_dates"].append(dict(slot=sl.get("kind"), delay=float(dl)))
    res = dict(network=dict(max_step="200n", reltol="1e-5", dates=f"({e}, {l}] (config.json timing)"),
               standalone=STANDALONE, inverters={})
    for n, p in per.items():
        d = [float(x) for x in p.pop("delays")]
        lt = [float(x) for x in p.pop("latch", [])]
        p["routed_delay_tu"] = [min(d), statistics.median(d), max(d)] if d else None
        p["latch_delay_tu"] = [min(lt), statistics.median(lt), max(lt)] if lt else None
        p["latch_delay_spread_tu"] = (max(lt) - min(lt)) if lt else None
        lo, hi = STANDALONE["emission_tu"][0], STANDALONE["emission_tu"][2]
        p["latch_delay_within_standalone_range"] = bool(lt) and lo <= min(lt) and max(lt) <= hi
        p["ok"] = (p["fired_when_absent"] == p["absent"] and p["silent_when_present"] == p["present"]
                   and not p["twice"] and not p["out_of_dates"])
        res["inverters"][n] = p
    (Path(out) / "invcompare.json").write_text(json.dumps(res, indent=1) + "\n")
    print(json.dumps(res, indent=1))
    return all(p["ok"] for p in res["inverters"].values())


if __name__ == "__main__":
    sys.exit(0 if main(sys.argv[1], sys.argv[2]) else 1)
