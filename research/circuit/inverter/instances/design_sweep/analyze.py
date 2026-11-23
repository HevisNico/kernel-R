import json, sys
from fractions import Fraction as F
from pathlib import Path

D = Path(__file__).resolve().parent
base = json.loads((D / "C0_base.json").read_text())["cell"]


def area(c):
    a = 0.0
    for k, n in (("help_mirror", 2), ("inhib_mirror", 2), ("switch_n", 1), ("switch_p", 1), ("reset_n", 1), ("reset_p", 1)):
        a += n * c[k]["w"] * c[k]["l"]
    return a


def row(n):
    cfg = json.loads((D / f"{n}.json").read_text())
    c = cfg["cell"]
    out = D / f"out_{n}"
    nom = D / f"nom_{n}"
    s = json.loads((out / "SUMMARY.json").read_text())
    res = {"name": n, "k0": s["k_eligible_K0"], "k3": s["k_room_K3"], "n": s["n_started"], "seeds": {}}
    for r in s["rows"]:
        if r["status"] != "ok":
            res["seeds"][r["seed"]] = r["status"]
            continue
        g = json.loads((out / "gates" / f"GATE_{r['seed']}.json").read_text())
        m = json.loads((out / "runs" / str(r["seed"]) / "MEASURE.json").read_text())["measures"]
        sb = g["state_bound"]
        res["seeds"][r["seed"]] = dict(
            SM0=g["margins"]["K0"]["silence_margin"], SM3=g["margins"]["K3"]["silence_margin"],
            FM3=g["margins"]["K3"]["firing_margin"], K0=g["eligible_K0"], K3=g["room_K3"],
            xA=float(F(sb["xAbsent"])), xP=float(F(sb["xPresent"])), lim=float(F(sb["limit"])),
            emit=m["emit_absent_tu"], head=c["vdd_V"] - m["vq_max_present"], etaH=m["etaH"], Q=m["Q"],
            early=float(F(g["measures"]["K0"]["early"])), latch=m["latch_delay_tu"], agree=g["kernel_agrees_with_mirror"])
    ns = json.loads((nom / "SUMMARY.json").read_text())["rows"][0]
    nm = json.loads((nom / "runs" / "1" / "MEASURE.json").read_text())["measures"]
    ng = json.loads((nom / "gates" / "GATE_1.json").read_text())
    unit = c["cq_F"] * c["vunit_V"]
    res["nominal"] = dict(SM0=ng["margins"]["K0"]["silence_margin"], FM0=ng["margins"]["K0"]["firing_margin"],
                          emit=nm["emit_absent_tu"], cmp_delay=nm["comparator_delay_tu"], head=c["vdd_V"] - nm["vq_max_present"],
                          Q=nm["Q"])
    res["cost"] = dict(area_added_um2=area(c) - area(base),
                       help_ref_uA=c["H0"] * unit / c["tu_s"] * 1e6,
                       inhib_ref_uA=c["J0"] * unit / c["tu_s"] * 1e6,
                       inhib_charge_pC_per_slot=c["J0"] * c["tau"] * unit * 1e12,
                       inhib_energy_pJ_per_slot=c["J0"] * c["tau"] * unit * c["vdd_V"] * 1e12)
    return res


names = sys.argv[1:] or ["C0_base", "C1_J44", "C2_tau30", "C3_lvl95", "C4_hm4x8", "C5_hm2x16"]
for n in names:
    try:
        r = row(n)
    except FileNotFoundError as e:
        print(n, "missing", e)
        continue
    sd = {k: v for k, v in r["seeds"].items() if isinstance(v, dict)}
    mn = lambda k: min(v[k] for v in sd.values())
    mx = lambda k: max(v[k] for v in sd.values())
    print(f"\n== {n}: eligible {r['k0']}/{r['n']}, room {r['k3']}/{r['n']}, kernel agrees {sum(v['agree'] for v in sd.values())}/{len(sd)}")
    print(f"   min SM0 {mn('SM0'):.4f}  min SM3 {mn('SM3'):.4f}  min FM3 {mn('FM3'):.4f}  max xAbsent {mx('xA'):.4f} (lim {mx('lim'):.3f})  "
          f"emit {mn('emit'):.4f}-{mx('emit'):.4f}  min headroom {mn('head'):.3f} V")
    for s, v in sd.items():
        print(f"   {s}: SM0 {v['SM0']:+.4f} SM3 {v['SM3']:+.4f} FM3 {v['FM3']:.4f} xA {v['xA']:.4f} etaH {v['etaH']:.4f} Q {v['Q']:.4f} "
              f"emit {v['emit']:.4f} interval ({0.3 + v['early'] + v['latch']:.3f}, {0.6 + v['latch']:.3f}] K0 {v['K0']} K3 {v['K3']}")
    nm = r["nominal"]
    print(f"   nominal: SM0 {nm['SM0']:.4f} FM0 {nm['FM0']:.4f} emit {nm['emit']:.4f} cmp delay {nm['cmp_delay']:.5f} headroom {nm['head']:.3f} V Q {nm['Q']:.4f}")
    print("   cost:", {k: round(v, 4) for k, v in r["cost"].items()})
