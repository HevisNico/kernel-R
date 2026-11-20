"""Development only: G4 of DOSE_PLAN.md, "the scans are clean", judged on one set of measures of the nominal cell.
No simulation: it reads the runs' records and the guard-on deck's trace.

  g4.py REPO LABEL CAL_ON_DIR OUT.json NAME=RUN_DIR ...

NAME is one of: scan-a-pair, scan-b-pair, scan-c-line1, scan-c-line2, bothfire-c, onesided-a, onesided-b, and any
further onesided-<cell>-<tag> (reported apart, as exploratory). CAL_ON_DIR is the guard-on calibration deck of the
same cell at the same dose.

G4, as written: four consistent brackets of 1/256 stage, none contradictory after the majority; ceil(s*) equals the
deck's first firing stage, four of four; each scan's u(0) within 20 uV of the deck's; single ports silent at their
bound; both lines fire at the preset.
"""
from fractions import Fraction as F
import json
import math
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import dosedev

U0_TOL_V = F(20, 10 ** 6)
KIND = {"scan-a-pair": ("a", "both"), "scan-b-pair": ("b", "both"), "scan-c-line1": ("c", "port 1"), "scan-c-line2": ("c", "port 2")}


def judge(repo, label, cal_on, runs):
    dosedev.repo_paths(repo)
    import measure
    import reads4
    cal_on = Path(cal_on)
    rec = json.loads((cal_on / "record.json").read_text())
    result = json.loads((cal_on / "evidence" / "result.json").read_text())
    rows = reads4.calibration_reads(measure.Trace(cal_on / "evidence" / "trace.raw"), result, rec["reads"])
    by = {(r["cell"], r["stage"], r["read"]): r for r in rows}
    deck_u0 = {(c, p): F(by[(c, 0, "empty")]["ports"][str(p)]["u_before_mV"]) / 1000 for c in "abc" for p in (1, 2)}
    first = {name: next((k for k in range(8) if by[(c, k, read)]["fire"]), None) for name, (c, read) in KIND.items()}
    out = dict(label=label, guard_on_deck=str(cal_on.name), first_firing_stage_of_the_deck=first, scans={}, checks={}, exploratory={})

    def record(name):
        d = runs.get(name)
        if d is None or not (Path(d) / "record.json").exists():
            return None
        return json.loads((Path(d) / "record.json").read_text())

    def u0(name, r):
        c = name.split("-")[1]
        diffs = {p: float(F(r["u0_V"][str(p)]) - deck_u0[(c, p)]) * 1e6 for p in (1, 2)}
        return diffs, all(abs(F(r["u0_V"][str(p)]) - deck_u0[(c, p)]) <= U0_TOL_V for p in (1, 2))

    ok_brackets, ok_q1, ok_u0 = True, True, True
    for name in KIND:
        r = record(name)
        if r is None:
            out["scans"][name] = dict(missing=True)
            ok_brackets = ok_q1 = ok_u0 = False
            continue
        res = r["result"]
        diffs, within = u0(name, r)
        s = F(res["s_star"]) if res.get("consistent") else None
        x = dict(consistent=bool(res.get("consistent")), contradictory=res.get("contradictory"), why=res.get("why"),
                 s_star=None if s is None else str(s), s_star_float=None if s is None else float(s),
                 half_bracket=res.get("half_bracket"), bracket=res.get("bracket"),
                 ceil_s_star=None if s is None else math.ceil(s), first_firing_stage_of_the_deck=first[name],
                 u0_minus_deck_uV=diffs, u0_within_20uV=within, reads=len(r["reads"]), wall_s=r["wall_s"], delta=res.get("delta"))
        x["bracket_is_1_256"] = x["consistent"] and F(res["half_bracket"]) == F(1, 256)
        x["bracket_no_wider_than_1_256"] = x["consistent"] and F(res["half_bracket"]) <= F(1, 256)
        x["bracket_width_uV"] = None if not x["consistent"] else float(2 * F(res["half_bracket"]) * max(F(v) for v in r["D_V"].values()) * 10 ** 6)
        x["repeats_and_states"] = dict(reads_fired=sum(1 for y in r["reads"] if y.get("fire")), reads_silent=sum(1 for y in r["reads"] if y.get("fire") is False))
        x["need_agrees"] = s is not None and math.ceil(s) == first[name]
        ok_brackets = ok_brackets and x["consistent"] and x["bracket_is_1_256"] and not x["contradictory"]
        ok_q1 = ok_q1 and x["need_agrees"]
        ok_u0 = ok_u0 and within
        out["scans"][name] = x
    out["checks"]["four consistent brackets of 1/256 stage, none contradictory"] = ok_brackets
    out["beside_the_letter"] = {"four consistent brackets no wider than 1/256 stage, none contradictory":
                                all(v.get("consistent") and v.get("bracket_no_wider_than_1_256") and not v.get("contradictory") for v in out["scans"].values())}
    out["checks"]["ceil(s*) equals the deck's first firing stage, four of four"] = ok_q1
    r = record("bothfire-c")
    bf = None if r is None else dict(fired=bool(r["result"].get("fired")), u0=u0("bothfire-c", r), wall_s=r["wall_s"])
    out["bothfire"] = bf
    out["checks"]["both lines fire at the preset"] = bool(bf and bf["fired"])
    ok_u0 = ok_u0 and bool(bf and bf["u0"][1])
    ones, ok_ones = {}, True
    for name, d in runs.items():
        if not name.startswith("onesided-"):
            continue
        r = record(name)
        x = dict(missing=True) if r is None else dict(bounds=r["result"]["bounds"], silent=r["result"]["silent"], all_silent=r["result"]["all_silent"],
                                                       u0=u0(name, r), wall_s=r["wall_s"],
                                                       bound_float={p: float(F(v)) for p, v in r["result"]["bounds"].items()})
        if name in ("onesided-a", "onesided-b"):
            ones[name] = x
            ok_ones = ok_ones and not x.get("missing") and x["all_silent"]
            ok_u0 = ok_u0 and not x.get("missing") and x["u0"][1]
        else:
            out["exploratory"][name] = x
    out["onesided"] = ones
    out["checks"]["single ports silent at their bound"] = ok_ones and len(ones) == 2
    out["checks"]["each run's u(0) within 20 uV of the deck's"] = ok_u0
    out["G4"] = "go" if all(out["checks"].values()) else "stop"
    return out


if __name__ == "__main__":
    a = sys.argv[1:]
    res = judge(a[0], a[1], a[2], dict(x.split("=", 1) for x in a[4:]))
    Path(a[3]).write_text(json.dumps(res, indent=1) + "\n")
    print(json.dumps(dict(label=res["label"], G4=res["G4"], checks=res["checks"], beside_the_letter=res["beside_the_letter"],
                          half_bracket={k: v.get("half_bracket") for k, v in res["scans"].items()},
                          bracket_width_uV={k: v.get("bracket_width_uV") for k, v in res["scans"].items()},
                          contradictory={k: v.get("contradictory") for k, v in res["scans"].items()},
                          u0_uV={k: v.get("u0_minus_deck_uV") for k, v in res["scans"].items()},
                          s_star={k: v.get("s_star_float") for k, v in res["scans"].items()},
                          exploratory={k: (v if v.get("missing") else dict(all_silent=v["all_silent"], bound=v["bound_float"])) for k, v in res["exploratory"].items()}), indent=1))
