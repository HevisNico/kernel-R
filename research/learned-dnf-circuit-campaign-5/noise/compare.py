"""Phase 0: on extractions of devnoise.py, the cell-by-cell method against the full deck (V2c), V2 and V2b.

  compare.py OUT.json PERCELL_FULL_PAIRS... -- PERCELL...

PERCELL_FULL_PAIRS are pairs of files `percell.json:fulldeck.json` (the nominal cell and 7102; the second from
`devnoise.py extract --full`); PERCELL are the other per-cell extractions (7101, 7103), checked for V2 and V2b alone.
Tolerances, as fixed in VALIDATION_CRITERIA.md (V2, V2b, V2c):
"""
import json, sys
from pathlib import Path

TOL_AB, TOL_SHARE, TOL_RMS, TOL_OP = 0.01, 0.01, 0.01, 1e-6
COVER, SPREAD, LOGIC_SHARE = 0.99, 1.1, 0.01
LOGIC = (".xnad.", ".xiad.", ".xien.", ".xicb.", ".xnsa.", ".xla.", ".xia1.", ".xia2.", ".xnsc.", ".xlc.", ".xid1.",
         ".xid2.", ".xnsb.", ".xlb.", ".xnsi.", ".xisi.", ".xisd.", ".xicm.", ".xnsp.", ".xnrp.", ".xlp.", ".xip1.",
         ".xip2.", ".xi1.", ".xi2.")


def key(o):
    return (o["state"], o["cell"], o.get("port"))


MODEL_STATES = ("hold", "window", "fire", "pulse")       # preset serves V6 only
TOL_STAT = 0.25                                           # V2b


def v2(ex):
    """Per output of the four states of the model: completed, cover, flatness, logic share, and the checks of the
    devnoise method (logic outputs at the rails, no DC failure in the device and AC decks, drain currents of the
    device deck equal to those of `op`: max_rel_id_error <= 1, see devnoise.id_error). `preset` is reported only."""
    rows = []
    for o in ex["outputs"]:
        r = dict(state=o["state"], cell=o["cell"], port=o.get("port"), error=o.get("error"))
        if not o.get("error"):
            kept = [k for k in o["kept"] if k["kind"] != "res"]
            r.update(covered=o["covered"], kept=len(o["kept"]),
                     worst_spread=max([max(k["spread_white"], k["spread_flicker"] or 1) for k in kept] or [1.0]),
                     logic_share=max([k["share"] for k in kept if any(t in k["device"] for t in LOGIC)] or [0.0]),
                     logic_at_rails=o.get("logic_at_rails", True), dc_failures=o.get("device_dc_failures", 0) + o.get("ac_dc_failures", 0),
                     id_error=o.get("max_rel_id_error"))
            r["pass"] = (r["covered"] >= COVER and r["logic_share"] <= LOGIC_SHARE and r["worst_spread"] <= SPREAD
                         and r["logic_at_rails"] and r["dc_failures"] == 0 and (r["id_error"] is None or r["id_error"] <= 1))
        else:
            r["pass"] = False
        rows.append(r)
    om = ex.get("op_match", {})
    op_ok = all(v["max_abs_diff_V"] <= TOL_OP for v in om.values()) if om else None
    model_rows = [r for r in rows if r["state"] in MODEL_STATES]
    return dict(outputs=rows, all_pass=bool(model_rows) and all(r["pass"] for r in model_rows) and op_ok is not False,
                op_match=om, op_pass=op_ok)


def v2b(ex):
    """A device kept in more than one state of the model: its A and B in each state (the same in every output of a
    state, as they are the device's own noise at that state's operating point), max/min - 1 <= TOL_STAT."""
    per = {}
    for o in ex["outputs"]:
        if o.get("error") or o["state"] not in MODEL_STATES:
            continue
        for k in o["kept"]:
            if k["kind"] != "res":
                per.setdefault(k["device"], {})[o["state"]] = (k["white_A2_Hz"], k["flicker_B"])
    rows = []
    for d, st in sorted(per.items()):
        if len(st) < 2:
            continue
        A, B = [v[0] for v in st.values()], [v[1] for v in st.values()]
        dA, dB = max(A) / min(A) - 1, (max(B) / min(B) - 1 if min(B) > 0 else 0.0)
        rows.append(dict(device=d, states=sorted(st), max_rel_A=dA, max_rel_B=dB, pass_=dA <= TOL_STAT and dB <= TOL_STAT))
    return dict(devices=rows, all_pass=all(r["pass_"] for r in rows), worst=max([max(r["max_rel_A"], r["max_rel_B"]) for r in rows] or [0]))


def v2c(per, full):
    P, F = {key(o): o for o in per["outputs"]}, {key(o): o for o in full["outputs"]}
    rows = []
    for k in sorted(F, key=str):
        a, b = P.get(k), F[k]
        r = dict(state=k[0], cell=k[1], port=k[2])
        if a is None or a.get("error") or b.get("error"):
            r.update(pass_=False, why="missing or error")
            rows.append(r)
            continue
        ka, kb = {x["device"]: x for x in a["kept"]}, {x["device"]: x for x in b["kept"]}
        same = set(ka) == set(kb)
        rel = lambda x, y: abs(x - y) / max(abs(y), 1e-300)
        tr = [d for d in kb if d in ka and kb[d]["kind"] != "res"]
        dA = max((rel(ka[d]["white_A2_Hz"], kb[d]["white_A2_Hz"]) for d in tr), default=0)
        dB = max((rel(ka[d]["flicker_B"], kb[d]["flicker_B"]) for d in tr if kb[d]["flicker_B"] > 0), default=0)
        dS = max((abs(ka[d]["share"] - kb[d]["share"]) for d in kb if d in ka), default=0)
        dR = max(rel(a["rms_V"][band], b["rms_V"][band]) for band in b["rms_V"])
        r.update(same_devices=same, max_rel_A=dA, max_rel_B=dB, max_share_diff=dS, max_rel_rms=dR)
        r["pass_"] = same and dA <= TOL_AB and dB <= TOL_AB and dS <= TOL_SHARE and dR <= TOL_RMS
        rows.append(r)
    return dict(outputs=rows, all_pass=all(r["pass_"] for r in rows))


if __name__ == "__main__":
    out = sys.argv[1]
    args = sys.argv[2:]
    i = args.index("--")
    pairs, alone = [a.split(":") for a in args[:i]], args[i + 1:]
    res = dict(tolerances=dict(A_B=TOL_AB, share=TOL_SHARE, rms=TOL_RMS, op_V=TOL_OP, cover=COVER, spread=SPREAD,
                               logic_share=LOGIC_SHARE), v2c={}, v2={})
    for p, f in pairs:
        per, full = json.loads(Path(p).read_text()), json.loads(Path(f).read_text())
        res["v2c"][p] = v2c(per, full)
        res["v2"][p] = v2(per)
        res["v2"][f] = v2(full)
    for p in alone:
        res["v2"][p] = v2(json.loads(Path(p).read_text()))
    res["v2b"] = {p: v2b(json.loads(Path(p).read_text())) for p, _ in pairs}
    res["v2b"].update({p: v2b(json.loads(Path(p).read_text())) for p in alone})
    res["tolerances"]["stationarity"] = TOL_STAT
    Path(out).write_text(json.dumps(res, indent=1) + "\n")
    for p, r in res["v2c"].items():
        print("V2c", p, r["all_pass"], [(x["state"], x["cell"], x["port"], round(x.get("max_rel_A", -1), 4), round(x.get("max_rel_rms", -1), 4))
                                         for x in r["outputs"] if not x["pass_"]][:6])
    for p, r in res["v2b"].items():
        print("V2b", p, r["all_pass"], round(r["worst"], 4), [(x["device"], x["states"], round(x["max_rel_A"], 3), round(x["max_rel_B"], 3))
                                                         for x in r["devices"] if not x["pass_"]][:6])
    for p, r in res["v2"].items():
        print("V2", p, r["all_pass"], "op", {c: v["max_abs_diff_V"] for c, v in r["op_match"].items()},
              [(x["state"], x["cell"], x["port"], x.get("error"), x.get("covered"), x.get("worst_spread"), x.get("logic_share"), x.get("logic_at_rails"), x.get("dc_failures"), x.get("id_error"))
               for x in r["outputs"] if not x["pass"]][:8])
