"""Phase 0: the cell-by-cell extraction against the full deck (V2c), and V2 on every extraction.

  compare.py OUT.json PERCELL_FULL_PAIRS... -- PERCELL...

PERCELL_FULL_PAIRS are pairs of files `percell.json:fulldeck.json` (the nominal cell and 7102); PERCELL are the other
per-cell extractions (7101, 7103), checked for V2 alone. Tolerances, as fixed in VALIDATION_CRITERIA.md (V2, V2c):
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


def v2(ex):
    """Per output: completed, cover, flatness, logic share. `preset` is for V6 only and is not held to flatness."""
    rows = []
    for o in ex["outputs"]:
        r = dict(state=o["state"], cell=o["cell"], port=o.get("port"), error=o.get("error"))
        if not o.get("error"):
            kept = o["kept"]
            r.update(covered=o["covered"], kept=len(kept),
                     worst_spread=max(max(k["spread_white"], k["spread_flicker"] or 1) for k in kept),
                     logic_share=max([k["share"] for k in kept if any(t in k["device"] for t in LOGIC)] or [0.0]))
            r["pass"] = (r["covered"] >= COVER and r["logic_share"] <= LOGIC_SHARE
                         and (o["state"] == "preset" or r["worst_spread"] <= SPREAD))
        else:
            r["pass"] = False
        rows.append(r)
    om = ex.get("op_match", {})
    op_ok = all(v["max_abs_diff_V"] <= TOL_OP for v in om.values()) if om else None
    return dict(outputs=rows, all_pass=all(r["pass"] for r in rows) and op_ok is not False, op_match=om, op_pass=op_ok)


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
        dA = max((rel(ka[d]["white_A2_Hz"], kb[d]["white_A2_Hz"]) for d in kb if d in ka), default=0)
        dB = max((rel(ka[d]["flicker_B"], kb[d]["flicker_B"]) for d in kb if d in ka and kb[d]["flicker_B"] > 0), default=0)
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
    Path(out).write_text(json.dumps(res, indent=1) + "\n")
    for p, r in res["v2c"].items():
        print("V2c", p, r["all_pass"], [(x["state"], x["cell"], x["port"], round(x.get("max_rel_A", -1), 4), round(x.get("max_rel_rms", -1), 4))
                                         for x in r["outputs"] if not x["pass_"]][:6])
    for p, r in res["v2"].items():
        print("V2", p, r["all_pass"], "op", {c: v["max_abs_diff_V"] for c, v in r["op_match"].items()},
              [(x["state"], x["cell"], x["port"], x.get("error"), x.get("covered"), x.get("worst_spread"), x.get("logic_share"))
               for x in r["outputs"] if not x["pass"]][:8])
