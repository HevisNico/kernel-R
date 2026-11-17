"""Validation, the extractions: equality with phase 0, V2, V2b, V2c and V2's conditioning check.

  vextract.py OUT.json

The validation's extractions (DEVNOISE_*.json, FULLDECK_*.json, NOCOND_nominal.json of this folder) must give phase
0's results (../phase0/DEVNOISE_*.json, FULLDECK_*.json) to the last digit written: every output, every number, and
the operating-point check. V2, V2b and V2c are those of ../phase0/compare.py on the validation's files. The
conditioning check of V2: with and without the stack-node conductance, the shares of the kept devices of the
nominal cell agree within 0.01 (1 % of the output power), at every output of the four states.
"""
import json, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "phase0"))
import compare                                        # noqa: E402

DEV = ("7101", "7102", "7103")


def same(a, b):
    return json.dumps(a["outputs"], sort_keys=True) == json.dumps(b["outputs"], sort_keys=True) and \
        json.dumps(a["op_match"], sort_keys=True) == json.dumps(b["op_match"], sort_keys=True)


def main(out):
    v = lambda n: json.loads((HERE / n).read_text())
    p = lambda n: json.loads((HERE.parent / "phase0" / n).read_text())
    eq = {n: same(v(n), p(n)) for n in [f"DEVNOISE_{i}.json" for i in ("nominal",) + DEV] + ["FULLDECK_nominal.json", "FULLDECK_7102.json"]}
    V2 = {i: compare.v2(v(f"DEVNOISE_{i}.json")) for i in ("nominal",) + DEV}
    V2b = {i: compare.v2b(v(f"DEVNOISE_{i}.json")) for i in ("nominal",) + DEV}
    V2c = {i: compare.v2c(v(f"DEVNOISE_{i}.json"), v(f"FULLDECK_{i}.json")) for i in ("nominal", "7102")}
    a, b = v("DEVNOISE_nominal.json"), v("NOCOND_nominal.json")
    B = {(o["state"], o["cell"], o.get("port")): o for o in b["outputs"]}
    cond = []
    for o in a["outputs"]:
        if o["state"] not in compare.MODEL_STATES:
            continue
        q = B.get((o["state"], o["cell"], o.get("port")))
        if q is None or q.get("error"):
            cond.append(dict(state=o["state"], cell=o["cell"], port=o.get("port"), pass_=False, why="missing"))
            continue
        sq = {k["device"]: k["share"] for k in q["kept"]}
        d = max(abs(k["share"] - sq.get(k["device"], 0.0)) for k in o["kept"])
        cond.append(dict(state=o["state"], cell=o["cell"], port=o.get("port"), max_share_diff=d, pass_=d <= 0.01))
    res = dict(equal_to_phase0=eq, V2={i: dict(all_pass=r["all_pass"], op_match=r["op_match"], failing=[x for x in r["outputs"] if not x["pass"]]) for i, r in V2.items()},
               V2b={i: dict(all_pass=r["all_pass"], worst=r["worst"]) for i, r in V2b.items()},
               V2c={i: dict(all_pass=r["all_pass"], outputs=len(r["outputs"]),
                            worst=max(max(x.get(k, 0) for k in ("max_rel_A", "max_rel_B", "max_share_diff", "max_rel_rms")) for x in r["outputs"]))
                    for i, r in V2c.items()},
               conditioning=dict(outputs=cond, all_pass=all(c["pass_"] for c in cond)))
    res["pass_"] = dict(equal_to_phase0=all(eq.values()), V2=all(r["all_pass"] for r in V2.values()) and res["conditioning"]["all_pass"],
                        V2b=all(r["all_pass"] for r in V2b.values()), V2c=all(r["all_pass"] for r in V2c.values()))
    Path(out).write_text(json.dumps(res, indent=1) + "\n")
    print(json.dumps(res["pass_"]), json.dumps(eq))


if __name__ == "__main__":
    main(sys.argv[1])
