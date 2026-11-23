"""Development only: family_predict.py tested on B2's existing records and on the smoke, before it reads any top-up
file (TOPUP_RULES.md 3.5.11). No simulation is run.

  check_on_b2.py REPO GEN B2_DIR SMOKE_DIR OUT_DIR [--no-lean]

1. F1 on B2's ten instances, by the general path, against the frozen chain of B2's report (predict6.predict_instance
   under predict6_guard, then t1_gate.one_port, then the generator's legacy.spec_of): the spec must be equal field
   for field; the measured flag must agree; the mirror's verdicts and the frozen room model's (gate4.verdicts) are
   both reported, and B2's report's one-port verdicts beside them.
2. X2 and F2 on B2's ten: the prediction, the mirror, and the kernel.
3. The smoke on 8303 (port 1 of a and of b at 1.0, guard-on deck only, used for both decks): X1, F4 and F3 with
   B2's 8303 for the rest, as a dry run. The smoke has no port-2 reads; the test reads only port 1 (UNARY_READ
   narrowed for this test).
4. The synthetic chains of test_family_predict.py, one gate file per member, through the kernel.
Writes OUT_DIR/CHECK_ON_B2.json and the Lean files and logs.
"""
from fractions import Fraction as F
import json
import os
from pathlib import Path
import sys
import time
from unittest import mock

import family_predict as FP


def frozen_F1(seed, b2_dir, st):
    """The frozen chain of batch2x_report.one_instance for one instance: (x, y, t2) or (x, None, None)."""
    import predict6
    import predict6_guard
    import t1_gate
    rec = lambda d: json.loads((Path(d) / "record.json").read_text())
    scans, ones, bf = {}, {}, None
    for c, kind in predict6.CROSSINGS:
        if st.get(f"{seed}-scan-{c}-{kind}") == "complete":
            r = rec(b2_dir / f"{seed}-scan-{c}-{kind}")
            scans[(c, kind)] = dict(r["result"], u0_V=r["u0_V"])
    for c in "ab":
        if st.get(f"{seed}-onesided-{c}") == "complete":
            r = rec(b2_dir / f"{seed}-onesided-{c}")
            ones[c] = dict(r["result"], u0_V=r["u0_V"])
    if st.get(f"{seed}-bothfire-c") == "complete":
        r = rec(b2_dir / f"{seed}-bothfire-c")
        bf = dict(r["result"], u0_V=r["u0_V"])
    status = {k: v for k, v in st.items() if k.startswith(f"{seed}-")}
    on, off = b2_dir / f"{seed}-cal-on", b2_dir / f"{seed}-cal-off"
    with mock.patch.object(predict6.P, "instance", predict6_guard.guarded_instance):
        x = predict6.predict_instance(seed, "dev", status, on, off, scans, ones, bf)
    if "budgets" not in x:
        return x, None, None
    t, dose, _ = predict6.table(on, off)
    w = predict6.deck_w(on, predict6.doses_V(dose))
    t2 = predict6.mapped(t, w, predict6.anchors({k: F(scans[k]["s_star"]) for k in predict6.CROSSINGS}))
    y, _ = t1_gate.one_port(x, t2)
    return x, y, t2


def report_verdicts(prep):
    p = Path(prep) / "research" / "learned-dnf-circuit-campaign-7-prep" / "dev" / "batch2x" / "report" / "BATCH2X_REPORT.json"
    if not p.exists():
        return {}
    r = json.loads(p.read_text())
    return {str(i["seed"]): dict(one_port=i.get("one_port", {}).get("verdicts"), frozen=i.get("frozen", {}).get("verdicts"),
                                 one_port_room_at_K3=i.get("one_port", {}).get("room_at_K3")) for i in r["instances"]}


def main():
    repo, gen, b2_dir, smoke, out = sys.argv[1], sys.argv[2], Path(sys.argv[3]), Path(sys.argv[4]), Path(sys.argv[5])
    do_lean = "--no-lean" not in sys.argv
    FP.paths(repo, gen)
    predict6, P, spec, mirror, emit = FP.mods()
    import gate4
    import legacy
    out.mkdir(parents=True, exist_ok=True)
    lean = os.environ.get("LEAN", "lean")
    build = out / "build"
    st = FP.statuses(b2_dir)
    prep = Path(os.environ.get("PREP", "/home/user/owner-prep/wt/campaign-7-prep"))
    rep = report_verdicts(prep)
    res = dict(F1=[], X2_F2=[], smoke=None, synthetic=[], started=time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()))
    rows = []
    for seed in FP.SEEDS:
        t0 = time.time()
        row = FP.one_seed(seed, ["F1", "X2", "F2"], b2_dir, [], st, {})
        x = row["members"]["F1"]
        fx, fy, ft2 = frozen_F1(seed, b2_dir, st)
        e = dict(seed=seed, measured_mine=bool(x["measured"]), measured_frozen=bool(fx.get("measured")),
                 why_mine=x.get("why_not_measured", [])[:3], why_frozen=(fx.get("why_not_measured") or fx.get("why_not_eligible") or [])[:3])
        if fy is not None and x["measured"] and x.get("observation"):
            ref = legacy.spec_of(dict(fy, tag=f"F1_{seed}"), "B2", Path(repo) / "research" / "learned-dnf-circuit-campaign-5")
            mine = FP.raw_spec(x, f"F1_{seed}", "B2")
            e["spec_fields_equal"] = {k: ref[k] == mine[k] for k in ref if k not in ("lean", "verdicts", "inputs")}
            e["spec_equal"] = all(e["spec_fields_equal"].values())
            e["t2_equal"] = all(ft2[k] == v for k, v in x["t2"].items())
            e["frozen_room_model_one_port"] = gate4.verdicts(fy)
            e["report"] = rep.get(str(seed))
            # byte for byte: my spec in gate4 style against B2's report's Gate_<seed>_oneport.lean (predict6.gate_file)
            src = "the development batch's predictions (campaign 6)"
            v = gate4.verdicts(fy)
            s4 = spec.load(dict(mine, tag=str(seed), verdicts={K: v[K] for K in ("K0", "K3")},
                                lean=dict(style="gate4", namespace=legacy.GATE4_NAMESPACE, source=src, derive=True)))
            text = emit.lean_file([s4], {(str(seed), K): v[K] for K in ("K0", "K3")}, src)
            g = prep / "research" / "learned-dnf-circuit-campaign-7-prep" / "dev" / "batch2x" / "report" / f"Gate_{seed}_oneport.lean"
            e["gate4_file_byte_equal_to_B2_report"] = g.exists() and g.read_text() == text
        elif fy is not None or (x["measured"] and x.get("observation")):
            e["spec_equal"] = False
            e["why"] = "one path predicts and the other does not"
        e["wall_s"] = round(time.time() - t0, 1)
        res["F1"].append(e)
        rows.append(row)
        print(seed, "F1 spec equal:", e.get("spec_equal"), "measured", e["measured_mine"], e["measured_frozen"], flush=True)
    FP.gate_all(rows, out, gen, lean, build, do_lean)
    for row, e in zip(rows, res["F1"]):
        x = row["members"]["F1"]
        e["mirror"] = {K: v["checks"] for K, v in x.get("mirror", {}).items()}
        e["kernel"] = x.get("gate", {}).get("kernel")
        for m in ("X2", "F2"):
            y = row["members"][m]
            res["X2_F2"].append(dict(seed=row["seed"], member=m, measured=y["measured"], why=y.get("why_not_measured", [])[:3],
                                     needs=y.get("needs"), anchors=y.get("anchors"), Q=(y.get("Q1"), y.get("Q2")),
                                     mirror={K: dict(checks=v["checks"], failing=v["failing"][:6]) for K, v in y.get("mirror", {}).items()},
                                     kernel=y.get("gate", {}).get("kernel"), kernel_agrees_with_mirror=y.get("gate", {}).get("kernel_agrees_with_mirror"),
                                     room_K3=y.get("room_K3")))
            if m == "F2" and y.get("measured") and x.get("measured"):
                res["X2_F2"][-1]["same_K_d_as_F1"] = (y["anchors"]["K"], y["anchors"]["d"]) == (x["anchors"]["K"], x["anchors"]["d"])
    # --- the smoke, as a dry run of X1, F4 and F3 on port 1
    seed = 8303
    rec = lambda d: json.loads((Path(d) / "record.json").read_text())
    with mock.patch.object(FP, "UNARY_READ", {1: "port 1 at 1.0"}):
        tu = FP.source(smoke / "8303-cal-on-unary", smoke / "8303-cal-on-unary", unary=True)
        b2 = FP.source(b2_dir / f"{seed}-cal-on", b2_dir / f"{seed}-cal-off")
        b2_runs = FP.b2_inputs(seed, b2_dir, st)
        un, tu_runs = {}, {}
        for c in ("a", "b"):
            r = rec(smoke / f"8303-unary-scan-{c}")
            sc = dict(r["result"], u0_V=r["u0_V"])
            r = rec(smoke / f"8303-preset-{c}")
            pre = dict(r["result"], u0_V=r["u0_V"])
            port, det = FP.unary_port({1: sc, 2: None}, pre)
            un[c] = dict(port=port, detail=det)
            tu_runs[(c, "unary")], tu_runs[(c, "preset")] = sc, pre
        srow = dict(seed=seed, unary={c: v["detail"] for c, v in un.items()}, members={})
        for member in ("X1", "F4", "F3"):
            kd = FP.kinds(member)
            uport = {c: un[c]["port"] for c, k in kd.items() if k == "unary"}
            st_b2 = {i: st.get(i, "missing") for i in FP.b2_run_ids(seed, member)}
            st_tu = {i: "complete" for i in FP.tu_run_ids(seed, member, uport)}
            x, why = FP.predict(member, seed, dict(b2, status=st_b2), b2_runs, dict(tu, status=st_tu), tu_runs, uport)
            x["why_not_measured"] = why
            srow["members"][member] = x
    sdir = out / "smoke"
    sdir.mkdir(exist_ok=True)
    FP.gate_all([srow], sdir, gen, lean, build, do_lean)
    res["smoke"] = dict(unary=srow["unary"], members={m: dict(measured=x["measured"], why=x.get("why_not_measured", [])[:3], needs=x.get("needs"),
                                                            anchors=x.get("anchors"), Q=(x.get("Q1"), x.get("Q2")), budgets_K3=x.get("budgets", {}).get("K3"),
                                                            mirror={K: dict(checks=v["checks"], failing=v["failing"][:6]) for K, v in x.get("mirror", {}).items()},
                                                            kernel=x.get("gate", {}).get("kernel"), kernel_agrees_with_mirror=x.get("gate", {}).get("kernel_agrees_with_mirror"))
                                                  for m, x in srow["members"].items()})
    # --- the synthetic chains, through the kernel
    sys.argv[1:] = [repo, gen]
    import test_family_predict as T
    ydir = out / "synthetic"
    ydir.mkdir(exist_ok=True)
    for member in FP.STEP1:
        up = {"a": 1, "b": 2}
        x, _ = T.Synthetic("chain").chain(member, up)
        s = spec.load(FP.raw_spec(x, f"Syn_{member}", "synthetic"))
        mv = FP.mirror_verdicts(s)
        g = FP.lean_gate(s, mv, ydir, gen, lean, build) if do_lean else None
        res["synthetic"].append(dict(member=member, mirror={K: v["checks"] for K, v in mv.items()}, kernel=g and g["kernel"],
                                     kernel_agrees_with_mirror=g and g.get("kernel_agrees_with_mirror")))
    res["finished"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    (out / "CHECK_ON_B2.json").write_text(json.dumps(res, indent=1, default=str) + "\n")
    print(json.dumps(dict(F1_spec_equal=[e.get("spec_equal") for e in res["F1"]], smoke={m: v["kernel"] for m, v in res["smoke"]["members"].items()},
                          synthetic={e["member"]: e["kernel"] for e in res["synthetic"]}), default=str))


if __name__ == "__main__":
    main()
