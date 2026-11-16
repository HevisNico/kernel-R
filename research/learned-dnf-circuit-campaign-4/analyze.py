"""Campaign 4: the one analysis, after the last stage has ended on both machines. Run once.

  analyze.py RESULTS.json MEASURES_DIR_A MEASURES_DIR_B RUNS_DIR_A RUNS_DIR_B [--extractions DIR]

Order (PREDICTION.md, Rules of the analysis): (1) PREDICTED.json must be what predicted.py gives from the evidence of
the measures, or every claim is "not established"; (2) the regeneration check of the samples file of every noisy
run under the device model, before any word, output or score of a noisy run is read; (3) the claims, each with its
own verdict, and the declared comparisons. A run counts when the launcher recorded it complete and its own record
says that it reached its last date; any other is a missing run, never replaced.
"""
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent / "network-circuit"))
import c4                                               # noqa: E402
import measure                                          # noqa: E402
import noisemodel                                       # noqa: E402
import plans4                                           # noqa: E402
import reads4                                           # noqa: E402
from c4 import dnf                                      # noqa: E402

TRUTH = lambda key: dict(a="A" in key and "B" in key, b="C" in key and "D" in key,
                         c=("A" in key and "B" in key) or ("C" in key and "D" in key))


def state_records(*dirs):
    out = {}
    for d in dirs:
        for st in Path(d).rglob("STATE.json"):
            s = json.loads(st.read_text())
            for r in s["records"]:
                out[r["id"]] = dict(r, folder=str(st.parent / r["id"]))
    return out


def counts(rec):
    """A run counts when the launcher recorded it complete and its own record says it reached its last date."""
    if rec is None or rec["status"] != "complete":
        return False
    own = Path(rec["folder"]) / "record.json"
    return own.exists() and json.loads(own.read_text()).get("reached_its_last_date") is True


def rows_of(folder, needs, control):
    plan, slots = plans4.network(tuple(needs), control)
    ev = Path(folder) / "evidence"
    result = json.loads((ev / "result.json").read_text())
    tr = measure.Trace(ev / "trace.raw")
    return reads4.network_reads(tr, result, slots), result


def g_check(rows, noisy):
    """G on one run: every gated read moves no stored voltage by more than 0.01 mV (runs without noise) and raises
    no write and no write'."""
    bad = []
    for x in rows:
        for c, r in x["reads"].items():
            if not r["gated"]:
                continue
            for p, v in r["ports"].items():
                if v["writes"] or v["writes_prime"]:
                    bad.append(dict(slot=x["slot"], cell=c, port=p, writes=v["writes"], writes_prime=v["writes_prime"]))
                if not noisy and abs(v["move_mV"]) > c4.MOVE_BOUND_MV:
                    bad.append(dict(slot=x["slot"], cell=c, port=p, move_mV=v["move_mV"]))
    return bad


def h_check(rows, result):
    """H, observed and reported, never refuting: separation, late FIRE, routing, c's decoder, delivery."""
    out = dict(min_separation_units={}, late_fires=0, arrivals_not_routed=0, skews_above_bound=0, c_fire_outside=0,
               undelivered=sum(1 for o in result["occurrences"] if not o["delivered"]), queued=len(result["still_queued_at_the_horizon"]))
    for c in c4.CELLS:
        d = sorted({round(o["date_s"], 12) for o in result["occurrences"] if o["delivered"] and o["cell"] == c})
        gaps = [(b - a) / reads4.TU for a, b in zip(d, d[1:]) if (b - a) / reads4.TU > 3]
        out["min_separation_units"][c] = min(gaps) if gaps else None
    fires = {(f["cell"], round(f["date_s"], 12)) for f in result["fires"]}
    for x in rows:
        for c, r in x["reads"].items():
            out["late_fires"] += r["late_fires"]
        r = x["reads"].get("c")
        if r:
            for a in r["arrivals"]:
                src = "a" if a["port"] == 1 else "b"
                ok = a["fire_date_s"] is not None and (src, round(a["fire_date_s"], 12)) in fires and \
                    abs((a["date_s"] - a["fire_date_s"]) / reads4.TU - c4.WIRE) <= c4.SNAP + 1e-9
                out["arrivals_not_routed"] += not ok
            out["skews_above_bound"] += r["skew_units"] > c4.SKEW_C + 1e-9
            if r["fire"] and r["fire_date_s"] < max(a["date_s"] for a in r["arrivals"]):
                out["c_fire_outside"] += 1
    return out


def word_claims(w, z, x):
    """L1, L2, T of one run without noise against the predictions of an eligible instance."""
    bad = []
    for port in ("a1", "a2", "b1", "b2", "c1", "c2"):
        want = z["words"][port[0] if port[0] != "c" else port]
        if w["words"][port] != want:
            bad.append(dict(port=port, word=w["words"][port], predicted=want))
    for key, want in z["tests"].items():
        got = w["tests"][key]
        for c in c4.CELLS:
            if got[c] != want[c]:
                bad.append(dict(pattern=key, cell=c, output=got[c], predicted=want[c]))
    return bad


def n_own(word, need):
    """N-own on one port-run: the word, without the slots where the port received no pulse, is need letters s
    followed only by F. None if the port received fewer than need pulses (the port-run does not count)."""
    w = word.replace("-", "")
    if len(w) < need:
        return None
    return w[:need] == "s" * need and set(w[need:]) <= {"F"}


def main():
    out, mA, mB, rA, rB = map(Path, sys.argv[1:6])
    predicted = json.loads((HERE / "PREDICTED.json").read_text())
    before = json.loads((HERE / "BEFORE_M.json").read_text())
    import predicted as P
    res = dict(what="the one analysis of campaign 4; see analyze.py", missing=[], claims={}, comparisons={})
    recs = state_records(mA, mB, rA, rB)
    # (1) PREDICTED.json from the evidence of the measures
    same = True
    for x in predicted["instances"]:
        on, off = (recs.get(f"{c4.machine_of(x['seed'], before['I'])}-{x['seed']}-cal-{g}") for g in ("on", "off"))
        if not (counts(on) and counts(off)):
            same = same and not x["measured"]
            continue
        t, dose, bad = P.table(*P.load(on["folder"], off["folder"]))
        again = P.instance(x["seed"], t, dose, bad, predicted["constants"])
        same = same and json.dumps(again, sort_keys=True, default=str) == json.dumps({k: v for k, v in x.items() if k in again}, sort_keys=True, default=str)
    res["predicted_is_reproduced"] = same
    # (2) the regeneration check, before any word, output or score of a noisy run
    regen = dict(checked=0, dropped=[])
    noisy_ok = {}
    for r in predicted["network_runs"]:
        if r["noise"] == "none":
            continue
        rec = recs.get(r["id"])
        if not counts(rec):
            res["missing"].append(r["id"])
            continue
        own = json.loads((Path(rec["folder"]) / "record.json").read_text())
        if r["noise"] == "device":
            ex = json.loads((HERE.parent.parent / r["extraction"]["path"]).read_text())
            sha = noisemodel.regenerate_sha256(ex, c4.CELLS, own["noise"], Path(rec["folder"]) / "regen")
            regen["checked"] += 1
            if sha != own["noise"]["samples_sha256"]:
                regen["dropped"].append(r["id"])
                continue
        noisy_ok[r["id"]] = rec
    regen["all_fail"] = bool(regen["checked"]) and len(regen["dropped"]) == regen["checked"]
    res["regeneration_check"] = regen
    if not same:
        res["claims"] = {k: "not established" for k in ("primary", "G", "N-out", "N-own", "N-word", "U", "S")}
        Path(out).write_text(json.dumps(res, indent=1) + "\n")
        return
    inst = {x["seed"]: x for x in predicted["instances"]}
    # (3) the claims
    primary, G, H, m2 = [], [], [], []
    quiet = {}
    for r in predicted["network_runs"]:
        if r["noise"] != "none" or r["control"] != "skew":
            continue
        rec = recs.get(r["id"])
        if not counts(rec):
            res["missing"].append(r["id"])
            continue
        rows, result = rows_of(rec["folder"], plan_needs(r), "skew")
        w = reads4.words(rows)
        quiet[r["seed"]] = (rows, w)
        G += [dict(run=r["id"], **b) for b in g_check(rows, False)]
        H.append(dict(run=r["id"], **h_check(rows, result)))
        x = inst[r["seed"]]
        z = x.get("zero_error")
        if x.get("eligible"):
            primary += [dict(instance=r["seed"], **b) for b in word_claims(w, z, x)]
        elif z:
            m2.append(dict(instance=r["seed"], discrepancies=word_claims(w, z, x)))
    elig = [s for s, x in inst.items() if x.get("eligible")]
    counted = [s for s in elig if s in quiet]
    res["claims"]["primary"] = dict(instances=counted, discrepancies=primary,
                                    verdict="not established" if not counted else ("refuted" if primary else "held"))
    nout = {c: dict(output_runs=0, failures=[]) for c in c4.CELLS}
    nown = {p: dict(port_runs=0, not_counted=0, failures=[]) for p in ("a1", "a2", "b1", "b2", "c1", "c2")}
    nword = {p: dict(port_runs=0, failures=[]) for p in nown}
    m1 = []
    for r in predicted["network_runs"]:
        if r["id"] not in noisy_ok:
            continue
        x = inst[r["seed"]]
        rows, result = rows_of(noisy_ok[r["id"]]["folder"], plan_needs(r), None)
        G += [dict(run=r["id"], **b) for b in g_check(rows, True)]
        w = reads4.words(rows)
        for c in c4.CELLS:
            ok = all(w["tests"][k][c] == TRUTH(k)[c] for k in w["tests"])
            if x["counts_N_out"][c]:
                nout[c]["output_runs"] += 1
                if not ok:
                    nout[c]["failures"].append(r["id"])
            else:
                m1.append(dict(run=r["id"], output=c, as_predicted=ok))
        n = x["needs"]
        for port, lp in x["learning_ports"].items():
            need = n[port[0]] if port[0] != "c" else n[port]
            want = x["zero_error"]["words"][port[0] if port[0] != "c" else port]
            if lp["own_room"]:
                v = n_own(w["words"][port], need)
                if v is None:
                    nown[port]["not_counted"] += 1
                else:
                    nown[port]["port_runs"] += 1
                    if not v:
                        nown[port]["failures"].append(r["id"])
            if lp["room_up_to"]:
                nword[port]["port_runs"] += 1
                if w["words"][port] != want:
                    nword[port]["failures"].append(r["id"])
    verdict = lambda runs, fails: "not established" if not runs else ("refuted" if fails else "held")
    res["claims"]["G"] = dict(failures=G, verdict="refuted" if G else "held")
    res["claims"]["N-out"] = {c: dict(v, verdict=verdict(v["output_runs"], v["failures"])) for c, v in nout.items()}
    tot = lambda d, k: sum(v[k] for v in d.values())
    res["claims"]["N-own"] = dict(ports=nown, verdict=verdict(tot(nown, "port_runs"), [f for v in nown.values() for f in v["failures"]]))
    res["claims"]["N-word"] = dict(ports=nword, verdict=verdict(tot(nword, "port_runs"), [f for v in nword.values() for f in v["failures"]]))
    if regen["all_fail"]:
        for k in ("N-out", "N-own", "N-word"):
            res["claims"][k] = "not established: every noisy run failed the regeneration check (a fault of the generator)"
    # controls
    ctl = [r for r in predicted["network_runs"] if r["control"] == "untrained"]
    U = None
    for r in ctl:
        rec = recs.get(r["id"])
        if counts(rec):
            rows, _ = rows_of(rec["folder"], plan_needs(r), "untrained")
            w = reads4.words(rows)
            U = [dict(pattern=k, cell=c) for k, v in w["tests"].items() for c in c4.CELLS if v[c]]
        else:
            res["missing"].append(r["id"])
    res["claims"]["U"] = dict(fires=U, verdict="not established" if U is None else ("refuted" if U else "held"))
    S = [dict(instance=s, pattern=k, cell=c) for s, (rows, w) in quiet.items() for k, v in w["skew"].items() for c in ("a", "b") if v[c]]
    res["claims"]["S"] = dict(fires=S, verdict="not established" if not quiet else ("refuted" if S else "held"))
    res["claims"]["H"] = H
    res["comparisons"] = dict(M1=m1, M2=m2, M5={s: x.get("validation_residual_M5") for s, x in inst.items()})
    Path(out).write_text(json.dumps(res, indent=1) + "\n")


def plan_needs(r):
    return tuple(7 if v is None else v for v in r["needs"])


if __name__ == "__main__":
    main()
