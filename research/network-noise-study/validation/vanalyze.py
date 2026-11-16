"""Validation: the criteria from the runs of vplan.py (definitions in PROTOCOL.md).

  vanalyze.py WORK OUT.json
"""
import hashlib, json, math, re, statistics, sys
from pathlib import Path
import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import vrun                                  # noqa: E402
from vrun import net, INSTANCES, MODEL_STATES     # noqa: E402

DEV = ("7101", "7102", "7103")
LAGS = (0.36e-3, 2e-3, 5e-3, 10e-3, 19e-3)
READ = 40e-6
DT = 0.2e-6
TOL3, TOL4 = 0.10, {"nominal": (0.10, 0.15, 0.20)}
for _i in DEV:
    TOL4[_i] = (0.20, 0.25, 0.30)


def load(work, name):
    """WORK is one folder or several, separated by ':' (the two machines)."""
    for w in str(work).split(":"):
        p = Path(w) / f"{name}.json"
        if p.exists():
            return json.loads(p.read_text())
    return None


def reference(instance, state, cell, port):
    """(f, S) of an output: the extraction's onoise plus the shot terms; K/f^alpha fitted on 1-10 Hz."""
    ex = json.loads((HERE / f"DEVNOISE_{instance}.json").read_text())
    sh = json.loads((HERE / f"SHOT_{instance}.json").read_text())
    o = next(o for o in ex["outputs"] if o["state"] == state and o["cell"] == cell and o.get("port") == port)
    s = next(s for s in sh["outputs"] if s["state"] == state and s["cell"] == cell and s.get("port") == port)
    f = np.array(o["onoise"]["f"])
    S = np.array(o["onoise"]["total"]) + np.array(s["shot_V2_Hz"])
    m = (f >= 1) & (f <= 10)
    slope, icpt = np.polyfit(np.log(f[m]), np.log(S[m]), 1)
    return f, S, (math.exp(icpt), -slope)


def S_at(ref, x):
    f, S, (K, a) = ref
    x = np.asarray(x, float)
    out = np.exp(np.interp(np.log(np.maximum(x, f[0])), np.log(f), np.log(S)))
    low = x < f[0]
    out[low] = K / x[low] ** a
    return out


def integral(ref, w, lo=1e-9, hi=1e8, n=200001):
    x = np.logspace(math.log10(lo), math.log10(hi), n)
    return float(np.trapezoid(S_at(ref, x) * w(x), x))


def summaries(work, names, out_expr):
    S = []
    for n in names:
        r = load(work, n)
        if r is None or r["aborted"]:
            return None, f"{n} missing or aborted"
        S.append(r["summary"][out_expr])
    return S, None


def v3(work, instance, state, cell, port, names, out_expr):
    """From the per-draw summaries of vrun.summarize (the definitions of PROTOCOL.md)."""
    S, err = summaries(work, names, out_expr)
    if err:
        return dict(error=err), None, None
    N, dt = S[0]["points"], S[0]["dt_s"]
    T = N * dt
    fr = np.fft.rfftfreq(N, dt)
    ref = reference(instance, state, cell, port)
    bands = []
    for k, b in enumerate(S[0]["bands"]):
        lo, hi = b["lo"], b["hi"]
        if lo < 4 / T or hi > 464159.0:
            continue
        m = (fr >= lo) & (fr < hi)
        R = S_at(ref, fr[m]).mean()
        per = np.array([s["bands"][k]["P_mean"] for s in S])
        ratio = float(per.mean() / R)
        se = float(per.std(ddof=1) / math.sqrt(len(per)) / per.mean())
        ok = abs(ratio - 1) <= TOL3 or (hi <= 1000.1 and se > TOL3 and abs(ratio - 1) <= 3 * se)
        bands.append(dict(band_Hz=[lo, hi], ratio=ratio, rel_se=se, pass_=bool(ok)))
    return dict(draws=len(S), T_s=T, bands=bands, pass_=all(b["pass_"] for b in bands)), S, ref


def v4(instance, S, ref, positions):
    tol_d, tol_b, tol_r = TOL4[instance]
    drifts = []
    for lag in LAGS:
        ss = sum(s["drift"][f"{lag:g}"]["sum_sq"] for s in S)
        nn = sum(s["drift"][f"{lag:g}"]["n"] for s in S)
        meas = math.sqrt(ss / nn)
        refv = math.sqrt(integral(ref, lambda f: np.sinc(f * READ) ** 2 * 4 * np.sin(np.pi * f * lag) ** 2, lo=1e-3))
        drifts.append(dict(lag_s=lag, rms_V=meas, reference_V=refv, ratio=meas / refv, pass_=abs(meas / refv - 1) <= tol_d))
    pb = float(np.mean([s["band_25_1000_V2"] for s in S]))
    rb = integral(ref, lambda f: ((f >= 25) & (f <= 1000)).astype(float), lo=20, hi=1100, n=20001)
    T = S[0]["points"] * S[0]["dt_s"]
    means = [s["mean_V"] for s in S]
    diffs = [means[i + 1] - means[i] for i in range(len(means) - 1) if positions[i + 1] - positions[i] == 1]
    meas_r = float(np.sqrt(np.mean(np.square(diffs))))
    w = lambda f: np.sinc(f * T) ** 2 * 4 * np.sin(np.pi * f * 1000.0) ** 2
    ref_r = math.sqrt(integral(ref, w))
    below = math.sqrt(integral(ref, w, hi=1 / T))
    return dict(drifts=drifts, band_25_1000=dict(power_V2=pb, reference_V2=rb, ratio=pb / rb, pass_=abs(pb / rb - 1) <= tol_b),
                between_runs=dict(pairs=len(diffs), rms_V=meas_r, reference_V=ref_r, ratio=meas_r / ref_r,
                                  pass_=abs(meas_r / ref_r - 1) <= tol_r, reference_below_1_over_T_V=below),
                pass_=all(d["pass_"] for d in drifts) and abs(pb / rb - 1) <= tol_b and abs(meas_r / ref_r - 1) <= tol_r)


def hold_names(instance, kind="model"):
    if kind == "model":
        rr = range(1, 33) if instance == "nominal" else range(5, 13)
        return [f"v3_{instance}_hold_r{r}" for r in rr], [r - (1 if instance == "nominal" else 3) for r in rr]
    k = 32 if instance == "nominal" else 8
    return [f"v5_{instance}_hold_inj{j}" for j in range(k)], list(range(k))


def hold_outputs(instance):
    return [("a", 1)] if instance == "nominal" else [(c, p) for c in "ab" for p in net.PORTS]


def drift_only(instance, S, ref):
    r = v4(instance, S, ref, list(range(len(S))))
    r["between_runs"]["note"] = "injected model: consecutive draws, no virtual time"
    return r


def main(work, out):
    res = dict(V3={}, V4={}, V5={}, V6={}, V7={}, V8={}, constants={})
    ok = dict(V3=True, V4=True, V6=True, V7=True, V8=True)
    # V3/V4 hold, and V5's frozen part
    for i in ("nominal",) + DEV:
        for kind in ("model", "injected"):
            names, pos = hold_names(i, kind)
            for c, p in hold_outputs(i):
                key = f"{i} hold {c}{p}"
                r3, S, ref = v3(work, i, "hold", c, p, names, vrun.model.out_expr("hold", c, p))
                if S is None:
                    (res["V3"] if kind == "model" else res["V5"])[key] = r3
                    if kind == "model":
                        ok["V3"] = ok["V4"] = False
                    continue
                if kind == "model":
                    res["V3"][key] = r3
                    res["V4"][key] = v4(i, S, ref, pos)
                    ok["V3"] &= r3["pass_"]
                    ok["V4"] &= res["V4"][key]["pass_"]
                else:
                    res["V5"][key] = dict(spectrum=r3, low_frequency=drift_only(i, S, ref))
    # V3 window, fire, pulse
    from vplan import runs
    groups = {}
    for r in runs():
        if r[0] == "frozen" and r[8] == "model" and r[3] != "hold":
            groups.setdefault((r[2], r[3], r[4], r[5]), []).append(r[1])
    for (i, st, c, p), names in groups.items():
        pp = None if p == "-" else int(p)
        r3, _, _ = v3(work, i, st, c, pp, names, vrun.model.out_expr(st, c, pp))
        res["V3"][f"{i} {st} {c}{p.strip('-')}"] = r3
        ok["V3"] &= bool(r3.get("pass_"))
    # V6
    ex = {i: json.loads((HERE / f"DEVNOISE_{i}.json").read_text()) for i in ("nominal",) + DEV}
    for i in ("nominal",) + DEV:
        z = load(work, f"v6_{i}_zero")
        first = 57 if i == "nominal" else 61
        D = [load(work, f"v6_{i}_r{r}") for r in range(first, first + 32)]
        if z is None or any(d is None for d in D):
            res["V6"][i] = dict(error="missing"); ok["V6"] = False
            continue
        for c in "ab":
            for p in net.PORTS:
                o = next(o for o in ex[i]["outputs"] if o["state"] == "preset" and o["cell"] == c and o.get("port") == p)
                refvar = sum(v ** 2 for v in o["rms_V"].values())
                x = np.array([d["u_V"][f"{c}{p}"] - z["u_V"][f"{c}{p}"] for d in D])
                var = float(np.var(x, ddof=1))
                rr = var / refvar
                pas = abs(rr - 1) <= 0.25
                res["V6"][f"{i} {c}{p}"] = dict(var_V2=var, reference_var_V2=refvar, ratio=rr, pass_=pas,
                                                not_validated_below_0_75=rr < 0.75, aborted=any(d["aborted"] for d in D))
                ok["V6"] &= pas
    # V7, V8, constants
    res["V7"], ok["V7"] = v7(work)
    res["V8"], ok["V8"] = v8(work)
    res["constants"], res["V5"]["constants_injected"] = constants(work, "model"), constants(work, "injected")
    res["verdict_parts"] = ok
    Path(out).write_text(json.dumps(res, indent=1) + "\n")
    print(json.dumps(ok))


def train_result(work, name):
    for w in str(work).split(":"):
        p = Path(w) / name / "result.json"
        if p.exists():
            r = json.loads(p.read_text())
            m = p.parent / "meta.json"
            r["machine"] = json.loads(m.read_text()).get("machine") if m.exists() else None
            return r
    return None


def train_dir(work, name):
    return next(Path(w) / name for w in str(work).split(":") if (Path(w) / name / "result.json").exists())


def pulse(o, port):
    keep = ("date_s", "kind", "fire", "latency", "protected_until_units", "protected_at_start", "step_mV", "error_phase_units")
    r = {k: o[k] for k in keep if k in o}
    r["u_before_mV"], r["u_after_mV"] = o[f"u{port}_before_V"] * 1e3, o[f"u{port}_after_V"] * 1e3
    return r


def as_train(r, name):
    return dict(run=name, ports={f"{c}{p}": [pulse(o, p) for o in r["occurrences"] if (o["cell"], o["port"]) == (c, p)]
                                 for c in "ab" for p in net.PORTS})


def constants(work, kind):
    sys.path.insert(0, str(HERE.parent.parent / "network-circuit" / "phase1"))
    import constants as C
    M = json.loads((HERE.parent.parent / "network-circuit" / "phase1" / "MEASURES.json").read_text())
    out, offsets, squares, count, devs = {}, [], 0.0, 0, []
    for i in DEV:
        q = train_result(work, f"tr_{i}_quiet1")
        names = [f"tr_{i}_r{r}" for r in range(93, 98)] if kind == "model" else [f"tr_{i}_inj{k}" for k in range(5)]
        noisy = [train_result(work, n) for n in names]
        if q is None or any(x is None for x in noisy):
            out[i] = dict(error="missing")
            continue
        I = dict(section="tt_mm", seed=int(i), scans=M["instances"][i]["scans"], quiet_train=as_train(q, "quiet1"),
                 noisy_trains=[as_train(x, n) for x, n in zip(noisy, names)])
        r = C.instance(I)
        out[i] = r
        for pn, pr in r["ports"].items():
            offsets += pr["noise_run_offsets_mV"]
            for run in pr["noisy_trains"]:
                if run["same_word_as_without_noise"]:
                    pass
            devs += [x - pr["dose_mV"] for x in pr["noisy_doses_mV"]]
        # the pooled within-run scatter, as in constants.port: sum of squares over (fires - 1)
        for pn, pr in r["ports"].items():
            here = pr["train_18_quiet"]["slope_per_mV"]
            for x, n in zip(noisy, names):
                lat = [o["latency"] for o in x["occurrences"] if f"{o['cell']}{o['port']}" == pn and o["fire"]]
                run = next(e for e in pr["noisy_trains"] if e["run"] == n)
                if run["same_word_as_without_noise"]:
                    mu = statistics.mean(lat)
                    squares += sum((v - mu) ** 2 for v in lat) / here ** 2
                    count += len(lat) - 1
        out[i] = dict(noise_between_runs_mV=r.get("noise_between_runs_mV"), dose_noise_sd_mV=r["dose_noise_sd_mV"],
                      within_run_per_port_mV={pn: pr.get("noise_within_run_mV") for pn, pr in r["ports"].items()},
                      run_offsets=r["run_offsets"], excluded_trains={pn: sum(not e["same_word_as_without_noise"] for e in pr["noisy_trains"])
                                                                      for pn, pr in r["ports"].items()})
    pooled = dict(between_runs_mV=float(np.sqrt(np.mean(np.square(offsets)))) if offsets else None,
                  within_run_mV=math.sqrt(squares / count) if count else None,
                  per_dose_mV=float(np.sqrt(np.mean(np.square(devs)))) if devs else None,
                  run_offsets=len(offsets), doses=len(devs))
    if kind == "model":
        pooled["campaign_4_uses_mV"] = dict(between=max(pooled["between_runs_mV"] or 0, 0.111),
                                            within=max(pooled["within_run_mV"] or 0, 0.094),
                                            per_dose=max(pooled["per_dose_mV"] or 0, 0.009))
    return dict(per_instance=out, pooled=pooled)


def events(q, z):
    """As ../phase0/zerocheck.py, from the two result.json alone (the runs may be on different machines)."""
    flags = ("cell", "port", "origin", "calendar_date", "id", "delivered", "protected_when_scheduled", "protected_at_start", "fire")
    diff, dv = [], 0.0
    for a, b in zip(q["occurrences"], z["occurrences"]):
        bad = [k for k in a if (k in flags or k.startswith("writes")) and a.get(k) != b.get(k)]
        if bad:
            diff.append(dict(id=a.get("id"), fields=bad))
        for k in a:
            if k.endswith("_V") and isinstance(a[k], (int, float)) and isinstance(b.get(k), (int, float)):
                dv = max(dv, abs(a[k] - b[k]))
    dv = max([dv] + [abs(q["final_u_V"][k] - z["final_u_V"][k]) for k in q["final_u_V"]])
    fq = [(f["cell"], f["during"], f["routed"]) for f in q["fires"]]
    fz = [(f["cell"], f["during"], f["routed"]) for f in z["fires"]]
    ok = len(q["occurrences"]) == len(z["occurrences"]) and not diff and fq == fz and dv <= 1e-6
    return dict(occurrences=[len(q["occurrences"]), len(z["occurrences"])], occurrence_differences=diff, same_fires=fq == fz,
                max_read_voltage_diff_V=dv, passes=ok)


def v7(work):
    sys.path.insert(0, str(HERE.parent / "phase0"))
    import zerocheck
    sys.path.insert(0, str(HERE.parent.parent / "network-circuit" / "phase1"))
    import constants as C
    M = json.loads((HERE.parent.parent / "network-circuit" / "phase1" / "MEASURES.json").read_text())
    res, ok = {}, True
    for i in DEV:
        q1, q2, z = (train_result(work, f"tr_{i}_{k}") for k in ("quiet1", "quiet2", "zero"))
        if None in (q1, q2, z):
            res[i] = dict(error="missing"); ok = False
            continue
        same = q1["raw_sha256"] == q2["raw_sha256"]
        zc = events(q1, z)
        I = dict(section="tt_mm", seed=int(i), scans=M["instances"][i]["scans"], quiet_train=as_train(q1, "quiet1"), noisy_trains=[])
        ports = C.instance(I)["ports"]
        dl, dd = 0.0, 0.0
        for a, b in zip(q1["occurrences"], z["occurrences"]):
            pn = f"{a['cell']}{a['port']}"
            if a["fire"] and b["fire"]:
                dl = max(dl, abs(a["latency"] - b["latency"]) / abs(ports[pn]["train_18_quiet"]["slope_per_mV"]))
            if not a["fire"] and not b["fire"]:
                p = a["port"]
                sa = (a[f"u{p}_after_V"] - a[f"u{p}_before_V"]) * 1e3
                sb = (b[f"u{p}_after_V"] - b[f"u{p}_before_V"]) * 1e3
                dd = max(dd, abs(sa - sb))
        pas = same and zc["passes"] and dl <= 0.005 and dd <= 0.002
        res[i] = dict(quiet_identical=same, zerocheck=zc, machines=[q1.get("machine"), q2.get("machine"), z.get("machine")],
                      max_latency_diff_mV_equivalent=dl, max_dose_diff_mV=dd, pass_=pas)
        ok &= pas
    return res, ok


def op_nodes(text):
    return {m.group(1): m.group(2) for m in re.finditer(r"^(\S+)\s*=\s*(\S+)$", text, re.M)}


def v8(work):
    res, ok = {}, True
    for i in DEV:
        r3, r4, ra, q = (load(work, f"v8_{i}_{k}") for k in ("r3", "r4", "r3again", "quiet"))
        if None in (r3, r4, ra, q):
            res[i] = dict(error="missing"); ok = False
            continue
        o3, o4, oq = op_nodes(r3["op"]), op_nodes(r4["op"]), op_nodes(q["op"])
        common = sorted(set(o3) & set(oq))
        op_same = all(o3[k] == o4[k] == oq[k] for k in common) and len(common) > 100
        rerun = r3["raw_sha256"] == ra["raw_sha256"]
        y3, y4, yq = (np.array(x["y"]) for x in (r3, r4, q))
        L = min(len(y3), len(y4), len(yq))
        corr = [float(np.corrcoef(y3[:L, k] - yq[:L, k], y4[:L, k] - yq[:L, k])[0, 1]) for k in range(y3.shape[1])]
        pas = op_same and rerun and all(abs(c) < 0.1 for c in corr)
        res[i] = dict(op_nodes_compared=len(common), op_identical=op_same, rerun_identical=rerun, correlation=corr, pass_=pas)
        ok &= pas
    return res, ok


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
