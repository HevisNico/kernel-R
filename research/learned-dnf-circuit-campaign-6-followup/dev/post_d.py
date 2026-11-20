"""Development only: four descriptive analyses after step D of DOSE_PLAN.md. POST-HOC: every one was asked for after
G6 was read ("unclear"); none of them changes that verdict. No simulation: it reads analysis/G6.json (written by the
frozen g6.py), the runs' records and waveforms, and the measures of the nominal cell at each dose.

  post_d.py REPO CONFIG.json G6.json OUT.json

CONFIG.json: {"doses": {LABEL: {"cal_on", "cal_off", "quiet", "noisy": [...], "scans": {"a-pair", "b-pair", "c-line1",
"c-line2"}, "onesided": {"a", "b"}, "bothfire"}}}: folders.

A1. Influence. w, b (campaign 3's definition, the secant, all kinds, as G6) with one run left out, for each of the 8
    runs of each dose; and the ratios 2x / 1x with run 5200006 left out of 2x. That run was singled out AFTER the data
    were seen (its line-1 row has the largest `within`).
A2. Uncertainty. Bootstrap by run: the 8 runs of each dose drawn with replacement, 10 000 draws, random.Random(1), the
    1x draw before the 2x draw; the ratio 2x / 1x of w, b, d on each draw; the 95 % percentile interval is
    (sorted[250], sorted[9749]).
A3. Expected FIRE-bit differences, as the audit's test (noise_audit.m5, NOISE_AUDIT.md 4.8 and 5.4): if the margin of a
    firing read at the trained state moved by a Gaussian of sigma = sqrt(b^2 + w^2), each read would lose its FIRE with
    probability Phi(-(n - s*) D / sigma). Per dose, with the dose's own b and w of the kind's group (pairs, lines), its
    own doses D and its own scans' s*. Against the FIRE bits seen to differ.
A4. What the frozen budget gives. Campaign 6's prediction of one instance, by its frozen functions (predict6.table,
    deck_w, measure_instance, campaign 5's predicted.instance, predict6.augmented), on the nominal cell's measures at
    each dose, with three sets of constants: decision 5's (0.111 / 0.094 / 0.009 mV), the ones G6 just read at that
    dose (rounded to 0.0001 mV), and, at 2x only, the same with the measure term H of each cell raised to 0.030 mV of
    stored voltage (H is the scan's half bracket in score units, predict6.measure_instance; 0.030 mV / D stages in
    its place when that is larger). Budgets are given in stages: for a and b the budget over twice the guarded dose
    (the pair moves both ports), for c over the guarded dose (one line). The margins are the crossing's place in its
    step: below = s* - (n - 1), above = n - s*.
    The budget itself (research/learned-dnf-circuit-campaign-5/predicted.py, lines 220 to 230, and 268 to 280):
      K = 3: eps + ceil(sum over the read's ports of 3 s sqrt(w^2 + b^2 + n d^2));  K = 0: eps + ceil(0.030 mV x sum of s);
      a, b: training = max over k <= need of the two-port budget at k writes; testing = the same at the need;
      c: training = max over lines and k of the ONE-port budget; testing = the TWO-port budget at (n1, n2);
    and campaign 6 adds H_x + S_x to each (research/learned-dnf-circuit-campaign-6/batch/predict6.py, lines 213 to 221).
    Room is predicted.room (lines 298 to 334), called by predict6.augmented.
"""
from fractions import Fraction as F
import json
import math
from pathlib import Path
import random
import statistics
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import dosedev2

SINGLED_OUT = "none-2x-noisy-5200006"
DRAWS, SEED = 10000, 1
ALLOWANCE_MV = F("0.030")
KEY_OF_SCAN = {"a": ("a", "pair"), "b": ("b", "pair"), "c1": ("c", "line1"), "c2": ("c", "line2")}


def rms(xs):
    xs = list(xs)
    return math.sqrt(sum(x * x for x in xs) / len(xs)) if xs else None


def dose_moves(modules, cfg):
    """Per noisy run, the dose moves minus the quiet run's, on the reads where both runs write the port once and the
    FIRE bits agree: the same rule as g6.py (the total is checked against G6.json below)."""
    measure, plans4, reads4 = modules

    def rows_of(d):
        d = Path(d)
        rec = json.loads((d / "record.json").read_text())
        plan, slots = plans4.network(tuple(rec["needs"]), rec["control"])
        result = json.loads((d / "evidence" / "result.json").read_text())
        return rec, reads4.network_reads(measure.Trace(d / "evidence" / "trace.raw"), result, slots)

    qrec, qrows = rows_of(cfg["quiet"])
    qby = {r["slot"]: r for r in qrows}
    out = {}
    for d in cfg["noisy"]:
        rec, rows = rows_of(d)
        mine = []
        for x in rows:
            q = qby[x["slot"]]
            for c, r in x["reads"].items():
                qr = q["reads"].get(c)
                if qr is None or r["fire"] != qr["fire"]:
                    continue
                for p in ("1", "2"):
                    if r["ports"][p]["writes"] == 1 and qr["ports"][p]["writes"] == 1:
                        mine.append(r["ports"][p]["move_mV"] - qr["ports"][p]["move_mV"])
        out[rec["id"]] = mine
    return out


def constants(rows, d_by_run, runs, which=("a", "b", "c1", "c2")):
    """w, b, d over the given runs (a list, a run may be there more than once): the rms over their rows and moves."""
    by = {}
    for r in rows:
        if r["kind"] in which:
            by.setdefault(r["run"], []).append(r)
    mine = [r for run in runs for r in by.get(run, [])]
    return dict(rows=len(mine), w_mV=rms(r["within_sd_mV"] for r in mine), b_mV=rms(r["offset_mV"] for r in mine),
                w_mV_three_points=rms(r["within_sd_mV_three_points"] for r in mine), b_mV_three_points=rms(r["offset_mV_three_points"] for r in mine),
                w_units=rms(r["within_sd_units"] for r in mine), b_units=rms(r["offset_units"] for r in mine),
                w_stages=rms(r["within_sd_stages"] for r in mine), b_stages=rms(r["offset_stages"] for r in mine),
                d_mV=rms(v for run in runs for v in d_by_run[run]))


def ratios(one, two):
    return {k: (two[k] / one[k] if one[k] and two[k] is not None else None) for k in one if k != "rows"}


def frozen_prediction(label, cfg, sets):
    """A4: the frozen prediction of the nominal cell at one dose, once per set of constants. sets: {name: (const, measure
    term in mV or None)}."""
    import c4
    import predict6
    P = predict6.P
    rec = lambda d: json.loads((Path(d) / "record.json").read_text())
    scans = {}
    for name, d in cfg["scans"].items():
        c, kind = name.split("-")
        r = rec(d)
        scans[(c, kind)] = dict(r["result"], u0_V=r["u0_V"])
    ones = {c: dict(rec(d)["result"], u0_V=rec(d)["u0_V"]) for c, d in cfg["onesided"].items()}
    bf = dict(rec(cfg["bothfire"])["result"], u0_V=rec(cfg["bothfire"])["u0_V"])
    on, off = cfg["cal_on"], cfg["cal_off"]
    t, dose, bad = predict6.table(on, off)
    D = predict6.doses_V(dose)
    w = predict6.deck_w(on, D) if not bad else None
    statuses = {f"{label}-{k}": "complete" for k in ["cal-on", "cal-off", "bothfire-c", *[f"scan-{n}" for n in cfg["scans"]], *[f"onesided-{c}" for c in ones]]}
    why, data = predict6.measure_instance(label, statuses, t, dose, bad, scans, ones, predict6.deck_u0(on), bf, w)
    out = dict(measured=not why, why_not_measured=why, D_mV={f"{c}{p}": float(v) for (c, p), v in D.items()})
    if why:
        return out
    S = {k: F(scans[v]["s_star"]) for k, v in KEY_OF_SCAN.items()}
    margins = {k: dict(s_star=float(s), n=math.ceil(s), below_stages=float(s - (math.ceil(s) - 1)), above_stages=float(math.ceil(s) - s)) for k, s in S.items()}
    out.update(margins=margins, H=data["H"], anchors=data["anchors"], half_bracket=data["half_bracket"])
    out["sets"] = {}
    for name, (const, term_mV) in sets.items():
        H = dict(data["H"])
        if term_mV is not None:
            an = dict(d=data["anchors"]["d"], d_c=data["anchors"]["d_c"])
            H30 = dict(a=math.ceil(F(str(term_mV)) / min(D[("a", 1)], D[("a", 2)]) * 2 * an["d"]), b=math.ceil(F(str(term_mV)) / min(D[("b", 1)], D[("b", 2)]) * 2 * an["d"]),
                       c=max(math.ceil(F(str(term_mV)) / D[("c", p)] * an["d_c"]) for p in (1, 2)))
            H = {c: max(H[c], H30[c]) for c in H}
        try:
            x = predict6.augmented(P.instance(label, data["t2"], dose, [], const), H, data["S"], data["t2"])
        except Exception as e:                               # campaign 6 counts an instance on which this raises as not eligible
            out["sets"][name] = dict(raised=repr(e))
            continue
        g = x["guarded"]["dose"]
        res = dict(constants=const, measure_term_mV=term_mV, H_used=H, needs=x["needs"], eligible_K0=x["eligible"], room_at_K3=x["room_at_K3"],
                   counts_N_out=x["counts_N_out"], without_room_K3={c: v["without_room"] for c, v in x["room"]["K3"].items()},
                   without_room_K0={c: v["without_room"] for c, v in x["room"]["K0"].items()},
                   guarded_dose=g, epsilon=x["epsilon"], cells={})
        for K in ("K0", "K3"):
            for c in ("a", "b"):
                tr, te = (float(F(x["budgets"][K][c][s], 2 * g[c])) for s in ("training", "testing"))
                m = margins[c]
                res["cells"].setdefault(c, {})[K] = dict(training_stages=tr, testing_stages=te, below_minus_training=m["below_stages"] - tr,
                                                         above_minus_training=m["above_stages"] - tr, above_minus_testing=m["above_stages"] - te,
                                                         training_plus_testing=tr + te)
            tr, te = (float(F(x["budgets"][K]["c"][s], g["c"])) for s in ("training", "testing"))
            res["cells"].setdefault("c", {})[K] = dict(
                training_stages=tr, testing_stages=te, training_plus_testing=tr + te,
                lines={p: dict(below_minus_training=margins[f"c{p}"]["below_stages"] - tr, above_minus_training=margins[f"c{p}"]["above_stages"] - tr,
                               above_minus_testing=margins[f"c{p}"]["above_stages"] - te) for p in ("1", "2")})
        out["sets"][name] = res
    return out


if __name__ == "__main__":
    repo, config, g6_path, dest = sys.argv[1:5]
    dosedev2.repo_paths(repo)
    import c4
    import measure
    import plans4
    import reads4
    cfg = json.loads(Path(config).read_text())["doses"]
    g6 = json.loads(Path(g6_path).read_text())
    assert g6["G6"]["G6"] == "unclear", "this script describes the G6 that was read; it does not judge"
    res = dict(what="post-hoc, descriptive; asked for after G6 was read; changes no verdict", G6_as_read=g6["G6"]["G6"])

    rows = {l: g6[l]["campaign_3"]["rows"] for l in ("1x", "2x")}
    runs = {l: [r["id"] for r in g6[l]["runs"]] for l in ("1x", "2x")}
    d_by = {l: dose_moves((measure, plans4, reads4), cfg[l]) for l in ("1x", "2x")}
    full = {l: constants(rows[l], d_by[l], runs[l]) for l in ("1x", "2x")}
    for l in ("1x", "2x"):                                   # the same figures as the frozen reader, or stop
        a = g6[l]["campaign_3"]["all"]
        assert full[l]["rows"] == a["port_runs"] == 32 and len(runs[l]) == 8
        for k, ref in (("w_mV", a["w_mV"]), ("b_mV", a["b_mV"]), ("d_mV", g6[l]["d_mV"]["rms"]), ("w_stages", a["w_stages"])):
            assert abs(full[l][k] - ref) <= 1e-12 * abs(ref), (l, k, full[l][k], ref)
        assert sum(len(v) for v in d_by[l].values()) == g6[l]["d_mV"]["n"]

    # A1
    loo = {l: {run: constants(rows[l], d_by[l], [r for r in runs[l] if r != run]) for run in runs[l]} for l in ("1x", "2x")}
    without = constants(rows["2x"], d_by["2x"], [r for r in runs["2x"] if r != SINGLED_OUT])
    res["A1_influence"] = dict(
        all_runs={l: full[l] for l in full}, ratios_all_runs=ratios(full["1x"], full["2x"]),
        one_run_left_out={l: {run: {k: v[k] for k in ("w_mV", "b_mV", "d_mV")} for run, v in loo[l].items()} for l in loo},
        range_one_run_left_out={l: {k: [min(v[k] for v in loo[l].values()), max(v[k] for v in loo[l].values())] for k in ("w_mV", "b_mV", "d_mV")} for l in loo},
        singled_out_after_the_data=SINGLED_OUT, at_2x_without_it=without, ratios_without_it=ratios(full["1x"], without),
        lines_only=dict(all_runs={l: constants(rows[l], d_by[l], runs[l], ("c1", "c2")) for l in full},
                        at_2x_without_it=constants(rows["2x"], d_by["2x"], [r for r in runs["2x"] if r != SINGLED_OUT], ("c1", "c2"))),
        pairs_only=dict(all_runs={l: constants(rows[l], d_by[l], runs[l], ("a", "b")) for l in full}))
    res["A1_influence"]["lines_only"]["ratios_all_runs"] = ratios(*[res["A1_influence"]["lines_only"]["all_runs"][l] for l in ("1x", "2x")])
    res["A1_influence"]["lines_only"]["ratios_without_it"] = ratios(res["A1_influence"]["lines_only"]["all_runs"]["1x"], res["A1_influence"]["lines_only"]["at_2x_without_it"])
    res["A1_influence"]["pairs_only"]["ratios_all_runs"] = ratios(*[res["A1_influence"]["pairs_only"]["all_runs"][l] for l in ("1x", "2x")])

    # A2
    rng = random.Random(SEED)
    cuts = {"all": ("a", "b", "c1", "c2"), "pairs": ("a", "b"), "lines": ("c1", "c2")}
    draws = {name: [] for name in cuts}
    for _ in range(DRAWS):
        one, two = rng.choices(runs["1x"], k=8), rng.choices(runs["2x"], k=8)
        for name, which in cuts.items():
            draws[name].append(ratios(constants(rows["1x"], d_by["1x"], one, which), constants(rows["2x"], d_by["2x"], two, which)))
    res["A2_bootstrap_by_run"] = dict(draws=DRAWS, seed=SEED, interval="95 % percentile: (sorted[250], sorted[9749])")
    for name in cuts:
        ks = ("w_mV", "b_mV", "d_mV", "w_mV_three_points", "b_mV_three_points", "w_units", "b_units", "w_stages", "b_stages")
        res["A2_bootstrap_by_run"][name] = {}
        for k in ks:
            xs = sorted(d[k] for d in draws[name])
            res["A2_bootstrap_by_run"][name][k] = dict(low=xs[250], high=xs[9749], median=statistics.median(xs),
                                                       share_of_draws_above_1=sum(1 for v in xs if v > 1) / DRAWS, share_of_draws_above_1_60=sum(1 for v in xs if v > 1.6) / DRAWS,
                                                       share_of_draws_within_25_percent=sum(1 for v in xs if abs(v - 1) <= 0.25) / DRAWS)

    # A4 first (A3 uses its margins)
    measured = {l: {k: round(full[l][f"{n}_mV"], 4) for k, n in (("within_mV", "w"), ("between_mV", "b"), ("per_dose_mV", "d"))} for l in ("1x", "2x")}
    res["A4_frozen_budget"] = dict(constants_read_at_each_dose=measured)
    for l in ("1x", "2x"):
        sets = {"decision 5's constants": (dict(c4.DECISION5), None), "the constants read at this dose": (measured[l], None)}
        if l == "2x":
            sets["the constants read at this dose, measure term 0.030 mV"] = (measured[l], "0.030")
        res["A4_frozen_budget"][l] = frozen_prediction(l, cfg[l], sets)

    # A3
    phi = lambda z: 0.5 * math.erfc(z / math.sqrt(2))
    res["A3_expected_fire_bit_differences"] = {}
    for l in ("1x", "2x"):
        m = res["A4_frozen_budget"][l].get("margins")
        if not m:
            res["A3_expected_fire_bit_differences"][l] = "no margins: the measures did not pass"
            continue
        tests = {}
        for name, bk, wk in (("secant", "b_mV", "w_mV"), ("three points", "b_mV_three_points", "w_mV_three_points")):
            total, n, parts = 0.0, 0, {}
            for kind in ("a", "b", "c1", "c2"):
                group = g6[l]["campaign_3"]["pair" if kind in "ab" else "line"]
                sig = math.sqrt(group[bk] ** 2 + group[wk] ** 2)
                Dk = g6[l]["slopes"][kind]["dose_mV"]
                k = sum(r["fires"] for r in rows[l] if r["kind"] == kind)
                z = m[kind]["above_stages"] / (sig / Dk)
                parts[kind] = dict(firing_reads=k, above_stages=m[kind]["above_stages"], sigma_mV=sig, sigma_stages=sig / Dk, z=z, expected=k * phi(z))
                total += k * phi(z)
                n += k
            tests[name] = dict(firing_reads=n, expected_to_differ=total, seen=len(g6[l]["fire_bits_that_differ_from_quiet"]), by_kind=parts)
        res["A3_expected_fire_bit_differences"][l] = tests

    Path(dest).write_text(json.dumps(res, indent=1, default=str) + "\n")
    print(json.dumps({k: v for k, v in res.items() if k != "A1_influence"}, indent=1, default=str))
