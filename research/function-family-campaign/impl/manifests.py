"""The family campaign's stage manifests (PREDICTION.md section 7): per machine and stage, the jobs with their limits.
No simulation here; `stage` runs one stage through batch2x.run_wave (dosedev2.many), as B2 and the top-up did.

  manifests.py plan REPO RUNS NGSPICE PDK                    every machine's planned jobs, with place-holders, as JSON
  manifests.py stage MACHINE STAGE REPO RUNS NGSPICE PDK     run stage D, S or O of one machine (RUNS: that machine's folder)

Stage D: the decks (and, on M5, the duplicate). Stage S: the scans and checks, with the doses of the instance's own
decks (the plain deck's for pair scans, c's scans and c's check; the unary deck's for unary scans and preset checks).
Stage O: the one-sided sets of the pair cells, at s*_x + K + h_x with K over the consistent pair scans (TOPUP_RULES
3.5.2, as family_predict.anchors computes it). A job whose input run did not give what it needs is not started and is
listed with the reason. The limits are 10 x ceil(2 x mean / 10) over section 2's means.

The network stages (sections 4 and 7), from PREDICTED.json only:
  manifests.py network PREDICTED.json                         Q, N1, N2, N3 per machine (campaign) or R-N (rehearsal)
Q: each eligible instance's run without noise and each member's untrained run; Nk: the noisy runs of round k. Every run
is on the machine that measured its instance. One run only per (instance, kind, round), kind quiet, noisy or untrained;
in the campaign an instance is its seed, so that is one run per (seed, kind, round). The rehearsal's runs must be
exactly campaign_predict.rehearsal_runs' placement. The limits and the run command are place-holders: the limits come
from the rehearsal's amendment, the command from family_net.py once frozen; `network_stage` refuses to start a job
whose limit is not a number, or a stage that was already started.
"""
from fractions import Fraction as F
import json
from pathlib import Path
import sys

import campaign_common as CC

ME = Path(__file__).resolve().parent / "campaign_measure.py"


def job(repo, runs, machine, stage, rid, kind, seed, args, ngspice, pdk, folder=None):
    out = Path(runs) / (folder or rid)
    return dict(id=rid, kind=kind, machine=machine, stage=stage, seed=seed, limit_s=CC.limit_s(kind), expected_s=CC.MEANS[kind],
                argv=[sys.executable, "-B", str(ME), kind, str(repo), str(out), str(seed), *[str(a) for a in args], str(ngspice), str(pdk)])


def stage_D(repo, runs, machine, ngspice, pdk):
    d = CC.draw()
    jobs = [job(repo, runs, machine, "D", rid, kind, s, [], ngspice, pdk)
            for s in CC.MACHINES[machine] for rid, kind, st in CC.measure_runs(s, d[s]) if st == "D"]
    if machine == CC.DUPLICATE["machine"]:
        jobs.append(job(repo, runs, machine, "D", CC.DUPLICATE["dup"].split("/")[-1], "cal-on-unary", CC.DUPLICATE["seed"], [], ngspice, pdk,
                        folder=CC.DUPLICATE["dup"]))
    return jobs, []


def stage_S(repo, runs, machine, ngspice, pdk, doses_plain, doses_unary):
    """doses_plain: {seed: {cell: (D1, D2)}} from the plain decks (None if not usable); doses_unary: {seed: {a|b: (D1, D2)}}."""
    d = CC.draw()
    jobs, not_started = [], []
    for s in CC.MACHINES[machine]:
        for rid, kind, st in CC.measure_runs(s, d[s]):
            if st != "S":
                continue
            tail = rid.split("-", 1)[1]
            unary = kind in ("unary-scan", "preset")
            D = (doses_unary if unary else doses_plain).get(s)
            if D is None:
                not_started.append(dict(id=rid, why=f"the {'unary' if unary else 'plain'} decks of {s} gave no doses"))
                continue
            if kind == "pair":
                c = tail.split("-")[1]
                args = [c, *D[c]]
            elif kind == "line":
                args = [tail[-1], *D["c"]]
            elif kind == "bothfire":
                args = [*D["c"]]
            elif kind == "unary-scan":
                c, p = tail[-2], tail[-1]
                args = [c, p, *D[c]]
            else:
                c = tail[-1]
                args = [c, *D[c]]
            jobs.append(job(repo, runs, machine, "S", rid, kind, s, args, ngspice, pdk))
    return jobs, not_started


def bounds_of(pair):
    """pair: {a|b: scan result or None}. The one-sided bound s*_x + K + h_x of each consistent pair cell, K over the
    consistent pair scans (8 if none), exactly, as strings."""
    ok = {x: r for x, r in pair.items() if r and r.get("crossing") and r.get("consistent")}
    S = {x: F(r["s_star"]) for x, r in ok.items()}
    K = max(max(8 - v, v) for v in S.values()) if S else F(8)
    return {x: str(S[x] + K + F(ok[x]["half_bracket"])) for x in ok}


def stage_O(repo, runs, machine, ngspice, pdk, doses_plain, pair_scans):
    """pair_scans: {seed: {a|b: result or None}}."""
    d = CC.draw()
    jobs, not_started = [], []
    for s in CC.MACHINES[machine]:
        for rid, kind, st in CC.measure_runs(s, d[s]):
            if st != "O":
                continue
            c = rid[-1]
            b = bounds_of(pair_scans.get(s, {}))
            D = doses_plain.get(s)
            if c not in b or D is None:
                not_started.append(dict(id=rid, why=f"the pair scan of {c} is not consistent, or the decks gave no doses"))
                continue
            jobs.append(job(repo, runs, machine, "O", rid, kind, s, [c, b[c], *D[c]], ngspice, pdk))
    return jobs, not_started


def plan(repo, runs, ngspice, pdk):
    """Every machine's jobs if every run completes, with place-holders where a value comes from an earlier stage."""
    out = {}
    for m, seeds in CC.MACHINES.items():
        dp = {s: {c: ("<D1>", "<D2>") for c in "abc"} for s in seeds}
        pairs = {s: {x: dict(crossing=True, consistent=True, s_star="2", half_bracket="1/512") for x in "ab"} for s in seeds}
        D, _ = stage_D(repo, runs, m, ngspice, pdk)
        S, _ = stage_S(repo, runs, m, ngspice, pdk, dp, dp)
        O, _ = stage_O(repo, runs, m, ngspice, pdk, dp, pairs)
        for j in O:
            j["argv"][8] = "<bound from its pair scans>"
        out[m] = dict(D=D, S=S, O=O)
    return out


# ------------------------------------------------------------------------------------------------ network stages

NETWORK_STAGES = ("Q", "N1", "N2", "N3")
LIMIT_PLACEHOLDER = "<limit: from the rehearsal's amendment>"
COMMAND_PLACEHOLDER = "<command: family_net.py, once frozen>"
SLOT_FACTOR = dict(X1=0.37, X2=0.47, F4=0.59, F2=0.76, F3=0.73)        # section 4, against F1 [FD 0.6, a guess]
F1_EXPECTED_S = dict(quiet=(689, 1292), noisy=(1179, 2676))             # section 4, F1 at the design point, never measured


def kind_of(r):
    return dict(skew="quiet", untrained="untrained").get(r["control"], "noisy") if r["noise"] == "none" else "noisy"


def network_job(r, x, stage, mode):
    k = kind_of(r)
    exp = [round(v * SLOT_FACTOR[r["member"]]) for v in F1_EXPECTED_S[k]] if k in F1_EXPECTED_S else "not estimated (section 4 gives none)"
    return dict(id=r["id"], stage=stage, machine=r.get("machine"), seed=r["seed"], member=r["member"], kind=k, round=r["round"],
                scenario=r["scenario"], control=r["control"], noise=r["noise"], noise_seed=r.get("noise_seed"),
                needs=x["needs"], unary_ports=x["unary_ports"], Q1=x["Q1"], Q2=x["Q2"],
                expected_s=exp, limit_s=LIMIT_PLACEHOLDER, argv=COMMAND_PLACEHOLDER, mode=mode)


def check_network_runs(predicted):
    """The record's network runs against sections 4 and 7: refuses anything else. Returns the instances by key."""
    import campaign_predict as CP
    mode = predicted["mode"]
    inst = {(x["seed"], x["member"]): x for x in predicted["instances"]}
    runs = predicted["network_runs"]
    keys = [(r["seed"], r["member"], kind_of(r), r["round"]) for r in runs]
    assert len(set(keys)) == len(keys), f"refused: two runs on one (instance, kind, round): {sorted(k for k in keys if keys.count(k) > 1)}"
    assert len({r["id"] for r in runs}) == len(runs), "refused: a run id appears twice"
    for r in runs:
        x = inst.get((r["seed"], r["member"]))
        assert x and x["eligible"], f"refused: {r['id']} is on an instance that is not eligible"
        if r["noise"] != "none":
            assert x["room_K3"], f"refused: noisy run {r['id']} on an instance without room at K = 3"
    if mode == "campaign":
        sk = [(s, k, n) for s, _, k, n in keys]
        assert len(set(sk)) == len(sk), "refused: two runs on one (seed, kind, round)"
        assert all(s in CC.SEEDS for s, *_ in keys), "refused: a seed outside 8501-8515"
        want = CC.network_runs(list(inst.values()))
    else:
        assert mode == "rehearsal" and all(s in CC.REHEARSAL_SEEDS for s, *_ in keys), "refused: not a rehearsal seed"
        want = CP.rehearsal_runs(list(inst.values()))
    assert runs == want, "refused: the record's network runs are not the ones sections 4 and 7 give from its instances"
    for r in runs:
        if r["noise"] != "none":
            ns = CC.noise_seed(r["seed"], r["round"]) if mode == "campaign" else CC.REHEARSAL_NOISE[(r["seed"], r["member"], r["round"])]
            assert r["noise_seed"] == ns, f"refused: {r['id']} has noise seed {r['noise_seed']}, not {ns}"
        if mode == "campaign":
            assert r["machine"] == CC.machine_of(r["seed"]), f"refused: {r['id']} is not on the machine that measured it"
    return inst


def network_plan(predicted):
    """{machine: {stage: [jobs]}} (campaign) or {"rehearsal": {"R-N": [jobs]}}, in seed order then the untrained runs."""
    inst = check_network_runs(predicted)
    mode = predicted["mode"]
    job = lambda r, st: network_job(r, inst[(r["seed"], r["member"])], st, mode)
    runs = predicted["network_runs"]
    if mode == "rehearsal":
        return {"rehearsal": {"R-N": [job(r, "R-N") for r in runs]}}
    out = {m: {st: [] for st in NETWORK_STAGES} for m in CC.MACHINES}
    order = sorted(runs, key=lambda r: (kind_of(r) == "untrained", r["seed"]))
    for r in order:
        st = "Q" if kind_of(r) != "noisy" else f"N{r['round']}"
        out[r["machine"]][st].append(job(r, st))
    ids = [j["id"] for m in out.values() for js in m.values() for j in js]
    assert sorted(ids) == sorted(r["id"] for r in runs) and len(set(ids)) == len(ids)
    return out


def network_stage(predicted, machine, name, runs_dir, limits, launch, status_of):
    """Start one network stage of one machine, once. Refuses: a stage already started (its folder or JOBS file
    exists); a stage whose previous stage has not ended (status_of(runs_dir, stage) -> {run id: status}, the runner's);
    a job whose limit is not a positive number (limits: {run id: s}, from the rehearsal's amendment); a launcher that
    does not fill the command (launch.fills_argv, the frozen network runner's). launch(runs_dir, name, jobs) runs them."""
    assert __debug__, "refused: not with python -O, the guards are asserts"
    plan_ = network_plan(predicted)
    runs_dir = Path(runs_dir)
    stages = ("R-N",) if predicted["mode"] == "rehearsal" else NETWORK_STAGES
    assert name in stages and machine in plan_, (machine, name)
    assert not (runs_dir / name).exists() and not (runs_dir / f"JOBS_{name}.json").exists(), f"refused: stage {name} was already started"
    i = stages.index(name)
    if i:
        st = status_of(runs_dir, stages[i - 1])
        assert st is not None and "running" not in st.values(), f"refused: stage {stages[i - 1]} has not ended"
    assert getattr(launch, "fills_argv", False), "refused: the launcher does not give the command (family_net.py is not frozen)"
    jobs = [dict(j) for j in plan_[machine][name]]
    for j in jobs:
        lim = limits.get(j["id"])
        assert isinstance(lim, (int, float)) and not isinstance(lim, bool) and lim > 0, f"refused: {j['id']} has no limit from the amendment"
        j["limit_s"] = lim
    runs_dir.mkdir(parents=True, exist_ok=True)
    (runs_dir / f"JOBS_{name}.json").write_text(json.dumps(jobs, indent=1) + "\n")
    return launch(runs_dir, name, jobs)


def stage(machine, name, repo, runs, ngspice, pdk):
    """Run one stage of one machine, once (batch2x.run_wave). Stage S needs stage D ended, stage O stage S."""
    assert __debug__, "refused: not with python -O, the guards are asserts"
    import batch2x
    import topup
    topup.paths(repo)
    import dosedev2
    runs = Path(runs)
    dosedev2.outside(repo, runs)
    assert name in CC.STAGES and machine in CC.MACHINES
    assert not (runs / name).exists() and not (runs / f"JOBS_{name}.json").exists(), f"refused: stage {name} was already started"
    if name == "D":
        runs.mkdir(parents=True, exist_ok=True)
        if machine == CC.DUPLICATE["machine"]:
            (runs / CC.DUPLICATE["dup"]).parent.mkdir(exist_ok=True)
        jobs, ns = stage_D(repo, runs, machine, ngspice, pdk)
    else:
        prev = "D" if name == "S" else "S"
        st = batch2x.status_of(runs, prev)
        assert st and "running" not in st.values(), f"refused: stage {prev} has not ended"
        sd = batch2x.status_of(runs, "D")
        dp, du = {}, {}
        for s in CC.MACHINES[machine]:
            if sd.get(f"{s}-cal-on") == "complete" and sd.get(f"{s}-cal-off") == "complete":
                D, _ = batch2x.doses_of(repo, runs / f"{s}-cal-on", runs / f"{s}-cal-off")
                if D is not None:
                    dp[s] = D
            if sd.get(f"{s}-cal-on-unary") == "complete":
                D, bad = topup.doses_from_on(repo, runs / f"{s}-cal-on-unary")
                if D is not None:
                    du[s] = D
        if name == "S":
            jobs, ns = stage_S(repo, runs, machine, ngspice, pdk, dp, du)
        else:
            ss = batch2x.status_of(runs, "S")
            rec = lambda rid: json.loads((runs / rid / "record.json").read_text())["result"] if ss.get(rid) == "complete" else None
            pairs = {s: {x: rec(f"{s}-scan-{x}-pair") for x in "ab"} for s in CC.MACHINES[machine]}
            jobs, ns = stage_O(repo, runs, machine, ngspice, pdk, dp, pairs)
    (runs / f"NOT_STARTED_{name}.json").write_text(json.dumps(ns, indent=1) + "\n")
    return batch2x.run_wave(runs, name, jobs)


if __name__ == "__main__":
    a = sys.argv[1:]
    if a and a[0] == "plan":
        print(json.dumps(plan(*a[1:5]), indent=1))
    elif a and a[0] == "network":
        print(json.dumps(network_plan(json.loads(Path(a[1]).read_text())), indent=1))
    elif a and a[0] == "stage":
        print(json.dumps(stage(*a[1:7])))
    else:
        raise SystemExit(__doc__)
