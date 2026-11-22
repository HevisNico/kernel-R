"""The family campaign's prediction record (PREDICTION.md sections 3, 4 and 8): the frozen family_predict.py
(00b6a516…), called through its library functions on the campaign's instances, its Lean gates checked by the
generator's gencheck.sh, and PREDICTED.json written with what the network runner and the analysis read. New code;
family_predict.py is imported, never changed (its `main` loops over B2's seeds only and is not used).

  campaign_predict.py campaign REPO GEN RUNS_PARENT OUT [--no-lean]     RUNS_PARENT/M1 .. M6: the machines' RUNS folders
  campaign_predict.py rehearsal REPO GEN B2_DIR TOPUP_DIRS OUT [--no-lean]   8303 and 8306, all five members (section 7)

Per instance: measured and why not; the unary ports and the port rule's detail; needs, Q1, Q2; the kernel's K0 and K3
verdicts and the mirror's; eligible = measured and the kernel's K0; room_K3 = eligible and the kernel's K3; the
observation; and the predicted words and outputs, read off the observation (no other model).
"""
import hashlib
import json
import os
from pathlib import Path
import sys

import campaign_common as CC


def stage_statuses(run_dir):
    """{run id: status} from a campaign machine's stage states (D, S, O; DUP is not a measure of any prediction)."""
    out = {}
    for st in CC.STAGES:
        p = Path(run_dir) / st / "STATE.json"
        if p.exists():
            out.update({k: v["status"] for k, v in json.loads(p.read_text())["runs"].items()})
    return out


def ports_of(member, uport):
    """The learning ports: each pair cell's two ports, each unary cell's chosen port, each selected line of c."""
    kd = CC.KINDS[member]
    out = []
    for c, k in kd.items():
        out += [f"{c}1", f"{c}2"] if k == "pair" else [f"{c}{uport[c]}"]
    out += [f"c{p}" for p in range(1, len(kd) + 1)]
    return out


def predicted_words(member, uport, obs):
    """The words and outputs the observation predicts (s: a silent written read, F: a FIRE), in reads4.words' form:
    layer-1 ports over the training rounds, each line of c over its teaching slots, outputs on each test pattern,
    and every skew slot's pair cell silent."""
    import family_predict as FP
    cells = list(CC.KINDS[member])
    letter = lambda r: "F" if r["emissions"] else "s"
    words = {}
    for i, c in enumerate(cells):
        w = "".join(letter(row[i]) for row in obs["firstTrain"])
        for p in ports_of(member, uport):
            if p[0] == c:
                words[p] = w
    lines = [a for _ in range(len(obs["secondTrain"]) // len(cells)) for a in range(len(cells))]
    for a, c in enumerate(cells):
        words[f"c{FP.LINE_PORT[c]}"] = "".join(letter(obs["secondTrain"][m]) for m, b in enumerate(lines) if b == a)
    tests = {k: {**{c: bool(row[i]["emissions"]) for i, c in enumerate(cells)}, "c": bool(obs["secondTest"][k]["emissions"])}
             for k, row in obs["firstTest"].items()}
    terms = FP.MEMBERS[member]["terms"]
    skew = {"".join(terms[c]): {c: False} for c in cells if len(terms[c]) == 2}
    return dict(words=words, tests=tests, skew=skew)


def record(row, member, machine):
    x = row["members"][member]
    g = x.get("gate") or {}
    k = g.get("kernel")
    rec = dict(seed=row["seed"], member=member, machine=machine, measured=bool(x.get("measured")),
               why_not_measured=x.get("why_not_measured", []), unary=row.get("unary"), unary_ports=x.get("unary_ports", {}),
               needs=x.get("needs"), Q1=x.get("Q1"), Q2=x.get("Q2"), eligible_needs=x.get("eligible_needs", True),
               mirror={K: dict(checks=v["checks"], failing=v["failing"]) for K, v in x.get("mirror", {}).items()},
               kernel=k, kernel_agrees_with_mirror=g.get("kernel_agrees_with_mirror"),
               spec_refused=x.get("spec_refused"), why_no_observation=x.get("why_no_observation"))
    rec["eligible"] = bool(rec["measured"] and x.get("observation") and k and k["K0"])
    rec["room_K3"] = bool(rec["eligible"] and k["K3"])
    for f in ("anchors", "guarded", "epsilon", "budgets", "H", "question_1", "observation"):
        rec[f] = x.get(f)
    if x.get("observation"):
        rec["predicted"] = predicted_words(member, rec["unary_ports"], x["observation"])
    return rec


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def write(out, mode, instances, runs, gen):
    import family_predict as FP
    import c4
    res = dict(what=f"the family campaign's prediction record ({mode}), written by campaign_predict.py; no network run exists when it is written",
               mode=mode, family_predict_sha256=sha(FP.__file__), draw_sha256=sha(CC.CAMPAIGN / "DRAW.json"),
               generator=str(gen), constants={k: c4.DECISION5[k] for k in c4.DECISION5}, instances=instances, network_runs=runs)
    Path(out).mkdir(parents=True, exist_ok=True)
    (Path(out) / "PREDICTED.json").write_text(CC.record_text(res))
    return res


def campaign(repo, gen, runs_parent, out, do_lean=True, lean="lean"):
    import family_predict as FP
    FP.paths(repo, gen)
    d = CC.draw()
    rows, where = [], {}
    for m, seeds in CC.MACHINES.items():
        rd = Path(runs_parent) / m
        st = stage_statuses(rd)
        for s in seeds:
            rows.append(FP.one_seed(s, [d[s]], rd, [rd], st, st))
            where[s] = m
    FP.gate_all(rows, out, gen, lean, Path(out) / "build", do_lean)
    inst = [record(r, d[r["seed"]], where[r["seed"]]) for r in rows]
    return write(out, "campaign", inst, CC.network_runs(inst), gen)


def rehearsal_runs(instances):
    """Section 7's R-N on 8303 and 8306 [reading of this code: which instance carries each member's run without
    noise and untrained run is not fixed by section 7; they go where its noisy run is: X1, X2 and F2 on 8303, F4 and
    F3 on 8306]. A run is listed only if its (instance, member) is eligible; a noisy run only if it has room."""
    home = dict(X1=8303, X2=8303, F2=8303, F4=8306, F3=8306)
    el = {(x["seed"], x["member"]): x for x in instances}
    runs = []
    for m, s in home.items():
        x = el.get((s, m))
        if x and x["eligible"]:
            runs.append(dict(id=f"{s}-{m}-quiet", seed=s, member=m, scenario="quiet", control="skew", noise="none", round=0))
            runs.append(dict(id=f"{s}-{m}-untrained", seed=s, member=m, scenario="untrained", control="untrained", noise="none", round=0))
    for (s, m, n), ns in sorted(CC.REHEARSAL_NOISE.items()):
        x = el.get((s, m))
        if x and x["room_K3"]:
            runs.append(dict(id=f"{s}-{m}-r{n}", seed=s, member=m, scenario=f"r{n}", control=None, noise="injected", round=n, noise_seed=ns))
    return runs


def rehearsal(repo, gen, b2_dir, tdirs, out, do_lean=True, lean="lean"):
    import family_predict as FP
    FP.paths(repo, gen)
    st_b2, st_tu = FP.statuses(b2_dir), FP.statuses(*tdirs)
    rows = [FP.one_seed(s, list(CC.MEMBERS), b2_dir, tdirs, st_b2, st_tu) for s in CC.REHEARSAL_SEEDS]
    FP.gate_all(rows, out, gen, lean, Path(out) / "build", do_lean)
    inst = [record(r, m, None) for r in rows for m in CC.MEMBERS]
    return write(out, "rehearsal", inst, rehearsal_runs(inst), gen)


if __name__ == "__main__":
    assert __debug__, "refused: not with python -O, the guards are asserts"
    a = sys.argv[1:]
    do_lean = "--no-lean" not in a
    a = [x for x in a if x != "--no-lean"]
    lean = os.environ.get("LEAN", "lean")
    if a and a[0] == "campaign":
        r = campaign(a[1], a[2], a[3], a[4], do_lean, lean)
    elif a and a[0] == "rehearsal":
        r = rehearsal(a[1], a[2], Path(a[3]), a[4].split(os.pathsep), a[5], do_lean, lean)
    else:
        raise SystemExit(__doc__)
    print(json.dumps({f"{x['seed']}-{x['member']}": dict(eligible=x["eligible"], room_K3=x["room_K3"]) for x in r["instances"]}))
