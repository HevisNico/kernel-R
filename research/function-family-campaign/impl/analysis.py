"""The family campaign's analysis adapter (PREDICTION.md sections 5 and 9): the claims, per member and for the
family, from the prediction record and each network run's read words. New code. It decides by section 5's text:
campaign 6's claims (campaign 5's word_claims, n_own and the N/U/S loops, re-expressed per member) with this
campaign's minima. It reads no trace: a run's words come from the trace reader of the network code (reads4.words'
form: {words: {port: str}, tests: {pattern: {cell: bool}}, skew: {pattern: {cell: bool}}}), which is not part of
this file.

  analysis(predicted, runs) -> results       predicted: PREDICTED.json as a dict; runs: {run id: run record}
  run(pushed_text, regenerated, runs) -> results    section 9 first: the reproduction check, then analysis
  analysis.py PREDICTED.json RUNS.json REPO GEN RUNS_PARENT [--no-lean]   regenerates with campaign_predict.campaign

A run record: {counts: bool (launcher complete and reached its last date), words, tests, skew, G: [failures]}, and,
for the declared comparisons and H (comparisons.py), rows, result, words_prime and observation (comparisons.py's
docstring). Ports: a1 a2 b1 b2 for a pair cell, {cell}{p} for a unary cell on its chosen port, c1 c2 for c's lines.
Patterns: "".join(sorted(inputs)), "-" for none.

Section 9's first rule: the prediction record must be exactly what the frozen code gives from the evidence. `run`
compares the pushed PREDICTED.json's raw text with the serialization of the regenerated record (campaign_common.
record_text, the one campaign_predict.write uses), byte for byte. If it differs, every claim is "not established"
and no comparison is computed [reading of this code: a comparison against a record that is not the code's is not
made either]; the first differing line is reported. Nothing of the runs is read in that case.
"""
import json
from pathlib import Path
import sys

import campaign_common as CC

CLAIMS = ("primary", "G", "H", "N-out", "N-own", "N-word", "U", "S")


def n_own(word, need):
    """Campaign 5's n_own: the word without '-' is `need` letters s, then only F; None if fewer than need letters."""
    w = word.replace("-", "")
    if len(w) < need:
        return None
    return w[:need] == "s" * need and set(w[need:]) <= {"F"}


def need_of(x, port):
    return x["needs"][port] if port.startswith("c") else x["needs"][port[0]]


def discrepancies(pred, got):
    """L1, L2 and T (section 5.1): every predicted word and every predicted output, against the run's."""
    bad = []
    for port, want in pred["words"].items():
        if got["words"].get(port) != want:
            bad.append(dict(port=port, word=got["words"].get(port), predicted=want))
    for key, want in pred["tests"].items():
        g = got["tests"].get(key, {})
        for cell, v in want.items():
            if g.get(cell) != v:
                bad.append(dict(pattern=key, cell=cell, output=g.get(cell), predicted=v))
    return bad


def member_verdict(n, failed):
    if failed:
        return "refuted"
    return "established" if n >= 2 else ("held on one instance, not established" if n == 1 else "not established")


def pooled_verdict(instances, failed):
    """N claims (section 5.4): refuted by one failure; established with counted runs from at least N_N = 2 instances
    from at least 2 members; otherwise the wording that says how far it got."""
    members = {m for _, m in instances}
    if failed:
        return "refuted"
    if len(instances) >= 2 and len(members) >= 2:
        return "established, pooled over " + ", ".join(sorted(members))
    if len(instances) >= 2:
        return "held on one member, not established"
    return "held on one instance, not established" if len(instances) == 1 else "not established"


def reproduction(pushed_text, regenerated):
    """(reproduced, detail): the raw text against the regenerated record's serialization, byte for byte."""
    again = CC.record_text(regenerated)
    if again == pushed_text:
        return True, dict(bytes=len(pushed_text.encode()))
    a, b = pushed_text.split("\n"), again.split("\n")
    i = next((i for i, (u, v) in enumerate(zip(a, b)) if u != v), min(len(a), len(b)))
    return False, dict(first_differing_line=i + 1, pushed=a[i] if i < len(a) else None, regenerated=b[i] if i < len(b) else None,
                       lengths=(len(pushed_text.encode()), len(again.encode())))


def run(pushed_text, regenerated, runs, gate=None):
    ok, detail = reproduction(pushed_text, regenerated)
    if not ok:
        return dict(prediction_record_reproduced=False, reproduction=detail,
                    claims={k: "not established: the prediction record is not what the frozen code gives from the evidence (section 9)" for k in CLAIMS},
                    comparisons="not computed: the prediction record is not reproduced")
    res = analysis(json.loads(pushed_text), runs, gate)
    return dict(prediction_record_reproduced=True, reproduction=detail, **res)


def analysis(predicted, runs, gate=None):
    inst = {(x["seed"], x["member"]): x for x in predicted["instances"]}
    members = sorted({x["member"] for x in predicted["instances"]})
    res = dict(missing=[], claims={}, observed_without_prediction=[])
    rec = lambda r: runs.get(r["id"]) if runs.get(r["id"], {}).get("counts") else None
    # 1. primary, without noise (eligible instances only: no other has a run)
    prim = {m: dict(instances=[], discrepancies=[]) for m in members}
    G = []
    S = []
    for r in predicted["network_runs"]:
        if r["control"] != "skew":
            continue
        w = rec(r)
        if w is None:
            res["missing"].append(r["id"])
            continue
        x = inst[(r["seed"], r["member"])]
        G += [dict(run=r["id"], **g) for g in w.get("G", [])]
        prim[r["member"]]["instances"].append(r["seed"])
        prim[r["member"]]["discrepancies"] += [dict(instance=r["seed"], **b) for b in discrepancies(x["predicted"], w)]
        S += [dict(run=r["id"], pattern=k, cell=c) for k, v in w.get("skew", {}).items() for c, f in v.items() if f]
    for m, v in prim.items():
        v["verdict"] = member_verdict(len(v["instances"]), v["discrepancies"])
    refuted = [m for m, v in prim.items() if v["verdict"] == "refuted"]
    reached = [m for m, v in prim.items() if len(v["instances"]) >= 2]
    if refuted:
        fam = "refuted (" + ", ".join(refuted) + ")"
    elif len(reached) == len(members):
        fam = "established for the family"
    else:
        fam = ("established on the members " + ", ".join(reached) + "; " if reached else "") + \
              "; ".join(f"for {m}: {prim[m]['verdict']}" for m in members if m not in reached)
    res["claims"]["primary"] = dict(per_member=prim, family=fam)
    # 4, 5. noise claims, on counted noisy runs (every one is on an instance where every cell has room)
    nout, nown, nword = {}, {}, {}
    for r in predicted["network_runs"]:
        if r["noise"] == "none":
            continue
        w = rec(r)
        if w is None:
            res["missing"].append(r["id"])
            continue
        x = inst[(r["seed"], r["member"])]
        assert x["room_K3"], f"a noisy run on an instance without room: {r['id']}"
        G += [dict(run=r["id"], **g) for g in w.get("G", [])]
        pred = x["predicted"]
        for cell in next(iter(pred["tests"].values())):
            ok = all(w["tests"].get(k, {}).get(cell) == v[cell] for k, v in pred["tests"].items())
            d = nout.setdefault(cell, dict(instances=set(), failures=[]))
            d["instances"].add((r["seed"], r["member"]))
            if not ok:
                d["failures"].append(r["id"])
        for port, want in pred["words"].items():
            v = n_own(w["words"].get(port, ""), need_of(x, port))
            d = nown.setdefault(port[0] if port[0] != "c" else port, dict(instances=set(), not_counted=0, failures=[]))
            if v is None:
                d["not_counted"] += 1
            else:
                d["instances"].add((r["seed"], r["member"]))
                if not v:
                    d["failures"].append(r["id"])
            e = nword.setdefault(port[0] if port[0] != "c" else port, dict(instances=set(), failures=[]))
            e["instances"].add((r["seed"], r["member"]))
            if w["words"].get(port) != want:
                e["failures"].append(r["id"])

    def pooled(dd):
        allinst = set().union(*[v["instances"] for v in dd.values()]) if dd else set()
        fails = [f for v in dd.values() for f in v["failures"]]
        per_member = {m: member_verdict(len({s for s, mm in allinst if mm == m}), [f for f in fails if f"-{m}-" in f]) for m in members}
        return dict(by={k: dict(v, instances=sorted(v["instances"])) for k, v in dd.items()}, per_member=per_member,
                    verdict=pooled_verdict(allinst, fails))
    res["claims"]["N-out"] = pooled(nout)
    res["claims"]["N-own"] = pooled(nown)
    res["claims"]["N-word"] = pooled(nword)
    res["claims"]["G"] = dict(failures=G, verdict="refuted" if G else "held")
    # 6. controls
    U = {}
    for r in predicted["network_runs"]:
        if r["control"] != "untrained":
            continue
        w = rec(r)
        if w is None:
            res["missing"].append(r["id"])
            U[r["member"]] = dict(verdict="not established")
            continue
        fires = [dict(pattern=k, cell=c) for k, v in w["tests"].items() for c, f in v.items() if f]
        U[r["member"]] = dict(fires=fires, verdict="refuted" if fires else "held")
    res["claims"]["U"] = U
    quiet_counted = sum(len(v["instances"]) for v in prim.values())
    res["claims"]["S"] = dict(fires=S, verdict="not established" if not quiet_counted else ("refuted" if S else "held"))
    import comparisons as C
    comp = C.comparisons(predicted, runs, gate)
    res["claims"]["H"] = dict(per_member=comp.pop("H"), verdict="observed and reported, never refuting (section 5.3)")
    res["comparisons"] = comp
    return res


def main(a):
    import os
    import tempfile
    import campaign_predict as CP
    do_lean = "--no-lean" not in a
    a = [x for x in a if x != "--no-lean"]
    pushed = Path(a[0]).read_text()
    runs = json.loads(Path(a[1]).read_text())
    work = Path(tempfile.mkdtemp(prefix="family-analysis-"))
    lean = os.environ.get("LEAN", "lean")
    again = CP.campaign(a[2], a[3], a[4], work / "regenerated", do_lean, lean)
    gate = dict(out_dir=work / "M8", gen=a[3], lean=lean, build=work / "M8" / "build") if do_lean else None
    if gate:
        Path(gate["out_dir"]).mkdir(parents=True)
    return run(pushed, again, runs, gate)


if __name__ == "__main__":
    assert __debug__, "refused: not with python -O, the guards are asserts"
    print(json.dumps(main(sys.argv[1:]), indent=1, default=str))
