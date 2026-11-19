"""Campaign 6's one analysis (PREDICTION.md 5, 8 and 9): campaign 5's analyze.py, whose claim functions are used
unchanged, through an adapter that maps exactly four things. New code.

  analyze6.py OUT_DIR PREDICTED.json --measures-a DIR... --measures-b DIR... --runs-a DIR... --runs-b DIR...
      each DIR: one collected stage folder (its STATE.json at its top): M1 to M3 of each machine, then Q and the N stages
  analyze6.py --rehearsal OUT_DIR PREDICTED_RN.json BATCH_DIR --runs-a DIR... --runs-b DIR...
      RN's analysis (PREDICTION.md 7): its record recomputed from the batch's merged evidence (BATCH_DIR), round 1 only

The analysis reads exactly the stage folders named (the audit of 2026-11-19, C4): each run id must appear once, and
must be a run of the record (the campaign's measure runs and the record's network runs); any other refuses.

1. The reproduction check. analyze.main recomputes PREDICTED.json with campaign 5's predicted.predictions (the
   nominal-level prediction). Here it is recomputed with predicted6.predictions from the same measures (each
   instance's Lean file and check.sh again included), and the RAW text of the pushed PREDICTED.json is compared with
   it byte for byte, in the same serialization as analyze.py's (json.dumps(indent=1, default=str) + newline). If it
   differs, every claim is "not established" (PREDICTION.md 9), whatever analyze.main returns: analyze.main compares
   only the mapped records, and the mapping overwrites `eligible`.
2. `eligible`. analyze.py reads an instance's `eligible`; campaign 6's eligibility is measured, eligible and gate_K0
   (PREDICTION.md 3). The record handed to analyze.py carries `eligible` = that, with the original kept as
   `eligible_python`.
3. The run list and the constants come from PREDICTED.json. analyze.py reads campaign 5's BEFORE_M.md only to pass it
   to predicted.predictions, which mapping 1 replaces, so no record before stage M is read (an empty one is given).
4. The minimum of 2 counted eligible instances (PREDICTION.md 5, the owner's decisions of 2026-11-18). analyze.py's
   verdicts, failures and counts are kept unchanged; the number of distinct eligible instances behind each claim's
   counted runs is added; "held" with fewer than 2 becomes "held on one instance, not established" (1) or "not
   established" (0); "refuted" is never changed. The instances are those of exactly the runs and port-runs analyze.py
   counts, under its own conditions: a noisy run counts when campaign 5's P.counts holds for its kit record (analyze.py's
   noisy_ok under the injected model); an output-run of N-out when the instance's counts_N_out holds for that output; a
   port-run of N-word when its learning port has room_up_to; a port-run of N-own when it has own_room and campaign 5's
   n_own does not return None on its word (rows_of and reads4.words, the same functions, read-only, on the same runs);
   the primary claim's instances are analyze.py's own list.
5. M8's assumption on c (analyze.assumption_on_c, for an eligible instance with c1 != c2) reads the instance's
   observation.secondTest[k].start and .emissions[i], for k in AB and CD, through predicted.exact, which accepts numbers
   only; campaign 5's own predicted.rd writes exactly these fields as strings (str of a Fraction, "5752921/10000"), so
   it raised on every such instance (the audit of 2026-11-19, finding 14; campaign 5's analysis never ran this branch:
   no eligible instance with c1 != c2 reached it). analyze.assumption_on_c is given a copy of the instance in which
   exactly these fields, and no others, are read back as the rationals they encode (Fraction of the string); a field that
   is not such a string is left as it is (predicted.exact then refuses it, as before), and an absent field stays absent
   (campaign 5's code then raises, as before). Nothing else changes type.
The adapter decides no claim of its own.
"""
import copy
from fractions import Fraction
import json
import os
import re
from pathlib import Path
import sys
import tempfile
from unittest import mock

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import c6                                               # noqa: E402
import c4                                               # noqa: E402
import predicted6                                       # noqa: E402
import analyze                                          # noqa: E402  (campaign 5, frozen)
import reads4                                           # noqa: E402

HELD_ON_ONE = "held on one instance, not established"
RATIONAL = re.compile(r"-?\d+(/\d+)?")
M8_FIELDS = ("AB", "CD")                                 # the second-test reads assumption_on_c reads (lines and c)


def rational(v):
    return Fraction(v) if isinstance(v, str) and RATIONAL.fullmatch(v) else v


def m8_fields(x):
    """Mapping 5: a copy of the instance with exactly observation.secondTest[k].start and .emissions[i], k in AB and CD,
    read back as the rationals their strings encode; every other field unchanged."""
    y = copy.deepcopy(x)
    st = y.get("observation", {}).get("secondTest", {})
    for k in M8_FIELDS:
        if k in st:
            if "start" in st[k]:                         # converted only where present: an absent key stays absent
                st[k]["start"] = rational(st[k]["start"])
            if "emissions" in st[k]:
                st[k]["emissions"] = [rational(e) for e in st[k]["emissions"]]
    return y


def assumption_on_c(real):
    def wrapped(rows, x):
        return real(rows, m8_fields(x))
    return wrapped


def mapped(p):
    """Mapping 2: eligible = measured, eligible and gate_K0; the original kept beside it."""
    q = copy.deepcopy(p)
    for x in q["instances"]:
        x["eligible_python"] = x.get("eligible")
        x["eligible"] = bool(x.get("measured") and x.get("eligible") and x.get("gate_K0"))
    return q


def minimum(verdict, n):
    """Mapping 4 on one verdict: "held" needs at least 2 distinct eligible instances; "refuted" is never changed."""
    if verdict != "held":
        return verdict
    return "held" if n >= 2 else (HELD_ON_ONE if n == 1 else "not established")


def counted_instances(p, res, recs):
    """The distinct eligible instances behind each claim's counted runs (mapping 4)."""
    inst = {x["seed"]: x for x in p["instances"]}
    noisy = [r for r in p["network_runs"] if r["noise"] == "injected" and analyze.counts(recs.get(r["id"]))]     # analyze.py's noisy_ok
    out = {"primary": set(res["claims"]["primary"]["instances"]) if isinstance(res["claims"].get("primary"), dict) else set()}
    for c in c4.CELLS:
        out[f"N-out:{c}"] = {r["seed"] for r in noisy if inst[r["seed"]]["counts_N_out"][c]}
    out["N-word"] = {r["seed"] for r in noisy for lp in inst[r["seed"]]["learning_ports"].values() if lp["room_up_to"]}
    own = set()
    for r in noisy:
        x = inst[r["seed"]]
        ports = [(port, lp) for port, lp in x["learning_ports"].items() if lp["own_room"]]
        if not ports:
            continue
        rows, _ = analyze.rows_of(recs[r["id"]]["folder"], analyze.plan_needs(r), None)
        w = reads4.words(rows)
        for port, _ in ports:
            need = x["needs"][port[0]] if port[0] != "c" else x["needs"][port]
            if analyze.n_own(w["words"][port], need) is not None:
                own.add(r["seed"])
    out["N-own"] = own
    return {k: sorted(v) for k, v in out.items()}


def apply_minimum(res, counted):
    claims = res["claims"]
    if isinstance(claims.get("primary"), dict):
        claims["primary"]["counted_instances"] = counted["primary"]
        claims["primary"]["verdict"] = minimum(claims["primary"]["verdict"], len(counted["primary"]))
    if isinstance(claims.get("N-out"), dict):
        for c in c4.CELLS:
            v = claims["N-out"][c]
            v["counted_instances"] = counted[f"N-out:{c}"]
            v["verdict"] = minimum(v["verdict"], len(counted[f"N-out:{c}"]))
    for k in ("N-own", "N-word"):
        if isinstance(claims.get(k), dict):
            claims[k]["counted_instances"] = counted[k]
            claims[k]["verdict"] = minimum(claims[k]["verdict"], len(counted[k]))
    res["minimum_of_2"] = "PREDICTION.md 5: held needs counted runs from at least 2 eligible instances (the owner's decisions of 2026-11-18)"
    return res


MEASURE_TAILS = ("cal-on", "cal-off", "scan-a-pair", "scan-b-pair", "scan-c-line1", "scan-c-line2", "bothfire-c", "onesided-a", "onesided-b")


def allowed_ids(record, rehearsal=False):
    """The run ids the analysis may read: the record's network runs, and the campaign's measure runs (none for RN)."""
    ids = {r["id"] for r in record["network_runs"]}
    if not rehearsal:
        ids |= {f"{s}-{t}" for s in c6.SEEDS for t in MEASURE_TAILS}
    return ids


def assemble(folders, dest, allowed, seen):
    """One folder for analyze.main from exactly the collected stage folders named: each one's STATE.json copied and a
    link per run. Refuses a folder without the kit's STATE.json, a run id seen twice, or one outside `allowed`."""
    dest.mkdir(parents=True)
    for i, f in enumerate(Path(x) for x in folders):
        state = json.loads((f / "STATE.json").read_text())
        assert "records" in state, f"refused: {f} is not a collected stage folder of the kit"
        d = dest / f"{i:02d}-{f.name}"
        d.mkdir()
        (d / "STATE.json").write_text(json.dumps(state))
        for r in state["records"]:
            assert r["id"] not in seen, f"refused: run {r['id']} appears twice ({seen.get(r['id'])} and {f})"
            assert r["id"] in allowed, f"refused: run {r['id']} in {f} is not a run of this record"
            seen[r["id"]] = str(f)
            if (f / r["id"]).exists():
                os.symlink((f / r["id"]).resolve(), d / r["id"])
    return dest


def run(outdir, predicted_path, measures_a, measures_b, runs_a, runs_b, check=True, rehearsal=False, **prediction):
    """measures_*, runs_*: lists of collected stage folders (C4). prediction: predicted6.predictions' seeds, machine_of,
    batch_dir and rounds, for the rehearsal's RN (rehearsal=True, campaign6/README.md)."""
    outdir = Path(outdir)
    pushed = json.loads(Path(predicted_path).read_text())
    work = Path(tempfile.mkdtemp(prefix="c6-analysis-"))
    allowed, seen = allowed_ids(pushed, rehearsal), {}
    measures_a, measures_b, runs_a, runs_b = (assemble(x, work / "in" / n, allowed, seen) for x, n in
                                              ((measures_a, "measures-a"), (measures_b, "measures-b"), (runs_a, "runs-a"), (runs_b, "runs-b")))
    again = predicted6.predictions([measures_a, measures_b], work / "gate", check, **prediction)          # mapping 1
    reproduced = predicted6.text(again) == Path(predicted_path).read_text()
    handed = work / "PREDICTED.json"
    handed.write_text(predicted6.text(mapped(pushed)))
    regenerated = mapped(again)
    with mock.patch.object(analyze.P, "predictions", lambda *a, **k: (regenerated, {})), \
            mock.patch.object(analyze.plan, "read_before_m", lambda path: {}), \
            mock.patch.object(analyze, "assumption_on_c", assumption_on_c(analyze.assumption_on_c)):   # mappings 3 and 5
        res = analyze.main([str(outdir), str(measures_a), str(measures_b), str(runs_a), str(runs_b)], here=work, predicted_path=handed)
    res["predicted6_is_reproduced"] = reproduced
    if not reproduced:                                                       # PREDICTION.md 9, whatever analyze.main returned
        res["claims"] = {k: "not established" for k in ("primary", "G", "N-out", "N-own", "N-word", "U", "S")}
    elif res.get("predicted_is_reproduced"):
        recs = analyze.state_records(measures_a, measures_b, runs_a, runs_b)
        res = apply_minimum(res, counted_instances(mapped(pushed), res, recs))
    (outdir / "RESULTS.json").write_text(json.dumps(res, indent=1, default=str) + "\n")
    return res


def parse(a):
    """--measures-a/--measures-b/--runs-a/--runs-b, each followed by its folders."""
    out, key = {k: [] for k in ("--measures-a", "--measures-b", "--runs-a", "--runs-b")}, None
    for x in a:
        if x in out:
            key = x
        else:
            assert key is not None, f"refused: {x} comes before any of {sorted(out)}"
            out[key].append(x)
    return [out[k] for k in ("--measures-a", "--measures-b", "--runs-a", "--runs-b")]


def main(argv=None):
    a = sys.argv[1:] if argv is None else argv
    c6.require_debug()
    if a[0] == "--rehearsal":
        _, _, ra, rb = parse(a[4:])
        res = run(a[1], a[2], [], [], ra, rb, True, rehearsal=True, seeds=tuple(c6.REHEARSAL_SEEDS),
                  machine_of=dict(c6.REHEARSAL_SEEDS), batch_dir=Path(a[3]), rounds=(1,))
    else:
        res = run(a[0], a[1], *parse(a[2:]))
    print(json.dumps({k: (v.get("verdict") if isinstance(v, dict) and "verdict" in v else v) for k, v in res["claims"].items() if k != "H"}, default=str))


if __name__ == "__main__":
    main()
