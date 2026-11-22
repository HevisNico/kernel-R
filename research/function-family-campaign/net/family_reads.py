"""Development only: the trace reader of a network run of a member of the step-1 family. It turns one run's folder
(family_net's output: record.json, evidence/result.json, evidence/trace.raw) into the record that the family's
analysis takes (M1's analysis.analysis(predicted, runs)):

  {counts: bool, words: {port: str}, tests: {pattern: {cell: bool}}, skew: {pattern: {cell: bool}}, G: [failure dicts]}
  and, with with_rows: rows (reads4.network_reads' rows), result (evidence/result.json), words_prime, and with the
  prediction record: observation (the RUN's, as campaign 5's analyze.run_observation builds it) and observation_predicted.

The frozen functions do the reading, unchanged:
  - reads4.network_reads (campaign 5): every read of every slot, from the trace, the delivered occurrences and the slots.
    It is already general: it reads the slot's stage, pattern, line and writes, and every cell that got a pulse;
  - reads4.words (campaign 5): the letters s F w o m of reads4.letter, '-' where no read happened, the tests and the
    skew slots. Its output is kept on the member's own ports and cells only: for F1 that is all of it, unchanged;
  - analyze.g_check (campaign 5's analyze.py, loaded by path): G, the gated reads (no write, no write'; and, without noise, no move above
    c4.MOVE_BOUND_MV);
  - predicted.counts (campaign 5): a run counts when its launcher recorded it complete and its record says it reached
    its last date.

Ports: a pair cell's two ports; a unary cell's chosen port only; c's lines c1 (line a) and c2 (line b), c2 only with b.
Cells of tests: the layer-1 cells, then c. Cells of skew: the layer-1 cells (reads4's a and b for F1). Skew keys: the
pair term's letters ("AB", "BC"), which is the skew slot's pattern in family_net.calendar.

  family_reads.py read  REPO RUN_FOLDER STATUS [--rows] [--predicted=PREDICTED.json]   prints the record of one run
  family_reads.py collect REPO RUNS_DIR ID...               the records of the runs ID, with STATUS from RUNS_DIR/*/STATE.json

PYTHONPATH as family_net's.
"""
import json
from pathlib import Path
import sys

import family_net as N
import family_predict as fp


def js(x):
    return json.dumps(x, sort_keys=True)


def ports_of(member, unary_ports):
    """The word ports of a member, in reads4's order: a, b (pair: both ports; unary: its port), then c1, c2."""
    ports = N.check_ports(member, unary_ports)
    out = []
    for c, k in fp.kinds(member).items():
        out += [f"{c}1", f"{c}2"] if k == "pair" else [f"{c}{ports[c]}"]
    out += [f"c{fp.LINE_PORT[c]}" for c in N.layer1(member)]
    order = ["a1", "a2", "b1", "b2", "c1", "c2"]
    return sorted(out, key=order.index)


def rows_of(folder, member, needs, unary_ports, control):
    """reads4.network_reads on the run's trace, with the slots of family_net.network. The plan the run played (its
    result.json) must be the plan of its member, needs, ports and control, or the folder is refused."""
    import measure
    import reads4
    plan, slots = N.network(member, needs, unary_ports, control)
    ev = Path(folder) / "evidence"
    result = json.loads((ev / "result.json").read_text())
    assert js(result["plan"]) == js(json.loads(json.dumps(plan))), "refused: the run's plan is not the plan of its member, needs, ports and control"
    tr = measure.Trace(ev / "trace.raw")
    return reads4.network_reads(tr, result, slots), result


def words(member, unary_ports, rows, prime=False):
    """reads4.words, kept on the member's ports and cells."""
    import reads4
    w = reads4.words(rows, prime)
    L1 = N.layer1(member)
    keep = ports_of(member, unary_ports)
    cells = [c for c in ("a", "b", "c") if c in L1 or c == "c"]
    return dict(words={p: w["words"][p] for p in keep},
                tests={k: {c: v[c] for c in cells} for k, v in w["tests"].items()},
                skew={k: {c: v[c] for c in ("a", "b") if c in L1} for k, v in w["skew"].items()})


def skew_keys(member):
    """The skew slots' keys: the pair terms' letters, as family_net.calendar writes them."""
    return ["".join(t) for c, t in fp.MEMBERS[member]["terms"].items() if len(t) == 2]


def c5_analyze():
    """Campaign 5's analyze.py (g_check), loaded by its path as `c5_analyze`: research/circuit/analyze.py, earlier on
    the path that dosedev.repo_paths sets, has the same module name."""
    import importlib.util
    import reads4
    if "c5_analyze" not in sys.modules:
        path = Path(reads4.__file__).resolve().parent / "analyze.py"
        spec = importlib.util.spec_from_file_location("c5_analyze", path)
        mod = importlib.util.module_from_spec(spec)
        sys.modules["c5_analyze"] = mod
        spec.loader.exec_module(mod)
    mod = sys.modules["c5_analyze"]
    assert Path(mod.__file__).resolve().parent.name == "learned-dnf-circuit-campaign-5", mod.__file__
    return mod


def predicted_row(predicted, seed, member):
    """The prediction record's row of (seed, member), in either shape (family_net.read_predicted), or None."""
    rows = N.read_predicted(predicted).get(int(seed), {})
    return rows.get(member)


def observation_of(predicted, seed, member):
    """The PREDICTED observation (family_predict.observation's serialized form) of (seed, member), or None."""
    row = predicted_row(predicted, seed, member)
    return None if row is None else row.get("observation")


def run_observation(member, unary_ports, rows, folder, po):
    """The RUN's observation, in the serialized format of the predicted one: campaign 5's analyze.run_observation
    generalised by the member's wiring. Its dates, arrivals and emissions are the run's (reads4's rows and the trace);
    its values are the run's scores (q peaks; THETA at least on a FIRE); its scores are the predicted calibration
    scores `po` on the submasks the run did not observe, and the run's own on the one it did. For F1 it is
    analyze.run_observation, line for line (test_family_reads.RunObservation).
    The layer-1 inputs are the member's inputs in its order; the lines of c are LINE_PORT of its layer-1 cells."""
    import measure
    import net
    import predicted as P
    import reads4
    from c4 import dnf
    A = c5_analyze()
    units = A.units
    folder = Path(folder)
    tr = measure.Trace(folder / "evidence" / "trace.raw")
    result = json.loads((folder / "evidence" / "result.json").read_text())
    delivered = [o for o in result["occurrences"] if o["delivered"]]
    inputs = fp.MEMBERS[member]["inputs"]
    L1 = N.layer1(member)
    wire = fp.wiring(member, N.check_ports(member, unary_ports))
    INPUT_OF = {(c, p): n for c in L1 for n, p in wire[c].items()}
    lines = [fp.LINE_PORT[c] for c in L1]
    score = lambda r: P.zint(r["q_peak"]) if not r["fire"] else max(P.zint(r["q_peak_before_fire"]), P.THETA)

    def layer1(x_, c, own_target=False):
        lo, hi = reads4.c4_at(x_["date"]) - 1e-9, reads4.c4_at(x_["date"] + dnf.SLOT) - 1e-9
        arr = {INPUT_OF[(o["cell"], o["port"])]: units(o["date_s"]) for o in delivered if lo <= o["date_s"] < hi and o["cell"] in L1
               and (not own_target or o["cell"] == c)}
        arrivals = [None if k not in arr else str(arr[k]) for k in inputs]
        r = x_["reads"].get(c)
        if r is None:
            here = [o["date_s"] for o in delivered if lo <= o["date_s"] < hi and o["cell"] in L1]
            start = min(here) if here else net.snap(reads4.c4_at(x_["date"]))
            fires = tr.crossings(f"v(x{c}.p)", lo, hi)
            peak = reads4.q_peak(tr, c, start, start + 3 * reads4.TU)
            value = P.zint(peak) if not fires else max(P.zint(reads4.q_peak(tr, c, start, fires[0])), P.THETA)
            return dict(start=str(units(start)), arrivals=arrivals, emissions=[str(units(f)) for f in fires], value=value)
        return dict(start=str(units(r["start_s"])), arrivals=arrivals, emissions=[str(units(f)) for f in r["slot_fires_s"]], value=score(r))

    def layer2(x_):
        r = x_["reads"].get("c")
        lo, hi = reads4.c4_at(x_["date"]) - 1e-9, reads4.c4_at(x_["date"] + dnf.SLOT) - 1e-9
        if r is None:
            start = net.snap(reads4.c4_at(x_["date"])) + 1.5 * reads4.TU
            fires = tr.crossings("v(xc.p)", lo, hi)
            return dict(start=str(units(net.snap(reads4.c4_at(x_["date"]))) + P.F(3, 2)), arrivals=[None] * len(lines),
                        emissions=[str(units(f)) for f in fires], value=P.zint(reads4.q_peak(tr, "c", start, start + 3 * reads4.TU)))
        arr = {a["port"]: units(a["date_s"]) for a in r["arrivals"]}
        return dict(start=str(units(r["start_s"])), arrivals=[str(arr[p]) if p in arr else None for p in lines],
                    emissions=[str(units(f)) for f in r["slot_fires_s"]], value=score(r))
    o = dict(firstTrain=[], teach=[], secondTrain=[], firstTest={}, secondTest={}, scores={})
    for x_ in rows:
        if x_["stage"] == "layer 1":
            o["firstTrain"].append([layer1(x_, c, own_target=True) for c in L1])
        elif x_["stage"] == "layer 2":
            o["teach"].append([layer1(x_, c) for c in L1])
            o["secondTrain"].append(layer2(x_))
        elif x_["stage"] == "test":
            k = "".join(sorted(x_["pattern"])) or "-"
            o["firstTest"][k] = [layer1(x_, c) for c in L1]
            o["secondTest"][k] = layer2(x_)
            sc = dict(po["scores"][k])
            mask = "".join(str(p) for p, v in zip(lines, o["secondTest"][k]["arrivals"]) if v is not None) or "-"
            sc[mask] = o["secondTest"][k]["value"]
            o["scores"][k] = sc
    return o


def record_of(folder, status, with_rows=False, prime=False, predicted=None):
    """The analysis' record of one run. A run that does not count is still read when its files allow it (reported as
    observed, counting for nothing); a counted run that cannot be read is an error.
    with_rows adds what M1's comparisons read: `rows` (reads4.network_reads' rows), `result` (the run's
    evidence/result.json), `words_prime` (reads4.words with prime=True, on the member's ports) and, with `predicted`
    (the prediction record, either shape): `observation`, the RUN's observation (run_observation: the run's dates,
    emissions and q peaks, the predicted calibration scores only on the submasks the run did not observe), and
    `observation_predicted`, the prediction's own. A field that cannot be given is left out ("no data" for M1)."""
    import predicted as P
    analyze = c5_analyze()
    folder = Path(folder)
    counts = P.counts(dict(status=status, folder=str(folder)))
    own = folder / "record.json"
    if not own.exists():
        assert not counts
        return dict(counts=False, words=None, tests=None, skew=None, G=None, unread="no record.json")
    rec = json.loads(own.read_text())
    member = N.check_member(rec["member"])
    ports = N.check_ports(member, rec["unary_ports"])
    needs = N.check_needs(member, rec["needs"])
    noisy = rec["noise"]["model"] == "injected"
    try:
        rows, result = rows_of(folder, member, needs, ports, rec["control"])
    except (OSError, KeyError, ValueError) as e:            # missing or truncated evidence; a refused plan is an AssertionError
        assert not counts, f"a counted run cannot be read: {e}"
        return dict(counts=False, words=None, tests=None, skew=None, G=None, unread=f"{type(e).__name__}: {e}")
    w = words(member, ports, rows, prime)
    out = dict(counts=counts, words=w["words"], tests=w["tests"], skew=w["skew"], G=analyze.g_check(rows, noisy))
    if with_rows:
        out.update(rows=rows, result=result, words_prime=words(member, ports, rows, prime=True)["words"])
        po = observation_of(predicted, rec["seed"], member) if predicted is not None and rec.get("seed") is not None else None
        if po is not None:
            out["observation"] = run_observation(member, ports, rows, folder, po)
            out["observation_predicted"] = po
    return out


def statuses(runs_dir):
    """{id: status} from every RUNS_DIR/*/STATE.json in dosedev2.many's form ({"runs": {id: {"status"}}})."""
    out = {}
    for st in sorted(Path(runs_dir).glob("*/STATE.json")):
        for rid, v in json.loads(st.read_text())["runs"].items():
            assert rid not in out, f"run {rid} is listed in two STATE.json files"
            out[rid] = v["status"]
    return out


def collect(ids, runs_dir, with_rows=False, predicted=None):
    """{id: record} for the analysis: the run's folder is RUNS_DIR/<id>; a run absent from every STATE.json is missing."""
    st = statuses(runs_dir)
    out = {}
    for rid in ids:
        if rid not in st or not (Path(runs_dir) / rid).is_dir():
            out[rid] = dict(counts=False, words=None, tests=None, skew=None, G=None, unread="missing")
            continue
        out[rid] = record_of(Path(runs_dir) / rid, st[rid], with_rows, predicted=predicted)
    return out


def main(argv=None):
    N.require_debug()
    a = sys.argv[1:] if argv is None else argv
    cmd = a[0] if a else None
    if cmd == "read":
        repo, folder, status, *flags = a[1:]
        N.paths(repo)
        pred = next((f.split("=", 1)[1] for f in flags if f.startswith("--predicted=")), None)
        print(json.dumps(record_of(folder, status, with_rows="--rows" in flags, predicted=pred), indent=1))
    elif cmd == "collect":
        repo, runs_dir, *ids = a[1:]
        N.paths(repo)
        print(json.dumps(collect(ids, runs_dir), indent=1))
    else:
        raise SystemExit(__doc__)


if __name__ == "__main__":
    main()
