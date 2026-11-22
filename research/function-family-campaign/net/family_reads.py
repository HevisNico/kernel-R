"""Development only: the trace reader of a network run of a member of the step-1 family. It turns one run's folder
(family_net's output: record.json, evidence/result.json, evidence/trace.raw) into the record that the family's
analysis takes (M1's analysis.analysis(predicted, runs)):

  {counts: bool, words: {port: str}, tests: {pattern: {cell: bool}}, skew: {pattern: {cell: bool}}, G: [failure dicts]}
  and, on request, rows: reads4.network_reads' rows.

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

  family_reads.py read  REPO RUN_FOLDER STATUS [--rows]     prints the record of one run
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


def record_of(folder, status, with_rows=False, prime=False):
    """The analysis' record of one run. A run that does not count is still read when its files allow it (reported as
    observed, counting for nothing); a counted run that cannot be read is an error."""
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
        rows, _ = rows_of(folder, member, needs, ports, rec["control"])
    except (OSError, KeyError, ValueError) as e:            # missing or truncated evidence; a refused plan is an AssertionError
        assert not counts, f"a counted run cannot be read: {e}"
        return dict(counts=False, words=None, tests=None, skew=None, G=None, unread=f"{type(e).__name__}: {e}")
    w = words(member, ports, rows, prime)
    out = dict(counts=counts, words=w["words"], tests=w["tests"], skew=w["skew"], G=analyze.g_check(rows, noisy))
    if with_rows:
        out["rows"] = rows
    return out


def statuses(runs_dir):
    """{id: status} from every RUNS_DIR/*/STATE.json in dosedev2.many's form ({"runs": {id: {"status"}}})."""
    out = {}
    for st in sorted(Path(runs_dir).glob("*/STATE.json")):
        for rid, v in json.loads(st.read_text())["runs"].items():
            assert rid not in out, f"run {rid} is listed in two STATE.json files"
            out[rid] = v["status"]
    return out


def collect(ids, runs_dir, with_rows=False):
    """{id: record} for the analysis: the run's folder is RUNS_DIR/<id>; a run absent from every STATE.json is missing."""
    st = statuses(runs_dir)
    out = {}
    for rid in ids:
        if rid not in st or not (Path(runs_dir) / rid).is_dir():
            out[rid] = dict(counts=False, words=None, tests=None, skew=None, G=None, unread="missing")
            continue
        out[rid] = record_of(Path(runs_dir) / rid, st[rid], with_rows)
    return out


def main(argv=None):
    N.require_debug()
    a = sys.argv[1:] if argv is None else argv
    cmd = a[0] if a else None
    if cmd == "read":
        repo, folder, status, *flags = a[1:]
        N.paths(repo)
        print(json.dumps(record_of(folder, status, with_rows="--rows" in flags), indent=1))
    elif cmd == "collect":
        repo, runs_dir, *ids = a[1:]
        N.paths(repo)
        print(json.dumps(collect(ids, runs_dir), indent=1))
    else:
        raise SystemExit(__doc__)


if __name__ == "__main__":
    main()
