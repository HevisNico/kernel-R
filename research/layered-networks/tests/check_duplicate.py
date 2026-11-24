"""The duplicate-run identity criterion (CAMPAIGN_PLAN_DRAFT.md §6), fixed before any campaign run.

  check_duplicate.py DIR_A DIR_B      exit 0 iff the two runs are identical under the criterion

Criterion:
  1. input.spice byte-identical;
  2. every record file present in either folder (record.json, noisy_record.json, untrained_record.json) present in
     both, and equal after removing the excepted fields;
  3. every verdict file (*.verdict.json, comparison.json) present in both and equal under the same exception;
  4. trace.raw (the simulator's trace, ngspice `write` at the end of the session) byte-identical except its one
     `Date:` header line, as campaign (a) compared trace.raw (evidence/function-family-campaign-predicted,
     research/function-family-campaign/PREDICTION.md §6: `trace.raw` compared with its `Date:` header line excluded);
     When trace.raw has been removed from either folder, the two trace.digest.json files are compared instead (size,
     sha256 of the header without its Date: line, sha256 of the data), as written by controls2.py;
  5. session.log (ngspice's whole pipe output: every command, answer and printed vector value) identical except the
     lines " Reference value :  <t>", ngspice's progress lines during a transient, printed on a wall-clock timer, so
     that their number and times differ between identical runs (305 against 304 on two NOT1 runs of one machine).
     The number of excluded lines is reported, and any other differing line is listed;
  6. the run logs (*.log next to the folder) and every other file are not compared.
Excepted fields, at any depth: "cost" (wall and CPU times), and any key "wall_s", "cpu_s" or ending in "_wall_s" or
"_cpu_s".
"""
import hashlib
import json
from pathlib import Path
import sys

RECORDS = ("record.json", "noisy_record.json", "untrained_record.json")
VERDICT_GLOBS = ("*.verdict.json", "comparison.json")


def excepted(k):
    return k in ("cost", "wall_s", "cpu_s") or k.endswith(("_wall_s", "_cpu_s"))


def strip(x):
    if isinstance(x, dict):
        return {k: strip(v) for k, v in x.items() if not excepted(k)}
    if isinstance(x, list):
        return [strip(v) for v in x]
    return x


def first_diff(a, b, path=""):
    if type(a) is not type(b):
        return path or "/"
    if isinstance(a, dict):
        for k in sorted(set(a) | set(b)):
            if k not in a or k not in b:
                return f"{path}/{k}"
            d = first_diff(a[k], b[k], f"{path}/{k}")
            if d:
                return d
        return None
    if isinstance(a, list):
        if len(a) != len(b):
            return f"{path} (length {len(a)} vs {len(b)})"
        for i, (x, y) in enumerate(zip(a, b)):
            d = first_diff(x, y, f"{path}[{i}]")
            if d:
                return d
        return None
    return None if a == b else (path or "/")


def raw_compare(a, b):
    """trace.raw: the text header line by line (the `Date:` line excluded), then the data after it byte for byte."""
    ra, rb = (d.read_bytes() for d in (a, b))
    def split(x):
        for mark in (b"Binary:\n", b"Values:\n"):
            i = x.find(mark)
            if i >= 0:
                return x[:i + len(mark)], x[i + len(mark):]
        return x, b""
    (ha, da), (hb, db) = split(ra), split(rb)
    la = [l for l in ha.split(b"\n") if not l.startswith(b"Date:")]
    lb = [l for l in hb.split(b"\n") if not l.startswith(b"Date:")]
    dates = sum(l.startswith(b"Date:") for l in ha.split(b"\n")), sum(l.startswith(b"Date:") for l in hb.split(b"\n"))
    other = [(x, y) for x, y in zip(la, lb) if x != y] + ([("length", (len(la), len(lb)))] if len(la) != len(lb) else [])
    same_data = da == db
    return not other and same_data, dict(size=(len(ra), len(rb)), date_lines=dates, header_diffs=other[:5],
                                         data_identical=same_data, data_sha256=hashlib.sha256(da).hexdigest()[:12])


def log_compare(a, b):
    tag = " Reference value :"
    la, lb = (d.read_text(errors="replace").splitlines() for d in (a, b))
    ka, kb = [l for l in la if not l.startswith(tag)], [l for l in lb if not l.startswith(tag)]
    other = [(i, x, y) for i, (x, y) in enumerate(zip(ka, kb)) if x != y]
    if len(ka) != len(kb):
        other.append(("length", len(ka), len(kb)))
    return not other, dict(excluded=(len(la) - len(ka), len(lb) - len(kb)), other_diffs=other[:5])


def main(a, b):
    a, b = Path(a), Path(b)
    ok = True
    ha, hb = (hashlib.sha256((d / "input.spice").read_bytes()).hexdigest() for d in (a, b))
    print(f"input.spice: {'identical' if ha == hb else 'DIFFERS'} ({ha[:12]})")
    ok &= ha == hb
    names = sorted({p.name for d in (a, b) for p in d.iterdir() if p.name in RECORDS} |
                   {p.name for d in (a, b) for g in VERDICT_GLOBS for p in d.glob(g)})
    for n in names:
        if not (a / n).exists() or not (b / n).exists():
            print(f"{n}: present in one folder only")
            ok = False
            continue
        x, y = (strip(json.loads((d / n).read_text())) for d in (a, b))
        d = first_diff(x, y)
        print(f"{n}: {'identical (excepted fields removed)' if d is None else 'DIFFERS at ' + d}")
        ok &= d is None
    if not names:
        print("no record or verdict file")
        ok = False
    if not ((a / "trace.raw").exists() and (b / "trace.raw").exists()) and \
            (a / "trace.digest.json").exists() and (b / "trace.digest.json").exists():
        x, y = (json.loads((d / "trace.digest.json").read_text()) for d in (a, b))
        keys = ("size", "header_sha256_without_date", "data_sha256")
        same = all(x[k] == y[k] for k in keys)
        print(f"trace.raw (by its digests, the raw files removed): {'identical under the criterion' if same else 'DIFFERS'} "
              f"{ {k: (x[k], y[k]) for k in keys if x[k] != y[k]} or x['data_sha256'][:12]}")
        ok &= same
        checks = (("session.log", log_compare),)
    else:
        checks = (("trace.raw", raw_compare), ("session.log", log_compare))
    for name, fn in checks:
        if not (a / name).exists() or not (b / name).exists():
            print(f"{name}: missing in {'both' if not (a / name).exists() and not (b / name).exists() else 'one'} folder(s)")
            ok = False
            continue
        same, info = fn(a / name, b / name)
        print(f"{name}: {'identical under the criterion' if same else 'DIFFERS'} {info}")
        ok &= same
    print("DUPLICATE IDENTICAL" if ok else "DUPLICATE DIFFERS")
    return ok


if __name__ == "__main__":
    sys.exit(0 if main(sys.argv[1], sys.argv[2]) else 1)
