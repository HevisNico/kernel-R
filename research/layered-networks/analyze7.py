"""analyze6.py with the cross-machine duplicates judged by check_duplicate's own rule (the owner's decision, relayed
2026-11-25). Development only. analyze6.py and the earlier analyses are kept as they are.

The defect: analyze3's `cross_machine_duplicates` compares the two N0/trace.digest.json files byte for byte. Each file
holds its run's `date_line`, so a true duplicate always read "trace.digest.json_identical: false", where
tests/check_duplicate.py (the duplicate criterion, CAMPAIGN_PLAN_DRAFT.md §6) said IDENTICAL.

Here every cross-machine duplicate (DUPX_<inst> on one root, <inst> on another) is judged by **check_duplicate.py
itself**, run on <orig root>/<inst>/N0 and <dup root>/DUPX_<inst>/N0. The criterion is:
- input.spice identical;
- the records and comparison.json identical without the excepted fields;
- trace.raw identical without its Date: line, or the digests' size, header-without-Date and data sha256 when a raw file
  is removed;
- session.log identical outside ngspice's progress lines.

The checker is the file `tests/check_duplicate.py` of the controls tree, PLAN `noise_tree` of the original's root
(or `controls=DIR`, a layered-networks folder). Its sha256 is recorded. Reported per duplicate:
- `identical` (the checker's verdict) and the checker's printed lines (no paths in them);
- DUPX_<inst>/seal_check.json (the seal checks, without its local seal_dir path);
- DUPX_<inst>/N0/comparison.json's verdict, and whether it equals the original's N0/comparison.json without the
  excepted fields;
- DUPX_<inst>/seal_fetch.json, when the seal came from the log branch.

The analysis' other parts are analyze6's, unchanged; analyze3's entries are kept under `cross_machine_duplicates_v3`.

  analyze7.py OUTDIR ROOT [ROOT ...] [times=...] [thresholds=thresholds.json] [controls=DIR]
"""
import contextlib
import importlib.util
import io
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import analyze as A  # noqa: E402
import analyze6 as A6  # noqa: E402

FORMAT = "layered-campaign-results/7"


def strip(x):
    """check_duplicate's exception: "cost", "wall_s", "cpu_s" and keys ending in "_wall_s" or "_cpu_s", at any depth."""
    if isinstance(x, dict):
        return {k: strip(v) for k, v in x.items()
                if not (k in ("cost", "wall_s", "cpu_s") or k.endswith(("_wall_s", "_cpu_s")))}
    if isinstance(x, list):
        return [strip(v) for v in x]
    return x


def checker(path):
    spec = importlib.util.spec_from_file_location("check_duplicate_v7", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def judge(chk, a, b):
    out = io.StringIO()
    with contextlib.redirect_stdout(out):
        ok = bool(chk.main(str(a), str(b)))
    return ok, out.getvalue().splitlines()


def main(outdir, *args):
    args = [str(a) for a in args]
    kw = dict(a.split("=", 1) for a in args if "=" in a)
    A6.main(outdir, *[a for a in args if not a.startswith("controls=")])
    out = Path(outdir)
    res = json.loads((out / "RESULTS.json").read_text())
    roots = [Path(a) for a in args if "=" not in a]
    where = {}
    for k, root in enumerate(roots, start=1):
        for st in root.glob("*/status.json"):
            where.setdefault(st.parent.name, (k, root))
    xs = []
    for k, root in enumerate(roots, start=1):
        for dx in sorted(root.glob("DUPX_*")):
            name = dx.name[len("DUPX_"):]
            e = dict(instance=name, duplicate_machine=f"machine_{k}")
            if name not in where:
                e["why"] = "original instance not in the analysed OUTROOTs"
                xs.append(e)
                continue
            ok_, oroot = where[name]
            e["original_machine"] = f"machine_{ok_}"
            ctl = Path(kw["controls"]) if "controls" in kw else \
                Path(json.loads((oroot / "PLAN.json").read_text())["noise_tree"]) / "research" / "layered-networks"
            cp = ctl / "tests" / "check_duplicate.py"
            e["checker"] = dict(file="tests/check_duplicate.py", sha256=A.sha(cp) if cp.exists() else None)
            if cp.exists():
                ident, lines = judge(checker(cp), oroot / name / "N0", dx / "N0")
                e.update(identical=ident, checker_lines=lines)
            else:
                e.update(identical=None, why="check_duplicate.py not found")
            sc = dx / "seal_check.json"
            if sc.exists():
                s = json.loads(sc.read_text())
                s.pop("seal_dir", None)
                e["seal_check"] = s
            sf = dx / "seal_fetch.json"
            if sf.exists():
                f = json.loads(sf.read_text())
                f.pop("remote", None)
                e["seal_fetch"] = f
            c_dup, c_orig = dx / "N0" / "comparison.json", oroot / name / "N0" / "comparison.json"
            if c_dup.exists():
                cd = json.loads(c_dup.read_text())
                e["comparison"] = dict(verdict=cd.get("verdict"), equals_original=c_orig.exists() and
                                       strip(cd) == strip(json.loads(c_orig.read_text())))
            else:
                e["comparison"] = None
            xs.append(e)
    res["controls"]["cross_machine_duplicates_v3"] = res["controls"].pop("cross_machine_duplicates", [])
    res["controls"]["cross_machine_duplicates"] = xs
    res.update(format=FORMAT, analyze7_sha256=A.sha(__file__))
    (out / "RESULTS.json").write_bytes(A.canon(res))
    (out / "SHA256SUMS").write_text(f"{A.sha(out / 'RESULTS.json')}  RESULTS.json\n")
    print(json.dumps(dict(results_sha256=A.sha(out / "RESULTS.json"),
                          cross_machine_duplicates=[dict(instance=x["instance"], identical=x.get("identical"),
                                                         comparison=(x.get("comparison") or {}).get("verdict"))
                                                    for x in xs]), indent=1))
    return True


if __name__ == "__main__":
    sys.exit(0 if main(*sys.argv[1:]) else 1)
