"""Equivalence test (b): instances run end to end by campaign.py against the same instances run by the chain.

  equiv_b.py OUT.json NEW_DIR=REF_DIR[@REF_DRIVER] [...]

Each pair names an instance folder written by campaign.py and the same instance (spec, seed, round set) written by
the chain (campaign_run17 roots, or an older chain root). Every file in either folder is compared, except the PDK
copies (pdk/), ngspice's .spiceinit and the run logs (*.log beside the steps, which carry the driver's own lines):
  - a JSON file: every differing path is listed (not only the first). A difference is "listed" when its path matches
    one rule of LISTED below (each with its reason); any other difference fails the pair;
  - trace.raw: check_duplicate's raw_compare (only the Date: line excepted);
  - session.log and the inverter measures' ngspice.log: check_duplicate's log_compare (only the wall-clock " Reference value :" lines excepted);
  - every other file: byte-identical.
A file present in one folder only fails the pair, unless it matches FILES_LISTED (with its reason).
The verdict per pair is "identical except listed" or "DIFFERS"; the listed differences are printed in full in OUT.json.

  equiv_b.py analysis OUT.json LABEL:A10_DIR:AN1_DIR:AN2_DIR [...]

analysis.py against analyze10 on the same roots: RESULTS.json of analyze10 (A10_DIR) and of two analysis.py runs.
The two analysis.py runs must be byte-identical. Against analyze10, every top-level key must be equal except the
ANALYSIS_LISTED ones (CAMPAIGN_DIFFERENCES.md, analysis.py vs analyze10).
"""
import hashlib
import importlib.util
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
_spec = importlib.util.spec_from_file_location("check_duplicate_b", HERE / "check_duplicate.py")
CD = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(CD)

# (name, path regex on "file:/json/path", reason). Paths are matched in full.
LISTED = [
    ("cost", r".*:(.*/)?(cost|wall_s|cpu_s|[^/]*_wall_s|[^/]*_cpu_s)(/.*)?",
     "wall and CPU times (check_duplicate's exception)"),
    ("other_times", r".*:(.*/)?(cpu_min|seconds|seconds_total|machine_s|machine_s_total|wall_minutes|network_op_s)(/.*)?",
     "other wall and CPU time fields (Lean's seconds, the inverter measures' machine time)"),
    ("date_line", r".*:(.*/)?date_line(/.*)?", "the trace's Date: line, as in check_duplicate"),
    ("derived_hash", r".*:(.*/)?(inverter_gate/sha256|inverter_gate/source/sha256|prediction_sha256|instances/sha256|"
                     r"measure_sha256|extract/sha256|files/ngspice\.log)",
     "the sha256 of another file of the same pair, which is itself compared here field by field (it differs only by "
     "listed fields: times, the ENV hash)"),
    ("kernel_paths", r"D/kernel/.*:(.*/)?prediction", "the absolute path of prediction.json given to Lean"),
    ("times", r".*:(.*/)?(started|ended|at|time|utc|[^/]*_utc|pushed_at[^/]*|date)(/.*)?",
     "UTC dates of the run"),
    ("env", r".*:(.*/)?(env_sha256|env|ENV_sha256)(/.*)?",
     "the ENV.json hash: ENV.json differs by its paths, uptime and the new `campaign` key"),
    ("seal_log", r".*:(.*/)?(seal_log|record_seal_log|commit|line|seal_branch|branch|remote|seal_dir)(/.*)?",
     "the seal-log commit: another log repository, another commit and time"),
    ("seal_sha", r".*:(.*/)?(seal_sha256|seal_sha|manifest_sha256|sha256sums_sha256)(/.*)?",
     "the seal's hash, which follows the ENV hash sealed inside it"),
    ("seal_sums", r"seal/SHA256SUMS:.*|N\d/SEAL_LOG\.json:.*|seal_push\.json:.*",
     "the seal's file list hashes and the push record, which follow the ENV hash and the log repository"),
    ("code", r".*:(.*/)?(code|code_sha256|driver[^/]*|[^/]*script[^/]*_sha256|sources)(/.*)?",
     "hashes of the code files: another clone, and the chain's or campaign.py's driver"),
    ("kernel", r".*:(.*/)?(kernel|kernel_build|kernel_[^/]*)(/.*)?",
     "the kernel build reference (absent in stage_d5-era roots)"),
    ("paths", r".*:(.*/)?(path|dir|root|out|cwd|argv|deck)(/.*)?",
     "absolute paths of another root"),
]
FILES_LISTED = [
    (r"(.*/)?SHA256SUMS", "the instance's file list: follows the files above"),
    (r"(.*/)?status\.json", "the driver's status file (steps' times, cores, mode)"),
    (r"D/kernel(/.*)?", "the kernel build folder"),
    (r"N\d/extract(/.*)?", "trace extracts: compared through trace.digest.json"),
    (r"N\d/ref_extract\.json", "an older chain's extract file name"),
    (r"seal_wait\.json", "the duplicate's wait log, written by campaign_run15 onwards and by campaign.py; "
                         "campaign_run14 wrote none"),
    (r"N0/trace\.raw", "deleted from the reference roots after their analysis (RAWS_DELETED_AFTER_ANALYSIS.txt); "
                        "trace.digest.json is compared instead"),
]
SKIP = re.compile(r"(^|/)(pdk|\.spiceinit)(/|$)|^[^/]+\.log$")


def walk(d):
    return {str(p.relative_to(d)) for p in d.rglob("*") if p.is_file() and not SKIP.search(str(p.relative_to(d)))}


def diffs(a, b, path=""):
    if type(a) is not type(b):
        return [path or "/"]
    if isinstance(a, dict):
        out = []
        for k in sorted(set(a) | set(b)):
            out += [f"{path}/{k}"] if (k not in a or k not in b) else diffs(a[k], b[k], f"{path}/{k}")
        return out
    if isinstance(a, list):
        if len(a) != len(b):
            return [f"{path} (length {len(a)} vs {len(b)})"]
        return [d for i, (x, y) in enumerate(zip(a, b)) for d in diffs(x, y, f"{path}[{i}]")]
    return [] if a == b else [path or "/"]


def listed(f, p):
    key = f"{f}:{re.sub(r'\[\d+\]', '', p)}"
    for name, rx, _ in LISTED:
        if re.fullmatch(rx, key):
            return name
    return None


def compare(new, ref):
    fn, fr = walk(new), walk(ref)
    out = dict(new=str(new), ref=str(ref), files={}, only_new=[], only_ref=[], unlisted=[])
    for side, names in (("only_new", fn - fr), ("only_ref", fr - fn)):
        for f in sorted(names):
            why = next((w for rx, w in FILES_LISTED if re.fullmatch(rx, f)), None)
            out[side].append(dict(file=f, listed=why))
            if why is None:
                out["unlisted"].append(f"{side}: {f}")
    for f in sorted(fn & fr):
        a, b = new / f, ref / f
        if any(re.fullmatch(rx, f) for rx, _ in FILES_LISTED) and f.endswith(("SHA256SUMS", "status.json")):
            out["files"][f] = dict(compared="listed file, not compared",
                                   identical=a.read_bytes() == b.read_bytes())
            continue
        if f.endswith(".json"):
            try:
                x, y = json.loads(a.read_text()), json.loads(b.read_text())
            except ValueError:
                x = y = None
            if x is not None:
                ds = diffs(x, y)
                cls = [(d, listed(f, d)) for d in ds]
                bad = [d for d, c in cls if c is None]
                out["files"][f] = dict(compared="json", differences=len(ds),
                                       listed={c: sorted({d for d, cc in cls if cc == c}) for c in sorted({c for _, c in cls if c})},
                                       unlisted=bad)
                out["unlisted"] += [f"{f}:{d}" for d in bad]
                continue
        if f.endswith("trace.raw"):
            same, info = CD.raw_compare(a, b)
            out["files"][f] = dict(compared="raw_compare", identical=same, info=str(info))
        elif f.endswith(("session.log", "ngspice.log")):
            same, info = CD.log_compare(a, b)
            out["files"][f] = dict(compared="log_compare", identical=same, info=str(info))
        else:
            same = a.read_bytes() == b.read_bytes()
            out["files"][f] = dict(compared="bytes", identical=same,
                                   sha256=hashlib.sha256(a.read_bytes()).hexdigest()[:12] if same else None)
        if not same:
            out["unlisted"].append(f"{f}: differs ({out['files'][f]['compared']})")
    out["verdict"] = "identical except listed" if not out["unlisted"] else "DIFFERS"
    return out


def main(outp, *pairs):
    res = dict(format="layered-equiv-b/1", script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
               listed_rules=[dict(name=n, regex=r, reason=w) for n, r, w in LISTED],
               files_listed=[dict(regex=r, reason=w) for r, w in FILES_LISTED], pairs=[])
    for p in pairs:
        n, r = p.split("=", 1)
        r, _, drv = r.partition("@")
        c = compare(Path(n), Path(r))
        c["ref_driver"] = drv or None
        res["pairs"].append(c)
        print(f"{c['verdict']:26s} {Path(n).parent.name}/{Path(n).name} vs {r}"
              + (f"  unlisted: {c['unlisted'][:6]}" if c["unlisted"] else ""))
    res["all_identical_except_listed"] = all(c["verdict"] != "DIFFERS" for c in res["pairs"])
    Path(outp).write_text(json.dumps(res, indent=1, sort_keys=True) + "\n")
    return res["all_identical_except_listed"]


ANALYSIS_LISTED = {
    "format": "layered-campaign-analysis/1 in place of analyze10's format",
    "analysis_sha256": "new: analysis.py's own hash",
    "analyze3_sha256 .. analyze10_sha256": "dropped: the layered hashes of analyze3 to analyze10",
    "mode": "new: campaign or test",
    "root_drivers": "new: each root's driver, template and mode, from ENV.json",
    "roots_sha256sums": "new: every root's SHA256SUMS hashed before and after",
    "pins": "new: the FREEZE_PINS.json check of the analysis tree (audit A5)",
}


def main_analysis(outp, *sets):
    res = dict(format="layered-equiv-b-analysis/1", script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
               listed=ANALYSIS_LISTED, sets=[])
    for spec in sets:
        label, a10, an1, an2 = spec.split(":")
        fa, f1, f2 = (Path(d) / "RESULTS.json" for d in (a10, an1, an2))
        a, b = json.loads(fa.read_text()), json.loads(f1.read_text())
        old = {k for k in a if re.fullmatch(r"analyze\d+_sha256", k)}
        new = {"analysis_sha256", "mode", "root_drivers", "roots_sha256sums", "pins"}
        bad = sorted((set(a) - old) ^ (set(b) - new)) + sorted(k for k in (set(a) - old) & (set(b) - new)
                                                             if k != "format" and a[k] != b[k])
        same12 = f1.read_bytes() == f2.read_bytes()
        res["sets"].append(dict(label=label, analyze10=str(fa), analysis_runs=[str(f1), str(f2)],
                                two_runs_byte_identical=same12, keys_compared=len((set(a) - old) & (set(b) - new)),
                                dropped=sorted(old), added=sorted(set(b) & new), unlisted=bad,
                                verdict="identical except listed" if same12 and not bad else "DIFFERS"))
        print(res["sets"][-1]["verdict"], label, "two runs byte-identical" if same12 else "TWO RUNS DIFFER", bad)
    res["all_identical_except_listed"] = all(x["verdict"] != "DIFFERS" for x in res["sets"])
    Path(outp).write_text(json.dumps(res, indent=1, sort_keys=True) + "\n")
    return res["all_identical_except_listed"]


if __name__ == "__main__":
    if sys.argv[1] == "analysis":
        sys.exit(0 if main_analysis(*sys.argv[2:]) else 1)
    sys.exit(0 if main(*sys.argv[1:]) else 1)
