"""Reproduction tests for the defects D8, D9 and D10 of analysis.py, written from the defect descriptions and the code
at ef374ccd, not from the fix.

  python -B tests/test_analysis_defects.py [OUT.json]

Each case builds small roots in a temporary folder from the run2 test roots and runs analysis.py's real entry point
(`analysis.py test OUTDIR ROOT ... times=bare`) as a subprocess. Lean 4.35.0 (the pinned binary) must be on PATH:
the entry point builds the kernel library and regenerates each seal with stage_d6.py. No case needs ngspice.

Sources, fetched by branch name only from this clone's `origin` into temporary repositories:
- the roots: evidence/devtest-run2-K05 (out_K05: NOT1_6212, NOT1_6220) and evidence/devtest-run2-K06 (out_K06: the
  control DUPX_NOT1_6212). Set LAYERED_DEFECT_SOURCES to a folder holding out_K05 and out_K06 to skip this fetch.
- the seal log: evidence/devtest-seals2-K05, pushed into a local bare repository. Each root's PLAN.json then names
  that bare repository as its seal_push remote, and its push_times.log holds the GitHub push times recorded in
  dev/equiv/b/run2/RESULTS_times_github_ef374ccd.json. So `times=bare` gives the same seal-log verdicts as the
  GitHub run, offline.
Every file a case changes on purpose is re-declared in the SHA256SUMS that lists it, except in the D10 cases, where
the mismatch is the point. So the roots stay consistent for a fix that verifies the manifests. Each case records
`roots_manifest_problems`, the test's own check of every line of every manifest (SHA256SUMS*, SHA256SUMS.instances
included) of its roots. It is ASSERTED: empty in every case except one_byte_in_comparison and listed_file_missing,
where it must be exactly the file tampered with (`fixture_ok`).

Cases (a defect case passes only when the analysis behaves as the fix must; at ef374ccd each defect case fails):
- D8 planned_seed_not_started (test mode, no draw): K05 with seed 6230 added to NOT1 in PLAN.json (no folder).
  Must: exit 0, each level's rows of NOT1 sum to 3 (the planned size), and a not_run entry for NOT1_6230 at K0 and K3.
- D8 planned_machine_no_root (test mode, no draw): K06 alone. Its PLAN.json names K05 as the home machine of
  NOT1_6212, and K05 has no root. Must: exit 0 (no refusal) and a not_run entry naming NOT1_6212.
- D8 draw_machine_without_root: the dummy draw dev/freeze/DRAW_dummy.json (NOT1 6212, 6213 over 12 machines) split by
  plan_split3.py with campaign_template.json, as in dev/freeze/PROOF.md: K01 holds NOT1_6212, K02 NOT1_6213, K03 the
  duplicate of NOT1_6212. Only K01's root is given (out_K05 with its PLAN.json replaced by PLAN_K01.json byte for
  byte, NOT1_6220 removed), with draw=DRAW_dummy.json. Must: exit 0, NOT1 rows sum to 2 at each level, and a not_run
  entry for NOT1_6213. (NOT1_6212 is not sealed there: the plan's seal branch evidence/combined-seals-K01 does not
  exist. That is not asserted either way.)
- D8 draw_duplicate_machine_only: only K03's root (out_K06 with PLAN_K03.json), with draw=. Must: exit 0, NOT1 rows
  sum to 2, and not_run entries for NOT1_6212 and NOT1_6213 at each level.
- D9 same_root_30_times: K05 given 30 times by the same path. Must: refused, no RESULTS.json counting NOT1 more than
  twice, and no verdict "established".
- D9 draw_same_machine_twice: two copies of the K01 draw root (see draw_machine_without_root) at two paths, with
  draw=. Must: refused, the output naming K01 (the plan match names each root's machine). Without draw=, test mode
  names roots machine_<k>, so the same machine is caught as a home instance given twice (same_machine_two_paths).
- D9 same_machine_two_paths: two copies of K05 at two paths. Must: the same.
- D9 home_instance_twice: K05 and a second root (out_K07: K05 without NOT1_6220, with its own seal branch, its
  records' seal_log branch and plan text changed to match) that also holds NOT1_6212. Must: the same.
- D10 one_byte_in_comparison: one byte of NOT1_6212/N0/comparison.json changed ("cell_bits": 2 -> 3), its manifest
  kept. Must: refused, the output naming "N0/comparison.json".
- D10 listed_file_missing: NOT1_6212/N2/extract/extract.json deleted, still listed, with no declaration. Must:
  refused, the output naming "extract.json".
- D10 stopped_mid_instance: K05 as a machine stopped during NOT1_6220's round N2. The end-of-run files of the root
  (SHA256SUMS, SHA256SUMS.instances, RESULT*.json, DONE, INSTANCES_DONE, INVENTORY_END) are removed, and so are
  NOT1_6220/SHA256SUMS, N2, N3 and their logs. Its status.json has N2 "running" and no C2, N3, C3. One letter of
  N1/noisy_record.json is changed (word 1/0/0 "ssFF" -> "sFFF"), and N1/comparison.json is recomputed with
  compare_d2.py, which gives "refuted". Must: exit 0, NOT1_6220 in the K3 refuted row, an entry naming NOT1_6220 that
  says "manifest not final", and NOT1_6212 held at K0 and K3.
- control k05_alone and control k05_with_dupx (K05 + K06): must pass before and after the fix: exit 0 and NOT1
  counted 2 at K0 and K3 (DUPX_ folders are controls, never counted).

A refusal is matched on exit code != 0 and the substring "refused" (every refusal of analysis.py starts with
"refused:"), plus, for D10, the name of the file. A not_run entry is a dict with a value starting with "not_run" or "not run"
beside a value naming the instance, or a key "not_run" (or "not run") whose content names it. The draw argument's
name is the constant DRAW_ARG ("draw"). No other wording of the fix is assumed.
"""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time

HERE = Path(__file__).resolve().parents[1]
REPO = HERE.parents[1]
ANALYSIS = HERE / "analysis.py"
PY = sys.executable
SEAL_BRANCH = "evidence/devtest-seals2-K05"
DRAW_ARG = "draw"                                     # the fix's argument: draw=PATH (a DRAW.json)
DRAW = HERE / "dev" / "freeze" / "DRAW_dummy.json"    # NOT1 [6212, 6213] over 12 machines
TIMES_RECORD = HERE / "dev" / "equiv" / "b" / "run2" / "RESULTS_times_github_ef374ccd.json"


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def git(*a, cwd=None):
    return subprocess.run(["git", *a], cwd=cwd, check=True, capture_output=True, text=True).stdout


def origin_url():
    return git("remote", "get-url", "origin", cwd=REPO).strip()


# ------------------------------------------------------------------------------------------------ the sources

def sources(tmp):
    given = os.environ.get("LAYERED_DEFECT_SOURCES")
    if given:
        return Path(given)
    out = tmp / "sources"
    work = tmp / "fetch"
    work.mkdir(parents=True)
    git("init", "-q", cwd=work)
    out.mkdir()
    for m in ("K05", "K06"):
        git("fetch", "-q", origin_url(), f"refs/heads/evidence/devtest-run2-{m}", cwd=work)
        tar = subprocess.run(["git", "archive", "FETCH_HEAD", f"out_{m}"], cwd=work, check=True, capture_output=True).stdout
        subprocess.run(["tar", "-x", "-C", str(out)], input=tar, check=True)
    return out


def push_times():
    """{commit: GitHub push time} recorded for the K05 seal log."""
    r = json.loads(TIMES_RECORD.read_text())
    return {i["seal"]["log"]["commit"]: i["seal"]["log"]["pushed_utc"] for i in r["instances"]
            if i["machine"] == "machine_3"}


def bare_remote(tmp, branch):
    """A local bare repository holding the K05 seal log under `branch`, with a push_times.log."""
    b = tmp / "remotes" / (branch.replace("/", "_") + ".git")
    if b.exists():
        return b
    b.mkdir(parents=True)
    git("init", "-q", "--bare", cwd=b)
    git("fetch", "-q", origin_url(), f"refs/heads/{SEAL_BRANCH}:refs/heads/{branch}", cwd=b)
    tip = git("rev-parse", f"refs/heads/{branch}", cwd=b).strip()
    chain = git("rev-list", "--first-parent", "--reverse", tip, cwd=b).split()
    tm = push_times()
    assert set(tm) <= set(chain), (tm, chain)
    (b / "push_times.log").write_text("".join(f"{c} refs/heads/{branch} {tm[c]}\n" for c in chain if c in tm))
    return b


# ------------------------------------------------------------------------------------------------ root edits

def manifests(root):
    """Every manifest of a root: the files named SHA256SUMS* (SHA256SUMS, SHA256SUMS.instances), deepest first."""
    fs = [p for p in Path(root).rglob("SHA256SUMS*") if p.is_file() and "lean_build" not in p.parts]
    return sorted(fs, key=lambda p: (-len(p.parts), str(p)))


def redeclare(root, rel):
    """Re-declare `rel` (relative to root) in every manifest of the root that lists it, then, in turn, each manifest
    so changed: bottom-up, the instance SHA256SUMS, then SHA256SUMS.instances, then the root SHA256SUMS."""
    rel_p = root / rel
    for sums in manifests(root):
        base = sums.parent
        try:
            r = rel_p.relative_to(base)
        except ValueError:
            continue
        lines, hit = [], False
        for line in sums.read_text().splitlines():
            h, name = line.split("  ", 1)
            if name == str(r):
                h, hit = sha(rel_p), True
            lines.append(f"{h}  {name}")
        if hit:
            sums.write_text("".join(x + "\n" for x in lines))
            redeclare(root, sums.relative_to(root))


def drop_lines(root, prefix):
    """Remove the lines naming `prefix`/... from the root-level manifests (SHA256SUMS, SHA256SUMS.instances)."""
    for f in ("SHA256SUMS", "SHA256SUMS.instances"):
        p = root / f
        if p.exists():
            keep = [x for x in p.read_text().splitlines() if not x.split("  ", 1)[1].startswith(prefix + "/")]
            p.write_text("".join(x + "\n" for x in keep))
    redeclare(root, "SHA256SUMS.instances")


def edit_plan(root, edit):
    p = root / "PLAN.json"
    d = json.loads(p.read_text())
    edit(d)
    p.write_text(json.dumps(d, indent=1) + "\n")
    redeclare(root, "PLAN.json")


def place(src, dst, tmp, branch=None):
    """Copy a source root to dst, its seal_push remote pointed at a local bare repository."""
    shutil.copytree(src, dst, symlinks=True)
    plan = json.loads((dst / "PLAN.json").read_text())
    sp = plan.get("seal_push") or {}
    if sp and not sp.get("dry"):
        br = branch or sp["branch"]
        rem = bare_remote(tmp, br)

        def e(d):
            d["seal_push"].update(remote=str(rem), branch=br)
        edit_plan(dst, e)
    return dst


# ------------------------------------------------------------------------------------------------ running

def manifest_problems(roots):
    """Every manifest line (SHA256SUMS*) of the roots whose file is missing or differs (the test's own check)."""
    bad = []
    for root in dict.fromkeys(roots):
        for sums in manifests(root):
            for line in sums.read_text().splitlines():
                h, name = line.split("  ", 1)
                f = sums.parent / name
                if not f.exists() or sha(f) != h:
                    bad.append(f"{Path(root).name}/{f.relative_to(root)}: {'missing' if not f.exists() else 'differs'}"
                               f" (listed in {sums.relative_to(root)})")
    return bad


def run(tmp, roots, label, extra=()):
    out = tmp / f"OUT_{label}"
    problems = manifest_problems(roots)
    t0 = time.time()
    r = subprocess.run([PY, "-B", str(ANALYSIS), "test", str(out), *map(str, roots), "times=bare", *extra],
                       cwd=HERE, capture_output=True, text=True)
    res = json.loads((out / "RESULTS.json").read_text()) if r.returncode == 0 and (out / "RESULTS.json").exists() else None
    obs = dict(roots_manifest_problems=problems, exit=r.returncode, seconds=round(time.time() - t0, 1),
               message=(r.stderr.strip().splitlines() or [""])[-1][:600] if r.returncode else None)
    if res is not None:
        obs["counts"] = {g: {lv: dict(instances=x["instances"], counted=x["counted"],
                                      **{k: x[k]["n"] for k in ("held", "refuted", "not_completed", "no_prediction")})
                             for lv, x in v.items()} for g, v in res["counts"].items()}
        obs["verdicts"] = {g: {lv: v[lv]["verdict"] for lv in ("K0", "K3")} for g, v in res["groups"].items()}
    return r, res, obs


def refused(r):
    return r.returncode != 0 and "refused" in (r.stdout + r.stderr)


def not_inflated(res, group="NOT1", most=2):
    if res is None:
        return True
    c = res["counts"].get(group, {})
    return all(c[lv]["counted"] <= most for lv in c)


def entries(x):
    if isinstance(x, dict):
        yield x
        for v in x.values():
            yield from entries(v)
    elif isinstance(x, list):
        for v in x:
            yield from entries(v)


NOT_RUN = ("not run", "not_run")


def not_run_entry(res, *names, where=None):
    """An entry marking one of `names` as not run: a dict with a value starting with "not run" (or "not_run", e.g.
    "not run (home root absent)") beside a value naming it, or a key "not_run" (or "not run") whose content names it."""
    for e in entries(where if where is not None else res):
        flat = [v for v in e.values() if isinstance(v, str)]
        if any(v.startswith(NOT_RUN) for v in flat) and any(n in v for v in flat for n in names):
            return e
        for k in NOT_RUN:
            if k in e and any(n in json.dumps(e[k]) for n in names):
                return {k: e[k]}
    return None


def rows_sum(res, group, size):
    """Each level's rows of counts[group] sum to `size`, and `instances` is `size`."""
    c = (res or {}).get("counts", {}).get(group)
    if not c:
        return False
    return all(x["instances"] == size and sum(v["n"] for v in x.values() if isinstance(v, dict) and "n" in v) == size
               for x in c.values())


# ------------------------------------------------------------------------------------------------ the cases

def case_k05_alone(tmp, src):
    r, res, obs = run(tmp, [place(src / "out_K05", tmp / "a" / "out_K05", tmp)], "k05_alone")
    ok = r.returncode == 0 and res is not None and all(res["counts"]["NOT1"][lv]["counted"] == 2 for lv in ("K0", "K3"))
    return ok, obs


def case_k05_with_dupx(tmp, src):
    roots = [place(src / "out_K05", tmp / "a" / "out_K05", tmp), place(src / "out_K06", tmp / "a" / "out_K06", tmp)]
    r, res, obs = run(tmp, roots, "k05_with_dupx")
    ok = r.returncode == 0 and res is not None and all(res["counts"]["NOT1"][lv]["counted"] == 2 for lv in ("K0", "K3"))
    return ok, obs


def case_planned_seed_not_started(tmp, src):
    root = place(src / "out_K05", tmp / "a" / "out_K05", tmp)
    edit_plan(root, lambda d: d["groups"]["NOT1"]["seeds"].append(6230))
    r, res, obs = run(tmp, [root], "planned_seed_not_started")
    ok = r.returncode == 0 and rows_sum(res, "NOT1", 3) and all(
        not_run_entry(res, "NOT1_6230", where=res["counts"]["NOT1"][lv]) for lv in ("K0", "K3"))
    return ok, obs


def case_planned_machine_no_root(tmp, src):
    r, res, obs = run(tmp, [place(src / "out_K06", tmp / "a" / "out_K06", tmp)], "planned_machine_no_root")
    found = not_run_entry(res, "NOT1_6212") if res is not None else None
    obs["not_run_entry"] = found
    return r.returncode == 0 and found is not None, obs


END_OF_RUN = ("SHA256SUMS", "SHA256SUMS.instances", "RESULT.json", "RESULT_INSTANCES.json", "DONE", "INSTANCES_DONE",
              "INVENTORY_END")


def case_stopped_mid_instance(tmp, src):
    """K05 stopped during NOT1_6220's round N2: no final manifest, no N2/N3, a refuting N1."""
    root = place(src / "out_K05", tmp / "a" / "out_K05", tmp)
    d = root / "NOT1_6220"
    for f in END_OF_RUN:                                    # a stopped driver writes none of its end-of-run files
        (root / f).unlink(missing_ok=True)
    (d / "SHA256SUMS").unlink()
    for x in ("N2", "N3"):
        shutil.rmtree(d / x)
    for x in ("N2.log", "N3.log", "C2.log", "C3.log"):
        (d / x).unlink(missing_ok=True)
    rec = d / "N1" / "noisy_record.json"
    b = rec.read_bytes()
    assert b.count(b'"ssFF"') == 1
    rec.write_bytes(b.replace(b'"ssFF"', b'"sFFF"'))       # one letter: position 1, s -> F
    c = subprocess.run([PY, "-B", str(HERE / "compare_d2.py"), str(d / "seal"), str(HERE / "specs" / "not1.json"),
                        str(rec), "noisy", str(d / "N1" / "comparison.json")], cwd=HERE, capture_output=True, text=True)
    assert c.returncode == 0 and json.loads((d / "N1" / "comparison.json").read_text())["verdict"] == "refuted", c.stderr
    st = json.loads((d / "status.json").read_text())
    for k in ("C2", "N3", "C3"):
        st["steps"].pop(k, None)
    st["steps"]["N2"] = {k: v for k, v in st["steps"]["N2"].items() if k not in ("ended", "outputs", "cpu_s", "wall_s")}
    st["steps"]["N2"]["status"] = "running"
    st["steps"]["N1"]["outputs"]["N1/noisy_record.json"] = sha(rec)
    st["steps"]["C1"]["outputs"]["N1/comparison.json"] = sha(d / "N1" / "comparison.json")
    (d / "status.json").write_text(json.dumps(st, indent=1, sort_keys=True) + "\n")
    r, res, obs = run(tmp, [root], "stopped_mid_instance")
    if res is None:
        return False, obs
    k3 = res["counts"]["NOT1"]["K3"]
    flag = next((e for e in entries(res) if any(isinstance(v, str) and "NOT1_6220" in v for v in e.values())
                 and "manifest not final" in json.dumps(e)), None)
    obs["manifest_not_final_entry"] = None if flag is None else str(flag)[:300]
    ok = (r.returncode == 0 and "NOT1_6220" in k3["refuted"]["list"] and flag is not None
          and all("NOT1_6212" in res["counts"]["NOT1"][lv]["held"]["list"] for lv in ("K0", "K3")))
    return ok, obs


def draw_plans(tmp):
    """The plans plan_split3.py writes from the dummy draw and campaign_template.json (as in dev/freeze/PROOF.md)."""
    out = tmp / "draw_plans"
    if not out.exists():
        subprocess.run([PY, "-B", str(HERE / "plan_split3.py"), str(DRAW), str(HERE / "campaign_template.json"), str(out)],
                       cwd=HERE, check=True, capture_output=True)
    return out


def draw_root(src, dst, tmp, source, plan):
    """A root of the dummy draw's machine `plan` (PLAN_Knn.json), from a run2 root: its PLAN.json is the plan
    plan_split3.py writes, byte for byte (seal_push remote and branch included), re-declared in SHA256SUMS; the
    instance folders the plan does not hold are removed."""
    shutil.copytree(src / source, dst, symlinks=True)
    plans = draw_plans(tmp)
    want = json.loads((plans / plan).read_text())
    keep = {f"NOT1_{s}" for s in want["groups"].get("NOT1", {}).get("seeds", [])}
    for st in sorted(dst.glob("*/status.json")):
        if st.parent.name not in keep:
            shutil.rmtree(st.parent)
            drop_lines(dst, st.parent.name)
    shutil.copyfile(plans / plan, dst / "PLAN.json")
    redeclare(dst, "PLAN.json")
    return dst


def case_draw_machine_without_root(tmp, src):
    root = draw_root(src, tmp / "a" / "out_K01", tmp, "out_K05", "PLAN_K01.json")
    r, res, obs = run(tmp, [root], "draw_machine_without_root", extra=[f"{DRAW_ARG}={DRAW}"])
    ok = r.returncode == 0 and rows_sum(res, "NOT1", 2) and all(
        not_run_entry(res, "NOT1_6213", where=res["counts"]["NOT1"][lv]) for lv in ("K0", "K3"))
    return ok, obs


def case_draw_duplicate_machine_only(tmp, src):
    root = draw_root(src, tmp / "a" / "out_K03", tmp, "out_K06", "PLAN_K03.json")
    r, res, obs = run(tmp, [root], "draw_duplicate_machine_only", extra=[f"{DRAW_ARG}={DRAW}"])
    ok = r.returncode == 0 and rows_sum(res, "NOT1", 2) and all(
        not_run_entry(res, n, where=res["counts"]["NOT1"][lv]) for lv in ("K0", "K3") for n in ("NOT1_6212", "NOT1_6213"))
    return ok, obs


def case_draw_same_machine_twice(tmp, src):
    roots = [draw_root(src, tmp / x / "out_K01", tmp, "out_K05", "PLAN_K01.json") for x in ("a", "b")]
    r, res, obs = run(tmp, roots, "draw_same_machine_twice", extra=[f"{DRAW_ARG}={DRAW}"])
    return refused(r) and "K01" in (r.stdout + r.stderr) and not_inflated(res, most=1), obs


def case_same_root_30_times(tmp, src):
    root = place(src / "out_K05", tmp / "a" / "out_K05", tmp)
    r, res, obs = run(tmp, [root] * 30, "same_root_30_times")
    established = res is not None and any(v[lv]["verdict"] == "established" for v in res["groups"].values()
                                          for lv in ("K0", "K3"))
    return refused(r) and not_inflated(res) and not established, obs


def case_same_machine_two_paths(tmp, src):
    roots = [place(src / "out_K05", tmp / "a" / "out_K05", tmp), place(src / "out_K05", tmp / "b" / "out_K05", tmp)]
    r, res, obs = run(tmp, roots, "same_machine_two_paths")
    return refused(r) and not_inflated(res), obs


def case_home_instance_twice(tmp, src):
    a = place(src / "out_K05", tmp / "a" / "out_K05", tmp)
    b = place(src / "out_K05", tmp / "a" / "out_K07", tmp, branch="evidence/devtest-seals2-K07")
    shutil.rmtree(b / "NOT1_6220")
    drop_lines(b, "NOT1_6220")
    old, new = b'"branch": "evidence/devtest-seals2-K05"', b'"branch": "evidence/devtest-seals2-K07"'
    for f in sorted((b / "NOT1_6212").glob("N*/**/noisy_record.json")):   # the records name their machine's seal branch
        if old in f.read_bytes():
            f.write_bytes(f.read_bytes().replace(old, new))
            redeclare(b, f.relative_to(b))

    def e(d):
        d["groups"]["NOT1"].update(seeds=[6212], d4_audit=[])
        d["what"] = "defect test D9: a copy of K05 without NOT1_6220, on its own seal branch (TEST)"
    edit_plan(b, e)
    r, res, obs = run(tmp, [a, b], "home_instance_twice")
    return refused(r) and not_inflated(res), obs


def case_one_byte_in_comparison(tmp, src):
    root = place(src / "out_K05", tmp / "a" / "out_K05", tmp)
    f = root / "NOT1_6212" / "N0" / "comparison.json"
    b = f.read_bytes()
    assert b.count(b'"cell_bits": 2') == 1
    f.write_bytes(b.replace(b'"cell_bits": 2', b'"cell_bits": 3'))
    r, res, obs = run(tmp, [root], "one_byte_in_comparison")
    return refused(r) and "N0/comparison.json" in (r.stdout + r.stderr), obs


def case_listed_file_missing(tmp, src):
    root = place(src / "out_K05", tmp / "a" / "out_K05", tmp)
    f = root / "NOT1_6212" / "N2" / "extract" / "extract.json"
    assert "N2/extract/extract.json" in (root / "NOT1_6212" / "SHA256SUMS").read_text()
    f.unlink()
    r, res, obs = run(tmp, [root], "listed_file_missing")
    return refused(r) and "extract.json" in (r.stdout + r.stderr), obs


# The manifest problems a case makes on purpose. Every other case must leave its roots' manifests consistent: that is
# asserted, so a refusal in a D8 or D9 case cannot come from the fixture.
TAMPERED = {
    "one_byte_in_comparison": ["out_K05/NOT1_6212/N0/comparison.json: differs"],
    "listed_file_missing": ["out_K05/NOT1_6212/N2/extract/extract.json: missing"],
}

CASES = [
    ("control", "k05_alone", case_k05_alone, "exit 0; NOT1 counted 2 at K0 and K3"),
    ("control", "k05_with_dupx", case_k05_with_dupx, "exit 0; NOT1 counted 2 at K0 and K3 (the DUPX_ folder is a control)"),
    ("D8", "planned_seed_not_started", case_planned_seed_not_started,
     "exit 0; NOT1 rows sum to 3 at K0 and K3; a not_run entry for NOT1_6230 at each level"),
    ("D8", "planned_machine_no_root", case_planned_machine_no_root,
     "no draw: exit 0 and a not_run entry naming NOT1_6212 (the home instance K06's plan names); no refusal"),
    ("D8", "draw_machine_without_root", case_draw_machine_without_root,
     "draw=: exit 0; NOT1 rows sum to 2 at K0 and K3; a not_run entry for NOT1_6213 (K02, no root) at each level"),
    ("D8", "draw_duplicate_machine_only", case_draw_duplicate_machine_only,
     "draw=: exit 0; NOT1 rows sum to 2 at K0 and K3; not_run entries for NOT1_6212 (K01) and NOT1_6213 (K02)"),
    ("D9", "same_root_30_times", case_same_root_30_times,
     "refused; NOT1 not counted more than twice; no verdict \"established\""),
    ("D9", "draw_same_machine_twice", case_draw_same_machine_twice,
     "draw=: refused, the output naming K01; NOT1 not counted more than once"),
    ("D9", "same_machine_two_paths", case_same_machine_two_paths, "refused; NOT1 not counted more than twice"),
    ("D9", "home_instance_twice", case_home_instance_twice, "refused; NOT1 not counted more than twice"),
    ("D10", "one_byte_in_comparison", case_one_byte_in_comparison, "refused; the output names N0/comparison.json"),
    ("D10", "listed_file_missing", case_listed_file_missing, "refused; the output names extract.json"),
    ("D10", "stopped_mid_instance", case_stopped_mid_instance,
     "exit 0; NOT1_6220 refuted at K3 with an entry saying \"manifest not final\"; NOT1_6212 held at K0 and K3"),
]


def main(out_json=None):
    lean = shutil.which("lean")
    head = git("rev-parse", "HEAD", cwd=REPO).strip()
    code = git("log", "-1", "--format=%H", "--", "research/layered-networks/analysis.py", cwd=REPO).strip()
    report = dict(format="layered-analysis-defects/1", script_sha256=sha(__file__), analysis_sha256=sha(ANALYSIS),
                  tree_head=head, analysis_last_commit=code, lean=dict(path=lean, sha256=sha(lean) if lean else None),
                  cases=[])
    with tempfile.TemporaryDirectory() as t:
        t = Path(t)
        src = sources(t)
        for defect, name, fn, asserts in CASES:
            w = t / name
            w.mkdir()
            try:
                ok, obs = fn(w, src)
                got = sorted(x.split(" (listed in")[0] for x in obs.get("roots_manifest_problems", []))
                want = sorted(TAMPERED.get(name, []))
                obs["fixture_ok"] = got == want                       # only the D10 tampering, nothing else
                ok = ok and obs["fixture_ok"]
            except Exception as e:                                     # a crash of the setup, not of the analysis
                ok, obs = False, dict(setup_error=repr(e))
            print(f"{'PASS' if ok else 'FAIL'}  {defect:7} {name}: {json.dumps(obs)[:400]}", flush=True)
            report["cases"].append(dict(defect=defect, case=name, asserts=asserts, result="PASS" if ok else "FAIL",
                                        observed=obs))
            shutil.rmtree(w, ignore_errors=True)
    if out_json:
        Path(out_json).write_text(json.dumps(report, indent=1, sort_keys=True) + "\n")
    bad = [c["case"] for c in report["cases"] if c["result"] != "PASS"]
    print(f"{len(report['cases']) - len(bad)} of {len(report['cases'])} cases pass" + (f"; failing: {bad}" if bad else ""))
    return not bad


if __name__ == "__main__":
    sys.exit(0 if main(*sys.argv[1:2]) else 1)
