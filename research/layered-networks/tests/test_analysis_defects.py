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
  compare_d2.py, which gives "refuted". Must: exit 0, NOT1_6220 in the K3 refuted row, its instance row's K3 refuted
  and flagged (a key or text "manifest_not_final" / "manifest not final"), and NOT1_6212 held at K0 and K3.
- draw standin_*: a real draw stands in for the campaign's (see `standin`: quicknet round 1000000 as published, the
  announce push time 600 s before its time, draw_seeds.draw over the pinned EXCLUDED.json with NOT1=2 ANDOR3=1
  XOR3=1, DRAW_ANNOUNCE.txt in mode test, passed as draw=, excluded=, announce=). The root is K03's of that draw
  (out_K05 with the plan's PLAN.json and no instance or U_ folder). standin_draw_valid must give exit 0 with every
  planned instance not run; each mutation (one seed changed; the push time +3 s; one signature byte; an exclusion
  list that is not a superset of the pinned one; one whose bytes are not the announced ones) must be refused, and
  counts as passed only if standin_draw_valid passed in the same run (so a refusal of the arguments or of the root
  does not count).
  Not exercised: the push time read from GitHub, the round fetched from drand.
- E2 standin_activity_*: the stand-in draw with activity=PATH, a JSON list of the raw GitHub activity items of the
  announce branch (activity_type, after, before, ref, timestamp). clean: one branch_creation whose "after" is the
  announce commit, at announce.push_utc; must be accepted. redone: a branch_creation of another commit an hour
  earlier, its branch_deletion, then the branch_creation of the announce commit that DRAW.json uses; must be refused.
  force_push: the clean creation, then a force_push; must be refused. The two refusals count only if clean passed in
  the same run. Not exercised: reading the activity from GitHub (campaign and rehearsal).
- beacon *: one signed drand value has several writings the verifiers accept (upper case, mixed case; spaces and a 0x
  prefix pass bytes.fromhex), and draw_seeds.draw hashes the string as given. beacon_canonical (control): the
  lowercase draw gives the seeds of the ef374ccd formula over the pinned list (derived at run time). beacon_<writing>: draw_seeds.draw (the narrowest real function) on that writing
  must raise or give the canonical seeds. sizes_permutations: the sizes dict in all 6 orders, at 166 per group (the
  smallest equal sizes where the groups collide at round 1000000), must give identical seeds. standin_beacon_<writing>:
  the analysis's entry point on a DRAW.json written that way (seeds drawn on that writing, a root matching its plan)
  must refuse it, or accept it with the canonical seeds; gated on standin_draw_valid. That DRAW.json is built as a
  forger would build it, with the ef374ccd seed formula inline (forger_groups), not with the pinned draw_seeds.py,
  which may refuse the writing; a fixture that raises records setup_error and fails the case.
- X1 *: one signature has several byte strings that decode to the same point (zero bytes in front). The real function
  beacon_verify.verify must accept round 1000000 as published (control) and refuse it with 00, 0000 or 000000 in
  front (value = sha256 of the padded bytes). standin_signature_<pad>: a forged DRAW.json with that signature, its value
  as beacon and randomness, and the seeds a forger draws on it (forger_groups); the analysis must refuse it.
  standin_signature_flip: one signature byte flipped, value and seeds from it; the refusal must come from the
  signature check ("does not verify against the pinned quicknet key" or a decoding failure). The earlier
  standin_signature_byte (flip only, value kept) stays. verify_other_round and standin_signature_other_round present
  round 20000000's valid signature as round 1000000's (value = sha256 of it, the forger's seeds): the point decodes and
  is in the subgroup, so the refusal must come from the pairing itself (no decoding failure).
- X2 *: plan_split3.py run as a command on the DRAW.json file (json.loads sorts the keys) must give, at 6/6/6 and at
  60/32/37, the same 12 plans as plan_split3.split of the draw in memory (the analysis's expected plans).
  standin_plans_from_command: the 6/6/6 stand-in with plans from the command, a root for each machine holding remote
  duplicates, draw=; must be accepted (exit 0). Gated on standin_draw_valid.
- R *: the rehearsal draw (round 1000000, 6/6/6, mode rehearsal, the pinned list) and a campaign draw on round
  20000000 (n 2/1/1, mode test), each with its announce, excluded file and clean activity, passed offline as draw=,
  excluded=, announce=, activity= and rehearsal_draw=, rehearsal_excluded=, rehearsal_announce=, rehearsal_activity=;
  one root, the first campaign machine holding a home instance (out_K05, no instance folder). rehearsal_full_list
  (control): the campaign list is the pinned list plus every rehearsal seed S and 10 S + 0..3; exit 0. Then one S left
  out, one 10 S + 1 left out (each refused and named), and the rounds swapped so the rehearsal's announce is later
  (refused). The mutations count only if the control passed. Not tested: campaign mode without rehearsal_draw= (campaign
  mode refuses these TEST roots before any draw check).
- E1 round_own_check_failed: K05 with NOT1_6220's round N2 left as the driver leaves a run stopped by its own check
  (see failed_round: the record's status "failed: the tail leak must be set before it starts", N2 failed with why
  "exit 1", no C2, no N2/comparison.json, an unlisted placeholder N2/trace.raw (a real header, data cut off; only its
  presence matters), the manifests and RESULT_INSTANCES.json rebuilt by the driver's rules). Must:
  exit 0, NOT1_6220 among the K3 refuted instances, and a node of counts.NOT1.K3 naming it with its status and "own
  check" in its key path or text; NOT1_6212 held at K0 and K3.
- E1 round_simulator_ended (the twin): the same (placeholder trace.raw included) with "failed: the simulator ended during: tran 1n 2n". Must: exit 0,
  NOT1_6220 in the K3 not_completed row and not refuted; NOT1_6212 held. (Expected to pass before the fix too.)
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
    row = next((i for i in res["instances"] if i["instance"] == "NOT1_6220"), {})
    k3_row = row.get("K3") or {}
    flag = k3_row.get("refuted") is True and any(x in json.dumps(k3_row) for x in ("manifest not final", "manifest_not_final"))
    obs["NOT1_6220_K3"] = k3_row
    ok = (r.returncode == 0 and "NOT1_6220" in k3["refuted"]["list"] and flag
          and all("NOT1_6212" in res["counts"]["NOT1"][lv]["held"]["list"] for lv in ("K0", "K3")))
    return ok, obs


def draw_plans(tmp):
    """The plans plan_split3.py writes from the dummy draw and campaign_template.json (as in dev/freeze/PROOF.md)."""
    out = tmp / "draw_plans"
    if not out.exists():
        subprocess.run([PY, "-B", str(HERE / "plan_split3.py"), str(DRAW), str(HERE / "campaign_template.json"), str(out)],
                       cwd=HERE, check=True, capture_output=True)
    return out


def draw_root(src, dst, tmp, source, plan, plans=None, controls=True):
    """A root of the dummy draw's machine `plan` (PLAN_Knn.json), from a run2 root: its PLAN.json is the plan
    plan_split3.py writes, byte for byte (seal_push remote and branch included), re-declared in SHA256SUMS; the
    instance folders the plan does not hold are removed."""
    shutil.copytree(src / source, dst, symlinks=True)
    plans = plans or draw_plans(tmp)
    want = json.loads((plans / plan).read_text())
    keep = {f"{g}_{s}" for g, v in want["groups"].items() for s in v.get("seeds", [])}
    gone = [st.parent for st in sorted(dst.glob("*/status.json")) if st.parent.name not in keep]
    if not controls:                                        # also the controls (they belong to the old seeds)
        gone += sorted(dst.glob("U_*")) + sorted(dst.glob("DUPX_*"))
    for d in gone:
        shutil.rmtree(d)
        drop_lines(dst, d.name)
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


# ------------------------------------------------------------------------------------------------ a real draw (stand-in)
# drand quicknet round 1000000 as published (tests/test_beacon_published.py), the announce push time set 600 s before
# its time, so that beacon_verify.round_after gives exactly 1000000; draw_seeds.draw over the pinned EXCLUDED.json with
# small sizes; DRAW_ANNOUNCE.txt in mode test. What is exercised: the BLS signature, randomness = sha256(signature),
# the round rule, the recomputation of the seeds and bytes, the exclusion list's sha and superset checks, the plans
# from the recomputed draw. What is not: the push time read from GitHub and the round fetched from drand.

ROUND_1M = dict(round=1000000, randomness="b22aad4794f7451896f7a371aa46106fd84d919f3f569acd5b2fddf1d1440af3",
                signature="83ad29e4c409f9470fc2ef02f90214df49e02b441a1a241a82d622d9f608ef98fd8b11a029f1bee9d9e83b45088abe72")
STANDIN_SIZES = dict(NOT1=2, ANDOR3=1, XOR3=1)
STANDIN_COMMIT = hashlib.sha1(b"defect test stand-in announce").hexdigest()


STANDIN_BRANCH = "evidence/defect-test-standin-draw"


def activity_items(kind, commit, t0, utc):
    """Raw GET /repos/{o}/{r}/activity items of the announce branch (the keys sealpush.github_times reads)."""
    ref, zero = f"refs/heads/{STANDIN_BRANCH}", "0" * 40
    other = hashlib.sha1(b"defect test: the first, deleted announce").hexdigest()
    item = lambda t, typ, after, before=zero: dict(activity_type=typ, after=after, before=before, ref=ref, timestamp=utc(t))
    if kind == "clean":
        return [item(t0, "branch_creation", commit)]
    if kind == "redone":                    # created, deleted, created again later; the DRAW.json uses the second
        return [item(t0 - 3600, "branch_creation", other), item(t0 - 1800, "branch_deletion", zero, other),
                item(t0, "branch_creation", commit)]
    if kind == "force_push":                # the clean creation, then a force push on the branch
        return [item(t0, "branch_creation", commit), item(t0 + 60, "force_push", other, commit)]
    raise ValueError(kind)


# One drand value, several writings: the verifiers compare the randomness case-insensitively (and bytes.fromhex accepts
# spaces), while draw_seeds.draw hashes the beacon string as given.
WRITINGS = {
    "upper": lambda h: h.upper(),
    "mixed": lambda h: "".join(c.upper() if i % 2 else c for i, c in enumerate(h)),
    "spaces": lambda h: " ".join(h[i:i + 2] for i in range(0, len(h), 2)),
    "0x": lambda h: "0x" + h,
}
def canonical_seeds():
    """The stand-in's seeds, derived at run time (they follow the pinned EXCLUDED.json, which each rescan changes): the
    seed formula as written at ef374ccd (forger_groups, inline), on the canonical lowercase value of round 1000000, over
    the pinned list, at STANDIN_SIZES. At 2/1/1 no group collides, so the group order does not matter."""
    ex = json.loads((HERE / "EXCLUDED.json").read_text())
    return forger_groups(ROUND_1M["randomness"], ROUND_1M["round"], ex, dict(STANDIN_SIZES))[0]
COLLIDING_SIZES = dict(NOT1=166, ANDOR3=166, XOR3=166)   # the smallest equal sizes where groups collide at round 1000000


def forger_groups(beacon, rnd, excluded, sizes):
    """The seed formula as draw_seeds.py had it at ef374ccd, inline: S = 10000 + sha256("<beacon>|<round>|<group>|<k>")
    mod 90000, the beacon string hashed as given, groups in the order given, `drawn` shared across groups. It is how a
    forger builds a DRAW.json without the fixed draw_seeds.py (which refuses a non-canonical writing)."""
    ex, drawn, groups, tried = set(excluded["seeds"]), set(), {}, {}
    for g, n in sizes.items():
        out, k = [], 0
        while len(out) < n:
            s_ = 10000 + int.from_bytes(hashlib.sha256(f"{beacon}|{rnd}|{g}|{k}".encode()).digest(), "big") % 90000
            k += 1
            if s_ in ex or s_ in drawn or any(10 * s_ + j in ex for j in range(4)):
                continue
            out.append(s_)
            drawn.add(s_)
        groups[g], tried[g] = out, k
    return groups, tried


def forged_draw(canonical, written, excluded, sizes=None, signature=None):
    """The canonical stand-in DRAW (its keys as the pinned draw_seeds writes them), with the beacon and
    beacon_round.randomness set to `written` (another writing, or the value of another signature) and the seeds a
    forger draws on it; `signature`, if given, replaces beacon_round.signature."""
    D = json.loads(json.dumps(canonical))
    groups, tried = forger_groups(written, ROUND_1M["round"], excluded, dict(sizes or STANDIN_SIZES))
    D.update(beacon=written, groups=groups)
    if "candidates_tried" in D:
        D["candidates_tried"] = tried
    D["beacon_round"]["randomness"] = written
    if signature is not None:
        D["beacon_round"]["signature"] = signature
    return D


def forged_signature(kind):
    """Signature bytes a forger can publish for round 1000000: zero bytes in front ("pad00", "pad0000", ...), or one
    byte flipped ("flip"). Returns (signature hex, value = sha256(signature bytes) hex)."""
    sig = bytes.fromhex(ROUND_1M["signature"])
    if kind.startswith("pad"):
        sig = bytes.fromhex(kind[3:]) + sig
    elif kind == "other_round":                              # a valid on-curve point: round 20000000's signature
        sig = bytes.fromhex(ROUND_20M["signature"])
    elif kind == "flip":
        b = bytearray(sig)
        b[10] ^= 1
        sig = bytes(b)
    else:
        raise ValueError(kind)
    return sig.hex(), hashlib.sha256(sig).hexdigest()


def standin(tmp, seed_edit=False, push_shift_s=0, sig_flip=False, excluded="pinned", activity=None, writing=None,
            sizes=None, sig_forge=None, plans_cmd=False):
    """Write DRAW.json, DRAW_ANNOUNCE.txt and the excluded file of the stand-in draw, one mutation applied, and the
    plans of the VALID draw. Returns (args, plans)."""
    sys.path.insert(0, str(HERE))
    import beacon_chain as BC
    import beacon_verify as BV
    import draw_seeds as DS
    import plan_split3 as P3
    import datetime
    d = tmp / "draw"
    d.mkdir(parents=True)
    pinned_b = (HERE / "EXCLUDED.json").read_bytes()
    pinned = json.loads(pinned_b)
    t0 = BV.round_time(BC.QUICKNET, ROUND_1M["round"]) - 600
    utc = lambda t: datetime.datetime.fromtimestamp(t, datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    assert BV.round_after(BC.QUICKNET, utc(t0)) == ROUND_1M["round"]

    sizes = dict(sizes or STANDIN_SIZES)

    def make(ex, beacon=ROUND_1M["randomness"]):
        D = DS.draw(beacon, ROUND_1M["round"], ex, dict(sizes))
        D["beacon_round"] = dict(ROUND_1M, randomness=beacon)
        D["announce"] = dict(branch=STANDIN_BRANCH, commit=STANDIN_COMMIT, push_utc=utc(t0))
        return D

    if writing is not None:
        valid = forged_draw(make(pinned), WRITINGS[writing](ROUND_1M["randomness"]), pinned, sizes)
    elif sig_forge is not None:
        sig_hex, value = forged_signature(sig_forge)
        valid = forged_draw(make(pinned), value, pinned, sizes, signature=sig_hex)
    else:
        valid = make(pinned)
    plans = tmp / "draw_plans"                              # the plans of the draw as written (a matching root)
    plans.mkdir()
    for k, pl in enumerate(P3.split(valid, json.loads((HERE / "campaign_template.json").read_text()), 12)[0], start=1):
        (plans / f"PLAN_K{k:02d}.json").write_bytes(DS.canon(pl))
    ex_b, announced = pinned_b, hashlib.sha256(pinned_b).hexdigest()
    D = valid
    if excluded == "not_superset":                          # one seed less, consistent in itself and announced
        seeds = pinned["seeds"][1:]
        ex = dict(pinned, seeds=seeds, count=len(seeds), seeds_sha256=hashlib.sha256(DS.canon(seeds)).hexdigest())
        ex_b = DS.canon(ex)
        announced = hashlib.sha256(ex_b).hexdigest()
        D = make(ex)
    elif excluded == "sha_differs":                         # the same seeds, other bytes: not the announced file
        ex_b = (json.dumps(pinned, indent=1, sort_keys=True) + "\n").encode()
        assert json.loads(ex_b) == pinned and ex_b != pinned_b
    D = json.loads(json.dumps(D))
    if seed_edit:
        D["groups"]["NOT1"][1] += 1
    if push_shift_s:
        D["announce"]["push_utc"] = utc(t0 + push_shift_s)
    if sig_flip:
        b = bytearray(bytes.fromhex(D["beacon_round"]["signature"]))
        b[10] ^= 1
        D["beacon_round"]["signature"] = b.hex()
    (d / "DRAW.json").write_bytes(DS.canon(D))
    (d / "EXCLUDED.json").write_bytes(ex_b)
    if plans_cmd:                                          # the plans as the procedure makes them: the command, on the file
        shutil.rmtree(plans)
        subprocess.run([PY, "-B", str(HERE / "plan_split3.py"), str(d / "DRAW.json"), str(HERE / "campaign_template.json"),
                        str(plans)], cwd=HERE, check=True, capture_output=True)
    words = " ".join(f"{g}={n}" for g, n in sizes.items())
    (d / "DRAW_ANNOUNCE.txt").write_text(f"format layered-draw-announce/1\nmode test\nexcluded_sha256 {announced}\n"
                                         f"sizes {words}\n")
    args = [f"{DRAW_ARG}={d / 'DRAW.json'}", f"excluded={d / 'EXCLUDED.json'}", f"announce={d / 'DRAW_ANNOUNCE.txt'}"]
    if activity:
        (d / "activity.json").write_text(json.dumps(activity_items(activity, STANDIN_COMMIT, t0, utc), indent=1) + "\n")
        args.append(f"activity={d / 'activity.json'}")
    return args, plans


def standin_run(tmp, src, label, **mutation):
    args, plans = standin(tmp, **mutation)
    root = draw_root(src, tmp / "a" / "out_K03", tmp, "out_K05", "PLAN_K03.json", plans=plans, controls=False)
    return run(tmp, [root], label, extra=args)


# ------------------------------------------------------------------------------------------------ X1: padded signatures
PADS = ("pad00", "pad0000", "pad000000")
# Published by drand quicknet (tests/test_beacon_published.py): a valid signature, but of another round.
ROUND_20M = dict(round=20000000, randomness="f39c98df5525968e6622e0c63edb3d1f9c5607cf780db78abdded36e4b3dba95",
                 signature="96892582a33552a7b67ba44ef09c3ccd535bbebe760c93ecf45be8958d0c0f06390c6d19d7bf492eb806af7eef6b125c")


def case_verify_other_round(tmp, src):
    """beacon_verify.verify: round 20000000's signature (and its own randomness) presented as round 1000000's. The
    point decodes and is in the subgroup; only the pairing can refuse it."""
    sig_hex, value = forged_signature("other_round")
    assert value == ROUND_20M["randomness"]
    r = bv_verify(sig_hex, value)
    ok = r.get("ok") is False and r.get("subgroups_ok") is True and r.get("signature_ok") is False and not r.get("why")
    return ok, dict(verify=r)


def bv_verify(sig_hex, value):
    sys.path.insert(0, str(HERE))
    import beacon_chain as BC
    import beacon_verify as BV
    return BV.verify(BC.QUICKNET, dict(round=ROUND_1M["round"], signature=sig_hex, randomness=value))


def case_verify_signature_real(tmp, src):
    """beacon_verify.verify (the real function) on round 1000000 as published: accepted."""
    r = bv_verify(ROUND_1M["signature"], ROUND_1M["randomness"])
    return r.get("ok") is True, dict(verify=r)


def verify_pad_case(kind):
    def case(tmp, src):
        sig_hex, value = forged_signature(kind)
        try:
            r = bv_verify(sig_hex, value)
        except Exception as e:                                   # a refusal by exception is a refusal
            return True, dict(signature_prefix=sig_hex[:12], raised=repr(e)[:300])
        return r.get("ok") is not True, dict(signature_prefix=sig_hex[:12], value=value, verify=r)
    case.__name__ = f"case_verify_signature_{kind}"
    return case


def standin_sig_case(kind, want=None, avoid=()):
    def case(tmp, src):
        r, res, obs = standin_run(tmp, src, f"standin_signature_{kind}", sig_forge=kind)
        obs["control_passed"] = STANDIN_CONTROL.get("ok", False)
        text = r.stdout + r.stderr
        ok = (refused(r) and obs["control_passed"] and (want is None or any(w in text for w in want))
              and not any(a in text for a in avoid))
        return ok, obs
    case.__name__ = f"case_standin_signature_{kind}"
    return case


# ------------------------------------------------------------------------------------------------ X2: the plan split
X2_SIZES = (dict(NOT1=6, ANDOR3=6, XOR3=6), dict(NOT1=60, ANDOR3=32, XOR3=37))


def command_vs_split(tmp, sizes):
    """plan_split3.py run as a command on the DRAW.json file, against plan_split3.split on the draw in memory (the
    analysis's expected plans: plan_split3.split of the recomputed draw, the frozen template, 12 machines)."""
    sys.path.insert(0, str(HERE))
    import draw_seeds as DS
    import plan_split3 as P3
    ex = json.loads((HERE / "EXCLUDED.json").read_text())
    D = DS.draw(ROUND_1M["randomness"], ROUND_1M["round"], ex, dict(sizes))
    (tmp / "DRAW.json").write_bytes(DS.canon(D))
    subprocess.run([PY, "-B", str(HERE / "plan_split3.py"), str(tmp / "DRAW.json"), str(HERE / "campaign_template.json"),
                    str(tmp / "plans")], cwd=HERE, check=True, capture_output=True)
    mem = P3.split(D, json.loads((HERE / "campaign_template.json").read_text()), 12)[0]
    diff = {}
    for k, pl in enumerate(mem, start=1):
        f = json.loads((tmp / "plans" / f"PLAN_K{k:02d}.json").read_text())
        if f != pl:
            diff[f"K{k:02d}"] = {key: dict(command=f.get(key), split=pl.get(key)) for key in sorted(set(f) | set(pl))
                                 if f.get(key) != pl.get(key)}
    return diff


def plans_case(sizes):
    def case(tmp, src):
        diff = command_vs_split(tmp, sizes)
        return not diff, dict(sizes=sizes, differing=json.loads(json.dumps(diff))) if diff else dict(sizes=sizes)
    case.__name__ = "case_plans_command_" + "_".join(str(n) for n in sizes.values())
    return case


def case_standin_plans_from_command(tmp, src):
    """The stand-in draw at 6/6/6, its plans made by the plan_split3.py command on the DRAW.json file; a root for each
    machine holding remote duplicates (out_K06 with that plan, no instance, U_ or DUPX_ folder), with draw=."""
    args, plans = standin(tmp, sizes=X2_SIZES[0], plans_cmd=True)
    ks = [f.name for f in sorted(plans.glob("PLAN_K*.json")) if json.loads(f.read_text())["remote_duplicates"]]
    roots = [draw_root(src, tmp / "a" / f"out_{f[5:8]}", tmp, "out_K06", f, plans=plans, controls=False) for f in ks]
    r, res, obs = run(tmp, roots, "standin_plans_from_command", extra=args)
    obs.update(machines=[f[5:8] for f in ks], control_passed=STANDIN_CONTROL.get("ok", False))
    return r.returncode == 0 and obs["control_passed"], obs


# ------------------------------------------------------------------------------------------------ E1: a run's own check
# How it arises (controls4.py stagen and campaign.py Instance.step / Instance.round): when noise2.train_and_test raises
# inside controls4.stagen, the exception is caught, the trace is still written (trace.digest.json), and the record
# N<n>/noisy_record.json is written with status "failed: <message>" and empty lessons, words, tests and skews; stagen
# exits 1. Both outputs exist, so campaign.py records N<n> as {status: "failed", why: "exit 1"} with no outputs; the
# round stops there, so C<n> never runs, N<n>/comparison.json does not exist, and after_comparison (the extract) never
# runs. The other rounds run in parallel and are untouched. At the end the driver writes the instance's SHA256SUMS
# (every *.json but status.json), RESULT_INSTANCES.json (its summary: step statuses, verdicts, times),
# SHA256SUMS.instances, RESULT.json and the root SHA256SUMS. All are rebuilt here by the same rules.
# The raw trace stays: N<n>/trace.raw is left in place, in no manifest, since neither the extract nor the comparison
# ran. The fixture puts a placeholder there: the header of a real trace.raw of the same root (up to and including its
# "Binary:" line), the data cut off. Its content is not read; only its presence matters (an unlisted file).

OWN_CHECK = "failed: the tail leak must be set before it starts"      # instrument.py's assertion during training
SIM_ENDED = "failed: the simulator ended during: tran 1n 2n"          # session.py's RuntimeError


def driver_dumps(obj):
    return json.dumps(obj, indent=1, sort_keys=True) + "\n"          # campaign.dumps


def failed_round(root, inst, n, status):
    """Instance `inst` of `root` as the driver leaves it when N<n>'s own run fails with `status`."""
    d = root / inst
    nd = d / f"N{n}"
    rec = json.loads((nd / "noisy_record.json").read_text())
    rec.update(status=status, lessons=[], words={}, tests=[], skews=[])
    (nd / "noisy_record.json").write_text(json.dumps(rec, indent=1, default=str) + "\n")   # controls4's writer
    (nd / "comparison.json").unlink()
    shutil.rmtree(nd / "extract", ignore_errors=True)
    real = next(iter(sorted(root.glob("*/N*/trace.raw"))))                # kept raws of the root (plan keep_raw)
    head = real.read_bytes()
    (nd / "trace.raw").write_bytes(head[:head.index(b"Binary:\n") + len(b"Binary:\n")])
    (d / f"C{n}.log").unlink(missing_ok=True)
    st = json.loads((d / "status.json").read_text())
    old = st["steps"][f"N{n}"]
    st["steps"][f"N{n}"] = dict(argv=old["argv"], started=old["started"], status="failed", why="exit 1",
                                wall_s=old.get("wall_s"), cpu_s=old.get("cpu_s"), ended=old["ended"], cores=old.get("cores", 1))
    st["steps"].pop(f"C{n}", None)
    (d / "status.json").write_text(driver_dumps(st))
    files = sorted(p for p in d.rglob("*.json") if p.name != "status.json" and "lean_build" not in p.parts)
    (d / "SHA256SUMS").write_text("".join(f"{sha(p)}  {p.relative_to(d)}\n" for p in files))   # Instance.summary
    for f in ("RESULT_INSTANCES.json", "RESULT.json"):
        if not (root / f).exists():
            continue
        r = json.loads((root / f).read_text())
        for x in r["instances"]:
            if f"{x['tag']}_{x['seed']}" == inst:
                x["steps"] = {k: v["status"] for k, v in st["steps"].items()}
                x["verdicts"].pop(f"C{n}", None)
                for k in ("cpu_s", "wall_s"):
                    x[k] = {k_: v.get(k) for k_, v in st["steps"].items()}
        (root / f).write_text(driver_dumps(r))
    for f in (f"{inst}/SHA256SUMS", "RESULT_INSTANCES.json", "RESULT.json"):
        redeclare(root, f)


def own_check_entry(res, inst, status):
    """A node under counts.NOT1.K3 naming `inst` and its status, with "own check" in its path or content."""
    def walk(x, path):
        if isinstance(x, dict):
            yield path, x
            for k, v in x.items():
                yield from walk(v, path + [str(k)])
        elif isinstance(x, list):
            for i, v in enumerate(x):
                yield from walk(v, path + [str(i)])
    k3 = ((res or {}).get("counts", {}).get("NOT1") or {}).get("K3") or {}
    for path, node in walk(k3, []):
        if node is k3:
            continue
        text = json.dumps(node) + " " + " ".join(path)
        if inst in text and status.split("failed: ", 1)[1] in text and ("own check" in text or "own_check" in text):
            return dict(path=path, node=node)
    return None


def case_round_own_check_failed(tmp, src):
    root = place(src / "out_K05", tmp / "a" / "out_K05", tmp)
    failed_round(root, "NOT1_6220", 2, OWN_CHECK)
    r, res, obs = run(tmp, [root], "round_own_check_failed")
    hit = own_check_entry(res, "NOT1_6220", OWN_CHECK)
    obs["own_check_entry"] = hit
    g = ((res or {}).get("groups") or {}).get("NOT1", {}).get("K3", {})
    ok = (r.returncode == 0 and hit is not None and "NOT1_6220" in g.get("refuted_instances", [])
          and all("NOT1_6212" in res["counts"]["NOT1"][lv]["held"]["list"] for lv in ("K0", "K3")))
    return ok, obs


def case_round_simulator_ended(tmp, src):
    root = place(src / "out_K05", tmp / "a" / "out_K05", tmp)
    failed_round(root, "NOT1_6220", 2, SIM_ENDED)
    r, res, obs = run(tmp, [root], "round_simulator_ended")
    if res is None:
        return False, obs
    k3 = res["counts"]["NOT1"]["K3"]
    nc = json.dumps(k3["not_completed"]["list"])
    ok = (r.returncode == 0 and "NOT1_6220" in nc and "NOT1_6220" not in res["groups"]["NOT1"]["K3"]["refuted_instances"]
          and all("NOT1_6212" in res["counts"]["NOT1"][lv]["held"]["list"] for lv in ("K0", "K3")))
    return ok, obs


STANDIN_CONTROL = {}


def draw_function(beacon, sizes=None):
    sys.path.insert(0, str(HERE))
    import draw_seeds as DS
    ex = json.loads((HERE / "EXCLUDED.json").read_text())
    return DS.draw(beacon, ROUND_1M["round"], ex, dict(sizes or STANDIN_SIZES))["groups"]


def case_beacon_canonical(tmp, src):
    """draw_seeds.draw (the narrowest real function; no root needed) on the canonical lowercase beacon."""
    got = draw_function(ROUND_1M["randomness"])
    want = canonical_seeds()
    return got == want, dict(seeds=got, want=want)


def beacon_writing_case(name):
    def case(tmp, src):
        w = WRITINGS[name](ROUND_1M["randomness"])
        try:
            got = draw_function(w)
        except Exception as e:                                    # refused: acceptable
            return True, dict(writing=w, refused=repr(e)[:300])
        want = canonical_seeds()
        return got == want, dict(writing=w, seeds=got, canonical=want)
    case.__name__ = f"case_beacon_{name}"
    return case


def case_sizes_permutations(tmp, src):
    """draw_seeds.draw with the sizes dict in each of its 6 orders, at sizes where the groups collide."""
    import itertools
    out = {}
    for perm in itertools.permutations(COLLIDING_SIZES):
        try:
            g = draw_function(ROUND_1M["randomness"], {k: COLLIDING_SIZES[k] for k in perm})
        except Exception as e:
            return False, dict(order=perm, error=repr(e)[:300])
        out[",".join(perm)] = g
    first = next(iter(out.values()))
    diff = {o: {k: sorted(set(v[k]) ^ set(first[k])) for k in v if v[k] != first[k]} for o, v in out.items() if v != first}
    return not diff, dict(sizes=COLLIDING_SIZES, reference_order=next(iter(out)), differing_orders=diff)


def standin_writing_case(name):
    def case(tmp, src):
        r, res, obs = standin_run(tmp, src, f"standin_beacon_{name}", writing=name)
        obs["control_passed"] = STANDIN_CONTROL.get("ok", False)
        if not obs["control_passed"]:
            return False, obs
        if refused(r):
            return True, obs
        planned = sorted(json.dumps(res or {}).count(f"NOT1_{s}") > 0 for s in canonical_seeds()["NOT1"])
        obs["accepted_with_canonical_NOT1"] = planned
        return r.returncode == 0 and all(planned), obs
    case.__name__ = f"case_standin_beacon_{name}"
    return case


# ------------------------------------------------------------------------------------------------ R: rehearsal seeds
# The rehearsal draw (6/6/6, mode rehearsal, the pinned list) and a campaign draw on another published round, whose
# announced exclusion list must hold every rehearsal seed S and its noise seeds 10 S + n (n = 0..3). Test mode,
# offline: draw=/excluded=/announce=/activity= for the campaign draw, rehearsal_draw=/rehearsal_excluded=/
# rehearsal_announce=/rehearsal_activity= for the rehearsal's.
REHEARSAL_SIZES = dict(NOT1=6, ANDOR3=6, XOR3=6)


def announced_draw(d, name, rnd, ex_obj, ex_bytes, sizes, mode, branch):
    """Write <name>.json (DRAW), <name>_EXCLUDED.json, <name>_ANNOUNCE.txt and <name>_activity.json for `rnd` (a
    published round dict). The announce is pushed 600 s before the round's time. Returns (draw, paths, push time)."""
    sys.path.insert(0, str(HERE))
    import beacon_chain as BC
    import beacon_verify as BV
    import draw_seeds as DS
    import datetime
    t0 = BV.round_time(BC.QUICKNET, rnd["round"]) - 600
    utc = lambda t: datetime.datetime.fromtimestamp(t, datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    commit = hashlib.sha1(f"defect test announce {name}".encode()).hexdigest()
    D = DS.draw(rnd["randomness"], rnd["round"], ex_obj, dict(sizes))
    D["beacon_round"] = dict(rnd)
    D["announce"] = dict(branch=branch, commit=commit, push_utc=utc(t0))
    paths = dict(draw=d / f"{name}.json", excluded=d / f"{name}_EXCLUDED.json", announce=d / f"{name}_ANNOUNCE.txt",
                 activity=d / f"{name}_activity.json")
    paths["draw"].write_bytes(DS.canon(D))
    paths["excluded"].write_bytes(ex_bytes)
    words = " ".join(f"{g}={n}" for g, n in sizes.items())
    paths["announce"].write_text(f"format layered-draw-announce/1\nmode {mode}\nexcluded_sha256 "
                                 f"{hashlib.sha256(ex_bytes).hexdigest()}\nsizes {words}\n")
    paths["activity"].write_text(json.dumps([dict(activity_type="branch_creation", after=commit, before="0" * 40,
                                                  ref=f"refs/heads/{branch}", timestamp=utc(t0))], indent=1) + "\n")
    return D, paths, t0


def rehearsal_run(tmp, src, label, drop=None, swap_rounds=False):
    """drop: None (the full list), "seed" (one rehearsal seed left out) or "noise" (one of its noise seeds left out).
    swap_rounds: the rehearsal on round 20000000 and the campaign on 1000000, so the rehearsal's announce is later."""
    sys.path.insert(0, str(HERE))
    import draw_seeds as DS
    import plan_split3 as P3
    d = tmp / "draws"
    d.mkdir(parents=True)
    pinned_b = (HERE / "EXCLUDED.json").read_bytes()
    pinned = json.loads(pinned_b)
    r_round, c_round = (ROUND_20M, ROUND_1M) if swap_rounds else (ROUND_1M, ROUND_20M)
    R, rp, rt0 = announced_draw(d, "REHEARSAL", r_round, pinned, pinned_b, REHEARSAL_SIZES, "rehearsal",
                                "evidence/combined-rehearsal-draw")
    rseeds = sorted(s_ for v in R["groups"].values() for s_ in v)
    extra = set(rseeds) | {10 * s_ + j for s_ in rseeds for j in range(4)}
    removed = None
    if drop == "seed":
        removed = rseeds[0]
    elif drop == "noise":
        removed = 10 * rseeds[0] + 1
    seeds = sorted((set(pinned["seeds"]) | extra) - ({removed} if removed is not None and removed not in pinned["seeds"]
                                                      else set()))
    assert removed is None or removed not in seeds, "the removed seed is in the pinned list itself"
    ex = dict(pinned, seeds=seeds, count=len(seeds), seeds_sha256=hashlib.sha256(DS.canon(seeds)).hexdigest())
    C, cp, ct0 = announced_draw(d, "CAMPAIGN", c_round, ex, DS.canon(ex), STANDIN_SIZES, "test",
                                "evidence/combined-draw")
    plans = tmp / "plans"
    plans.mkdir()
    for k, pl in enumerate(P3.split(C, json.loads((HERE / "campaign_template.json").read_text()), 12)[0], start=1):
        (plans / f"PLAN_K{k:02d}.json").write_bytes(DS.canon(pl))
    home = next(f.name for f in sorted(plans.glob("PLAN_K*.json")) if json.loads(f.read_text())["groups"])
    root = draw_root(src, tmp / "a" / f"out_{home[5:8]}", tmp, "out_K05", home, plans=plans, controls=False)
    args = [f"{DRAW_ARG}={cp['draw']}", f"excluded={cp['excluded']}", f"announce={cp['announce']}",
            f"activity={cp['activity']}", f"rehearsal_draw={rp['draw']}", f"rehearsal_excluded={rp['excluded']}",
            f"rehearsal_announce={rp['announce']}", f"rehearsal_activity={rp['activity']}"]
    r, res, obs = run(tmp, [root], label, extra=args)
    obs.update(rehearsal_seeds=rseeds, removed=removed, rehearsal_push=rt0, campaign_push=ct0, root=home[5:8])
    return r, res, obs


REHEARSAL_CONTROL = {}


def case_rehearsal_full_list(tmp, src):
    r, res, obs = rehearsal_run(tmp, src, "rehearsal_full_list")
    REHEARSAL_CONTROL["ok"] = ok = r.returncode == 0
    return ok, obs


def rehearsal_mutation(label, **kw):
    def case(tmp, src):
        r, res, obs = rehearsal_run(tmp, src, label, **kw)
        obs["control_passed"] = REHEARSAL_CONTROL.get("ok", False)
        text = r.stdout + r.stderr
        named = obs["removed"] is None or str(obs["removed"]) in text
        return refused(r) and obs["control_passed"] and named, obs
    case.__name__ = f"case_{label}"
    return case


def case_standin_draw_valid(tmp, src):
    """The control of the draw mutations: the valid stand-in draw, K03's root with none of its instances run."""
    r, res, obs = standin_run(tmp, src, "standin_draw_valid")
    ok = r.returncode == 0 and all(rows_sum(res, g, n) for g, n in STANDIN_SIZES.items()) and all(
        not_run_entry(res, f"NOT1_{n}", where=res["counts"]["NOT1"][lv]) for lv in ("K0", "K3")
        for n in canonical_seeds()["NOT1"])
    obs["expected_NOT1"] = canonical_seeds()["NOT1"]
    STANDIN_CONTROL["ok"] = ok
    return ok, obs


def mutation(r, obs):
    """A draw mutation passes only if refused AND the valid control passed with the same code: a refusal of the
    arguments themselves, or of the root, is then excluded."""
    obs["control_passed"] = STANDIN_CONTROL.get("ok", False)
    return refused(r) and obs["control_passed"]


def case_standin_seed_changed(tmp, src):
    r, res, obs = standin_run(tmp, src, "standin_seed_changed", seed_edit=True)
    return mutation(r, obs), obs


def case_standin_round_off_by_one(tmp, src):
    r, res, obs = standin_run(tmp, src, "standin_round_off_by_one", push_shift_s=3)
    return mutation(r, obs), obs


def case_standin_signature_byte(tmp, src):
    r, res, obs = standin_run(tmp, src, "standin_signature_byte", sig_flip=True)
    return mutation(r, obs), obs


def case_standin_excluded_not_superset(tmp, src):
    r, res, obs = standin_run(tmp, src, "standin_excluded_not_superset", excluded="not_superset")
    return mutation(r, obs), obs


def case_standin_excluded_sha_differs(tmp, src):
    r, res, obs = standin_run(tmp, src, "standin_excluded_sha_differs", excluded="sha_differs")
    return mutation(r, obs), obs


def case_standin_activity_clean(tmp, src):
    """E2 control: the valid stand-in draw with activity= holding one clean branch_creation at announce.push_utc."""
    r, res, obs = standin_run(tmp, src, "standin_activity_clean", activity="clean")
    ok = r.returncode == 0 and all(rows_sum(res, g, n) for g, n in STANDIN_SIZES.items())
    STANDIN_CONTROL["activity_ok"] = ok
    return ok, obs


def activity_mutation(r, obs):
    obs["control_passed"] = STANDIN_CONTROL.get("activity_ok", False)
    return refused(r) and obs["control_passed"]


def case_standin_activity_redone(tmp, src):
    r, res, obs = standin_run(tmp, src, "standin_activity_redone", activity="redone")
    return activity_mutation(r, obs), obs


def case_standin_activity_force_push(tmp, src):
    r, res, obs = standin_run(tmp, src, "standin_activity_force_push", activity="force_push")
    return activity_mutation(r, obs), obs


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
    ("draw", "standin_draw_valid", case_standin_draw_valid,
     "the valid stand-in draw (round 1000000): exit 0; every group's rows sum to its size; not_run for both NOT1 "
     "seeds of canonical_seeds() (derived at run time from the pinned list)"),
    ("draw", "standin_seed_changed", case_standin_seed_changed, "one drawn seed changed, signature kept: refused"),
    ("draw", "standin_round_off_by_one", case_standin_round_off_by_one, "push_utc + 3 s, the round off by one: refused"),
    ("draw", "standin_signature_byte", case_standin_signature_byte, "one signature byte changed: refused"),
    ("draw", "standin_excluded_not_superset", case_standin_excluded_not_superset,
     "an exclusion list missing one pinned seed (announced, and the draw recomputed over it): refused"),
    ("draw", "standin_excluded_sha_differs", case_standin_excluded_sha_differs,
     "an exclusion list with the pinned seeds but other bytes than announced: refused"),
    ("E2", "standin_activity_clean", case_standin_activity_clean,
     "the valid stand-in draw with activity= one clean branch_creation of the announce commit: exit 0, rows sum"),
    ("E2", "standin_activity_redone", case_standin_activity_redone,
     "activity= branch_creation, branch_deletion, a second later branch_creation used by DRAW.json: refused "
     "(gated on standin_activity_clean)"),
    ("E2", "standin_activity_force_push", case_standin_activity_force_push,
     "activity= the clean branch_creation then a force_push on the announce branch: refused (gated)"),
    ("beacon", "beacon_canonical", case_beacon_canonical,
     "draw_seeds.draw on the canonical lowercase beacon gives the seeds of the ef374ccd formula over the pinned list "
     "(canonical_seeds(), derived at run time)"),
    *[("beacon", f"beacon_{n}", beacon_writing_case(n),
       f"draw_seeds.draw on the beacon written {n}: raises, or gives the canonical seeds") for n in WRITINGS],
    ("beacon", "sizes_permutations", case_sizes_permutations,
     "draw_seeds.draw with the sizes dict in all 6 orders at sizes 166 each: identical seeds"),
    *[("beacon", f"standin_beacon_{n}", standin_writing_case(n),
       f"analysis with a DRAW.json whose beacon and beacon_round.randomness are written {n} (the seeds drawn on that "
       f"writing, a matching root): refused, or accepted with the canonical NOT1 seeds (gated on standin_draw_valid)")
      for n in WRITINGS],
    ("X1", "verify_signature_real", case_verify_signature_real,
     "beacon_verify.verify on round 1000000 as published: ok (control)"),
    *[("X1", f"verify_signature_{k}", verify_pad_case(k),
       f"beacon_verify.verify on the signature with {k[3:]} in front and value sha256(those bytes): not ok")
      for k in PADS],
    *[("X1", f"standin_signature_{k}", standin_sig_case(k),
       f"analysis on a forged DRAW.json: the signature with {k[3:]} in front, value and seeds from it: refused (gated)")
      for k in PADS],
    ("X1", "standin_signature_flip", standin_sig_case("flip", ("does not verify against the pinned quicknet key",
                                                               "decod")),
     "analysis on a forged DRAW.json: one signature byte flipped, value = sha256(flipped bytes), seeds from it: "
     "refused by the signature check (\"does not verify against the pinned quicknet key\" or a decoding failure)"),
    *[("X2", "plans_command_" + "_".join(str(n) for n in sz.values()), plans_case(sz),
       f"plan_split3.py on the DRAW.json file at {sz}: all 12 plans equal plan_split3.split of the draw") for sz in X2_SIZES],
    ("X1", "verify_other_round", case_verify_other_round,
     "beacon_verify.verify on round 20000000's signature presented as round 1000000's: not ok, with subgroups_ok "
     "true and signature_ok false (the pairing refuses it, not the decoding)"),
    ("X1", "standin_signature_other_round", standin_sig_case("other_round", ("does not verify against the pinned "
                                                                             "quicknet key",), avoid=("decod",)),
     "analysis on a forged DRAW.json: round 20000000's signature as round 1000000's, value = sha256 of it, seeds "
     "from it: refused by the pairing (\"does not verify against the pinned quicknet key\", no decoding failure)"),
    ("X2", "standin_plans_from_command", case_standin_plans_from_command,
     "the 6/6/6 stand-in, plans from the plan_split3.py command, roots for its remote-duplicate machines, draw=: "
     "exit 0 (gated)"),
    ("R", "rehearsal_full_list", case_rehearsal_full_list,
     "rehearsal draw (round 1000000, 6/6/6) and campaign draw (round 20000000) whose excluded= list is the pinned list "
     "plus every rehearsal seed and its noise seeds: exit 0 (control)"),
    ("R", "rehearsal_seed_missing", rehearsal_mutation("rehearsal_seed_missing", drop="seed"),
     "the same with one rehearsal seed left out of the campaign's list: refused, naming the seed (gated)"),
    ("R", "rehearsal_noise_missing", rehearsal_mutation("rehearsal_noise_missing", drop="noise"),
     "the same with one rehearsal noise seed (10 S + 1) left out: refused, naming it (gated)"),
    ("R", "rehearsal_announce_later", rehearsal_mutation("rehearsal_announce_later", swap_rounds=True),
     "the rehearsal on round 20000000 and the campaign on 1000000 (the rehearsal announced later), the list full: "
     "refused (gated)"),
    ("E1", "round_own_check_failed", case_round_own_check_failed,
     "N2 of NOT1_6220 stopped by its own check (" + OWN_CHECK + "): exit 0; refuted at K3, in a sub-row about the "
     "run's own check listing the status; NOT1_6212 held"),
    ("E1", "round_simulator_ended", case_round_simulator_ended,
     "the twin, N2 ended by the simulator (" + SIM_ENDED + "): exit 0; NOT1_6220 not completed at K3, not refuted; "
     "NOT1_6212 held"),
    ("D10", "one_byte_in_comparison", case_one_byte_in_comparison, "refused; the output names N0/comparison.json"),
    ("D10", "listed_file_missing", case_listed_file_missing, "refused; the output names extract.json"),
    ("D10", "stopped_mid_instance", case_stopped_mid_instance,
     "exit 0; NOT1_6220 refuted at K3, its K3 flagged manifest not final; NOT1_6212 held at K0 and K3"),
]


def main(out_json=None):
    lean = shutil.which("lean")
    head = git("rev-parse", "HEAD", cwd=REPO).strip()
    code = git("log", "-1", "--format=%H", "--", "research/layered-networks/analysis.py", cwd=REPO).strip()
    report = dict(format="layered-analysis-defects/1", script_sha256=sha(__file__), analysis_sha256=sha(ANALYSIS), draw_seeds_sha256=sha(HERE / "draw_seeds.py"),
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
