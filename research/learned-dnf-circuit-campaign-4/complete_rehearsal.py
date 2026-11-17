"""Campaign 4, amendment 8: the completion of the rehearsal's attempt 2. It writes REHEARSAL.json.

  complete_rehearsal.py --attempt ATTEMPT_DIR --ngspice BIN --pdk DIR --work NEW_DIR --report REHEARSAL.json

Attempt 2 (`rehearsal.py` on commit 3156ee4, work folder ATTEMPT_DIR) ran every stage of the rehearsal through the
kit, then stopped on check.sh's audit of M8.lean, before writing its record. This script, run on the frozen commit of
amendment 8, writes that record from attempt 2's collected folders with rehearsal.py's own functions (checks,
limits_basis, no_campaign_seed, stage_tamper, all_passed; rehearsal.py is unchanged), and reruns only the memory
stages, MEMD2 and MEMI2, through the kit, with the machine's memory sampled as PREDICTION.md (Memory) requires:
attempt 2's samples of the machine's memory were held in memory by rehearsal.py and lost when it stopped.

Everything else comes from attempt 2: no other run is launched. The two refusals that rehearsal.py tested outside a
kit launch, which simulate nothing (the seed guard outside the kit, and the safeguards of the stage files), are
tested again here, on the frozen code of this commit.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.path.insert(0, str(HERE))
import c4                                               # noqa: E402
import plan                                             # noqa: E402
import rehearsal as R                                   # noqa: E402

BASE = c4.BASE
RUNS_COMMIT = "3156ee40ab35dea396b6fa8785177b84b7667c76"   # the frozen commit attempt 2 ran on
STAGES = ("M", "X", "E", "N", "MEMD", "MEMI", "GUARD")      # attempt 2's stages, in order


def git_of(repo):
    return lambda *args: R.sh(["git", *args], repo).strip()


def kernel():
    """Amendment 8: the completion's numbers are those of OpenBLAS's SkylakeX kernel, as attempt 2's were. It refuses
    to run on a CPU without avx512f, or without OPENBLAS_CORETYPE=SkylakeX set by its wrapper (numpy reads it once,
    when it is loaded), and records the CPU model and the core OpenBLAS reports."""
    info = Path("/proc/cpuinfo").read_text()
    cpu = next(l.split(":", 1)[1].strip() for l in info.splitlines() if l.startswith("model name"))
    assert "avx512f" in info.split(), f"refused (amendment 8): this CPU ({cpu}) has no avx512f"
    assert os.environ.get("OPENBLAS_CORETYPE") == "SkylakeX", "refused (amendment 8): OPENBLAS_CORETYPE=SkylakeX must be set by the wrapper"
    p = subprocess.run([sys.executable, "-B", "-c", "import numpy"], env=dict(os.environ, OPENBLAS_VERBOSE="2"), capture_output=True, text=True)
    core = re.search(r"Core: (\S+)", p.stdout + p.stderr)
    assert core and core.group(1) == "SkylakeX", f"refused (amendment 8): OpenBLAS reports {core.group(0) if core else 'no core'}"
    return dict(cpu_model=cpu, avx512f=True, OPENBLAS_CORETYPE=os.environ["OPENBLAS_CORETYPE"], openblas_core=core.group(1))


def attempt_checks(attempt, meta):
    """Amendment 8's checks on attempt 2, before its record is completed."""
    rb2 = attempt / "repo" / BASE
    g2 = git_of(attempt / "repo")
    uptimes = sorted(set(re.findall(r"uptime-s=(\d{4}-\d\d-\d\d \d\d:\d\d:\d\d)", (meta / "uptime.log").read_text())))
    stages = {}
    for st in STAGES:
        man = json.loads((rb2 / f"CAMPAIGN_{st}.json").read_text())
        for m in "ab":
            src, col = attempt / f"{st}-{m}", attempt / f"collected-{st}-{m}"
            s = json.loads((col / "STATE.json").read_text())
            surv = json.loads((col / "SURVIVORS.json").read_text())
            stages[f"{st}-{m}"] = dict(
                status=s["status"], runs_as_in_the_manifest=sorted(r["id"] for r in s["records"]) == sorted(r["id"] for r in man["runs"] if r["machine"] == m),
                run_status=sorted({r["status"] for r in s["records"]}),
                collected_equal_to_the_evidence=all(hashlib.sha256((src / f["path"]).read_bytes()).hexdigest() == f["sha256"] for f in surv["files"])
                and len(surv["files"]) == sum(1 for p in src.rglob("*") if p.is_file()))
    frozen2 = {n: hashlib.sha256((attempt / "repo" / n).read_bytes()).hexdigest() for n in plan.FROZEN}
    at_runs = {n: hashlib.sha256(subprocess.run(["git", "-C", str(ROOT), "show", f"{RUNS_COMMIT}:{n}"], check=True, capture_output=True).stdout).hexdigest()
               for n in plan.FROZEN}
    ok_stage = lambda k, v: v["runs_as_in_the_manifest"] and v["collected_equal_to_the_evidence"] and (
        v["status"] == "complete" and v["run_status"] == ["complete"] if not k.startswith("GUARD") else v["run_status"] == ["failed-never-rerun"])
    out = dict(uptime_s_values=uptimes, no_restart=len(uptimes) == 1, stages=stages, stages_complete_and_collected=all(ok_stage(k, v) for k, v in stages.items()),
               clone_base=g2("merge-base", "HEAD", RUNS_COMMIT), clone_uncommitted=g2("status", "--porcelain"),
               frozen_files_equal_to_the_runs_commit=frozen2 == at_runs)
    out["all"] = bool(out["no_restart"] and out["stages_complete_and_collected"] and out["clone_base"] == RUNS_COMMIT and not out["clone_uncommitted"]
                      and out["frozen_files_equal_to_the_runs_commit"])
    return out


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--attempt", type=Path, required=True)
    p.add_argument("--meta", type=Path, required=True, help="attempt 2's meta folder (uptime.log, rehearsal.log)")
    p.add_argument("--ngspice", type=Path, required=True)
    p.add_argument("--pdk", type=Path, required=True)
    p.add_argument("--work", type=Path, required=True)
    p.add_argument("--report", type=Path, required=True)
    a = p.parse_args()
    print(c4.require_pinned())
    numerics = kernel()
    started = time.time()
    attempt, work = a.attempt.resolve(), a.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    for name in R.sh(["git", "-C", ROOT, "status", "--porcelain", "--", BASE, "research/learned-dnf-circuit", "research/network-circuit",
                      "research/circuit", plan.CLOSURE, "research/learned-coincidence", ".github"], work).splitlines():
        raise AssertionError("commit first: the completion runs the committed files: " + name)
    head = R.sh(["git", "-C", ROOT, "rev-parse", "HEAD"], work).strip()
    tree = R.sh(["git", "-C", ROOT, "rev-parse", head + "^{tree}"], work).strip()
    changed = R.sh(["git", "-C", ROOT, "diff", "--name-only", RUNS_COMMIT, head], work).split()
    folders = sorted({"/".join(f.split("/")[:4]) for f in changed if f.startswith(f"{BASE}/rehearsal/run-")})
    differing = dict(files=[f for f in changed if not any(f.startswith(d + "/") for d in folders)],
                     evidence_folders={d: dict(files=sum(f.startswith(d + "/") for f in changed),
                                               list_sha256=hashlib.sha256("".join(f + "\n" for f in changed if f.startswith(d + "/")).encode()).hexdigest())
                                       for d in folders})
    pre = attempt_checks(attempt, a.meta.resolve())
    assert pre["all"], json.dumps(pre, indent=1)

    rb2 = attempt / "repo" / BASE                     # attempt 2's clone: its records (BEFORE_M.md, PREDICTED.json, ...)
    before = plan.read_before_m(rb2 / "BEFORE_M.md")
    cost, I = plan.costs(before), 1
    P = json.loads((rb2 / "PREDICTED.json").read_text())
    collected = {st: {m: attempt / f"collected-{st}-{m}" for m in "ab"} for st in STAGES}
    report = dict(scope="rehearsal of campaign 4 on the nominal cell (no mismatch, no seed), which is not an instance of the campaign; the launch "
                        "kit's synthetic kind, a local Git remote; not a registered run. Attempt 2, completed (amendment 8)",
                  runs_commit=RUNS_COMMIT, frozen_commit=head, frozen_tree=tree, source_commit=head, differing_files=differing,
                  frozen_files={n: hashlib.sha256((ROOT / n).read_bytes()).hexdigest() for n in plan.FROZEN},
                  attempt=dict(work=str(attempt), log_tail=(a.meta / "rehearsal.log").read_text().splitlines()[-3:], checks_before_completion=pre),
                  interpreter=c4.interpreter(), numerics=numerics, stages={}, checks={}, reuse_trip=before["reuse_trip"],
                  no_reuse_supplement="not run: the trip value is reused in the rehearsal (amendment 5, section 5)")
    for st in STAGES:                                  # attempt 2's stages, from the kit's records (their stage wall times were lost)
        for m in "ab":
            s = json.loads((collected[st][m] / "STATE.json").read_text())
            report["stages"].setdefault(st, {})[m] = dict(status=s["status"], wall_s=None, memory=None, from_attempt_2=True,
                                                          runs={r["id"]: dict(status=r["status"], wall_s=r.get("wall_s")) for r in s["records"]})

    # ----- the clone of this commit for MEMD2 and MEMI2, with attempt 2's records (amendment 5, section 1, item 3)
    repo, remote = work / "repo", work / "remote.git"
    R.sh(["git", "clone", "--quiet", "--shared", ROOT, repo], work)
    git = git_of(repo)
    git("config", "user.name", "Rehearsal")
    git("config", "user.email", "rehearsal@example.invalid")
    R.sh(["git", "init", "--quiet", "--bare", remote], work)
    R.sh(["git", "-C", remote, "config", "receive.shallowUpdate", "true"], work)
    git("remote", "set-url", "origin", str(remote))
    git("checkout", "--quiet", "-b", "rehearsal")
    kit = [sys.executable, "-B", repo / plan.CLOSURE / "launchkit" / "launch.py"]
    env = ["--ngspice", a.ngspice.resolve(), "--pdk", a.pdk.resolve()]
    rb = repo / BASE
    records = [f for f in R.sh(["git", "-C", attempt / "repo", "diff", "--name-only", RUNS_COMMIT, "HEAD"], work).split()
               if not Path(f).name.startswith("INVENTORY_")]
    for f in records:
        (repo / f).parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(attempt / "repo" / f, repo / f)
    for machine in ("a", "b"):
        R.sh(kit + ["inventory", "--machine", machine, "--out", rb / f"INVENTORY_{machine}.json"] + env, repo)
    git("add", *records, f"{BASE}/INVENTORY_a.json", f"{BASE}/INVENTORY_b.json")
    git("commit", "--quiet", "-m", "Completion: attempt 2's records (its BEFORE_M.md, PREDICTED.json, stage files ...), inventories")
    frozen = git("rev-parse", "HEAD~1")
    assert frozen == head, (frozen, head)

    def lim(r, model="device"):
        """A rehearsal run is a measurement (amendment 5, section 5): its time limit is 3 times its expected cost."""
        e = plan.expected(r, cost, model)
        return dict(r, estimate_s=plan.ceil10(e), timeout_s=plan.ceil10(3 * e), expected_s=e)

    def stage(name, runs, memory=False):
        """rehearsal.py's stage (a closure of its main, copied without change but for its names): its stage file, its run
        list, its manifest; one launch of the kit on each machine, one after the other; the collected folders."""
        gov = plan.governing_of(name)
        gcommit = git("log", "-1", "--format=%H", "--", gov)
        (repo / plan.stage_path(name)).write_text(plan.stage_file_text(name, gov, gcommit, hashlib.sha256((repo / gov).read_bytes()).hexdigest()))
        git("add", plan.stage_path(name))
        git("commit", "--quiet", "-m", f"Completion: the protocol of stage {name}")
        stage_commit = git("rev-parse", "HEAD")
        rl = f"{BASE}/STAGE_{name}_RUNS.json"
        (repo / rl).write_text(json.dumps(dict(stage=name, I=I, runs=runs), indent=1) + "\n")
        git("add", rl)
        git("commit", "--quiet", "-m", f"Completion: the runs of stage {name}")
        source = git("rev-parse", "HEAD")
        m = plan.manifest(name, runs, I, stage_commit, f"STAGE_{name}.md", source, root=repo, frozen_commit=frozen)
        m["source_sha256"][rl] = hashlib.sha256((repo / rl).read_bytes()).hexdigest()
        m.update(kind="synthetic", campaign_id="synthetic-c4-rehearsal-" + name.lower(), runs=[R.entry_of(r, I, name) for r in runs])
        del m["expected_workflows"]
        m["budget_s"] = min(14400, max(1, int(plan.stage_cap(runs)) + 1))
        path = rb / f"CAMPAIGN_{name}.json"
        path.write_text(json.dumps(m, indent=1) + "\n")
        common = ["--repo", repo, "--manifest", path] + env
        git("add", str(path.relative_to(repo)))
        git("commit", "--quiet", "-m", f"Completion: manifest of stage {name}")
        git("push", "--quiet", "origin", "rehearsal")
        R.sh(kit + ["preflight"] + common, repo)
        R.sh(kit + ["prepare"] + common, repo)
        git("add", m["marker_path"])
        git("commit", "--quiet", "-m", f"Completion: attempt marker of stage {name}")
        git("push", "--quiet", "origin", "rehearsal")
        out = {}
        for machine in ("a", "b"):
            folder = work / f"{name}-{machine}"
            t0 = time.time()
            if memory:
                with R.Memory() as mem:
                    R.sh(kit + ["run-machine"] + common + ["--branch", "rehearsal", "--machine", machine, "--out", folder], repo, expect=None)
                memrec = dict(peak_used_kB=mem.peak, before_kB=mem.base, total_kB=mem.total, peak_fraction=mem.peak / mem.total)
            else:
                R.sh(kit + ["run-machine"] + common + ["--branch", "rehearsal", "--machine", machine, "--out", folder], repo, expect=None)
                memrec = None
            state = json.loads((folder / "STATE.json").read_text())
            R.sh(kit + ["run-machine"] + common + ["--branch", "rehearsal", "--machine", machine, "--out", work / f"again-{name}-{machine}"], repo, expect=1)
            assert not any(x.is_symlink() for x in folder.rglob("*")), "a link in the evidence"
            target = work / f"collected-{name}-{machine}"
            R.sh(kit + ["collect", "--out", folder, "--destination", target], repo)
            out[machine] = target
            report["stages"].setdefault(name, {})[machine] = dict(status=state["status"], wall_s=time.time() - t0, memory=memrec,
                                                                  runs={r["id"]: dict(status=r["status"], wall_s=r.get("wall_s")) for r in state["records"]})
        collected[name] = out
        return out, m

    # ----- MEMD2, MEMI2: rehearsal.py's memory stages, the same runs (their ids marked "-2"), on this commit
    untrained = lambda rid, machine: lim(R.check_run(rid, machine, "network", needs=[4, 4, 4, 4], control="untrained", noise="none"))
    n1 = next(r for r in plan.stage_runs("N1", here=rb)[0] if r.get("round") == 1)
    mem_d = [lim(R.check_run(f"a-None-need7-device-{k}-2", "a", "network", needs=[7, 7, 7, 7], control=None, noise="device", round=1 + k % 3,
                             extraction=n1["extraction"])) for k in range(4)]
    stage("MEMD2", mem_d + [untrained("b-None-untrained-filler-d-2", "b")], memory=True)
    mem_i = [lim(R.check_run(f"b-None-need7-injected-{k}-2", "b", "network", needs=[7, 7, 7, 7], control=None, noise="injected", round=1 + k % 3), "injected")
             for k in range(4)]
    stage("MEMI2", [untrained("a-None-untrained-filler-i-2", "a")] + mem_i, memory=True)
    attempt2_rss = {st: {r["id"]: json.loads((collected[st][m] / r["id"] / "record.json").read_text()).get("peak_rss_MB")
                         for m in "ab" for r in json.loads((collected[st][m] / "STATE.json").read_text())["records"]} for st in ("MEMD", "MEMI")}
    report["checks"]["memory"] = dict(device=report["stages"]["MEMD2"]["a"]["memory"], injected=report["stages"]["MEMI2"]["b"]["memory"])
    report["memory_attempt_2_per_run_peak_rss_MB"] = dict(note="attempt 2's per-run peaks, for comparison only: they do not measure the machine's peak",
                                                         **attempt2_rss)

    # ----- the split extraction against the single one (rehearsal.py, unchanged in substance)
    ex = P["extractions"]["None"]
    merged = (attempt / "repo" / ex["path"]).read_bytes()
    single = json.loads((collected["X"]["b"] / "b-None-extract-single" / "extraction.json").read_text())
    single_text = (json.dumps(single, indent=1) + "\n").encode()
    report["checks"]["split_extraction_identity"] = dict(reuse_trip=before["reuse_trip"], merged_sha256=hashlib.sha256(merged).hexdigest(),
                                                         single_sha256=hashlib.sha256(single_text).hexdigest(), identical=merged == single_text,
                                                         V2_V2b_isolation=ex)
    # ----- the gate on the rehearsal's prediction: attempt 2's Gate4.lean, audited by this commit's check.sh
    lean_gate = R.sh(["bash", HERE / "check.sh", rb2 / "Gate4.lean"], ROOT).strip().splitlines()[-3:]
    report["checks"]["gate_on_the_rehearsal_prediction"] = dict(check_sh=lean_gate, eligible=P["instances"][0].get("eligible"),
                                                                 why_not_eligible=P["instances"][0].get("why_not_eligible"))
    # ----- the seed guard: attempt 2's GUARD stage, and the refusal outside the kit, tested here
    guard_out = {}
    for machine, folder in collected["GUARD"].items():
        st = json.loads((folder / "STATE.json").read_text())
        rec = st["records"][0]
        err = (folder / rec["id"] / "stderr.log").read_text()
        guard_out[rec["id"]] = dict(status=rec["status"], refused_by_the_guard="AssertionError" in err and ("is not one of" in err),
                                    simulated=any((folder / rec["id"]).rglob("input.spice")), stderr_tail=err.strip().splitlines()[-1:])
    outside = subprocess.run([sys.executable, "-B", rb / "run4.py", "--out", work / "outside-kit", "--ngspice", a.ngspice, "--pdk", a.pdk, "--id", "x",
                              "--kind", "cal", "--guard", "on", "--seed", "7501", "--instances", "9"], cwd=repo, capture_output=True, text=True)
    guard_out["outside the kit, seed 7501, I = 9"] = dict(returncode=outside.returncode, refused="only inside a launch of the kit" in outside.stderr,
                                                          simulated=any((work / "outside-kit").rglob("input.spice")) if (work / "outside-kit").exists() else False)
    tampered = R.stage_tamper(repo, rb, a, work)
    report["checks"]["seed_guard"] = dict(runs=guard_out, all_refused_before_simulation=all(
        (v.get("refused_by_the_guard") or v.get("refused")) and not v["simulated"] for v in guard_out.values()))
    report["checks"]["stage_safeguards"] = tampered
    # ----- the analysis, on attempt 2's outputs, and check.sh on its M8.lean
    import analyze
    an = work / "analysis"
    an.mkdir()
    res = analyze.main([an, collected["M"]["a"], collected["M"]["b"], collected["N"]["a"], collected["N"]["b"], collected["E"]["a"], collected["E"]["b"]],
                       here=rb2)
    m8 = R.sh(["bash", HERE / "check.sh", an / "M8.lean"], ROOT).strip().splitlines()[-2:]
    report["checks"]["analysis"] = dict(predicted_is_reproduced=res["predicted_is_reproduced"], regeneration_check=res["regeneration_check"],
                                        claims={k: (v if isinstance(v, str) else v.get("verdict") if isinstance(v, dict) and "verdict" in v else "see RESULTS")
                                                for k, v in res["claims"].items()},
                                        records_are_the_waveforms={k: v["record_is_the_waveform"] for k, v in res["runs"].items()}, m8_check_sh=m8,
                                        results_sha256=hashlib.sha256((an / "RESULTS.json").read_bytes()).hexdigest(),
                                        results_equal_to_attempt_2=(an / "RESULTS.json").read_bytes() == (attempt / "analysis" / "RESULTS.json").read_bytes(),
                                        m8_equal_to_attempt_2=(an / "M8.lean").read_bytes() == (attempt / "analysis" / "M8.lean").read_bytes())
    shutil.copy(an / "RESULTS.json", work / "RESULTS_analysis.json")
    # ----- rehearsal.py's checks, limits and seeds, on attempt 2's collected folders and the two memory stages
    report["checks"].update(R.checks(work, {st: collected[st] for st in STAGES}, P, rb2))
    report["limits_basis"], report["wall_times"] = R.limits_basis(collected, cost)
    seeds = [R.no_campaign_seed(attempt), R.no_campaign_seed(work)]
    report["no_seed_from_7501_simulated"] = dict(attempt_2=seeds[0], completion=seeds[1], none_from_7501=all(s["none_from_7501"] for s in seeds))
    report["total_wall_s"] = dict(completion=time.time() - started)
    report["all_checks_passed"] = R.all_passed(report)
    a.report.write_text(json.dumps(report, indent=1, default=str) + "\n")
    print(json.dumps(dict(all_checks_passed=report["all_checks_passed"], limits_basis=report["limits_basis"]), indent=1))


if __name__ == "__main__":
    main()
