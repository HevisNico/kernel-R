"""Rehearsal of the whole chain on the real simulator: launcher, runner, collection, analysis. Not a registered run.

  rehearsal.py --ngspice BIN --pdk DIR --work NEW_DIR --report FILE

A local clone of this repository and a local bare remote stand for GitHub; the launch kit runs in its
`synthetic` kind, which never contacts GitHub and consumes no registered attempt. Four runs of the
real runner on the real cell, **three services each and no leakage jump** (the jump value is the
reference leak): none of them is a scenario of PREDICTION.md, and no jump is simulated before the
campaign. What is checked is the plumbing: the runner under the launcher, its evidence without any
link, the fingerprints, the collection, and the analysis reading it all back.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.path.insert(0, str(HERE))
import plan

SERVICES = 3
RUNS = [dict(id="a0-x-tt27", machine="a", scenario="x", config="tt27", mode="supervised", noise=0, version=2, seed=31001),
        dict(id="a1-y-tt27", machine="a", scenario="y", config="tt27", mode="supervised", noise=1, version=2, seed=31002),
        dict(id="b0-x-mm2001", machine="b", scenario="x", config="mm2001", mode="supervised", noise=1, version=2, seed=2001),
        dict(id="b1-y-tt-40", machine="b", scenario="y", config="tt-40", mode="self", noise=0, version=0, seed=31004)]


def sh(argv, cwd, expect=0):
    p = subprocess.run([str(x) for x in argv], cwd=cwd, capture_output=True, text=True)
    if (p.returncode == 0) != (expect == 0):
        raise AssertionError(" ".join(str(x) for x in argv) + "\n" + p.stdout[-3000:] + "\n" + p.stderr[-3000:])
    return p.stdout


def main():
    p = argparse.ArgumentParser(description=__doc__)
    for name in ("ngspice", "pdk", "work", "report"):
        p.add_argument("--" + name, type=Path, required=True)
    a = p.parse_args()
    work = a.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    repo, remote = work / "repo", work / "remote.git"
    sh(["git", "clone", "--quiet", "--no-hardlinks", ROOT, repo], work)
    for name in sh(["git", "-C", ROOT, "status", "--porcelain", "--", plan.BASE, plan.CLOSURE], work).splitlines():
        raise AssertionError("commit first: the rehearsal runs the committed files: " + name)
    git = lambda *args: sh(["git", *args], repo).strip()
    git("config", "user.name", "Rehearsal")
    git("config", "user.email", "rehearsal@example.invalid")
    sh(["git", "init", "--quiet", "--bare", remote], work)
    git("remote", "set-url", "origin", str(remote))
    git("checkout", "--quiet", "-b", "rehearsal")
    source = git("rev-parse", "HEAD")
    protocol = git("log", "-1", "--format=%H", "--", plan.BASE + "/PREDICTION.md")
    m = plan.manifest(protocol, source)
    runner = plan.BASE + "/run.py"
    entries = []
    for r in RUNS:
        argv = ["{python}", "{repo}/" + runner, "--out", "{out}/evidence", "--ngspice", "{ngspice}", "--pdk", "{pdk}", "--id", r["id"], "--scenario", r["scenario"],
                "--config", r["config"], "--mode", r["mode"], "--noise", str(r["noise"]), "--jump", "1e-11", "--version", str(r["version"]),
                "--seed", str(r["seed"]), "--services", str(SERVICES)]
        entries.append(dict(id=r["id"], machine=r["machine"], scenario=r["scenario"], deck="research/circuit/cell.spice", runner=runner, argv=argv, estimate_s=120,
                            timeout_s=400, required_outputs=plan.OUTPUTS, diagnostic_logs=["evidence/session.log"], noise_fingerprint="evidence/noise.sha256"))
    m.update(kind="synthetic", campaign_id="synthetic-rehearsal", scenario_order=["x", "y"], jobs=2, budget_s=2000, runs=entries,
             marker_path="REHEARSAL/RUN_ATTEMPT.json", inventory_a_path="REHEARSAL/INVENTORY_a.json", inventory_b_path="REHEARSAL/INVENTORY_b.json")
    del m["expected_workflows"]
    (repo / "REHEARSAL").mkdir()
    (repo / "REHEARSAL" / "CAMPAIGN.json").write_text(json.dumps(m, indent=1) + "\n")
    kit = [sys.executable, "-B", repo / plan.CLOSURE / "launchkit" / "launch.py"]
    env = ["--ngspice", a.ngspice.resolve(), "--pdk", a.pdk.resolve()]
    common = ["--repo", repo, "--manifest", repo / "REHEARSAL" / "CAMPAIGN.json"] + env
    for machine in ("a", "b"):
        sh(kit + ["inventory", "--machine", machine, "--out", repo / "REHEARSAL" / f"INVENTORY_{machine}.json"] + env, repo)
    git("add", "REHEARSAL")
    git("commit", "--quiet", "-m", "Rehearsal manifest and inventories")
    git("push", "--quiet", "origin", "rehearsal")
    sh(kit + ["preflight"] + common, repo)
    sh(kit + ["prepare"] + common, repo)
    git("add", "REHEARSAL/RUN_ATTEMPT.json")
    git("commit", "--quiet", "-m", "Rehearsal attempt")
    git("push", "--quiet", "origin", "rehearsal")
    collected = []
    for machine in ("a", "b"):
        out = work / ("machine-" + machine)
        sh(kit + ["run-machine"] + common + ["--branch", "rehearsal", "--machine", machine, "--out", out], repo)
        state = json.loads((out / "STATE.json").read_text())
        assert state["status"] == "complete", state
        sh(kit + ["run-machine"] + common + ["--branch", "rehearsal", "--machine", machine, "--out", work / ("again-" + machine)], repo, expect=1)
        assert not any(x.is_symlink() for x in out.rglob("*")), "a link in the evidence"
        target = work / ("collected-" + machine)
        sh(kit + ["collect", "--out", out, "--destination", target], repo)
        collected.append(target)
    # the two runs without noise share the fingerprint of zeros: the command lists them and exits with status 2
    noise = json.loads(subprocess.run([str(x) for x in kit + ["check-noise", "--evidence", *collected]], cwd=repo, capture_output=True, text=True).stdout)
    # the analysis of the campaign, on these four runs instead of the 124
    sys.path.insert(0, str(repo / plan.BASE))
    import analyze
    planned = [dict(r, jump_S=1e-11, services=SERVICES) for r in RUNS]
    rows = analyze.gather(collected, planned)
    measures = {r["id"]: r["measures"] for r in rows}
    assert all(r["status"] == "complete" and r["counts"] for r in rows), [(r["id"], r["status"]) for r in rows]
    for name, x in measures.items():
        assert x["record_is_the_waveform"] and x["entered"] and x["report_differs_from_waveform"] == 0 and len(x["services"]) == SERVICES, name
        assert x["writes_not_as_commanded"] == 0 and x["fires_outside_reads"] == 0 and not x["enclosure_broken"], name
    supervised = [x for x in measures.values() if x["mode"] == "supervised"]
    assert all(x["refused_at_period"] == [None, None] and all(s["correct"] for s in x["services"]) for x in supervised)
    assert len({x["fingerprint"] for x in measures.values() if x["noise"]}) == 2
    report = dict(scope="rehearsal on the real cell: four runs of three services, no leakage jump, synthetic kind of the launch kit, local Git remote; not a registered run",
                  source_commit=source, files={name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest() for name in plan.FROZEN},
                  runs={name: dict(mode=x["mode"], noise=x["noise"], services=[dict(read=s["read"], correct=s["correct"], latency=s["latency"]) for s in x["services"]],
                                   preparation_cycles=x["preparation_cycles"], refused_at_period=x["refused_at_period"], wall_s=x["wall_s"]) for name, x in measures.items()},
                  second_launch_refused=True, no_link_in_the_evidence=True, collected_files={t.name: len(json.loads((t / "SURVIVORS.json").read_text())["files"]) for t in collected},
                  waveform_bytes={r["id"]: (c / r["id"] / "evidence" / "trace.raw").stat().st_size for r in RUNS for c in collected if (c / r["id"]).exists()},
                  check_noise=dict(runs_with_fingerprint=noise["runs_with_fingerprint"], shared=noise["shared"]), all_checks_passed=True)
    a.report.write_text(json.dumps(report, indent=1) + "\n")
    print(json.dumps(report, indent=1))


if __name__ == "__main__":
    main()
