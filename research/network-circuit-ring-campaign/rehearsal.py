"""Rehearsal of the whole chain on the real simulator: launcher, runner, collection, prediction, Lean check, second
launch, analysis. Not a registered run, and not an instance of the campaign.

  rehearsal.py --ngspice BIN --pdk DIR --work NEW_DIR --report FILE

A local clone of this repository and a local bare remote stand for GitHub; the launch kit runs in its `synthetic`
kind, which never contacts GitHub and consumes no registered attempt. The cell is the **nominal cell** (model
section `tt`, no mismatch, no seed), which is not one of the six instances: its five measure runs, then
`predicted.py`, then its five network runs (the run without noise, the control and three shortened noisy runs).
The runs are spread over the two "machines" of the kit, both on this container, so that both shards exist: the
scans and the runs without noise on `a`, the train and the noisy runs on `b`.

What is checked is the plumbing: two launches under two protocols with their own claims, the second bound to
PREDICTED.json; the runner under the launcher; the collection; the prediction step, its Lean file and the analysis
reading it all back; and what the runs cost.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.path.insert(0, str(HERE))
import plan

WHICH = [dict(seed="none", machine="a")]
SECTION = "tt"


def moved(r, machine):
    return dict(r, machine=machine, id=machine + r["id"][1:])


def measure_runs():
    return [moved(r, "b" if r["kind"] == "train" else "a") for r in plan.measure_runs(WHICH)]


def network_runs(needs, control, which):
    runs, removed = plan.network_runs(needs, control, which)
    return [moved(r, "b" if r["noise"] else "a") for r in runs], removed


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
    for name in sh(["git", "-C", ROOT, "status", "--porcelain", "--", plan.BASE, plan.RING, plan.NET, plan.CLOSURE], work).splitlines():
        raise AssertionError("commit first: the rehearsal runs the committed files: " + name)
    sh(["git", "clone", "--quiet", "--shared", ROOT, repo], work)
    git = lambda *args: sh(["git", *args], repo).strip()
    git("config", "user.name", "Rehearsal")
    git("config", "user.email", "rehearsal@example.invalid")
    sh(["git", "init", "--quiet", "--bare", remote], work)
    git("remote", "set-url", "origin", str(remote))
    git("checkout", "--quiet", "-b", "rehearsal")
    kit = [sys.executable, "-B", repo / plan.CLOSURE / "launchkit" / "launch.py"]
    env = ["--ngspice", a.ngspice.resolve(), "--pdk", a.pdk.resolve()]
    (repo / "REHEARSAL").mkdir()
    for machine in ("a", "b"):
        sh(kit + ["inventory", "--machine", machine, "--out", repo / "REHEARSAL" / f"INVENTORY_{machine}.json"] + env, repo)

    def stage(name, protocol, source, runs):
        """One launch of the kit on both machines; returns the collected evidence folders."""
        m = plan.manifest(name, protocol, source, runs=runs, section=SECTION, root=repo)
        m.update(kind="synthetic", campaign_id="synthetic-ring-" + name, budget_s=14400, marker_path=f"REHEARSAL/RUN_ATTEMPT_{name}.json",
                 inventory_a_path="REHEARSAL/INVENTORY_a.json", inventory_b_path="REHEARSAL/INVENTORY_b.json")
        del m["expected_workflows"]
        path = repo / "REHEARSAL" / f"CAMPAIGN_{name}.json"
        path.write_text(json.dumps(m, indent=1) + "\n")
        common = ["--repo", repo, "--manifest", path] + env
        git("add", "REHEARSAL")
        git("commit", "--quiet", "-m", f"Rehearsal: manifest of the {name}")
        git("push", "--quiet", "origin", "rehearsal")
        sh(kit + ["preflight"] + common, repo)
        sh(kit + ["prepare"] + common, repo)
        git("add", "REHEARSAL")
        git("commit", "--quiet", "-m", f"Rehearsal: attempt marker of the {name}")
        git("push", "--quiet", "origin", "rehearsal")
        collected = []
        for machine in ("a", "b"):
            out = work / f"{name}-{machine}"
            sh(kit + ["run-machine"] + common + ["--branch", "rehearsal", "--machine", machine, "--out", out], repo)
            state = json.loads((out / "STATE.json").read_text())
            assert state["status"] == "complete", state
            sh(kit + ["run-machine"] + common + ["--branch", "rehearsal", "--machine", machine, "--out", work / f"again-{name}-{machine}"], repo, expect=1)
            assert not any(x.is_symlink() for x in out.rglob("*")), "a link in the evidence"
            target = work / f"collected-{name}-{machine}"
            sh(kit + ["collect", "--out", out, "--destination", target], repo)
            shutil.rmtree(out)                              # the collected copy is byte for byte
            collected.append(target)
        return collected, m

    source = git("rev-parse", "HEAD")
    protocol = git("log", "-1", "--format=%H", "--", plan.BASE + "/PREDICTION.md")
    runs_m = measure_runs()
    measures, manifest_m = stage("measures", protocol, source, runs_m)

    # the prediction step, in the clone, from the collected evidence; then its two commits
    sys.path.insert(0, str(repo / plan.BASE))
    import analyze
    import predicted
    setup = dict(which=WHICH, section=SECTION, runs=runs_m, network=network_runs)
    predicted.build(repo / plan.BASE, measures, **setup)
    git("add", f"{plan.BASE}/MEASURES.json", f"{plan.BASE}/PREDICTED.json")
    git("commit", "--quiet", "-m", "Rehearsal: predictions")
    protocol_r = git("rev-parse", "HEAD")
    checked = sh(["bash", repo / plan.BASE / "check.sh"], repo).strip().splitlines()[-1] if shutil.which("lean") else "lean is not installed here: Predicted.lean was not checked"
    git("add", f"{plan.BASE}/Predicted.lean")
    git("commit", "--quiet", "-m", "Rehearsal: the per-port statements for the Lean kernel")
    source_r = git("rev-parse", "HEAD")
    P = json.loads((repo / plan.BASE / "PREDICTED.json").read_text())
    network, manifest_r = stage("runs", protocol_r, source_r, P["network_runs"])
    assert manifest_m["protocol_sha256"] != manifest_r["protocol_sha256"]
    claims = sh(["git", "ls-remote", "--heads", remote], work).split()[1::2]

    R = analyze.analyse(P, measures, network, **setup)
    (work / "RESULTS.json").write_text(json.dumps(R, indent=1) + "\n")
    (work / "REPORT.md").write_text(analyze.report(R, P))
    assert R["predictions_are_those_of_the_measures"] and R["lean_file_is_that_of_the_measures"] and not R["runs_not_in_the_predictions"]
    assert all(v == "complete" for v in list(R["measure_runs"].values()) + list(R["network_runs"].values()))
    assert all(x["record_is_the_waveform"] for x in R["runs"].values())
    walls, limits = {}, {}
    for folder, m in [(f, manifest_m) for f in measures] + [(f, manifest_r) for f in network]:
        timeout = {e["id"]: e["timeout_s"] for e in m["runs"]}
        for record in json.loads((folder / "STATE.json").read_text())["records"]:
            walls[record["id"]], limits[record["id"]] = round(record["wall_s"]), timeout[record["id"]]
    sizes = {f.name: {x["path"]: x["bytes"] for x in json.loads((f / "SURVIVORS.json").read_text())["files"] if x["path"].endswith("trace.raw")} for f in measures + network}
    I = P["instances"]["none"]
    report = dict(scope="rehearsal on the nominal cell (no mismatch), which is not an instance of the campaign: its five measure runs, the prediction step and its Lean "
                        "check, its five network runs, the analysis; synthetic kind of the launch kit, local Git remote; not a registered run",
                  source_commit=source, files={name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest() for name in plan.FROZEN},
                  two_protocols=dict(measures=manifest_m["protocol_path"], runs=manifest_r["protocol_path"]), claims=sorted(claims),
                  second_launch_refused_at_each_stage=True, no_link_in_the_evidence=True, lean_check=checked,
                  predicted=dict(measured=P["measured_instances"], eligible=P["eligible_instances"], control=P["control_instance"], need=I.get("need"), laps=I.get("laps"),
                                 zero_error_words=I.get("zero_error_words"), budgets={k: dict(budget_mV=v["budget_mV"], own_room=v["own_room"], least_room_mV=v["least_room_mV"])
                                                                                      for k, v in I.get("budgets", {}).items()},
                                 network_runs=[(r["id"], r["machine"], r["laps"], r["timeout_s"]) for r in P["network_runs"]], kit_bound_s=P["kit_bound_s"]),
                  verdicts={k: R[k]["verdict"] for k in ("primary", "H", "P4", "N_own", "N_word", "C")},
                  primary=R["primary"]["rows"], N_own=R["N_own"], N_word=R["N_word"], C=R["C"], M4=R["M4"], M5=R["M5"],
                  runs={k: dict(words=x["words"], freeze_lap=x["freeze_lap"], H=x["H"], P4={p: v["holds"] for p, v in x["P4"].items()},
                                least_separation_units=x["least_separation_units"], largest_move_not_a_dose_mV=x["largest_move_not_a_dose_mV"], wall_s=x["wall_s"])
                        for k, x in R["runs"].items()},
                  wall_s=walls, limits_s=limits, waveform_bytes=sizes, all_checks_passed=True)
    a.report.write_text(json.dumps(report, indent=1) + "\n")
    print(json.dumps(dict(verdicts=report["verdicts"], wall_s=walls, lean=checked), indent=1))


if __name__ == "__main__":
    main()
