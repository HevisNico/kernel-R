"""Campaign 4: the rehearsal of the frozen implementation on the nominal cell, through the launch kit. Not a registered
run, and not an instance of the campaign: the nominal cell (model section `tt`, no mismatch, no seed) only.

  rehearsal.py --ngspice BIN --pdk DIR --work NEW_DIR --report REHEARSAL.json

A local clone of this repository and a local bare remote stand for GitHub; the kit runs in its `synthetic` kind, which
never contacts GitHub and consumes no registered attempt. The rehearsal follows the campaign's own path, with the
campaign's own code, under the device model (its BEFORE_M.md is the rehearsal's, in the clone only):

  M      a: the two calibration decks, a run without noise and without control (need 4, the zero-amplitude check's
            reference), the untrained control run; b: the single-run extraction, beside three injected noisy runs
            (two with one noise seed, one with another: reproducibility under the injected model)
  E      the 21 per-output extraction runs of the frozen code (MEASURED.json from stage M), split over a and b
  then   the merged extraction against the single-run one (byte identity); PREDICTED.json and its Lean gate, written
         by the frozen code from the collected evidence, committed as the protocol of the network stage
  N      a: Q and N1, N2, N3 of PREDICTED.json (plan.stage_runs); b: N1's noise seed again (device reproducibility), the
         zero-amplitude run (device model, xtrtol=7, every source at amplitude 0)
  MEM    a: four device noisy runs on the need-7 calendar, four at a time; b: four injected ones; the memory of the
         machine sampled over each shard
  GUARD  a run with a seed outside 7501 to 7500 + I, and a run whose seed is allowed but whose I is 0, both inside a
         real kit launch: both must be refused by run4.py's seed guard before any simulation; and a run with seed 7501
         outside the kit (refused)

Then the one analysis (analyze.py) on the rehearsal's outputs, check.sh on the gate and on M8, and the record:
reproducibility (records identical but `wall_s`, the run's id and its peak memory; waveforms identical but the date
line; two seeds, two noises; one operating point; the samples file regenerated to the same SHA-256), memory below 80 %,
the zero-amplitude check, the identity of the split extraction, the seed guard, no seed >= 7501 simulated, and the
measured wall times, whose ratios to the cost model are the limits basis of the campaign's manifests.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import threading
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.path.insert(0, str(HERE))
import c4                                               # noqa: E402
import plan                                             # noqa: E402

BASE = c4.BASE
DECISIONS = dict(noise_model="device", noise_model_source="rehearsal: the device model, before the validation's verdict",
                 constants_source="decision 5 (the rehearsal has no validated value)", costs_source="the cost model of PREDICTION.md",
                 reuse_trip=False, reuse_trip_source="rehearsal: the trip value not reused (the code of the noise study unchanged)")
ZERO_TOL_V, FIRE_TOL_S = 1e-6, 0.1e-6


def sh(argv, cwd, expect=0):
    """expect: 0 (must succeed), 1 (must fail), None (either)."""
    p = subprocess.run([str(x) for x in argv], cwd=cwd, capture_output=True, text=True)
    if expect is not None and (p.returncode == 0) != (expect == 0):
        raise AssertionError(" ".join(str(x) for x in argv) + "\n" + p.stdout[-3000:] + "\n" + p.stderr[-3000:])
    return p.stdout


class Memory:
    """The memory used on the machine (MemTotal - MemAvailable), sampled every half second while a shard runs."""

    def __init__(self):
        self.peak, self.stop = 0, threading.Event()
        self.total = self.read()[0]

    @staticmethod
    def read():
        m = {l.split(":")[0]: int(l.split()[1]) for l in Path("/proc/meminfo").read_text().splitlines()}
        return m["MemTotal"], m["MemTotal"] - m["MemAvailable"]

    def run(self):
        while not self.stop.is_set():
            self.peak = max(self.peak, self.read()[1])
            time.sleep(0.5)

    def __enter__(self):
        self.base = self.read()[1]
        self.t = threading.Thread(target=self.run, daemon=True)
        self.t.start()
        return self

    def __exit__(self, *a):
        self.stop.set()
        self.t.join()


def check_run(rid, machine, kind, **kw):
    """A run of the rehearsal that is not in PREDICTED.json (a check), costed by the cost model."""
    r = dict(id=rid, machine=machine, seed=None, kind=kind, **kw)
    if kind == "network":
        r.setdefault("round", 0)
        r.setdefault("scenario", "check")
        r.setdefault("extraction", None)
    return r


def entry_of(r, I):
    e = plan.entry(r, I, "stage")
    if r.get("scale") == "0":
        e["argv"] += ["--scale", "0"]
    return e


def main():
    p = argparse.ArgumentParser(description=__doc__)
    for name in ("ngspice", "pdk", "work", "report"):
        p.add_argument("--" + name, type=Path, required=True)
    a = p.parse_args()
    print(c4.require_pinned())
    work = a.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    started = time.time()
    repo, remote = work / "repo", work / "remote.git"
    for name in sh(["git", "-C", ROOT, "status", "--porcelain", "--", BASE, "research/learned-dnf-circuit", "research/network-circuit",
                    "research/circuit", plan.CLOSURE, "research/learned-coincidence"], work).splitlines():
        raise AssertionError("commit first: the rehearsal runs the committed files: " + name)
    head = sh(["git", "-C", ROOT, "rev-parse", "HEAD"], work).strip()
    sh(["git", "clone", "--quiet", "--shared", ROOT, repo], work)
    git = lambda *args: sh(["git", *args], repo).strip()
    git("config", "user.name", "Rehearsal")
    git("config", "user.email", "rehearsal@example.invalid")
    sh(["git", "init", "--quiet", "--bare", remote], work)
    sh(["git", "-C", remote, "config", "receive.shallowUpdate", "true"], work)
    git("remote", "set-url", "origin", str(remote))
    git("checkout", "--quiet", "-b", "rehearsal")
    kit = [sys.executable, "-B", repo / plan.CLOSURE / "launchkit" / "launch.py"]
    env = ["--ngspice", a.ngspice.resolve(), "--pdk", a.pdk.resolve()]
    rb = repo / BASE
    for machine in ("a", "b"):
        sh(kit + ["inventory", "--machine", machine, "--out", rb / f"INVENTORY_{machine}.json"] + env, repo)
    b = plan.before_m(DECISIONS)
    b.update(I=1, seeds=dict(a=[None], b=[]), machine_of={"None": "a"}, rehearsal="the nominal cell only; not the campaign's BEFORE_M.md")
    (rb / "BEFORE_M.md").write_text(plan.before_m_text(b))
    git("add", f"{BASE}/BEFORE_M.md", f"{BASE}/INVENTORY_a.json", f"{BASE}/INVENTORY_b.json")
    git("commit", "--quiet", "-m", "Rehearsal: BEFORE_M.md of the nominal cell, inventories")
    before = plan.read_before_m(rb / "BEFORE_M.md")
    cost, I = plan.costs(before), 1
    lim = lambda r, model="device": plan.with_limits(r, cost, model)
    report = dict(scope="rehearsal of campaign 4 on the nominal cell (no mismatch, no seed), which is not an instance of the campaign; the launch "
                        "kit's synthetic kind, a local Git remote; not a registered run", source_commit=head,
                  frozen_files={n: hashlib.sha256((ROOT / n).read_bytes()).hexdigest() for n in plan.FROZEN},
                  interpreter=c4.interpreter(), stages={}, checks={})
    collected = {}

    def stage(name, protocol_commit, protocol, runs, memory=False):
        """One launch of the kit on both machines, one after the other; the collected folders."""
        source = git("rev-parse", "HEAD")
        m = plan.manifest(name, runs, I, protocol_commit, protocol, source, root=repo)
        m.update(kind="synthetic", campaign_id="synthetic-c4-rehearsal-" + name.lower(), runs=[entry_of(r, I) for r in runs])
        del m["expected_workflows"]
        m["budget_s"] = min(14400, max(1, int(plan.stage_cap(runs)) + 1))
        path = rb / f"REHEARSAL_{name}.json"
        path.write_text(json.dumps(m, indent=1) + "\n")
        common = ["--repo", repo, "--manifest", path] + env
        git("add", str(path.relative_to(repo)))
        git("commit", "--quiet", "-m", f"Rehearsal: manifest of stage {name}")
        git("push", "--quiet", "origin", "rehearsal")
        sh(kit + ["preflight"] + common, repo)
        sh(kit + ["prepare"] + common, repo)
        git("add", m["marker_path"])
        git("commit", "--quiet", "-m", f"Rehearsal: attempt marker of stage {name}")
        git("push", "--quiet", "origin", "rehearsal")
        out = {}
        for machine in ("a", "b"):
            folder = work / f"{name}-{machine}"
            t0 = time.time()
            if memory:
                with Memory() as mem:
                    sh(kit + ["run-machine"] + common + ["--branch", "rehearsal", "--machine", machine, "--out", folder], repo, expect=None)
                memrec = dict(peak_used_kB=mem.peak, before_kB=mem.base, total_kB=mem.total, peak_fraction=mem.peak / mem.total)
            else:
                sh(kit + ["run-machine"] + common + ["--branch", "rehearsal", "--machine", machine, "--out", folder], repo, expect=None)
                memrec = None
            state = json.loads((folder / "STATE.json").read_text())
            sh(kit + ["run-machine"] + common + ["--branch", "rehearsal", "--machine", machine, "--out", work / f"again-{name}-{machine}"], repo, expect=1)
            assert not any(x.is_symlink() for x in folder.rglob("*")), "a link in the evidence"
            target = work / f"collected-{name}-{machine}"
            sh(kit + ["collect", "--out", folder, "--destination", target], repo)
            out[machine] = target
            report["stages"].setdefault(name, {})[machine] = dict(status=state["status"], wall_s=time.time() - t0, memory=memrec,
                                                                  runs={r["id"]: dict(status=r["status"], wall_s=r.get("wall_s")) for r in state["records"]})
        collected[name] = out
        return out, m

    protocol0 = git("log", "-1", "--format=%H", "--", f"{BASE}/PREDICTION.md")
    # ----- M
    runs_m = [lim(r) for r in plan.cal_runs(None, "a")]
    runs_m += [lim(check_run("a-None-quiet-nocontrol", "a", "network", needs=[4, 4, 4, 4], control=None, noise="none")),
               lim(check_run("a-None-untrained-check", "a", "network", needs=[4, 4, 4, 4], control="untrained", noise="none"))]
    runs_m += [lim(check_run("b-None-extract-single", "b", "extract", state="all", cell=None, port=None, isolation=False, reuse_trip=False))]
    runs_m += [lim(check_run(f"b-None-injected-{tag}", "b", "network", needs=[4, 4, 4, 4], control=None, noise="injected", round=rnd), "injected")
               for tag, rnd in (("r1", 1), ("r1-again", 1), ("r2", 2))]
    M, _ = stage("M", protocol0, "PREDICTION.md", runs_m)
    sh([sys.executable, "-B", rb / "plan.py", "measured", M["a"], M["b"], rb / "MEASURED.json"], repo)
    git("add", f"{BASE}/MEASURED.json")
    git("commit", "--quiet", "-m", "Rehearsal: MEASURED.json")
    # ----- E (the frozen code's split; the parts spread over both machines for the rehearsal)
    parts = [lim(r) for r in plan.extract_runs(None, "a", before["reuse_trip"])]
    for i, r in enumerate(parts):
        r["machine"] = "a" if i % 2 == 0 else "b"
    E, _ = stage("E", protocol0, "PREDICTION.md", parts)
    # ----- the predictions, the gate, the identity of the split extraction
    sh([sys.executable, "-B", rb / "predicted.py", "predictions", repo, M["a"], M["b"], "--extractions", E["a"], E["b"]], repo)
    P = json.loads((rb / "PREDICTED.json").read_text())
    ex = P["extractions"]["None"]
    merged = (repo / ex["path"]).read_bytes()
    single = json.loads((M["b"] / "b-None-extract-single" / "extraction.json").read_text())
    single_text = (json.dumps(single, indent=1) + "\n").encode()
    report["checks"]["split_extraction_identity"] = dict(merged_sha256=hashlib.sha256(merged).hexdigest(), single_sha256=hashlib.sha256(single_text).hexdigest(),
                                                         identical=merged == single_text, V2_V2b_isolation=ex)
    git("add", f"{BASE}/PREDICTED.json", ex["path"])
    git("commit", "--quiet", "-m", "Rehearsal: PREDICTED.json and the merged extraction")
    protocol_n = git("rev-parse", "HEAD")
    sh([sys.executable, "-B", rb / "gate4.py", "lean", rb / "PREDICTED.json", rb / "Gate4.lean"], repo)
    lean_gate = sh(["bash", rb / "check.sh", rb / "Gate4.lean"], repo).strip().splitlines()[-3:]
    git("add", f"{BASE}/Gate4.lean")
    git("commit", "--quiet", "-m", "Rehearsal: the Lean gate written from PREDICTED.json")
    report["checks"]["gate_on_the_rehearsal_prediction"] = dict(check_sh=lean_gate, eligible=P["instances"][0].get("eligible"),
                                                                 why_not_eligible=P["instances"][0].get("why_not_eligible"))
    # ----- N: Q and N1..N3 of PREDICTED.json, plus the checks
    stage_runs = []
    for name in ("Q", "N1", "N2", "N3"):
        rs, protocol, _ = plan.stage_runs(name, here=rb)
        assert protocol == "PREDICTED.json"
        stage_runs += rs
    n1 = next(r for r in stage_runs if r.get("round") == 1)
    checks_n = [dict(n1, id="b-None-n1-again", machine="b"),
                lim(check_run("b-None-zero-amplitude", "b", "network", needs=[4, 4, 4, 4], control=None, noise="device", round=1,
                              extraction=n1["extraction"], scale="0"))]
    N, _ = stage("N", protocol_n, "PREDICTED.json", stage_runs + checks_n)
    # ----- MEM: four noisy runs on the need-7 calendar, four at a time, per model
    mem = [lim(check_run(f"a-None-need7-device-{k}", "a", "network", needs=[7, 7, 7, 7], control=None, noise="device", round=1 + k % 3,
                         extraction=n1["extraction"])) for k in range(4)]
    mem += [lim(check_run(f"b-None-need7-injected-{k}", "b", "network", needs=[7, 7, 7, 7], control=None, noise="injected", round=1 + k % 3), "injected")
            for k in range(4)]
    MEM, _ = stage("MEM", protocol_n, "PREDICTED.json", mem, memory=True)
    # ----- GUARD: refusals inside a real kit launch, before any simulation
    guard = [lim(dict(id="a-7510-cal-on", machine="a", seed=7510, kind="cal", guard="on")),
             lim(dict(id="b-7501-cal-on", machine="b", seed=7501, kind="cal", guard="on"))]
    gm = plan.manifest("GUARD", guard, I, protocol0, "PREDICTION.md", git("rev-parse", "HEAD"), root=repo)
    gm["runs"][0]["argv"][gm["runs"][0]["argv"].index("--instances") + 1] = "9"      # 7510 is outside 7501 to 7509
    gm["runs"][1]["argv"][gm["runs"][1]["argv"].index("--instances") + 1] = "0"      # I = 0: no seed is allowed
    gm.update(kind="synthetic", campaign_id="synthetic-c4-rehearsal-guard", budget_s=14400)
    del gm["expected_workflows"]
    gp = rb / "REHEARSAL_GUARD.json"
    gp.write_text(json.dumps(gm, indent=1) + "\n")
    git("add", str(gp.relative_to(repo)))
    git("commit", "--quiet", "-m", "Rehearsal: manifest of the seed guard")
    git("push", "--quiet", "origin", "rehearsal")
    common = ["--repo", repo, "--manifest", gp] + env
    sh(kit + ["prepare"] + common, repo)
    git("add", gm["marker_path"])
    git("commit", "--quiet", "-m", "Rehearsal: marker of the seed guard")
    git("push", "--quiet", "origin", "rehearsal")
    guard_out = {}
    for machine in ("a", "b"):
        folder = work / f"GUARD-{machine}"
        sh(kit + ["run-machine"] + common + ["--branch", "rehearsal", "--machine", machine, "--out", folder], repo, expect=None)
        st = json.loads((folder / "STATE.json").read_text())
        rec = st["records"][0]
        err = (folder / rec["id"] / "stderr.log").read_text()
        guard_out[rec["id"]] = dict(status=rec["status"], refused_by_the_guard="AssertionError" in err and ("is not one of" in err),
                                    simulated=any((folder / rec["id"]).rglob("input.spice")), stderr_tail=err.strip().splitlines()[-1:])
    outside = subprocess.run([sys.executable, "-B", rb / "run4.py", "--out", work / "outside-kit", "--ngspice", a.ngspice, "--pdk", a.pdk, "--id", "x",
                              "--kind", "cal", "--guard", "on", "--seed", "7501", "--instances", "9"], cwd=repo, capture_output=True, text=True)
    guard_out["outside the kit, seed 7501, I = 9"] = dict(returncode=outside.returncode, refused="only inside a launch of the kit" in outside.stderr,
                                                          simulated=any((work / "outside-kit").rglob("input.spice")) if (work / "outside-kit").exists() else False)
    report["checks"]["seed_guard"] = dict(runs=guard_out, all_refused_before_simulation=all(
        (v.get("refused_by_the_guard") or v.get("refused")) and not v["simulated"] for v in guard_out.values()))
    # ----- the analysis, on the rehearsal's outputs
    import analyze
    an = work / "analysis"
    res = analyze.main([an, M["a"], M["b"], N["a"], N["b"], E["a"], E["b"]], here=rb)
    m8 = sh(["bash", rb / "check.sh", an / "M8.lean"], repo).strip().splitlines()[-2:]
    report["checks"]["analysis"] = dict(predicted_is_reproduced=res["predicted_is_reproduced"], regeneration_check=res["regeneration_check"],
                                        claims={k: (v if isinstance(v, str) else v.get("verdict") if isinstance(v, dict) and "verdict" in v else "see RESULTS")
                                                for k, v in res["claims"].items()},
                                        records_are_the_waveforms={k: v["record_is_the_waveform"] for k, v in res["runs"].items()}, m8_check_sh=m8,
                                        results_sha256=hashlib.sha256((an / "RESULTS.json").read_bytes()).hexdigest())
    shutil.copy(an / "RESULTS.json", work / "RESULTS_analysis.json")
    report["checks"].update(checks(work, collected, P, rb))
    report["limits_basis"], report["wall_times"] = limits_basis(collected, cost)
    report["no_seed_from_7501_simulated"] = no_campaign_seed(work)
    report["total_wall_s"] = time.time() - started
    report["all_checks_passed"] = all_passed(report)
    a.report.write_text(json.dumps(report, indent=1, default=str) + "\n")
    print(json.dumps(dict(all_checks_passed=report["all_checks_passed"], limits_basis=report["limits_basis"]), indent=1))


def folder_of(collected, rid):
    for st in collected.values():
        for f in st.values():
            if (f / rid).is_dir():
                return f / rid
    raise KeyError(rid)


def record(collected, rid):
    return json.loads((folder_of(collected, rid) / "record.json").read_text())


def without_date(raw):
    return b"\n".join(l for l in raw.split(b"\n") if not l.startswith(b"Date:"))


def checks(work, collected, P, rb):
    sys.path.insert(0, str(HERE.parent / "network-circuit"))
    import measure
    import noisemodel
    import plans4
    import reads4
    out = {}
    skip = ("id", "wall_s", "peak_rss_MB")
    same_rec = lambda x, y: {k: v for k, v in record(collected, x).items() if k not in skip} == {k: v for k, v in record(collected, y).items() if k not in skip}
    raw = lambda rid: (folder_of(collected, rid) / "evidence" / "trace.raw").read_bytes()
    first_point = lambda rid: (lambda tr: {k: float(v[0]) for k, v in tr.v.items()})(measure.Trace(folder_of(collected, rid) / "evidence" / "trace.raw"))
    pairs = dict(device=("a-None-n1", "b-None-n1-again", "a-None-n2"), injected=("b-None-injected-r1", "b-None-injected-r1-again", "b-None-injected-r2"))
    quiet = first_point("a-None-quiet-nocontrol")
    for model, (x, y, z) in pairs.items():
        fx = first_point(x)
        r = dict(records_identical_but_wall_s=same_rec(x, y), waveforms_identical_but_the_date_line=without_date(raw(x)) == without_date(raw(y)),
                 two_seeds_two_noises=record(collected, x)["noise_fingerprint"] != record(collected, z)["noise_fingerprint"],
                 same_operating_point=fx == first_point(y) == first_point(z))
        out[f"operating_point_against_the_run_without_noise_{model}"] = dict(max_abs_diff=max(abs(fx[k] - quiet[k]) for k in quiet if k in fx),
                                                                            vectors=len([k for k in quiet if k in fx]))
        if model == "device":
            ex = json.loads((rb.parent.parent / P["extractions"]["None"]["path"]).read_text())
            regen = noisemodel.regenerate_sha256(ex, c4.CELLS, record(collected, x)["noise"], work / "regen")
            r["samples_regenerated_to_the_same_sha256"] = regen == record(collected, x)["noise"]["samples_sha256"]
        out[f"reproducibility_{model}"] = r
    # zero amplitude (device model, xtrtol=7) against the run without noise of the same calendar
    plan_, slots = plans4.network((4, 4, 4, 4), None)

    def rows(rid):
        f = folder_of(collected, rid) / "evidence"
        return reads4.network_reads(measure.Trace(f / "trace.raw"), json.loads((f / "result.json").read_text()), slots), json.loads((f / "result.json").read_text())
    (zr, zres), (qr, qres) = rows("b-None-zero-amplitude"), rows("a-None-quiet-nocontrol")
    occ = lambda res: [(o["cell"], o["port"], o["delivered"], round(o["date_s"], 9)) for o in res["occurrences"]]
    ev = lambda rr: [(x["slot"], c, r["fire"], tuple(v["writes"] for v in r["ports"].values())) for x in rr for c, r in sorted(x["reads"].items())]
    du = max(abs(r1["ports"][p]["u_before_mV"] - r2["ports"][p]["u_before_mV"]) * 1e-3 for x1, x2 in zip(zr, qr) for c, r1 in x1["reads"].items()
             for r2 in [x2["reads"][c]] for p in r1["ports"])
    df = max([abs(r1["fire_date_s"] - x2["reads"][c]["fire_date_s"]) for x1, x2 in zip(zr, qr) for c, r1 in x1["reads"].items() if r1["fire"]] or [0.0])
    out["zero_amplitude"] = dict(same_occurrences=occ(zres) == occ(qres), same_writes_and_fire_events=ev(zr) == ev(qr), max_stored_voltage_diff_V=du,
                                 max_fire_date_diff_s=df, passed=occ(zres) == occ(qres) and ev(zr) == ev(qr) and du <= ZERO_TOL_V and df <= FIRE_TOL_S,
                                 xtrtol=record(collected, "b-None-zero-amplitude")["noise"].get("scale") == "0")
    return out


def limits_basis(collected, cost):
    """Per run kind, the largest ratio of a rehearsal run's measured wall time (the kit's record) to its expected cost."""
    walls, ratio = {}, {}
    for name, st in collected.items():
        for machine, f in st.items():
            m = json.loads((f / "STATE.json").read_text())
            for r in m["records"]:
                own = json.loads((f / r["id"] / "record.json").read_text()) if (f / r["id"] / "record.json").exists() else None
                if r["status"] != "complete" or own is None:
                    continue
                run = dict(kind=own["kind"], state=own.get("state"), isolation=own.get("isolation"), needs=own.get("needs"), control=own.get("control"),
                           noise="none" if own["kind"] != "network" else own["noise"]["model"])
                if run["kind"] == "extract" and run["state"] == "all":
                    walls[r["id"]] = dict(wall_s=r["wall_s"], kind="extract-single")
                    continue
                model = run["noise"] if run["noise"] in ("device", "injected") else "device"
                e = plan.expected(dict(run, noise=run["noise"]), cost, model)
                k = plan.run_kind(run)
                walls[r["id"]] = dict(wall_s=r["wall_s"], expected_s=e, kind=k, stage=name, machine=machine)
                ratio[k] = max(ratio.get(k, 0.0), r["wall_s"] / e)
    return ratio, walls


def no_campaign_seed(work):
    """Every deck simulated in the rehearsal, and every run's record: no setseed with a seed from 7501 up, no seed field."""
    import re
    seen = []
    for f in Path(work).rglob("input.spice"):
        for m in re.finditer(r"setseed\s+(\d+)", f.read_text()):
            seen.append((str(f), int(m.group(1))))
    seeds = []
    for f in Path(work).rglob("record.json"):
        s = json.loads(f.read_text()).get("seed")
        if s is not None:
            seeds.append((str(f), s))
    return dict(setseed_values=sorted({s for _, s in seen}), record_seeds=sorted({s for _, s in seeds}),
                none_from_7501=not any(s >= c4.FIRST_SEED for _, s in seen + seeds))


def all_passed(r):
    c = r["checks"]
    mem_ok = all(v["memory"]["peak_fraction"] < 0.8 for v in r["stages"]["MEM"].values())
    r["checks"]["memory"] = {m: v["memory"] for m, v in r["stages"]["MEM"].items()}
    return bool(c["split_extraction_identity"]["identical"] and c["seed_guard"]["all_refused_before_simulation"] and c["zero_amplitude"]["passed"]
                and all(all(v.values()) for k, v in c.items() if k.startswith("reproducibility_")) and mem_ok
                and r["no_seed_from_7501_simulated"]["none_from_7501"] and c["analysis"]["predicted_is_reproduced"]
                and all(v is not False for v in c["analysis"]["records_are_the_waveforms"].values())
                and all(s["status"] == "complete" for name, st in r["stages"].items() for s in st.values()))


if __name__ == "__main__":
    main()
