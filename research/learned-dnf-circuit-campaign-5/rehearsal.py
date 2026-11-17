"""Campaign 5: the rehearsal of the frozen implementation in the real conditions of the campaign (PREDICTION.md, 11).

It replaces campaign 4's rehearsal.py, which ran both machines' shards on one container in the kit's synthetic kind.
Campaign 5's rehearsal runs the kit's registered kind (the campaign's own path, live CI gate included) on the branch
research/learned-dnf-circuit-campaign-5-rehearsal, on the campaign's two machines. Every stage (RC, RM, RQ, RN, RMEM)
is one manifest over both machines, with the same runs on each (plan.rehearsal_runs). The kit's launches are made by
hand, by the procedure of the campaign's stages. This script writes what the frozen code writes and checks what 11.5
asks, each check appended to the checks file as soon as it is done, so that a stopped rehearsal resumes from its last
written check.

  rehearsal.py before OUT_DIR rc|dev                     the rehearsal's own BEFORE_M.md: the nominal cell (RC) or the
                                                         development instances (dev), machine a; never the campaign's
  rehearsal.py runs STAGE OUT.json [DEV_PREDICTED.json]  STAGE_<STAGE>_RUNS.json of a rehearsal stage (plan.rehearsal_runs)
  rehearsal.py predict BEFORE_DIR OUT_DIR MEASURES_DIR...  PREDICTED.json of the rehearsal (predicted.predictions, the
                                                         rehearsal's limits) and its gate (gate4.lean_file)
  rehearsal.py memory OUT.jsonl EVIDENCE_DIR             the machine's memory, sampled every second while the shard runs
  rehearsal.py guard CHECKS.jsonl                        RG: direct calls to the frozen code (11.2), appended as checks
  rehearsal.py check CHECKS.jsonl KIND ARGS...           one check of 11.5, appended (see CHECKS below)
  rehearsal.py record CHECKS.jsonl REHEARSAL.json        the record: every check, its verdict, and the rehearsal's verdict

The collection of a stage is collect.py, run once per machine. No word, output or score of a rehearsal run is a claim.
"""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.path.insert(0, str(HERE))
import c4                                               # noqa: E402
import plan                                             # noqa: E402

BASE = c4.BASE
PY = sys.executable
# the checks of 11.5, and whether each is required ("reported" ones are not)
CHECKS = dict(limits="required", reproducibility="required", noise_differs="required", operating_point="required",
              cross_machine="reported", memory="required", cases="required", gate_dev="required", mutations="required",
              guard="required", collection="required", analysis="required", no_campaign_seed="required", chain="required")
# what two runs of one deck, instance seed and noise seed may differ in (PREDICTION.md, section 6)
ALLOWED_RECORD_DIFFERENCES = ("id", "wall_s", "peak_rss_MB")
FILES_COMPARED_APART = ("trace.raw", "result.json", "session.log")


def append(checks, kind, ok, **details):
    """Appends one check to the checks file at once (11.6)."""
    assert kind in CHECKS, kind
    line = dict(check=kind, ok=bool(ok), required=CHECKS[kind] == "required", utc=time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), **details)
    with open(checks, "a") as f:
        f.write(json.dumps(line, sort_keys=True, default=str) + "\n")
        f.flush()
        os.fsync(f.fileno())
    print(json.dumps(dict(check=kind, ok=bool(ok))))
    return ok


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


# ---------------------------------------------------------------------------------------- the rehearsal's records

def before(kind):
    """The rehearsal's own record before its measures (never the campaign's BEFORE_M.md): the nominal cell for RC,
    the development instances for RM to RMEM, all on machine a, whose evidence the prediction reads."""
    cost = plan.costs()
    seeds = [None] if kind == "rc" else list(c4.DEV_SEEDS)
    b = dict(what=f"the rehearsal's record ({kind}), not the campaign's BEFORE_M.md", noise_model="injected",
             noise_model_source="PREDICTION.md, section 6", constants=dict(c4.DECISION5), constants_source="decision 5",
             costs=cost, costs_source="PREDICTION.md, 10.3", I=0, seeds=dict(a=seeds, b=[]),
             machine_of={str(s): "a" for s in seeds}, expected_compute_s=0.0, expected_compute_h=0.0, expected={},
             limits=plan.limits_record(cost), measure_stages={}, network_stage_caps_need4_s={},
             rehearsal=dict(path="(the rehearsal itself)", commit="-", sha256="-", verdict="-"))
    return b


def runs_file(name, dev_path=None):
    dev = json.loads(Path(dev_path).read_text()) if dev_path else None
    return dict(stage=name, I=0, rehearsal=True, runs=plan.rehearsal_runs(name, dev))


def predict(before_dir, out_dir, measure_dirs):
    import predicted as P
    import gate4
    b = plan.read_before_m(Path(before_dir) / "BEFORE_M.md")
    res, files = P.predictions(b, [Path(d) for d in measure_dirs], (), True)
    assert not files
    out = Path(out_dir)
    out.mkdir(parents=True, exist_ok=True)
    (out / "PREDICTED.json").write_text(json.dumps(res, indent=1, default=str) + "\n")
    xs = [dict(x, tag=str(x["seed"])) for x in res["instances"] if x.get("measured") and "observation" in x]
    (out / "Gate4.lean").write_text(gate4.lean_file(xs, "the rehearsal's PREDICTED.json") if xs else
                                    gate4.header("the rehearsal's PREDICTED.json") + "theorem no_instance_with_all_needs : True := trivial\n\n"
                                    "end LearnedCoincidence.MonotoneDNF.PremiseCheck.Campaign4\n")
    return res


# ------------------------------------------------------------------------------------------------ memory (11.5)

def meminfo():
    m = {l.split(":")[0]: int(l.split()[1]) for l in Path("/proc/meminfo").read_text().splitlines()}
    return m["MemTotal"], m["MemTotal"] - m["MemAvailable"]


def memory(out, evidence):
    """Samples the memory used on the machine (MemTotal - MemAvailable, kB) every second, appending each sample, until
    the shard's STATE.json exists and no longer reads running."""
    state = Path(evidence) / "STATE.json"
    with open(out, "a") as f:
        while True:
            total, used = meminfo()
            f.write(json.dumps(dict(unix=time.time(), total_kB=total, used_kB=used)) + "\n")
            f.flush()
            if state.exists():
                try:
                    if json.loads(state.read_text()).get("status") != "running":
                        break
                except ValueError:
                    pass
            time.sleep(1)


# ------------------------------------------------------------------------------------------------- RG (11.2)

def guard(checks):
    """RG: the seed guard's refusals, the noise-model guard's refusal, safeguards (i) and (ii), by direct calls."""
    import run4
    out = {}

    def refused(f, *a):
        try:
            f(*a)
        except (AssertionError, SystemExit) as e:
            return str(e)
        return None
    with tempfile.TemporaryDirectory() as d:
        o = Path(d) / "run"
        out["campaign seed 7601 outside the kit"] = refused(run4.guard, 7601, 12, o, None)
        out["seed 7501"] = refused(run4.guard, 7501, 12, o, None)
        out["development seed 7691 in campaign stage Q"] = refused(run4.guard, 7691, 12, o, "Q")
        out["development seed 7691 outside the kit, rehearsal stage RM"] = refused(run4.guard, 7691, 12, o, "RM")
        out["campaign seed 7601 in rehearsal stage RM"] = refused(run4.guard, 7601, 12, o, "RM")
        out["noise model device"] = refused(run4.noise_guard, "network", "device")
        out["an extraction run"] = refused(run4.noise_guard, "extract", "none")
        # the noise model refused before any simulation, by the runner itself: no deck is written
        p = subprocess.run([PY, "-B", str(HERE / "run4.py"), "--out", str(Path(d) / "dev"), "--ngspice", "/bin/false", "--pdk", d,
                            "--id", "x", "--kind", "network", "--seed", "none", "--needs", "4,4,4,4", "--noise", "device", "--round", "1"],
                           capture_output=True, text=True)
        out["run4.py --noise device"] = (p.stderr.strip().splitlines() or ["?"])[-1] if p.returncode != 0 and not (Path(d) / "dev").exists() else None
        # safeguard (i): a stage file whose governing protocol has another SHA-256
        sf = Path(d) / "STAGE_RM.md"
        sf.write_text(plan.stage_file_text("RM", f"{BASE}/c4.py", "0" * 40, "0" * 64))     # a governing file whose SHA-256 is not that one
        out["safeguard (i)"] = refused(run4.stage_check, str(sf))
        # safeguard (ii): a copy of the repository with a frozen file changed, and one with an allowed file only
        repo = Path(d) / "repo"
        subprocess.run(["git", "clone", "-q", "--shared", str(ROOT), str(repo)], check=True)
        g = lambda *a: subprocess.run(["git", "-C", str(repo), *a], check=True, capture_output=True, text=True).stdout.strip()
        g("config", "user.name", "rehearsal")
        g("config", "user.email", "rehearsal@example.invalid")
        head = g("rev-parse", "HEAD")
        (repo / BASE / "STAGE_RM.md").write_text("allowed\n")
        g("add", "-A")
        g("commit", "-q", "-m", "allowed")
        ok_commit = g("rev-parse", "HEAD")
        (repo / BASE / "c4.py").write_text((repo / BASE / "c4.py").read_text() + "# changed\n")
        g("add", "-A")
        g("commit", "-q", "-m", "frozen file changed")
        bad_commit = g("rev-parse", "HEAD")
        out["safeguard (ii), an allowed file only (accepted)"] = refused(plan.check_after_freeze, head, ok_commit, repo)
        out["safeguard (ii), a frozen file changed"] = refused(plan.check_after_freeze, head, bad_commit, repo)
    accepted = "safeguard (ii), an allowed file only (accepted)"
    ok = all(v for k, v in out.items() if k != accepted) and out[accepted] is None
    return append(checks, "guard", ok, results=out)


# ------------------------------------------------------------------------------------------------- the checks

def record_of(folder):
    return json.loads((Path(folder) / "record.json").read_text())


def same_run(f1, f2):
    """Section 6: two runs of one deck, instance seed and noise seed. Returns the differences found."""
    import measure  # noqa: F401  (research/network-circuit, via session4's path)
    r1, r2 = record_of(f1), record_of(f2)
    diff = []
    for k in sorted(set(r1) | set(r2)):
        if k in ALLOWED_RECORD_DIFFERENCES:
            continue
        if k == "files":
            for name in sorted(set(r1[k]) | set(r2[k])):
                if name not in FILES_COMPARED_APART and r1[k].get(name) != r2[k].get(name):
                    diff.append(f"files.{name}")
            continue
        if r1.get(k) != r2.get(k):
            diff.append(k)
    e1, e2 = Path(f1) / "evidence", Path(f2) / "evidence"
    strip = lambda b: b"\n".join(l for l in b.split(b"\n") if not l.startswith(b"Date:"))
    if strip((e1 / "trace.raw").read_bytes()) != strip((e2 / "trace.raw").read_bytes()):
        diff.append("trace.raw without its Date: line")
    j1, j2 = (json.loads((e / "result.json").read_text()) for e in (e1, e2))
    j1.pop("wall_s", None)
    j2.pop("wall_s", None)
    if j1 != j2:
        diff.append("result.json without wall_s")
    log = lambda e: [l for l in (e / "session.log").read_text().splitlines() if not l.startswith(" Reference value : ")]
    if log(e1) != log(e2):
        diff.append("session.log without its progress lines")
    return diff


def initial_point(folder):
    import measure
    tr = measure.Trace(Path(folder) / "evidence" / "trace.raw")
    return {k: float(v[0]) for k, v in sorted(tr.v.items())}


def check(checks, kind, args):
    if kind == "limits":                 # limits STAGE_RUNS.json COLLECTED_DIR...: the 0.75 rule (11.4)
        lst = json.loads(Path(args[0]).read_text())
        runs = {r["id"]: r for r in lst["runs"]}
        seen, bad = {}, []
        for d in args[1:]:
            st = json.loads((Path(d) / "STATE.json").read_text())
            for rec in st["records"]:
                r = runs[rec["id"]]
                share = (rec.get("wall_s") or 0) / r["campaign_limit_s"]
                seen[rec["id"]] = dict(status=rec["status"], wall_s=rec.get("wall_s"), campaign_limit_s=r["campaign_limit_s"],
                                       share=share, stopped_on_purpose=bool(r.get("stopped_on_purpose")))
                if r.get("stopped_on_purpose"):
                    continue
                if rec["status"] != "complete" or share > c4.LIMIT_SHARE:
                    bad.append(rec["id"])
        missing = [i for i in runs if i not in seen]
        return append(checks, "limits", not bad and not missing, stage=lst["stage"], runs=seen, failing=bad, never_recorded=missing)
    if kind == "reproducibility":        # reproducibility RUN_DIR RUN_DIR (one noise seed)
        d = same_run(*args)
        return append(checks, "reproducibility", not d, runs=args, differences=d)
    if kind == "noise_differs":          # noise_differs RUN_DIR RUN_DIR (two noise seeds, one deck and calendar)
        f = [record_of(a)["noise_fingerprint"] for a in args]
        return append(checks, "noise_differs", f[0] != f[1], runs=args, fingerprints=f)
    if kind == "operating_point":        # operating_point RUN_DIR...: every run starts from the same point
        pts = [initial_point(a) for a in args]
        names = set(pts[0])
        ok = all(set(p) == names for p in pts) and all(p[n] == pts[0][n] for p in pts for n in names if n in p and n != "time")
        return append(checks, "operating_point", ok, runs=args)
    if kind == "cross_machine":          # cross_machine RUN_DIR_A RUN_DIR_B (reported, not required)
        d = same_run(*args)
        return append(checks, "cross_machine", not d, runs=args, differences=d)
    if kind == "memory":                 # memory MACHINE INVENTORY.json SAMPLES.jsonl
        inv = json.loads(Path(args[1]).read_text())
        total = int(inv["memory"].split()[0])
        peak = max(json.loads(l)["used_kB"] for l in Path(args[2]).read_text().splitlines() if l.strip())
        return append(checks, "memory", peak <= 0.8 * total, machine=args[0], peak_kB=peak, total_kB=total, share=peak / total)
    if kind in ("cases", "mutations"):   # cases: check.sh (the cases, their targets and the mutations, regenerated and audited)
        p = subprocess.run(["bash", str(HERE / "check.sh")], capture_output=True, text=True, env=dict(os.environ, PYTHON=PY))
        tail = (p.stdout + p.stderr).splitlines()[-12:]
        return append(checks, kind, p.returncode == 0 and "check.sh: passed" in p.stdout, output=tail)
    if kind == "gate_dev":               # gate_dev PREDICTED_DIR: the gate on the development instances, and beta_3's true path
        import cases
        d = Path(args[0])
        pred = json.loads((d / "PREDICTED.json").read_text())
        p = subprocess.run(["bash", str(HERE / "check.sh"), str(d / "Gate4.lean")], capture_output=True, text=True, env=dict(os.environ, PYTHON=PY))
        per = {}
        for x in pred["instances"]:
            if x.get("measured") and "observation" in x:
                per[str(x["seed"])] = {f"K{K}": cases.per_checker(cases.conditions(x, K)) for K in (0, 3)}
        room3 = [str(x["seed"]) for x in pred["instances"] if x.get("room_at_K3") and all(x["room_at_K3"].values())]
        return append(checks, "gate_dev", p.returncode == 0, per_checker=per, check_sh=(p.stdout + p.stderr).splitlines()[-6:],
                      beta3_true_path_tried=bool(room3), instances_with_room_at_K3=room3,
                      note="" if room3 else "no development instance has room at K = 3: the true path of the beta_3 conjunction was not tried")
    if kind == "collection":             # collection COLLECTED_DIR...
        got = {}
        for d in args:
            m = json.loads((Path(d) / "COLLECTED.json").read_text())
            got[d] = dict(files=len(m["files"]), links=len(m["links"]), collector_sha256=m["collector_sha256"])
        ok = all(v["collector_sha256"] == sha(HERE / "collect.py") for v in got.values())
        return append(checks, "collection", ok, collections=got)
    if kind == "analysis":               # analysis BEFORE_DIR PREDICTED_DIR OUT_DIR MEAS_A MEAS_B RUNS_A RUNS_B
        import analyze
        b, pdir, out = Path(args[0]), Path(args[1]), Path(args[2])
        res = analyze.main([str(out)] + args[3:7], here=b, predicted_path=pdir / "PREDICTED.json", rehearsal=True)
        recs = {k: v["record_is_the_waveform"] for k, v in res["runs"].items() if v.get("record_is_the_waveform") is not None}
        p = subprocess.run(["bash", str(HERE / "check.sh"), str(pdir / "Gate4.lean"), str(out / "M8.lean")], capture_output=True, text=True,
                           env=dict(os.environ, PYTHON=PY))
        ok = res["predicted_is_reproduced"] and all(recs.values()) and p.returncode == 0
        return append(checks, "analysis", ok, predicted_is_reproduced=res["predicted_is_reproduced"], records_equal_files=recs,
                      check_sh=(p.stdout + p.stderr).splitlines()[-6:])
    if kind == "no_campaign_seed":       # no_campaign_seed COLLECTED_DIR...: every deck's setseed, every record's seed
        seen = []
        for d in args:
            for deck in Path(d).rglob("input.spice"):
                for l in deck.read_text().splitlines():
                    if l.strip().startswith("setseed"):
                        seen.append(int(l.split()[1]))
            for rec in Path(d).rglob("record.json"):
                s = json.loads(rec.read_text()).get("seed")
                if s is not None:
                    seen.append(s)
        bad = sorted({s for s in seen if s not in c4.DEV_SEEDS})
        return append(checks, "no_campaign_seed", not bad, seeds_seen=sorted(set(seen)), outside_the_development_seeds=bad)
    if kind == "chain":                  # chain STEP OK [NOTE]: a step of the chain test (11.3) ran and wrote its output
        return append(checks, "chain", args[1] == "ok", step=args[0], note=" ".join(args[2:]))
    raise SystemExit(f"unknown check {kind}")


def record(checks, out):
    lines = [json.loads(l) for l in Path(checks).read_text().splitlines() if l.strip()]
    required_failed = [l for l in lines if l["required"] and not l["ok"]]
    present = {l["check"] for l in lines}
    absent = sorted(k for k, v in CHECKS.items() if v == "required" and k not in present)
    rec = dict(what="the record of campaign 5's rehearsal (PREDICTION.md, 11), written by rehearsal.py record", interpreter=c4.interpreter(),
               checks_file_sha256=sha(checks), checks=lines, required_failed=[l["check"] for l in required_failed], required_absent=absent,
               all_required_passed=not required_failed and not absent)
    Path(out).write_text(json.dumps(rec, indent=1, sort_keys=True, default=str) + "\n")
    print(json.dumps(dict(all_required_passed=rec["all_required_passed"], required_failed=rec["required_failed"], required_absent=absent)))


def main():
    print(c4.require_pinned())
    cmd, args = sys.argv[1], sys.argv[2:]
    if cmd == "before":
        out = Path(args[0])
        out.mkdir(parents=True, exist_ok=True)
        (out / "BEFORE_M.md").write_text(plan.before_m_text(before(args[1])))
    elif cmd == "runs":
        Path(args[1]).write_text(json.dumps(runs_file(args[0], args[2] if len(args) > 2 else None), indent=1) + "\n")
    elif cmd == "predict":
        predict(args[0], args[1], args[2:])
    elif cmd == "memory":
        memory(args[0], args[1])
    elif cmd == "guard":
        guard(args[0])
    elif cmd == "check":
        check(args[0], args[1], args[2:])
    elif cmd == "record":
        record(args[0], args[1])
    else:
        raise SystemExit(__doc__)


if __name__ == "__main__":
    main()
