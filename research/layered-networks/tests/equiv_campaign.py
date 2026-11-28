"""Equivalence test (a): the chain (campaign_run17) and campaign.py start the same steps.

  python -B tests/equiv_campaign.py OUTDIR

For each machine of a plan_split3 split (m = 8) of NOT1 ×6 (6220 audited), XOR3 9803 and ANDOR3 6104, and each scenario
(eligible and room; eligible, no room; not eligible), it compares two lists of steps.
- **The chain:** campaign_run17's real cmd_run, in a subprocess, on a fresh root. The test replaces
  campaign_run.run_child with a recorder: nothing is simulated, and each step's declared outputs are written from
  fixtures. A prediction with the scenario's eligibility and room makes the chain take that branch. The remote
  duplicate finds its home's line on a local bare seal log built with seal.py. The recorder notes per child: argv, cwd,
  time limit, environment additions. The step wrapper notes the declared outputs, the kind and the cores.
- **campaign.py:** `campaign.py steps` (the no-run mode) on the same groups, the same root path and the same scenario,
  with its own test template.

They must be identical per instance and step: argv (the seal commit replaced by a placeholder), cwd, environment
additions, declared outputs, time limit, guarded or exempt, cores. The only allowed difference is listed: campaign.py
declares the outputs of U and of the duplicate's N0 and C0, which the chain checks without declaring them.
Writes OUTDIR/EQUIV_A.json; exit 1 on a difference.
`python -B tests/equiv_campaign.py OUTDIR negative` is the negative control: campaign.py's test template gets one time
limit changed (C + 1 s), and every case must then differ (OUTDIR/EQUIV_A_NEGATIVE.json).
"""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parents[1]
PY = sys.executable
DRAW = {"format": "layered-draw/1", "groups": {"NOT1": [6212, 6213, 6217, 6218, 6219, 6220], "XOR3": [9803], "ANDOR3": [6104]}}
SCENARIOS = {"eligible_room": (True, True), "eligible_noroom": (True, False), "not_eligible": (False, False)}
COMMIT = "c" * 40

CHAIN = r'''
import json, os, sys, threading
from pathlib import Path
sys.path.insert(0, {here!r})
import campaign_run as CR
import campaign_run2 as C2
base = set(os.environ)
ELIG, ROOM = {elig!r}, {room!r}
REC, LOCAL = [], threading.local()
_step = C2.Instance.step
def step(self, name, argv, outputs, kind, cwd=CR.HERE, env=None):
    LOCAL.ctx = (self.dir.name, name, list(outputs), kind)
    try:
        return _step(self, name, argv, outputs, kind, cwd, env)
    finally:
        LOCAL.ctx = None
C2.Instance.step = step
def write(p, obj):
    p = Path(p); p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(obj if isinstance(obj, str) else json.dumps(obj))
def fake(argv, cwd, log, timeout, env=None):
    a = [str(x) for x in argv]
    ctx = getattr(LOCAL, "ctx", None)
    REC.append(dict(ctx=ctx, argv=a, cwd=str(cwd), timeout=timeout, env_added=sorted(set(os.environ) - base)))
    script, cmd = Path(a[2]).name, a[3] if len(a) > 3 else None
    if script == "stage_d6.py" and cmd == "deck":
        write(a[5], "* deck\n")
    elif script == "indeck_noise4.py":
        out = Path(a[5]); write(out / "inverter_gate.json", {{}}); write(out / "SHA256SUMS", ""); write(out / "K3_BUDGET.json", {{"ok": True}})
    elif script == "stage_d6.py" and cmd == "run":
        out = Path(a[5]); write(out / "record.json", {{}})
        write(out / "prediction.json", dict(eligible_K0=ELIG, room_K3=ROOM, inverter_gate=dict(source="fixture", K0=True, K3=True), cells=[]))
    elif script == "stage_d6.py" and cmd == "seal":
        out = Path(a[4]); write(out / "SHA256SUMS", ""); write(out / "MANIFEST.json", {{}})
    elif script == "sealpush2.py":
        write(a[9], dict(pushed=True, commit={commit!r}, branch=a[5], seal_sha256="s", line="l", pushed_at_machine_utc="2020-01-01T00:00:00.000000Z"))
    elif script == "controls4.py" and cmd == "stagen":
        out = Path(a[5]); write(out / "noisy_record.json", {{}}); write(out / "trace.digest.json", {{}})
    elif script == "compare_d2.py":
        write(a[7], dict(verdict="agrees", run_kind="noisy"))
    elif script == "controls4.py" and cmd == "untrained":
        write(Path(a[5]) / "untrained_record.json", dict(tests=[], slots=[]))
    else:
        raise SystemExit(f"unexpected child {{a}}")
    return 0, 0.0, False
CR.run_child = fake
import campaign_run17 as C17
C17.cmd_run({plan!r}, {root!r}, "jobs=4", "template=" + {tpl!r})
st = {{}}
for p in Path({root!r}).glob("*/status.json"):
    s = json.loads(p.read_text())
    st[p.parent.name] = {{k: v.get("cores") for k, v in s["steps"].items()}}
json.dump(dict(rec=REC, cores=st), open({out!r}, "w"))
'''


def seal_log_fixture(remote, plans):
    """A bare seal log where every duplicate's home branch has its instance's line and seal folder."""
    sys.path.insert(0, str(HERE))
    import seal as sealmod
    import spec as specmod
    subprocess.run(["git", "init", "-q", "--bare", str(remote)], check=True)
    with tempfile.TemporaryDirectory() as w:
        w = Path(w)
        for p in plans.values():
            for x in p["remote_duplicates"]:
                tag = specmod.load(HERE / x["spec"])["tag"]
                pdir = w / f"pred_{x['seed']}"
                pdir.mkdir()
                pdir.joinpath("prediction.json").write_bytes(sealmod.canon(dict(
                    tag=tag, seed=x["seed"], status="done", eligible_K0=True, room_K3=True,
                    inverter_gate=dict(source="fixture"))))
                sd = w / f"seal_{x['seed']}"
                sealmod.seal(sd, pdir)
                wt = w / f"wt_{x['seed']}"
                subprocess.run(["git", "init", "-q", str(wt)], check=True)
                for k, v in (("user.name", "t"), ("user.email", "t@t")):
                    subprocess.run(["git", "-C", str(wt), "config", k, v], check=True)
                h = __import__("hashlib").sha256((sd / "SHA256SUMS").read_bytes()).hexdigest()
                (wt / "SEALS.txt").write_text(f"{x['home_instance']} {h} 2020-01-01T00:00:00Z\n")
                shutil.copytree(sd, wt / "seals" / x["home_instance"])
                subprocess.run(["git", "-C", str(wt), "add", "-A"], check=True)
                subprocess.run(["git", "-C", str(wt), "commit", "-q", "-m", "s"], check=True)
                subprocess.run(["git", "-C", str(wt), "push", "-q", str(remote), f"HEAD:refs/heads/{x['home_branch']}"], check=True)


def plans_for(d, template, remote, splitter="plan_split3.py", negative=False):
    pin = json.loads((HERE / template).read_text())
    t = dict(pin, seal_push=dict(pin["seal_push"], remote=str(remote)), what="equivalence test template")
    if negative:                                  # the negative control: one time limit changed by 1 s
        t["time_limits_s"] = dict(t["time_limits_s"], C=t["time_limits_s"]["C"] + 1)
    tf = d / f"T_{template}"
    tf.write_text(json.dumps(t, indent=1, sort_keys=True) + "\n")
    out = d / f"plans_{template}"
    subprocess.run([PY, "-B", str(HERE / splitter), str(d / "DRAW.json"), str(tf), str(out), "m=8"], check=True,
                   capture_output=True)
    return tf, {p.stem[5:]: (p, json.loads(p.read_text())) for p in sorted(out.glob("PLAN_K*.json"))}


def norm_argv(a):
    return [("seal_log=<seal commit>" if x.startswith("seal_log=") else x) for x in a]


def main(outdir, *rest):
    negative = "negative" in rest
    out = Path(outdir)
    out.mkdir(parents=True, exist_ok=True)
    work = Path(tempfile.mkdtemp(dir=out))
    (work / "DRAW.json").write_text(json.dumps(DRAW))
    remote = work / "log.git"
    t5, p5 = plans_for(work, "TEMPLATE_CAMPAIGN_5.json", remote)
    tc, pc = plans_for(work, "campaign_template.json", remote, negative=negative)
    seal_log_fixture(remote, {k: v[1] for k, v in p5.items()})
    kb = None
    report, diffs = [], 0
    for machine in sorted(p5):
        plan5, plan_c = p5[machine], pc[machine]
        if not plan5[1]["groups"] and not plan5[1]["remote_duplicates"]:
            continue
        for scen, (elig, room) in SCENARIOS.items():
            root = work / f"root_{machine}_{scen}"
            root.mkdir()
            if kb is not None:
                shutil.copytree(kb, root / "kernel_build")
            rec_f = work / f"chain_{machine}_{scen}.json"
            code = CHAIN.format(here=str(HERE), elig=elig, room=room, commit=COMMIT, plan=str(plan5[0]), root=str(root),
                                tpl=str(t5), out=str(rec_f))
            p = subprocess.run([PY, "-B", "-c", code], cwd=HERE, capture_output=True, text=True, timeout=1800)
            if p.returncode or not rec_f.exists():
                raise SystemExit(f"chain {machine} {scen} failed: {p.stdout[-800:]} {p.stderr[-2000:]}")
            if kb is None:
                kb = root / "kernel_build"
            chain = json.loads(rec_f.read_text())
            q = subprocess.run([PY, "-B", str(HERE / "campaign.py"), "steps", "test", str(tc), str(plan_c[0]), str(root),
                                f"room={'yes' if room else 'no'}", f"eligible={'yes' if elig else 'no'}"],
                               capture_output=True, text=True, cwd=HERE)
            if q.returncode:
                raise SystemExit(f"campaign.py steps {machine} {scen} failed: {q.stderr[-1500:]}")
            new = [json.loads(l) for l in q.stdout.splitlines() if l.strip()]
            a_rows = {}
            for r in chain["rec"]:
                if r["ctx"]:
                    inst, step, outs, kind = r["ctx"]
                    cores = chain["cores"].get(inst, {}).get(step)
                    outputs = outs
                else:                                    # U and the duplicate: children outside a step
                    a = r["argv"]
                    step = "U" if a[3] == "untrained" else ("N0" if Path(a[2]).name == "controls4.py" else "C0")
                    inst = Path(a[3] if step == "C0" else a[5]).parent.name
                    kind = {"U": "U", "N0": "dup", "C0": "C"}[step]
                    cores = 1 if step == "N0" else 0    # the duplicate's N0 takes a core; U and its C0 none
                    outputs = None
                a_rows[(inst, step)] = dict(argv=norm_argv(r["argv"]), cwd=r["cwd"], env_added=r["env_added"],
                                            outputs=outputs, time_limit_s=float(r["timeout"]),
                                            guarded=kind != "C", cores=cores)
            b_rows = {}
            for r in new:
                b_rows[(r["instance"], r["step"])] = dict(argv=norm_argv(r["argv"]), cwd=r["cwd"], env_added=sorted(r["env_added"]),
                                                          outputs=r["outputs"], time_limit_s=float(r["time_limit_s"]),
                                                          guarded=r["guarded"], cores=r["cores"])
            listed = []
            for k in set(a_rows) | set(b_rows):
                a, b = a_rows.get(k), b_rows.get(k)
                if a is None or b is None:
                    continue
                if a["outputs"] is None:                  # listed: the chain declares no outputs for U and the duplicate
                    listed.append(f"{k[0]} {k[1]}: outputs declared by campaign.py only: {b['outputs']}")
                    a = dict(a, outputs=b["outputs"])
                a_rows[k] = a
            bad = []
            for k in sorted(set(a_rows) | set(b_rows)):
                if a_rows.get(k) != b_rows.get(k):
                    bad.append(dict(key=list(k), chain=a_rows.get(k), campaign=b_rows.get(k)))
            diffs += len(bad)
            report.append(dict(machine=machine, scenario=scen, steps=len(b_rows), identical=not bad, differences=bad,
                               listed=sorted(listed), instances=sorted({k[0] for k in b_rows})))
            print(machine, scen, "steps", len(b_rows), "identical" if not bad else f"DIFFER {len(bad)}", flush=True)
    res = dict(format="layered-equiv-a/1", identical=diffs == 0, cases=report)
    if negative:
        res.update(negative_control=True, every_case_differs=all(not c["identical"] for c in report))
        (out / "EQUIV_A_NEGATIVE.json").write_text(json.dumps(res, indent=1, sort_keys=True) + "\n")
        shutil.rmtree(work, ignore_errors=True)
        return res["every_case_differs"]
    (out / "EQUIV_A.json").write_text(json.dumps(res, indent=1, sort_keys=True) + "\n")
    shutil.rmtree(work, ignore_errors=True)
    return diffs == 0


if __name__ == "__main__":
    sys.exit(0 if main(*sys.argv[1:]) else 1)
