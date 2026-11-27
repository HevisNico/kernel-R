"""Equivalence test (c): every path the chain never took, through campaign.py's real entry points (launch or run as a
subprocess), never by calling a function. Every failure is produced from outside: a test template, a signal, a stub
tree, a filled disk or a tampered input. Needs ngspice, Lean 4.35.0 and the pinned environment; about an hour.

  python -B tests/test_campaign.py WORKDIR [case ...]      WORKDIR/TEST_C.json; exit 1 if a case fails

The plans are plan_split3's on NOT1 6212, 6213, m = 8:
- K01 = NOT1_6212, the home: U and keep_raw;
- K02 = NOT1_6213;
- K03 = the duplicate of NOT1_6212.

The cases:
- refusals:
  - a template in the wrong mode (both ways);
  - a plan key missing, and one extra;
  - a short commit;
  - a disk at launch below disk_launch_gb;
  - analysis.py in campaign mode on a TEST root;
- timeout: a test template with a 0.001 s deck limit. The deck is "timeout", nothing follows, and the instance is not
  completed at the deck;
- guard: a test template with an impossible guard. Nothing starts, the deck is held (no status entry), and RESULT.json
  lists it;
- crash: SIGKILL, from outside, of stage D's process while it runs. D failed, not completed;
- interruption and resume: SIGTERM to the driver while stage D runs, and its child's process group killed (the machine
  stops). Then `run` again: D is "interrupted", is never relaunched, and nothing after it starts;
- kernel–mirror disagreement: a stub stage-D tree (a local commit whose fit.cell_valid says the dose clause is false).
  The kernel rejects that clause, D fails, and the prediction's kernel.disagreements names it;
- no pushed seal: the seal log refuses every push (pre-receive). sealpush fails, and N0 never starts;
- second seal: the same instance sealed twice on one branch. The second sealpush is refused;
- partial guard and resume: the disk is filled from outside while N0 runs, so that free space falls below the test
  template's guard and stays above the real campaign guard of any other run:
  - C0 runs (exempt, logged) and N1–N3 and U are held;
  - after the filler is removed, `run` again starts what was held and completes;
- differing duplicate: the duplicate machine runs on a stub noise tree (a local commit raising the temperature by 1 °C)
  against the home's seal. check_duplicate says it differs (analysis.py, test mode).
"""
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parents[1]
PY = sys.executable
DRAW = {"format": "layered-draw/1", "note": "tests (c)", "groups": {"NOT1": [6212, 6213]}}


def sh(*a, **k):
    return subprocess.run([str(x) for x in a], capture_output=True, text=True, **k)


def campaign(tree, *a, **k):
    return sh(PY, "-B", Path(tree) / "research" / "layered-networks" / "campaign.py", *a, **k)


def status(root, inst):
    f = Path(root) / inst / "status.json"
    return json.loads(f.read_text())["steps"] if f.exists() else {}


def wait_for(cond, timeout, every=2):
    t0 = time.time()
    while time.time() - t0 < timeout:
        if cond():
            return True
        time.sleep(every)
    return False


class Work:
    def __init__(self, wd):
        self.wd = Path(wd)
        self.wd.mkdir(parents=True, exist_ok=True)
        (self.wd / "DRAW.json").write_text(json.dumps(DRAW))
        self.trees = {}

    def tree(self, name, tamper=None):
        """A fresh clone of the dev branch, with its kit and noise worktrees; `tamper(clone)` makes a stub commit."""
        if name in self.trees:
            return self.trees[name]
        t = self.wd / f"tree_{name}"
        if t.exists():
            shutil.rmtree(t)
        src = subprocess.run(["git", "-C", str(HERE), "rev-parse", "--show-toplevel"], capture_output=True, text=True).stdout.strip()
        branch = subprocess.run(["git", "-C", str(HERE), "rev-parse", "--abbrev-ref", "HEAD"], capture_output=True, text=True).stdout.strip()
        common = subprocess.run(["git", "-C", str(HERE), "rev-parse", "--git-common-dir"], capture_output=True, text=True).stdout.strip()
        assert sh("git", "clone", "-q", "--depth", "1", "--branch", branch, f"file://{Path(common).resolve().parent}", t).returncode == 0
        tmpl = json.loads((HERE / "campaign_template.json").read_text())
        for c in (tmpl["kit_commit"], tmpl["noise_commit"]):
            sh("git", "-C", t, "fetch", "-q", "--depth", "1", "origin", c)
            sh("git", "-C", t, "worktree", "add", "-q", "--detach", f"{t}.wt-{c[:8]}", c)
        for x in (t, Path(f"{t}.wt-{tmpl['kit_commit'][:8]}"), Path(f"{t}.wt-{tmpl['noise_commit'][:8]}")):
            pdk = x / "research" / "circuit" / "pdk"
            if not pdk.exists():
                pdk.symlink_to(Path(src) / "research" / "circuit" / "pdk")
        for k, v in (("user.name", "test"), ("user.email", "test@invalid")):
            sh("git", "-C", t, "config", k, v)
        info = dict(tree=t, noise_commit=tmpl["noise_commit"])
        if tamper:
            info.update(tamper(t) or {})
        self.trees[name] = info
        return info

    def remote(self, name, refuse_all=False):
        r = self.wd / f"log_{name}.git"
        if r.exists():
            shutil.rmtree(r)
        sh("git", "init", "-q", "--bare", r)
        hooks = Path(__file__).resolve().parents[1] / "tests"
        pre = r / "hooks" / "pre-receive"
        pre.write_text("#!/bin/sh\necho refused by the test hook >&2; exit 1\n" if refuse_all else
                       "#!/bin/sh\nz=0000000000000000000000000000000000000000\nwhile read old new ref; do\n"
                       "  if [ \"$new\" = \"$z\" ]; then exit 1; fi\n"
                       "  if [ \"$old\" != \"$z\" ] && ! git merge-base --is-ancestor \"$old\" \"$new\"; then exit 1; fi\ndone\n")
        pre.chmod(0o755)
        post = r / "hooks" / "post-receive"
        post.write_text("#!/bin/sh\nwhile read old new ref; do echo \"$new $ref $(date -u +%Y-%m-%dT%H:%M:%S.%NZ)\" >> \"$GIT_DIR/push_times.log\"; done\n")
        post.chmod(0o755)
        return r

    def template(self, name, remote, **mods):
        t = json.loads((HERE / "campaign_template.json").read_text())
        t["seal_push"] = dict(t["seal_push"], remote=str(remote))
        t["disk_launch_gb"] = 0
        for k, v in mods.items():
            if k == "time_limits_s":
                t[k] = dict(t[k], **v)
            else:
                t[k] = v
        t["what"] = f"test template: {name}"
        f = self.wd / f"T_{name}.json"
        f.write_text(json.dumps(t, indent=1, sort_keys=True) + "\n")
        return f

    def plans(self, name, tree, template):
        out = self.wd / f"plans_{name}"
        p = sh(PY, "-B", Path(tree) / "research" / "layered-networks" / "plan_split3.py", self.wd / "DRAW.json", template,
               out, "m=8")
        assert p.returncode == 0, p.stderr
        return {k: out / f"PLAN_{k}.json" for k in ("K01", "K02", "K03")}


def check(checks, label, text, needle, target, exists_before):
    """One record of a check: the expected message, the line that matched it (None: no match), the target and whether
    it existed before the call. A check passes only if its own message matched and its target existed."""
    line = next((ln for ln in str(text).splitlines() if needle in ln), None)
    checks.append(dict(check=label, expected=needle, matched=line.strip()[-300:] if line else None,
                       target=str(target), target_exists=exists_before))
    return line is not None and exists_before is True


def result(root):
    f = Path(root) / "RESULT.json"
    return json.loads(f.read_text()) if f.exists() else None


# ================================================================================================ the cases

def case_refusals(w):
    tr = w.tree("main")["tree"]
    rem = w.remote("refusals")
    tt = w.template("refusals", rem)
    pl = w.plans("refusals", tr, tt)
    out, checks, oks = {}, [], []
    frozen = tr / "research/layered-networks/campaign_template.json"
    e = tt.exists() and pl["K02"].exists()
    out["campaign mode, test template"] = campaign(tr, "check", "campaign", tt, pl["K02"]).stdout.strip()
    oks.append(check(checks, "campaign mode, test template", out["campaign mode, test template"],
                     "campaign mode needs the frozen template", tt, e))
    e = frozen.exists() and pl["K02"].exists()
    out["test mode, frozen template"] = campaign(tr, "check", "test", frozen, pl["K02"]).stdout.strip()
    oks.append(check(checks, "test mode, frozen template", out["test mode, frozen template"],
                     "test mode needs a test template, not the frozen one", frozen, e))
    want = {"missing key rounds": "the plan differs from the template: missing key rounds",
            "extra key steps_until": "the plan differs from the template: key steps_until is not allowed",
            "short kit commit": "the plan differs from the template: kit_commit is 'd599300d'"}
    p = json.loads(pl["K02"].read_text())
    for label, mod in (("missing key rounds", lambda q: q.pop("rounds")), ("extra key steps_until", lambda q: q.update(steps_until="D")),
                       ("short kit commit", lambda q: q.update(kit_commit=q["kit_commit"][:8]))):
        q = json.loads(json.dumps(p))
        mod(q)
        f = w.wd / f"PLAN_bad_{label.replace(' ', '_')}.json"
        f.write_text(json.dumps(q))
        e = f.exists()
        r = campaign(tr, "launch", "test", tt, f, w.wd / f"root_bad_{label.replace(' ', '_')}")
        out[label] = (r.returncode, (r.stdout + r.stderr).strip()[-200:])
        oks.append(r.returncode != 0 and check(checks, label, r.stdout + r.stderr, want[label], f, e))
    big = w.template("bigdisk", rem, disk_launch_gb=10 ** 6)
    plb = w.plans("bigdisk", tr, big)
    e = big.exists() and plb["K02"].exists()
    r = campaign(tr, "launch", "test", big, plb["K02"], w.wd / "root_bigdisk")
    out["disk at launch"] = (r.returncode, (r.stdout + r.stderr).strip()[-200:])
    oks.append(r.returncode != 0 and check(checks, "disk at launch", r.stdout + r.stderr,
                                           "GB free at launch, 1e+06 GB needed (disk_launch_gb)", big, e))
    out["checks"] = checks
    ok = all(oks) and \
        all(not (w.wd / f"root_bad_{x}").exists() for x in ("missing_key_rounds", "extra_key_steps_until", "short_kit_commit")) and \
        not (w.wd / "root_bigdisk").exists()
    return ok, out


def case_timeout(w):
    tr = w.tree("main")["tree"]
    tt = w.template("timeout", w.remote("timeout"), time_limits_s=dict(deck=0.001))
    pl = w.plans("timeout", tr, tt)
    root = w.wd / "root_timeout"
    e = pl["K02"].exists()
    r = campaign(tr, "run", "test", tt, pl["K02"], root)
    st = status(root, "NOT1_6213")
    res = result(root)
    checks = []
    c = check(checks, "deck timed out", st.get("deck", {}).get("why"), "more than 0.001 s", pl["K02"], e)
    ok = c and r.returncode == 0 and st.get("deck", {}).get("status") == "timeout" and set(st) == {"deck"} and \
        (root / "DONE").exists()
    return ok, dict(steps={k: v["status"] for k, v in st.items()}, why=st.get("deck", {}).get("why"),
                    result_mode=(res or {}).get("campaign", {}).get("mode"), checks=checks)


def case_guard(w):
    tr = w.tree("main")["tree"]
    tt = w.template("guard", w.remote("guard"), disk_guard_gb=10 ** 6)
    pl = w.plans("guard", tr, tt)
    root = w.wd / "root_guard"
    e = pl["K02"].exists()
    r = campaign(tr, "run", "test", tt, pl["K02"], root)
    res = result(root)
    st = status(root, "NOT1_6213")
    checks = []
    c = check(checks, "deck held below the guard", json.dumps(res["stopped_for_disk"]), '"step": "deck"', pl["K02"], e)
    ok = c and r.returncode == 0 and st == {} and [h["step"] for h in res["stopped_for_disk"]] == ["deck"]
    return ok, dict(steps=st, stopped_for_disk=res["stopped_for_disk"], checks=checks)


def kill_group(pattern):
    pids = [int(x) for x in sh("pgrep", "-f", pattern).stdout.split()]
    for pid in pids:
        try:
            os.killpg(os.getpgid(pid), signal.SIGKILL)
        except ProcessLookupError:
            pass
    return pids


def run_bg(tree, *a):
    """The driver in the background; its output goes to <OUTROOT>.driver_bg.log beside the root (a refusal is kept)."""
    log = open(f"{a[-1]}.driver_bg.log", "w")
    return subprocess.Popen([PY, "-B", str(Path(tree) / "research" / "layered-networks" / "campaign.py"), *map(str, a)],
                            stdout=log, stderr=subprocess.STDOUT, start_new_session=True)


def case_crash(w):
    tr = w.tree("main")["tree"]
    tt = w.template("crash", w.remote("crash"))
    pl = w.plans("crash", tr, tt)
    root = w.wd / "root_crash"
    p = run_bg(tr, "run", "test", tt, pl["K02"], root)
    assert wait_for(lambda: status(root, "NOT1_6213").get("D", {}).get("status") == "running", 1800), \
        Path(f"{root}.driver_bg.log").read_text()[-400:]
    time.sleep(5)
    k = kill_group(f"stage_d6.py run .*{root}/NOT1_6213/D")   # the step's whole process group, from outside
    p.wait(timeout=1800)
    st = status(root, "NOT1_6213")
    checks = []
    c = check(checks, "D killed from outside", st["D"].get("why"), "exit -9", root, root.exists())
    ok = c and bool(k) and st["D"]["status"] == "failed" and "N0" not in st and (root / "DONE").exists()
    return ok, dict(killed_pids=k, D=dict(status=st["D"]["status"], why=st["D"].get("why")),
                    steps={k_: v["status"] for k_, v in st.items()}, checks=checks)


def case_interrupt(w):
    tr = w.tree("main")["tree"]
    tt = w.template("interrupt", w.remote("interrupt"))
    pl = w.plans("interrupt", tr, tt)
    root = w.wd / "root_interrupt"
    p = run_bg(tr, "run", "test", tt, pl["K02"], root)
    assert wait_for(lambda: status(root, "NOT1_6213").get("D", {}).get("status") == "running", 1800), \
        Path(f"{root}.driver_bg.log").read_text()[-400:]
    time.sleep(5)
    os.kill(p.pid, signal.SIGTERM)                      # the driver stops
    p.wait(timeout=120)
    kill_group(f"stage_d6.py run .*{root}/NOT1_6213/D")    # and so does the machine: its child's group goes too
    time.sleep(3)
    before = status(root, "NOT1_6213")
    r = campaign(tr, "run", "test", tt, pl["K02"], root)
    st = status(root, "NOT1_6213")
    checks = []
    c = check(checks, "D found running at the rerun", st["D"].get("why"), "found running at a resume", root, root.exists())
    ok = c and before["D"]["status"] == "running" and st["D"]["status"] == "interrupted" and "N0" not in st and \
        st["D"].get("started") == before["D"].get("started") and r.returncode == 0 and (root / "DONE").exists()
    return ok, dict(checks=checks, before={k: v["status"] for k, v in before.items()}, after={k: v["status"] for k, v in st.items()},
                    D_why=st["D"].get("why"), env_resumes=json.loads((root / "ENV_RESUMES.json").read_text())
                    if (root / "ENV_RESUMES.json").exists() else None)


def tamper_mirror(t):
    f = t / "research" / "layered-networks" / "fit.py"
    s = f.read_text()
    a = 'clauses = [("dose > 0", p["dose"])]'
    assert a in s
    f.write_text(s.replace(a, 'clauses = [("dose > 0", 0)]   # STUB: the mirror made wrong on one clause (test c)'))
    sh("git", "-C", t, "commit", "-q", "-am", "stub: tampered mirror (test)")


def case_kernel(w):
    tr = w.tree("stubmirror", tamper_mirror)["tree"]
    tt = w.template("kernel", w.remote("kernel"))
    pl = w.plans("kernel", tr, tt)
    root = w.wd / "root_kernel"
    r = campaign(tr, "run", "test", tt, pl["K02"], root)
    st = status(root, "NOT1_6213")
    pred = json.loads((root / "NOT1_6213" / "D" / "prediction.json").read_text()) if (root / "NOT1_6213" / "D" / "prediction.json").exists() else {}
    k = pred.get("kernel") or {}
    checks = []
    c = check(checks, "the kernel disagrees with the stub mirror", json.dumps(k.get("disagreements", [])),
              '"clause": "dose > 0"', root / "NOT1_6213" / "D" / "prediction.json",
              (root / "NOT1_6213" / "D" / "prediction.json").exists())
    ok = c and st.get("D", {}).get("status") == "failed" and "seal" not in st and not k.get("agrees", True)
    return ok, dict(D=st.get("D", {}).get("status"), disagreements=k.get("disagreements"), checks=checks)


def case_no_pushed_seal(w):
    tr = w.tree("main")["tree"]
    tt = w.template("nopush", w.remote("nopush", refuse_all=True))
    pl = w.plans("nopush", tr, tt)
    root = w.wd / "root_nopush"
    campaign(tr, "run", "test", tt, pl["K02"], root)
    st = status(root, "NOT1_6213")
    sp = json.loads((root / "NOT1_6213" / "seal_push.json").read_text()) if (root / "NOT1_6213" / "seal_push.json").exists() else None
    checks = []
    f = root / "NOT1_6213" / "seal_push.json"
    c = check(checks, "the push refused by the log's hook", (sp or {}).get("why"), "pre-receive hook declined", f, f.exists())
    ok = c and (sp or {}).get("pushed") is False and st.get("sealpush", {}).get("status") == "failed" and "N0" not in st
    return ok, dict(steps={k: v["status"] for k, v in st.items()}, seal_push=sp, checks=checks)


def case_github_times(w):
    """sealpush.github_times on a recorded activity API response (evidence/devtest-seals2-K05, 27 Nov 2026, the two
    seals' pushes) plus synthetic force_push and branch_deletion items: the branch-creating push and the later push
    count; the force push and the deletion never do."""
    import importlib.util
    spec = importlib.util.spec_from_file_location("sealpush_t", HERE / "sealpush.py")
    SPm = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(SPm)
    z = "0" * 40
    items = [dict(activity_type="push", before="5226d975283f5a905ba54abea8f8570685eef388",
                  after="80f2c0f5b46ce875cbb52ec4020a2e54ed0d4384", timestamp="2026-11-26T22:27:29Z",
                  ref="refs/heads/evidence/devtest-seals2-K05"),
             dict(activity_type="branch_creation", before=z, after="5226d975283f5a905ba54abea8f8570685eef388",
                  timestamp="2026-11-26T22:25:58Z", ref="refs/heads/evidence/devtest-seals2-K05"),
             dict(activity_type="force_push", before="80f2c0f5b46ce875cbb52ec4020a2e54ed0d4384", after="f" * 40,
                  timestamp="2026-11-26T23:00:00Z", ref="refs/heads/evidence/devtest-seals2-K05"),
             dict(activity_type="branch_deletion", before="f" * 40, after=z, timestamp="2026-11-26T23:10:00Z",
                  ref="refs/heads/evidence/devtest-seals2-K05")]
    tm = SPm.github_times(items)
    checks = []
    c1 = check(checks, "the branch-creating push counts", json.dumps(tm), '"5226d975283f5a905ba54abea8f8570685eef388": '
               '"2026-11-26T22:25:58Z"', HERE / "sealpush.py", (HERE / "sealpush.py").exists())
    c2 = check(checks, "the later push counts", json.dumps(tm), '"80f2c0f5b46ce875cbb52ec4020a2e54ed0d4384": '
               '"2026-11-26T22:27:29Z"', HERE / "sealpush.py", (HERE / "sealpush.py").exists())
    pages = {"two pages, no separator": json.dumps(items[:2]) + json.dumps(items[2:]),
             "two pages, a newline between": json.dumps(items[:2]) + "\n" + json.dumps(items[2:]) + "\n",
             "one page": json.dumps(items)}
    parsed = {k: SPm.github_times(SPm.activity_pages(v)) == tm for k, v in pages.items()}
    c3 = check(checks, "the pages parsed one after the other", json.dumps(parsed, sort_keys=True),
               '{"one page": true, "two pages, a newline between": true, "two pages, no separator": true}',
               HERE / "sealpush.py", (HERE / "sealpush.py").exists())
    ok = c1 and c2 and c3 and ("f" * 40) not in tm and z not in tm and len(tm) == 2
    return ok, dict(times=tm, pages=parsed, checks=checks)


def case_second_seal(w):
    tr = w.tree("main")["tree"]
    template = w.template("secondseal", w.remote("secondseal"))
    plans = w.plans("secondseal", tr, template)
    root = w.wd / "root_secondseal"
    campaign(tr, "run", "test", template, plans["K02"], root)  # K02 (6213) on its own branch: first seal
    root2 = w.wd / "root_secondseal_2"
    campaign(tr, "run", "test", template, plans["K02"], root2)  # the same instance, the same branch: a second seal
    st = status(root2, "NOT1_6213")
    sp = json.loads((root2 / "NOT1_6213" / "seal_push.json").read_text()) if (root2 / "NOT1_6213" / "seal_push.json").exists() else None
    log = (root2 / "NOT1_6213" / "sealpush.log").read_text()[-300:] if (root2 / "NOT1_6213" / "sealpush.log").exists() else ""
    checks = []
    f = root2 / "NOT1_6213" / "seal_push.json"
    c = check(checks, "the second seal refused", (sp or {}).get("why"), "a second seal is refused", f, f.exists())
    ok = c and status(root, "NOT1_6213").get("sealpush", {}).get("status") == "done" and \
        st.get("sealpush", {}).get("status") == "failed" and "N0" not in st
    return ok, dict(first=status(root, "NOT1_6213").get("sealpush", {}).get("status"),
                    second=st.get("sealpush", {}).get("status"), seal_push=sp, log=log, checks=checks)


def case_partial_guard(w):
    """Free space pushed below the test guard from outside, once N0 is done; then the filler removed and a rerun."""
    tr = w.tree("main")["tree"]
    free = shutil.disk_usage(w.wd).free / 1e9
    guard = round(free - 6, 1)                               # 6 GB above what the filler will leave
    rem = w.remote("partial")
    tt = w.template("partial", rem, disk_guard_gb=guard)
    pl = w.plans("partial", tr, tt)
    root = w.wd / "root_partial"
    filler = w.wd / "FILLER"
    p = run_bg(tr, "run", "test", tt, pl["K01"], root)
    # while N0 runs (about 90 s): C0 and the rounds then start below the guard (filling after N0 is too late: C0 and
    # the three rounds start within milliseconds of it)
    assert wait_for(lambda: status(root, "NOT1_6212").get("N0", {}).get("status") == "running", 3600, 1)
    now_free = shutil.disk_usage(w.wd).free / 1e9
    sh("fallocate", "-l", f"{int((now_free - guard + 1) * 1e9)}", filler)
    p.wait(timeout=3600)
    st1 = status(root, "NOT1_6212")
    res1 = result(root)
    ex = json.loads((root / "GUARD_EXEMPT.json").read_text()) if (root / "GUARD_EXEMPT.json").exists() else []
    filler.unlink()
    r = campaign(tr, "run", "test", tt, pl["K01"], root)
    st2 = status(root, "NOT1_6212")
    res2 = result(root)
    held1 = [(h["instance"], h["step"]) for h in res1["stopped_for_disk"]]
    checks = []
    c1 = check(checks, "C0 exempt from the guard", json.dumps(ex), '"step": "C0"', root / "GUARD_EXEMPT.json",
               (root / "GUARD_EXEMPT.json").exists())
    c2 = check(checks, "N1 held below the guard", json.dumps(res1["stopped_for_disk"]), '"step": "N1"', root, root.exists())
    ok = c1 and c2 and st1.get("C0", {}).get("status") == "done" and [e["step"] for e in ex] == ["C0"] and \
        ("NOT1_6212", "N1") in held1 and ("U_NOT1_6212", "U") in held1 and "N1" not in st1 and \
        all(st2.get(f"C{n}", {}).get("status") == "done" for n in range(4)) and res2["stopped_for_disk"] == [] and \
        res2["controls"]["U"][0].get("ok") is True
    return ok, dict(checks=checks, guard_gb=guard, held_first=held1, exempt=ex, steps_first={k: v["status"] for k, v in st1.items()},
                    steps_after_resume={k: v["status"] for k, v in st2.items()}, U_after=res2["controls"]["U"],
                    rc_resume=r.returncode), dict(root=root, remote=rem, template=tt, plans=pl)


def case_home(w):
    """A normal run of the home NOT1_6212 (K01), the original that the differing duplicate is judged against."""
    tr = w.tree("main")["tree"]
    rem = w.remote("home")
    tt = w.template("home", rem)
    pl = w.plans("home", tr, tt)
    root = w.wd / "root_home"
    r = campaign(tr, "run", "test", tt, pl["K01"], root)
    st = status(root, "NOT1_6212")
    res = result(root)
    checks = []
    c = check(checks, "every step done", json.dumps(sorted({v["status"] for v in st.values()})), '["done"]', root / "DONE",
              (root / "DONE").exists())
    ok = c and r.returncode == 0 and all(v["status"] == "done" for v in st.values()) and "C0" in st and \
        (root / "INSTANCES_DONE").exists()
    return ok, dict(steps={k: v["status"] for k, v in st.items()}, U=res["controls"]["U"], checks=checks), \
        dict(root=root, remote=rem)


def tamper_noise(t):
    tmpl = json.loads((HERE / "campaign_template.json").read_text())
    wt = Path(f"{t}.wt-{tmpl['noise_commit'][:8]}")
    f = wt / "research" / "layered-networks" / "config.json"
    c = json.loads(f.read_text())
    c["circuit"]["temperature"] = c["circuit"]["temperature"] + 1
    f.write_text(json.dumps(c, indent=2) + "\n")
    for k, v in (("user.name", "test"), ("user.email", "test@invalid")):
        sh("git", "-C", wt, "config", k, v)
    sh("git", "-C", wt, "commit", "-q", "-am", "stub: temperature + 1 (test)")
    return dict(noise_commit=sh("git", "-C", wt, "rev-parse", "HEAD").stdout.strip())


def case_differing_duplicate(w, home):
    info = w.tree("stubnoise", tamper_noise)
    tr = info["tree"]
    tt = w.template("dupdiff", home["remote"], noise_commit=info["noise_commit"])
    pl = w.plans("dupdiff", tr, tt)
    root = w.wd / "root_dupdiff"
    campaign(tr, "run", "test", tt, pl["K03"], root)
    res = result(root)
    an = w.wd / "analysis_dupdiff"
    a = sh(PY, "-B", HERE / "analysis.py", "test", an, home["root"], root, "times=bare")
    out = json.loads((an / "RESULTS.json").read_text()) if (an / "RESULTS.json").exists() else {}
    x = (out.get("controls") or {}).get("cross_machine_duplicates") or [{}]
    checks = []
    c = check(checks, "the duplicate judged not identical", json.dumps(dict(identical=x[0].get("identical"))),
              '"identical": false', an / "RESULTS.json", (an / "RESULTS.json").exists())
    ok = c and res["remote_duplicates"][0].get("ok") is True and x[0].get("identical") is False
    return ok, dict(checks=checks, duplicate=res["remote_duplicates"], analysis_rc=a.returncode, identical=x[0].get("identical"),
                    checker_last=(x[0].get("checker_lines") or [""])[-1], comparison=x[0].get("comparison"))


def case_analysis_refuses_test_root(w, root):
    """analysis.py of the dev tree: campaign mode is refused first by the tree's own pins (campaign.py, analysis.py
    and the template not pinned: the refusal of a TEST root is shown in analysis_forged_pins, in a pinned tree); an
    OUTDIR inside a root is refused."""
    an = w.wd / "analysis_campaign_on_test"
    checks, e = [], Path(root).exists()
    a = sh(PY, "-B", HERE / "analysis.py", "campaign", an, root, "times=bare")
    c1 = check(checks, "campaign mode in the unpinned dev tree", a.stderr, "campaign mode: not in FREEZE_PINS.json", root, e)
    inside = sh(PY, "-B", HERE / "analysis.py", "test", Path(root) / "analysis", root, "times=bare")
    c2 = check(checks, "OUTDIR inside the root", inside.stderr, "lies inside the root", root, e)
    ok = c1 and c2 and a.returncode != 0 and inside.returncode != 0
    return ok, dict(campaign_on_test=a.stderr.strip()[-200:], outdir_inside=inside.stderr.strip()[-200:], checks=checks)


# ------------------------------------------------------------------------------------- the audit's cases (D1–D3, A1–A5)

def tamper_pins(t):
    """A test commit regenerating FREEZE_PINS.json over this clone, so that every pin matches and campaign.py,
    analysis.py and campaign_template.json are pinned (as the next freeze will do)."""
    import hashlib
    f = t / "research" / "layered-networks" / "FREEZE_PINS.json"
    d = json.loads(f.read_text())
    must = ("research/layered-networks/campaign.py", "research/layered-networks/analysis.py",
            "research/layered-networks/campaign_template.json")
    d["groups"]["test: the consolidated driver, analysis and template"] = {
        m: hashlib.sha256((t / m).read_bytes()).hexdigest() for m in must}
    f.write_text(json.dumps(d, indent=1, sort_keys=True) + "\n")
    sh("git", "-C", t, "commit", "-q", "-am", "test: pins regenerated (test)")


def case_pins(w):
    """D1 and A5: campaign mode against FREEZE_PINS.json and a clean tree, through launch and analysis.py."""
    info = w.tree("pins", tamper_pins)
    tr = info["tree"]
    L = tr / "research" / "layered-networks"
    frozen = L / "campaign_template.json"
    pl = w.plans("pins", tr, frozen)
    out, checks = {}, []
    r = campaign(tr, "check", "campaign", frozen, pl["K02"])
    tc = json.loads(r.stdout or "{}")
    out["clean tree, every pin matching: check"] = dict(rc=r.returncode, ok=tc.get("ok"), pins=tc.get("pins"))
    pinned = L / "fit3.py"                                 # one pinned file changed by one byte, committed (tree clean)
    pinned.write_bytes(pinned.read_bytes() + b" ")
    sh("git", "-C", tr, "commit", "-q", "-am", "test: one byte (test)")
    e = pl["K02"].exists() and frozen.exists()
    r1 = campaign(tr, "launch", "campaign", frozen, pl["K02"], w.wd / "root_pins_byte")
    out["one pinned byte changed: launch"] = (r1.returncode, (r1.stdout + r1.stderr).strip()[-300:])
    c1 = check(checks, "one pinned byte changed: launch", r1.stderr,
               "pinned files differ from FREEZE_PINS.json: ['research/layered-networks/fit3.py']", pl["K02"], e)
    sh("git", "-C", tr, "reset", "-q", "--hard", "HEAD~1")
    (L / "stray.py").write_text("# untracked (test)\n")    # an untracked .py in the driver's tree
    r2 = campaign(tr, "launch", "campaign", frozen, pl["K02"], w.wd / "root_pins_untracked")
    out["untracked .py in the driver's tree: launch"] = (r2.returncode, (r2.stdout + r2.stderr).strip()[-300:])
    c2 = check(checks, "untracked .py in the driver's tree: launch", r2.stderr, "is not clean (a changed tracked file, "
               "or an untracked .py/.json)", pl["K02"], e)
    (L / "stray.py").unlink()
    kit = Path(f"{tr}.wt-{json.loads(frozen.read_text())['kit_commit'][:8]}")
    (kit / "stray.json").write_text("{}\n")                 # an untracked .json in the kit's tree
    r3 = campaign(tr, "launch", "campaign", frozen, pl["K02"], w.wd / "root_pins_kit")
    out["untracked .json in the kit tree: launch"] = (r3.returncode, (r3.stdout + r3.stderr).strip()[-300:])
    c3 = check(checks, "untracked .json in the kit tree: launch", r3.stderr, "no clean worktree at kit_commit", pl["K02"], e)
    (kit / "stray.json").unlink()
    out["checks"] = checks                 # analysis.py campaign in this tree: analysis_forged_pins, on a real root
    ok = r.returncode == 0 and tc.get("ok") is True and not tc["pins"]["mismatched"] and tc["pins"]["tree_clean"] and \
        not tc["pins"]["not_pinned"] and r1.returncode != 0 and c1 and r2.returncode != 0 and c2 and \
        r3.returncode != 0 and c3 and \
        not any((w.wd / x).exists() for x in ("root_pins_byte", "root_pins_untracked", "root_pins_kit"))
    return ok, out


def case_analysis_forged_pins(w, root):
    """analysis.py campaign in the pinned tree (tamper_pins), on real roots copied from the home run (TEST mode):
    - the refusals of A3 (times, thresholds, controls), of an untracked .py, and of the TEST root itself;
    - audit follow-up 1: a copy whose ENV.json is forged to this campaign.py, the frozen template and CAMPAIGN, but
      whose driver checked another FREEZE_PINS.json (the dev tree's) → refused for its pins;
    - the control: the same forged copy with TEMPLATE_CHECK.json's pins sha set to this tree's → NOT refused for its
      pins or as a root of another driver; it goes on, and is refused later for the ENV.json the forgery changed."""
    import hashlib
    info = w.tree("pins", tamper_pins)
    L = info["tree"] / "research" / "layered-networks"
    frozen = L / "campaign_template.json"
    checks, oks, out = [], [], {}

    def an(label, target, needle, *extra, absent=None):
        e = Path(target).exists()
        a = sh(PY, "-B", L / "analysis.py", "campaign", w.wd / f"an_forged_{len(checks)}", target, *extra)
        out[label] = (a.returncode, a.stderr.strip()[-300:])
        good = a.returncode != 0 and check(checks, label, a.stderr, needle, target, e)
        if absent:
            checks[-1]["must_not_contain"] = absent
            good = good and absent not in a.stderr
        oks.append(good)

    an("times=bare", root, "campaign mode: times must be github or lsremote:LOG, not 'bare'", "times=bare")
    an("thresholds=another file", root, "campaign mode reads the pinned thresholds.json only",
       f"thresholds={w.wd / 'DRAW.json'}")
    an("controls=another tree", root, "campaign mode: controls must be the noise tree at", f"controls={L}")
    an("the home run's TEST root itself", root, "roots not run by this campaign.py on the frozen template in campaign mode")
    (L / "stray.py").write_text("# untracked (test)\n")
    an("untracked .py in the analysis tree", root, "is not clean (a changed tracked file, or an untracked .py/.json)")
    (L / "stray.py").unlink()
    forged = w.wd / "root_home_forged_pins"
    shutil.rmtree(forged, ignore_errors=True)
    shutil.copytree(root, forged, symlinks=True)
    env = json.loads((forged / "ENV.json").read_text())
    env["campaign"] = dict(env["campaign"], driver_sha256=hashlib.sha256((L / "campaign.py").read_bytes()).hexdigest(),
                           template_sha256=hashlib.sha256(frozen.read_bytes()).hexdigest(), mode="CAMPAIGN")
    (forged / "ENV.json").write_text(json.dumps(env, indent=1, sort_keys=True) + "\n")
    an("a CAMPAIGN root whose driver checked another FREEZE_PINS.json", forged,
       "roots whose driver checked another FREEZE_PINS.json than this tree's")
    control = w.wd / "root_home_forged_control"
    shutil.rmtree(control, ignore_errors=True)
    shutil.copytree(forged, control, symlinks=True)
    tc = json.loads((control / "TEMPLATE_CHECK.json").read_text())
    tc["pins"]["pins_sha256"] = hashlib.sha256((L / "FREEZE_PINS.json").read_bytes()).hexdigest()
    (control / "TEMPLATE_CHECK.json").write_text(json.dumps(tc, indent=1, sort_keys=True) + "\n")
    an("control: the same forged root with this tree's pins", control, "mixed environments in one OUTROOT",
       absent="another FREEZE_PINS.json")
    oks[-1] = oks[-1] and "roots not run by this campaign.py" not in out["control: the same forged root with this tree's pins"][1]
    out["checks"] = checks
    return all(oks), out


def children_of(root):
    return [int(x) for x in sh("pgrep", "-f", f"stage_d6.py run .*{root}/NOT1_6213/D").stdout.split()]


def wait_done(tr, root):
    for _ in range(40):
        if campaign(tr, "wait", root, 580).returncode == 0:
            return True
    return False


def case_sigterm_driver_only(w):
    """D2: SIGTERM to the driver alone (its child left alone): the driver kills its children's groups, then a
    detached `resume` finds D running, records it interrupted and starts nothing after it."""
    tr = w.tree("main")["tree"]
    tt = w.template("sigterm", w.remote("sigterm"))
    pl = w.plans("sigterm", tr, tt)
    root = w.wd / "root_sigterm"
    p = run_bg(tr, "run", "test", tt, pl["K02"], root)
    assert wait_for(lambda: status(root, "NOT1_6213").get("D", {}).get("status") == "running", 1800), \
        Path(f"{root}.driver_bg.log").read_text()[-400:]
    time.sleep(5)
    kids = children_of(root)
    os.kill(p.pid, signal.SIGTERM)                       # the driver only
    p.wait(timeout=120)
    gone = wait_for(lambda: not children_of(root), 30, 1)
    sig = json.loads((root / "SIGNALS.json").read_text()) if (root / "SIGNALS.json").exists() else None
    r = campaign(tr, "resume", "test", tt, pl["K02"], root)
    done = r.returncode == 0 and wait_done(tr, root)
    st = status(root, "NOT1_6213")
    checks = []
    c1 = check(checks, "the driver logged the signal and killed its children", json.dumps(sig), '"signal": "SIGTERM"',
               root / "SIGNALS.json", (root / "SIGNALS.json").exists())
    c2 = check(checks, "the resume found D running", st.get("D", {}).get("why"), "found running at a resume", root, True)
    ok = c1 and c2 and bool(kids) and gone and sig[0]["killed_process_groups"] and \
        r.returncode == 0 and done and st["D"]["status"] == "interrupted" and "seal" not in st and (root / "DONE").exists()
    return ok, dict(checks=checks, children_before=kids, children_gone=gone, signals=sig, resume=(r.stdout + r.stderr).strip()[-300:],
                    steps={k: v["status"] for k, v in st.items()}, pids=(root / "DRIVER_PIDS.log").read_text()
                    if (root / "DRIVER_PIDS.log").exists() else None)


def case_sigkill_driver_only(w):
    """D2: SIGKILL to the driver alone: its child survives, and `run` and `resume` refuse while it runs. Once the
    child is gone, `run` records D interrupted and starts nothing after it."""
    tr = w.tree("main")["tree"]
    tt = w.template("sigkill", w.remote("sigkill"))
    pl = w.plans("sigkill", tr, tt)
    root = w.wd / "root_sigkill"
    p = run_bg(tr, "run", "test", tt, pl["K02"], root)
    assert wait_for(lambda: status(root, "NOT1_6213").get("D", {}).get("status") == "running", 1800), \
        Path(f"{root}.driver_bg.log").read_text()[-400:]
    time.sleep(5)
    os.kill(p.pid, signal.SIGKILL)                       # the driver only; it cannot clean up
    p.wait(timeout=60)
    kids = children_of(root)
    r1 = campaign(tr, "run", "test", tt, pl["K02"], root)
    r2 = campaign(tr, "resume", "test", tt, pl["K02"], root)
    kill_group(f"stage_d6.py run .*{root}/NOT1_6213/D")
    time.sleep(3)
    r3 = campaign(tr, "run", "test", tt, pl["K02"], root)
    st = status(root, "NOT1_6213")
    checks = []
    c1 = check(checks, "run while the orphan child runs", r1.stderr, "ngspice process(es) running", root, True)
    c2 = check(checks, "resume while the orphan child runs", r2.stderr, "ngspice process(es) running", root, True)
    c3 = check(checks, "the later run found D running", st.get("D", {}).get("why"), "found running at a resume", root, True)
    ok = c1 and c2 and c3 and bool(kids) and r1.returncode != 0 and r2.returncode != 0 \
        and r3.returncode == 0 and st["D"]["status"] == "interrupted" and "seal" not in st and (root / "DONE").exists()
    return ok, dict(checks=checks, children_after_kill=kids, run_while_child=r1.stderr.strip()[-200:],
                    resume_while_child=r2.stderr.strip()[-200:], steps={k: v["status"] for k, v in st.items()})


def tamper_k3(t):
    f = t / "research" / "layered-networks" / "indeck_noise4.py"
    s = f.read_text()
    a, b = "ok = r.returncode == 0 and bool(seen) and not bad", "sys.exit(0 if main(*sys.argv[1:]) else 1)"
    assert a in s and b in s
    s = s.replace(a, "ok = False   # STUB: K3_BUDGET not ok, exit 0 (test c)").replace(b, "main(*sys.argv[1:])\n    sys.exit(0)")
    f.write_text(s)
    sh("git", "-C", t, "commit", "-q", "-am", "stub: K3_BUDGET not ok with exit 0 (test)")


def case_k3_budget_stop(w):
    """D3: inverters done but inv/K3_BUDGET.json not ok (a stub tree): D is recorded refused, with the reason."""
    tr = w.tree("stubk3", tamper_k3)["tree"]
    tt = w.template("k3stop", w.remote("k3stop"))
    pl = w.plans("k3stop", tr, tt)
    root = w.wd / "root_k3stop"
    r = campaign(tr, "run", "test", tt, pl["K02"], root)
    st = status(root, "NOT1_6213")
    checks = []
    c = check(checks, "D refused for the K3 budget", st.get("D", {}).get("why"), "inv/K3_BUDGET.json is not ok",
              root / "NOT1_6213" / "inv" / "K3_BUDGET.json", (root / "NOT1_6213" / "inv" / "K3_BUDGET.json").exists())
    ok = c and r.returncode == 0 and st.get("inverters", {}).get("status") == "done" and \
        st.get("D", {}).get("status") == "refused" and "seal" not in st
    return ok, dict(steps={k: v["status"] for k, v in st.items()}, D=st.get("D"), checks=checks)


def case_analysis_tampered(w, home):
    """A1 and A2 on tampered copies of the home root (NOT1_6212, with room):
    - round 1 refuted, round 2 timed out (its comparison gone) → refuted at K3, not 'not completed';
    - D/prediction.json changed (room_K3 false) → the sealed prediction is the one read, and the instance is a seal
      defect, not counted."""
    out, oks, checks = {}, [], []
    for label in ("A1", "A2"):
        root = w.wd / f"root_tampered_{label}"
        if root.exists():
            shutil.rmtree(root)
        shutil.copytree(home["root"], root, symlinks=True)
        d = root / "NOT1_6212"
        if label == "A1":
            c = json.loads((d / "N1" / "comparison.json").read_text())
            c["verdict"] = "refuted"
            c["differences"] = (c.get("differences") or []) + [dict(what="word", note="tampered (test)")]
            (d / "N1" / "comparison.json").write_text(json.dumps(c, indent=1, sort_keys=True) + "\n")
            (d / "N2" / "comparison.json").unlink()
            st = json.loads((d / "status.json").read_text())
            st["steps"]["N2"].update(status="timeout", why="more than 7200 s (tampered, test)")
            st["steps"].pop("C2", None)
            (d / "status.json").write_text(json.dumps(st, indent=1, sort_keys=True) + "\n")
        else:
            p = json.loads((d / "D" / "prediction.json").read_text())
            p["room_K3"] = not p["room_K3"]
            (d / "D" / "prediction.json").write_text(json.dumps(p, indent=1, sort_keys=True) + "\n")
        an = w.wd / f"an_tampered_{label}"
        e = root.exists()
        a = sh(PY, "-B", HERE / "analysis.py", "test", an, root, "times=bare")
        res = json.loads((an / "RESULTS.json").read_text()) if (an / "RESULTS.json").exists() else {}
        row = next((r for r in res.get("instances", []) if r["instance"] == "NOT1_6212"), {})
        cnt = (res.get("counts") or {}).get("NOT1", {})
        if label == "A1":
            c = check(checks, "A1: K3 refuted beside a timed-out round", json.dumps(row.get("K3")),
                      '{"counted": true, "refuted": true}', root, e)
            ok = c and a.returncode == 0 and row.get("K3") == dict(counted=True, refuted=True) and \
                cnt["K3"]["refuted"]["list"] == ["NOT1_6212"] and res["groups"]["NOT1"]["K3"]["verdict"] == "refuted"
            out[label] = dict(rc=a.returncode, K3=row.get("K3"), counts_K3=cnt.get("K3"),
                              verdict=res.get("groups", {}).get("NOT1", {}).get("K3", {}).get("verdict"))
        else:
            ns = cnt.get("K3", {}).get("not_sealed", {}).get("list", [])
            c = check(checks, "A2: the changed D/prediction.json is a seal defect", (row.get("seal") or {}).get("regeneration_why"),
                      "D/prediction.json differs from its seal", root, e)
            ok = c and a.returncode == 0 and (row.get("stage_d") or {}).get("room_K3") is True and \
                (row.get("seal") or {}).get("regeneration_why", "").startswith("D/prediction.json differs") and \
                not (row.get("K0") or {}).get("counted") and not (row.get("K3") or {}).get("counted") and \
                [x["instance"] for x in ns] == ["NOT1_6212"] and "verdicts" in ns[0]
            out[label] = dict(rc=a.returncode, stage_d_room_K3=(row.get("stage_d") or {}).get("room_K3"),
                              seal=row.get("seal"), K0=row.get("K0"), K3=row.get("K3"), not_sealed_K3=ns)
        oks.append(ok)
    out["checks"] = checks
    return all(oks), out


def main(wd, *only):
    w = Work(wd)
    report = {}

    def run(name, f, *a):
        if only and name not in only:
            return None
        t0 = time.time()
        try:
            r = f(w, *a)
        except Exception as e:                            # a case that cannot run is a failed case
            r = (False, dict(error=repr(e)))
        ok, detail = r[0], r[1]
        report[name] = dict(ok=ok, seconds=round(time.time() - t0, 1), detail=detail)
        print(name, "PASS" if ok else "FAIL", round(time.time() - t0), "s", flush=True)
        (w.wd / "TEST_C.json").write_text(json.dumps(report, indent=1, sort_keys=True) + "\n")
        return r
    run("refusals", case_refusals)
    run("pins", case_pins)
    run("timeout", case_timeout)
    run("guard", case_guard)
    run("crash", case_crash)
    run("interrupt_and_resume", case_interrupt)
    run("kernel_mirror_disagreement", case_kernel)
    run("no_pushed_seal", case_no_pushed_seal)
    run("second_seal", case_second_seal)
    run("github_times", case_github_times)
    run("sigterm_driver_only", case_sigterm_driver_only)
    run("sigkill_driver_only", case_sigkill_driver_only)
    run("k3_budget_stop", case_k3_budget_stop)
    r = run("home_run", case_home)
    if r and len(r) > 2:
        run("differing_duplicate", case_differing_duplicate, r[2])
        run("analysis_refuses", case_analysis_refuses_test_root, r[2]["root"])
        run("analysis_tampered", case_analysis_tampered, r[2])
        run("analysis_forged_pins", case_analysis_forged_pins, r[2]["root"])
    run("partial_guard_and_resume", case_partial_guard)
    ok = all(v["ok"] for v in report.values())
    report["all_pass"] = ok
    (w.wd / "TEST_C.json").write_text(json.dumps(report, indent=1, sort_keys=True) + "\n")
    return ok


if __name__ == "__main__":
    sys.exit(0 if main(*sys.argv[1:]) else 1)
