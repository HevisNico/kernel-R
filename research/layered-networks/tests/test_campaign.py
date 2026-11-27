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
  against the home's seal. check_duplicate says it differs (analysis.py, test mode);
- duplicate after later seals (rehearsal 1's K09 scenario): the home pushes two more seals before the duplicate
  fetches; the duplicate records the seal's own introducing commit (and the tip read apart), check_duplicate says
  IDENTICAL; duplicate forged line: a forged line for the instance at the tip; the duplicate refuses, not completed;
- the analysis on copies of the home root (analysis.py test mode; LAYERED_TEST_ANALYSIS names another analysis.py,
  to record a case against an earlier commit): analysis_tampered (A1, A2 of 2026-11-26, consistent forgeries);
  analysis_d8_not_run (a planned instance never started), analysis_d9_copies (30 copies of one root),
  analysis_d10_manifest (one byte of a comparison, its manifest kept); analysis_hardening (the coordinator's selection
  of the audit's list, one check each).
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


def later_seals(remote, branch, lines, forged=None):
    """Push commits on top of `branch` of the bare `remote` (a plain fast-forward push each, as the home would): one
    per extra SEALS.txt line (another instance's seal), and, if `forged`, one that appends a forged line for an instance
    already sealed (its seal folder left as it is)."""
    with __import__("tempfile").TemporaryDirectory() as g:
        sh("git", "clone", "-q", "--branch", branch, str(remote), g)
        for k, v in (("user.name", "test"), ("user.email", "test@invalid")):
            sh("git", "-C", g, "config", k, v)
        for ln in list(lines) + ([forged] if forged else []):
            f = Path(g) / "SEALS.txt"
            f.write_text(f.read_text() + ln + "\n")
            sh("git", "-C", g, "commit", "-q", "-am", f"test: SEALS.txt line {ln.split()[0]}")
            assert sh("git", "-C", g, "push", "-q", "origin", f"HEAD:refs/heads/{branch}").returncode == 0
        return sh("git", "-C", g, "rev-parse", "HEAD").stdout.strip()


def home_seal_commit(home):
    """The home's own seal commit of NOT1_6212 (its SEAL_LOG.json), and its seal branch."""
    s = json.loads((Path(home["root"]) / "NOT1_6212" / "N0" / "SEAL_LOG.json").read_text())
    return s.get("commit"), s.get("branch")


def case_duplicate_after_later_seals(w, home):
    """The K09 scenario of rehearsal 1: the home seals NOT1_6212, then pushes TWO more seals before the duplicate
    fetches. The duplicate must name the seal's own (introducing) commit, not the tip it read, and check_duplicate
    must say IDENTICAL (analysis.py, test mode)."""
    rem = w.wd / "log_home_later.git"
    if rem.exists():
        shutil.rmtree(rem)
    shutil.copytree(home["remote"], rem, symlinks=True)
    own, branch = home_seal_commit(home)
    tip = later_seals(rem, branch, ["NOT1_9001 " + "1" * 64, "NOT1_9002 " + "2" * 64])
    tr = w.tree("main")["tree"]
    tt = w.template("dup_later", rem)
    pl = w.plans("dup_later", tr, tt)
    root = w.wd / "root_dup_later"
    campaign(tr, "run", "test", tt, pl["K03"], root)
    res = result(root) or {}
    d = root / "DUPX_NOT1_6212"
    chk = json.loads((d / "seal_check.json").read_text()) if (d / "seal_check.json").exists() else {}
    rec = json.loads((d / "N0" / "noisy_record.json").read_text()) if (d / "N0" / "noisy_record.json").exists() else {}
    an = w.wd / "analysis_dup_later"
    a = sh(PY, "-B", HERE / "analysis.py", "test", an, home["root"], root, "times=bare")
    out = json.loads((an / "RESULTS.json").read_text()) if (an / "RESULTS.json").exists() else {}
    x = ((out.get("controls") or {}).get("cross_machine_duplicates") or [{}])[0]
    checks = []
    c1 = check(checks, "the duplicate's seal_log commit is the home's own seal commit, not the tip read",
               json.dumps(dict(seal_log=chk.get("seal_log"), tip_read=chk.get("seal_log_tip_read"),
                               record=(rec.get("seal_log") or {}).get("commit"))),
               f'"record": "{own}"', d / "seal_check.json", True)
    c2 = check(checks, "check_duplicate: IDENTICAL", json.dumps((x.get("checker_lines") or [""])[-1]), "DUPLICATE IDENTICAL",
               an / "RESULTS.json", (an / "RESULTS.json").exists())
    ok = (c1 and c2 and own != tip and (chk.get("seal_log") or [None])[0] == own and chk.get("seal_log_tip_read") == tip
          and x.get("identical") is True and res.get("remote_duplicates", [{}])[0].get("ok") is True)
    return ok, dict(checks=checks, own_commit=own, tip_after_two_seals=tip, seal_check=chk, analysis_rc=a.returncode,
                    identical=x.get("identical"), checker_lines=x.get("checker_lines"))


def case_duplicate_forged_line(w, home):
    """The converse: a forged SEALS.txt line for NOT1_6212 (another sha256) appended at the tip of the home branch. Its
    introducing commit holds the original seal folder, which does not match the forged line: the duplicate refuses, is
    not completed, and runs no N0."""
    rem = w.wd / "log_home_forged.git"
    if rem.exists():
        shutil.rmtree(rem)
    shutil.copytree(home["remote"], rem, symlinks=True)
    own, branch = home_seal_commit(home)
    tip = later_seals(rem, branch, [], forged="NOT1_6212 " + "f" * 64)
    tr = w.tree("main")["tree"]
    tt = w.template("dup_forged", rem)
    pl = w.plans("dup_forged", tr, tt)
    root = w.wd / "root_dup_forged"
    campaign(tr, "run", "test", tt, pl["K03"], root)
    d = root / "DUPX_NOT1_6212"
    here = json.loads((d / "duplicate_here.json").read_text()) if (d / "duplicate_here.json").exists() else {}
    chk = json.loads((d / "seal_check.json").read_text()) if (d / "seal_check.json").exists() else {}
    checks = []
    c = check(checks, "refused, not completed, at the forged line's commit", json.dumps(here.get("why")),
              "refused, not completed", d / "duplicate_here.json", True)
    ok = (c and here.get("refused") is True and here.get("not_completed") is True and not (d / "N0" / "noisy_record.json").exists()
          and (chk.get("seal_log") or [None])[0] == tip)
    return ok, dict(checks=checks, own_commit=own, forged_tip=tip, duplicate_here=here, seal_check=chk)


def case_analysis_refuses_test_root(w, root):
    """analysis.py of the dev tree in campaign mode on a TEST root, made deterministic: the case first computes on its
    own whether every FREEZE_PINS.json entry matches this tree (the sha256 of each file). If one differs, it requires
    the pin refusal naming exactly the differing files it computed (the first five, sorted, as pins_refusal prints
    them). If all match but the tree is not clean (a changed tracked file, or an untracked .py/.json, computed here
    from git status), it requires the not-clean refusal naming the tree's HEAD. If all match and the tree is clean (a
    freeze candidate), it requires the next refusal, the roots not run by this campaign.py in campaign mode, naming
    root_1. It records the branch it took. An OUTDIR inside a root is refused."""
    import hashlib
    an = w.wd / "analysis_campaign_on_test"
    checks, e = [], Path(root).exists()
    top = HERE.parents[1]
    pins = json.loads((HERE / "FREEZE_PINS.json").read_text())
    differ = sorted(p for fs in pins["groups"].values() for p, h in fs.items()
                    if not (top / p).is_file() or hashlib.sha256((top / p).read_bytes()).hexdigest() != h)
    head = subprocess.run(["git", "-C", str(top), "rev-parse", "HEAD"], capture_output=True, text=True,
                          check=True).stdout.strip()
    st = subprocess.run(["git", "-C", str(top), "status", "--porcelain", "--untracked-files=all"], capture_output=True,
                        text=True, check=True).stdout.splitlines()
    dirty = [ln for ln in st if not ln.startswith("??") or ln.rstrip('"').endswith((".py", ".json"))]
    a = sh(PY, "-B", HERE / "analysis.py", "campaign", an, root, "times=github")
    if differ:
        branch = "pins differ"
        needle = f"refused: campaign mode: pinned files differ from FREEZE_PINS.json: {differ[:5]}"
        label = "campaign mode, a pin differs: the pin refusal names exactly the differing files"
    elif dirty:
        branch = "pins match, tree not clean"
        needle = f"refused: campaign mode: the tree at {head[:12]} is not clean"
        label = "campaign mode, every pin matches but the tree is not clean: the not-clean refusal"
    else:
        branch = "pins match"
        needle = "refused: roots not run by this campaign.py on the frozen template in campaign mode: ['root_1']"
        label = "campaign mode, every pin matches: the test root is refused as not run by this campaign.py"
    c1 = check(checks, label, a.stderr, needle, root, e)
    inside = sh(PY, "-B", HERE / "analysis.py", "test", Path(root) / "analysis", root, "times=bare")
    c2 = check(checks, "OUTDIR inside the root", inside.stderr, "lies inside the root", root, e)
    ok = c1 and c2 and a.returncode != 0 and inside.returncode != 0
    return ok, dict(branch=branch, pins_differing=differ, tree_head=head, tree_dirty=dirty, campaign_on_test=a.stderr.strip()[-200:],
                    outdir_inside=inside.stderr.strip()[-200:], checks=checks)

def tamper_pins(t):
    """A test commit regenerating FREEZE_PINS.json over this clone, so that every pin matches and campaign.py,
    analysis.py and campaign_template.json are pinned (as the next freeze will do)."""
    import hashlib
    f = t / "research" / "layered-networks" / "FREEZE_PINS.json"
    d = json.loads(f.read_text())
    for files in d["groups"].values():                  # every pin recomputed over this clone, as a freeze does
        for m in files:
            files[m] = hashlib.sha256((t / m).read_bytes()).hexdigest()
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

    an("times=bare", root, "campaign mode: times must be github, not 'bare'", "times=bare")
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
    an("control: the same forged root with this tree's pins", control, "campaign mode: draw=DRAW.json is required",
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
        if label == "A1":                    # a consistent forgery: the record, its comparison and the manifests
            rec = json.loads((d / "N1" / "noisy_record.json").read_text())
            k = sorted(rec["words"])[0]
            w0 = rec["words"][k]
            rec["words"][k] = ("s" if w0[0] == "F" else "F") + w0[1:]
            (d / "N1" / "noisy_record.json").write_text(json.dumps(rec, indent=1, default=str) + "\n")
            recompare(d, 1)
            (d / "N2" / "comparison.json").unlink()
            st = json.loads((d / "status.json").read_text())
            st["steps"]["N2"].update(status="timeout", why="more than 7200 s (tampered, test)")
            st["steps"].pop("C2", None)
            (d / "status.json").write_text(json.dumps(st, indent=1, sort_keys=True) + "\n")
            ri = json.loads((root / "RESULT_INSTANCES.json").read_text())
            for x in ri["instances"]:
                if f"{x['tag']}_{x['seed']}" == "NOT1_6212":
                    x["steps"] = {k_: v["status"] for k_, v in st["steps"].items()}
            (root / "RESULT_INSTANCES.json").write_text(json.dumps(ri, indent=1, sort_keys=True) + "\n")
        else:
            p = json.loads((d / "D" / "prediction.json").read_text())
            p["room_K3"] = not p["room_K3"]
            (d / "D" / "prediction.json").write_text(json.dumps(p, indent=1, sort_keys=True) + "\n")
        reseal(root)
        an = w.wd / f"an_tampered_{label}"
        e = root.exists()
        shutil.rmtree(an, ignore_errors=True)
        a = sh(PY, "-B", ANALYSIS, "test", an, root, "times=bare")
        res = json.loads((an / "RESULTS.json").read_text()) if (an / "RESULTS.json").exists() else {}
        row = next((r for r in res.get("instances", []) if r["instance"] == "NOT1_6212"), {})
        cnt = (res.get("counts") or {}).get("NOT1", {})
        if label == "A1":
            c = check(checks, "A1: K3 refuted beside a timed-out round", json.dumps(row.get("K3")),
                      '{"counted": true, "refuted": true}', root, e)
            ok = c and a.returncode == 0 and row.get("K3") == dict(counted=True, refuted=True) and \
                cnt["K3"]["refuted"]["list"] == ["NOT1_6212"] and res["groups"]["NOT1"]["K3"]["verdict"].startswith("refuted")
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


# ================================================================================================ the analysis, D8–D10
ANALYSIS = Path(os.environ.get("LAYERED_TEST_ANALYSIS", HERE / "analysis.py"))     # ef374ccd's, to record the failure


def reseal(root):
    """A forger's full rewrite: every manifest of the root recomputed over the files it lists (lines of files that no
    longer exist dropped), innermost first, so that only the analysis's own cross-checks can see the change."""
    import hashlib
    root = Path(root)
    ms = [p for p in root.rglob("SHA256SUMS*") if not any(x in ("lean_build", "kernel_build") for x in p.relative_to(root).parts)]
    ms.sort(key=lambda p: (-len(p.relative_to(root).parts), p.parent == root and p.name == "SHA256SUMS"))
    for m in ms:
        base = root if m.parent == root else m.parent
        lines = []
        for line in m.read_text().splitlines():
            h, n = line.split("  ", 1)
            if (base / n).is_file():
                lines.append(f"{hashlib.sha256((base / n).read_bytes()).hexdigest()}  {n}\n")
        m.write_text("".join(lines))


def copy_root(src, dst, hardlink=False):
    dst = Path(dst)
    if dst.exists():
        shutil.rmtree(dst)
    if hardlink:
        assert sh("cp", "-al", src, dst).returncode == 0
    else:
        shutil.copytree(src, dst, symlinks=True)
    return dst


def run_analysis(w, label, *a):
    an = w.wd / f"an_{label}"
    shutil.rmtree(an, ignore_errors=True)
    r = sh(PY, "-B", ANALYSIS, "test", an, *a)
    res = json.loads((an / "RESULTS.json").read_text()) if (an / "RESULTS.json").exists() else None
    return r, res


def recompare(d, n):
    """compare_d2 rerun on round n of instance folder d, as campaign.py runs it (C<n>)."""
    kind = "noiseless" if n == 0 else "noisy"
    r = sh(PY, "-B", HERE / "compare_d2.py", d / "seal", HERE / "specs" / "not1.json", d / f"N{n}" / "noisy_record.json",
           kind, d / f"N{n}" / "comparison.json")
    assert r.returncode == 0, r.stderr


def case_analysis_d8_not_run(w, home):
    """D8 (the owner's failure): a planned instance that never started. The home root's plan names NOT1 6212 and
    6213 (PLAN.json, PLAN_RESOLVED.json and PLAN_INPUT.json rewritten, the manifests resealed); only 6212 has a
    folder. Required: NOT1_6213 is a row, "not run" at K0 and K3, and the group has 2 instances."""
    root = copy_root(home["root"], w.wd / "root_d8")
    for f in ("PLAN.json", "PLAN_RESOLVED.json", "PLAN_INPUT.json"):
        p = json.loads((root / f).read_text())
        p["groups"]["NOT1"]["seeds"] = [6212, 6213]
        (root / f).write_text(json.dumps(p, indent=1, sort_keys=True) + "\n")
    reseal(root)
    a, res = run_analysis(w, "d8", root, "times=bare")
    checks, e = [], root.exists()
    cnt = ((res or {}).get("counts") or {}).get("NOT1", {})
    nr = lambda lv: [x["instance"] for x in (cnt.get(lv, {}).get("not_run") or {}).get("list", [])]
    c1 = check(checks, "K0: NOT1_6213 not run", json.dumps(nr("K0")), '["NOT1_6213"]', root, e)
    c2 = check(checks, "K3: NOT1_6213 not run", json.dumps(nr("K3")), '["NOT1_6213"]', root, e)
    ok = c1 and c2 and a.returncode == 0 and cnt["K0"]["instances"] == 2 and cnt["K3"]["instances"] == 2 and \
        cnt["K0"]["held"]["list"] == ["NOT1_6212"]
    return ok, dict(rc=a.returncode, stderr=a.stderr.strip()[-300:], counts_NOT1=cnt, checks=checks)


def case_analysis_d9_copies(w, home):
    """D9 (the owner's failure): 30 copies of one root give 30 counted instances and "established" at K0 (threshold
    30). Required: refused, for the home instance in more than one root; and one root given twice is refused."""
    roots = [copy_root(home["root"], w.wd / f"root_d9_{k:02d}", hardlink=True) for k in range(30)]
    checks, e = [], all(r.exists() for r in roots)
    a, res = run_analysis(w, "d9", *roots, "times=bare")
    c1 = check(checks, "30 copies refused", a.stderr, "the home instance NOT1 6212 is in more than one root", roots[1], e)
    b, _ = run_analysis(w, "d9_twice", roots[0], roots[0], "times=bare")
    c2 = check(checks, "one root twice refused", b.stderr, "a root is given more than once", roots[0], e)
    ok = c1 and c2 and a.returncode != 0 and b.returncode != 0 and res is None
    out = dict(rc=a.returncode, stderr=a.stderr.strip()[-300:], twice_rc=b.returncode, checks=checks)
    if res is not None:
        out["K0"] = res["groups"]["NOT1"]["K0"]
    for r in roots:
        shutil.rmtree(r, ignore_errors=True)
    return ok, out


def case_analysis_d10_manifest(w, home):
    """D10 (the owner's failure): one byte changed in NOT1_6212/N0/comparison.json, its manifest kept. Required:
    refused, naming the file."""
    root = copy_root(home["root"], w.wd / "root_d10")
    f = root / "NOT1_6212" / "N0" / "comparison.json"
    b = bytearray(f.read_bytes())
    i = b.index(b'"letters": ') + len(b'"letters": ')
    b[i] = ord("9") if b[i] != ord("9") else ord("8")
    f.write_bytes(bytes(b))
    a, res = run_analysis(w, "d10", root, "times=bare")
    checks, e = [], root.exists()
    c = check(checks, "the changed comparison refused, named", a.stderr,
              "NOT1_6212/N0/comparison.json: differs from NOT1_6212/SHA256SUMS", f, e)
    ok = c and a.returncode != 0 and res is None
    return ok, dict(rc=a.returncode, stderr=a.stderr.strip()[-400:], checks=checks,
                    K0=None if res is None else res["groups"]["NOT1"]["K0"])


def case_analysis_hardening(w, home):
    """The coordinator's selection of the audit's list (A1–A8, B1–B16), on copies of the home root, each check with its
    own message:
    - A4 an unknown key, a root path with '=', no root; A5 python -O; B10 a non-empty OUTDIR;
    - A6 an unknown verdict; B4 a comparison that compare_d2 does not reproduce; B8 a read file under no manifest line;
    (A2 and A1(ii) are in analysis_own_check, on a real driver run.) How each state arises in a real run: A4, A5, B10
    are command lines; A6, B4, B8, B16 are forgeries (a file changed and the manifests rewritten to match, or a draw
    file changed); B1/B2 a seal folder changed after sealing; B9 a driver stopped before its end (DONE not written);
    the stopped machine, a driver killed during N2 after a refuting N1 (here the refuting N1 is made by changing the
    record and rerunning compare_d2 as C1 would, and the end-of-run files are removed as a killed driver never writes
    them);
    - B1/B2 an extra file in the seal folder: a seal defect (held → not sealed);
    - B9 a root without DONE: analysed, "root not finished" at the top;
    - A7 the expected U control, present and passed;
    - B16/D8, the owner's full recomputation (test mode, offline announce): one seed changed with the signature kept,
      the round off by one (the announce 3 s later), one signature byte changed: each refuses; a valid draw (quicknet
      round 1000000, its signature verified, its announce 600 s before) goes on and refuses the root's plan as none of
      the expected plans;
    - the owner's rule on an incomplete machine: stopped after a differing N1 (no final manifest), NOT1_6212 counts
      refuted at K3, flagged manifest not final; K0 is not completed; the root is listed not finished."""
    out, checks, oks = {}, [], []
    base = home["root"]

    def refused(label, needle, *a, env=None, target=None):
        an = w.wd / f"an_h_{len(checks)}"
        shutil.rmtree(an, ignore_errors=True)
        r = sh(PY, *([] if env is None else env), "-B", ANALYSIS, *a) if a and a[0] in ("test", "campaign") else \
            sh(PY, *([] if env is None else env), "-B", ANALYSIS, "test", an, *a)
        out[label] = (r.returncode, r.stderr.strip()[-300:])
        t = target or base
        oks.append(r.returncode != 0 and check(checks, label, r.stderr, needle, t, Path(t).exists()))

    refused("A4: unknown key", "unknown argument 'colour=red'", base, "times=bare", "colour=red")
    eq = copy_root(base, w.wd / "root_h=eq", hardlink=True)
    refused("A4: a root path with '='", "unknown argument", eq, "times=bare", target=eq)
    refused("A4: no root", "refused: no root", "times=bare")
    refused("A5: python -O", "Python runs with -O", base, "times=bare", env=["-O"])
    full = w.wd / "an_h_full"
    full.mkdir(exist_ok=True)
    (full / "x").write_text("x\n")
    refused("B10: a non-empty OUTDIR", "exists and is not an empty folder", "test", full, base, "times=bare")

    r6 = copy_root(base, w.wd / "root_h_a6")
    c = json.loads((r6 / "NOT1_6212" / "N0" / "comparison.json").read_text())
    c["verdict"] = "agrees mostly"
    (r6 / "NOT1_6212" / "N0" / "comparison.json").write_text(json.dumps(c, indent=1, sort_keys=True) + "\n")
    reseal(r6)
    refused("A6: an unknown verdict", "unknown verdict 'agrees mostly'", r6, "times=bare", target=r6)

    r4 = copy_root(base, w.wd / "root_h_b4")
    c = json.loads((r4 / "NOT1_6212" / "N1" / "comparison.json").read_text())
    c["verdict"] = "refuted"
    (r4 / "NOT1_6212" / "N1" / "comparison.json").write_text(json.dumps(c, indent=1, sort_keys=True) + "\n")
    reseal(r4)
    refused("B4: a comparison compare_d2 does not reproduce", "NOT1_6212/N1/comparison.json is not what the pinned "
            "compare_d2 computes", r4, "times=bare", target=r4)

    r8 = copy_root(base, w.wd / "root_h_b8")
    m = r8 / "NOT1_6212" / "SHA256SUMS"
    m.write_text("".join(x + "\n" for x in m.read_text().splitlines() if not x.endswith("  D/record.json")))
    reseal(r8)
    refused("B8: a read file under no manifest line", "NOT1_6212/D/record.json is read but is under no verified "
            "manifest line", r8, "times=bare", target=r8)

    rb = copy_root(base, w.wd / "root_h_b2")
    (rb / "NOT1_6212" / "seal" / "NOT1_6212.copy.json").write_bytes((rb / "NOT1_6212" / "seal" / "NOT1_6212.json").read_bytes())
    a, res = run_analysis(w, "h_b2", rb, "times=bare")
    row = next((x for x in (res or {}).get("instances", []) if x["instance"] == "NOT1_6212"), {})
    oks.append(a.returncode == 0 and check(checks, "B1/B2: an extra file in the seal folder is a seal defect",
                                           (row.get("seal") or {}).get("regeneration_why"), "not exactly MANIFEST.json",
                                           rb, rb.exists()) and (row.get("K0") or {}).get("not_sealed") is True)
    out["B2"] = dict(rc=a.returncode, stderr=a.stderr.strip()[-300:], seal=row.get("seal"), K0=row.get("K0"))

    r9 = copy_root(base, w.wd / "root_h_b9")
    (r9 / "DONE").unlink()
    a, res = run_analysis(w, "h_b9", r9, "times=bare")
    oks.append(a.returncode == 0 and check(checks, "B9: a root without DONE is analysed, not finished",
                                           json.dumps((res or {}).get("NOTICE")), "root not finished: machine_1", r9, r9.exists())
               and res["groups"]["NOT1"]["K0"]["counted"] == 1)
    out["B9"] = dict(rc=a.returncode, notice=(res or {}).get("NOTICE"), stderr=a.stderr.strip()[-300:])

    a, res = run_analysis(w, "h_a7", base, "times=bare")
    s = ((res or {}).get("expected_controls") or {}).get("summary", {}).get("U")
    oks.append(a.returncode == 0 and check(checks, "A7: the expected U, present and passed", json.dumps(s, sort_keys=True),
                                           '"expected": 1, "failed": 0, "not_judged": 0, "passed": 1, "present": 1', base,
                                           Path(base).exists()))
    out["A7"] = s

    sys.path.insert(0, str(HERE))
    import beacon_chain
    import beacon_verify
    import draw_seeds
    import hashlib
    ex_f = HERE / "EXCLUDED.json"
    ex = json.loads(ex_f.read_text())
    n = dict(NOT1=2, ANDOR3=1, XOR3=1)

    def make_draw(label, rnd=1000000, shift_s=0, seed_change=False, sig_change=False, pad=False, float_round=False,
                  ex_file=None):
        exf = ex_file or ex_f
        br = dict(round=1000000, randomness="b22aad4794f7451896f7a371aa46106fd84d919f3f569acd5b2fddf1d1440af3",
                  signature="83ad29e4c409f9470fc2ef02f90214df49e02b441a1a241a82d622d9f608ef98fd8b11a029f1bee9d9e83b45088"
                            "abe72")
        t0 = beacon_verify.round_time(beacon_chain.QUICKNET, 1000000) - beacon_verify.DELAY_S + shift_s
        import datetime
        push = datetime.datetime.fromtimestamp(t0, datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
        ann = w.wd / f"ANNOUNCE_{label}.txt"
        ann.write_text(f"format layered-draw-announce/1\nmode test\nexcluded_sha256 {hashlib.sha256(exf.read_bytes()).hexdigest()}\n"
                       f"sizes NOT1={n['NOT1']} ANDOR3={n['ANDOR3']} XOR3={n['XOR3']}\n")
        if sig_change:                      # a changed signature, its randomness and the draw made consistent with it
            br["signature"] = br["signature"][:-2] + ("00" if br["signature"][-2:] != "00" else "11")
            br["randomness"] = hashlib.sha256(bytes.fromhex(br["signature"])).hexdigest()
        if pad:                             # zero bytes in front: the same point, another sha256 (the audit's X1)
            br["signature"] = "00" + br["signature"]
            br["randomness"] = hashlib.sha256(bytes.fromhex(br["signature"])).hexdigest()
        d = draw_seeds.draw(br["randomness"], rnd, ex, dict(n))
        if float_round:
            br["round"] = float(br["round"])
        if seed_change:
            d["groups"]["NOT1"][0] += 1
        f = w.wd / f"DRAW_{label}.json"
        f.write_bytes(draw_seeds.canon(dict(d, beacon_round=br, announce=dict(branch="test", commit="0" * 40, push_utc=push))))
        return [f"draw={f}", f"excluded={exf}", f"announce={ann}"]

    refused("B16: one seed changed, the signature kept", "DRAW.json is not draw_seeds.draw of its beacon and round",
            base, "times=bare", *make_draw("seed", seed_change=True))
    refused("B16: the round off by one (the announce pushed 3 s later)", "is not the round the announce's push time "
            "fixes", base, "times=bare", *make_draw("round", shift_s=3))
    refused("B16: one changed signature byte", "the beacon round does not verify", base, "times=bare",
            *make_draw("sig", sig_change=True))
    refused("B16/D8: a verified draw, the root's plan is none of the expected plans", "PLAN.json is none of the "
            "expected plans of the draw", base, "times=bare", *make_draw("good"))
    refused("X1: a zero-padded signature (it would verify)", "exactly 48 bytes", base, "times=bare",
            *make_draw("pad", pad=True))
    refused("N6: a round written 1000000.0", "is not an integer", base, "times=bare", *make_draw("float", float_round=True))
    wide = dict(ex)
    wide["seeds"] = sorted(set(ex["seeds"]) | set(range(10000, 40000)))
    wide["count"], wide["seeds_sha256"] = len(wide["seeds"]), hashlib.sha256(draw_seeds.canon(wide["seeds"])).hexdigest()
    wf = w.wd / "EXCLUDED_wide.json"
    wf.write_bytes(draw_seeds.canon(wide))
    refused("N5: an exclusion list rejecting more than 20 % of the range", "of the draw range, more than 20%", base,
            "times=bare", *make_draw("wide", ex_file=wf), target=wf)

    # the owner's rule: the campaign's list must hold the rehearsal's seeds and their noise seeds. Two published
    # quicknet rounds stand in: 20000000 for the rehearsal (6/6/6 over the freeze's list), 34278954 for the campaign
    # (the stand-in sizes, over list E); each announce 600 s before its round, as GitHub would have recorded it.
    import datetime

    def stand_in(label, br, mode, sizes, exf):
        t0 = beacon_verify.round_time(beacon_chain.QUICKNET, br["round"]) - beacon_verify.DELAY_S
        push = datetime.datetime.fromtimestamp(t0, datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
        ann = w.wd / f"ANNOUNCE_{label}.txt"
        ann.write_text(f"format layered-draw-announce/1\nmode {mode}\nexcluded_sha256 "
                       f"{hashlib.sha256(exf.read_bytes()).hexdigest()}\nsizes NOT1={sizes['NOT1']} ANDOR3={sizes['ANDOR3']} "
                       f"XOR3={sizes['XOR3']}\n")
        d = draw_seeds.draw(br["randomness"], br["round"], json.loads(exf.read_text()), dict(sizes))
        f = w.wd / f"DRAW_{label}.json"
        f.write_bytes(draw_seeds.canon(dict(d, beacon_round=br, announce=dict(
            branch="evidence/combined-rehearsal-draw" if mode == "rehearsal" else "test", commit="0" * 40, push_utc=push))))
        return d, f, ann
    rbr = dict(round=20000000, randomness="f39c98df5525968e6622e0c63edb3d1f9c5607cf780db78abdded36e4b3dba95",
               signature="96892582a33552a7b67ba44ef09c3ccd535bbebe760c93ecf45be8958d0c0f06390c6d19d7bf492eb806af7eef6b125c")
    cbr = dict(round=34278954, randomness="ca4a4015bcf54c6951e39ee81c085a65742d5794a66a9dceccb400d8cd97764e",
               signature="8fe9e583f82cdb77b61bf625b8e8f51782fbb4da2776f56455dc227b0e46e857fb6354a12b554bd530f8c8a5285f126d")
    rd, rf, ra = stand_in("rehearsal", rbr, "rehearsal", dict(NOT1=6, ANDOR3=6, XOR3=6), ex_f)
    rseeds = sorted(s for v in rd["groups"].values() for s in v)
    full = sorted(set(ex["seeds"]) | set(rseeds) | {10 * s + j for s in rseeds for j in range(4)})

    def listed(label, seeds):
        x = dict(ex, seeds=seeds, count=len(seeds), seeds_sha256=hashlib.sha256(draw_seeds.canon(seeds)).hexdigest())
        f = w.wd / f"EXCLUDED_{label}.json"
        f.write_bytes(draw_seeds.canon(x))
        return f
    reh = [f"rehearsal_draw={rf}", f"rehearsal_excluded={ex_f}", f"rehearsal_announce={ra}"]
    for label, seeds, needle in (
            ("a rehearsal seed missing", [s for s in full if s != rseeds[0]], f"lacks rehearsal2 seeds [{rseeds[0]}]"),
            ("a rehearsal noise seed missing", [s for s in full if s != 10 * rseeds[1] + 2],
             f"noise seeds [{10 * rseeds[1] + 2}]"),
            ("the full list: accepted (refused later, at the root's plan)", full, "PLAN.json is none of the expected plans")):
        exf = listed(label.split()[1] + str(len(seeds)), seeds)
        cd, cf, ca = stand_in("campaign" + str(len(seeds)), cbr, "test", n, exf)
        refused(f"owner: rehearsal seeds, {label}", needle, base, "times=bare", f"draw={cf}", f"excluded={exf}",
                f"announce={ca}", *reh, target=cf)
    out["rehearsal_seeds"] = rseeds
    for label, f in (("upper-case beacon", lambda d: dict(d, beacon=d["beacon"].upper())),
                     ("upper-case randomness", lambda d: dict(d, beacon_round=dict(d["beacon_round"], randomness=d["beacon_round"]["randomness"].upper()))),
                     ("upper-case signature", lambda d: dict(d, beacon_round=dict(d["beacon_round"], signature=d["beacon_round"]["signature"].upper())))):
        args = make_draw("w" + label[:5])
        fd = Path(args[0].split("=", 1)[1])
        fd.write_bytes(draw_seeds.canon(f(json.loads(fd.read_text()))))
        refused(f"owner: one value, one writing ({label})", "not written in canonical form" if "signature" in label
                else "another writing of the value is refused", base, "times=bare", *args, target=fd)

    # the owner's rule: a machine stopped after a differing N1 keeps that refutation (manifest not final)
    rp = copy_root(base, w.wd / "root_h_partial")
    d = rp / "NOT1_6212"
    for f in ("SHA256SUMS", "SHA256SUMS.instances", "RESULT.json", "RESULT_INSTANCES.json", "DONE", "INSTANCES_DONE",
              "INVENTORY_END"):
        (rp / f).unlink(missing_ok=True)
    (d / "SHA256SUMS").unlink()
    for x in ("N2", "N3"):
        shutil.rmtree(d / x)
    rec = json.loads((d / "N1" / "noisy_record.json").read_text())
    k = sorted(rec["words"])[0]
    rec["words"][k] = ("s" if rec["words"][k][0] == "F" else "F") + rec["words"][k][1:]
    (d / "N1" / "noisy_record.json").write_text(json.dumps(rec, indent=1, default=str) + "\n")
    recompare(d, 1)
    st = json.loads((d / "status.json").read_text())
    for x in ("C2", "N3", "C3"):
        st["steps"].pop(x, None)
    st["steps"]["N2"] = dict(status="running", started=st["steps"]["N2"].get("started"))
    st["steps"]["N1"]["outputs"]["N1/noisy_record.json"] = hashlib.sha256((d / "N1" / "noisy_record.json").read_bytes()).hexdigest()
    st["steps"]["C1"]["outputs"]["N1/comparison.json"] = hashlib.sha256((d / "N1" / "comparison.json").read_bytes()).hexdigest()
    (d / "status.json").write_text(json.dumps(st, indent=1, sort_keys=True) + "\n")
    a, res = run_analysis(w, "h_partial", rp, "times=bare")
    row = next((x for x in (res or {}).get("instances", []) if x["instance"] == "NOT1_6212"), {})
    cnt = ((res or {}).get("counts") or {}).get("NOT1", {})
    oks.append(a.returncode == 0 and check(checks, "owner: stopped after a differing N1, refuted (manifest not final)",
                                           json.dumps(row.get("K3"), sort_keys=True),
                                           '"counted": true, "manifest_not_final": true, "refuted": true', rp, rp.exists())
               and cnt["K3"]["refuted"]["list"] == ["NOT1_6212"]
               and [x["instance"] for x in cnt["K0"]["not_completed"]["list"]] == ["NOT1_6212"]
               and any("root not finished: machine_1" in x for x in res["NOTICE"]))
    out["partial"] = dict(rc=a.returncode, stderr=a.stderr.strip()[-300:], K0=row.get("K0"), K3=row.get("K3"),
                          notice=(res or {}).get("NOTICE"), counts_K0_not_completed=cnt.get("K0", {}).get("not_completed"))
    out["checks"] = checks
    return all(oks), out


def tamper_own_check(t):
    """A stub noise tree for analysis_own_check: controls4.py raises inside its try, after the lessons, at round 2,
    an AssertionError for NOT1 6212 (a run's own check) and session.py's simulator-end RuntimeError for NOT1 6213.
    controls4 then records status "failed: ..." in N2/noisy_record.json and exits 1, and campaign.py marks N2
    "failed" and never runs C2: the driver's real state for both."""
    tmpl = json.loads((HERE / "campaign_template.json").read_text())
    wt = Path(f"{t}.wt-{tmpl['noise_commit'][:8]}")
    f = wt / "research" / "layered-networks" / "controls4.py"
    src = f.read_text()
    old = "        lessons, words, tests = noise2.train_and_test(net, s, cfg, log)\n"
    assert src.count(old) == 1
    src = src.replace(old, old + "        if rnd == 2 and int(seed) == 6212:\n"
                      "            raise AssertionError(\"stub: the run's own check (test)\")\n"
                      "        if rnd == 2 and int(seed) == 6213:\n"
                      "            raise RuntimeError(\"the simulator ended during: stub (test)\")\n")
    f.write_text(src)
    for k, v in (("user.name", "test"), ("user.email", "test@invalid")):
        sh("git", "-C", wt, "config", k, v)
    sh("git", "-C", wt, "commit", "-q", "-am", "stub: round 2 stopped by its own check, or by a simulator end (test)")
    return dict(noise_commit=sh("git", "-C", wt, "rev-parse", "HEAD").stdout.strip())


def case_analysis_own_check(w):
    """A2 and A1(ii) on a real driver run (the audit's defect 1): campaign.py run, test mode, on a stub noise tree
    (tamper_own_check), one machine holding NOT1 6212 and 6213 (plan K01 with 6213 added to its seeds, an input).
    Round 2 of 6212 is stopped by its own check and round 2 of 6213 by a simulator end; neither has a comparison.json
    (C2 never runs). Required, from analysis.py on that root: 6212 refuted at K3 in its own row, listed with its full
    status; 6213 not completed at K3; both held at K0. Then A1(ii): the same root with 6212's D/prediction.json changed
    (a seal defect, as when the file changes after sealing; the manifests rewritten to match) keeps 6212 refuted,
    flagged seal_defect, and its K0 agreement no longer counts."""
    info = w.tree("ownchk", tamper_own_check)
    tr = info["tree"]
    rem = w.remote("ownchk")
    tt = w.template("ownchk", rem, noise_commit=info["noise_commit"])
    pl = w.plans("ownchk", tr, tt)
    p = json.loads(pl["K01"].read_text())
    p["groups"]["NOT1"]["seeds"] = [6212, 6213]
    plan = w.wd / "PLAN_ownchk.json"
    plan.write_text(json.dumps(p, indent=1, sort_keys=True) + "\n")
    root = w.wd / "root_ownchk"
    r = campaign(tr, "run", "test", tt, plan, root)
    checks, out = [], dict(run_rc=r.returncode)
    st = {i: status(root, i) for i in ("NOT1_6212", "NOT1_6213")}
    out["steps"] = {i: {k: v["status"] for k, v in s.items()} for i, s in st.items()}
    real = all(s.get("N2", {}).get("status") == "failed" and "C2" not in s and
               not (root / i / "N2" / "comparison.json").exists() for i, s in st.items())
    a, res = run_analysis(w, "ownchk", root, "times=bare")
    cnt = ((res or {}).get("counts") or {}).get("NOT1", {})
    stopped = (res or {}).get("stopped_by_own_check") or []
    c1 = check(checks, "6212 refuted at K3, stopped by its own check, with its status", json.dumps(
        (cnt.get("K3", {}).get("refuted_stopped_by_own_check") or {}).get("list")),
        '[{"instance": "NOT1_6212", "stopped_by_own_check": [{"round": "C2", "status": "failed: stub: the run\'s own check '
        '(test)"}]}]', root, root.exists())
    c2 = check(checks, "6212 listed with its full status", json.dumps(stopped),
               "failed: stub: the run's own check (test)", root, root.exists())
    c3 = check(checks, "6213, a simulator end: not completed at K3", json.dumps(
        [x["instance"] for x in (cnt.get("K3", {}).get("not_completed") or {}).get("list", [])]), '["NOT1_6213"]', root,
        root.exists())
    ok = real and r.returncode == 0 and a.returncode == 0 and c1 and c2 and c3 and \
        sorted(cnt["K0"]["held"]["list"]) == ["NOT1_6212", "NOT1_6213"] and \
        [(x["instance"], x["round"]) for x in stopped] == [("NOT1_6212", "C2")]
    out.update(analysis_rc=a.returncode, stderr=a.stderr.strip()[-300:], counts=cnt, stopped=stopped)
    r1 = copy_root(root, w.wd / "root_ownchk_a1")
    d = r1 / "NOT1_6212"
    pr = json.loads((d / "D" / "prediction.json").read_text())
    pr["env_note"] = "changed after sealing (test)"
    (d / "D" / "prediction.json").write_text(json.dumps(pr, indent=1, sort_keys=True) + "\n")
    reseal(r1)
    a, res = run_analysis(w, "ownchk_a1", r1, "times=bare")
    row = next((x for x in (res or {}).get("instances", []) if x["instance"] == "NOT1_6212"), {})
    c4 = check(checks, "A1(ii): refuted with a defective seal, flagged", json.dumps(row.get("K3"), sort_keys=True),
               '"seal_defect": true', r1, r1.exists())
    ok = ok and a.returncode == 0 and c4 and row["K3"].get("refuted") is True and (row.get("K0") or {}).get("not_sealed") is True
    out.update(A1ii=dict(rc=a.returncode, K0=row.get("K0"), K3=row.get("K3")), checks=checks, fixture_is_the_driver_state=real)
    return ok, out


def case_analysis_announce(w):
    """The audit's defect 2 on recorded activity items: analysis.announce_time. The items of a clean announce branch
    are GitHub's own (evidence/devtest-seals2-K05, 27 Nov 2026: its branch_creation and a later push), as a real
    branch's activity reads. Required: the clean branch gives its creation's time for the commit it created; with a
    branch_deletion and a second branch_creation appended (the announce deleted and pushed again), and with a
    force_push appended, it refuses; a commit that is not the creation's `after` refuses."""
    import importlib.util
    spec = importlib.util.spec_from_file_location("analysis_t", HERE / "analysis.py")
    A = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(A)
    z, c0, c1 = "0" * 40, "5226d975283f5a905ba54abea8f8570685eef388", "80f2c0f5b46ce875cbb52ec4020a2e54ed0d4384"
    ref = "refs/heads/evidence/devtest-seals2-K05"
    clean = [dict(activity_type="push", before=c0, after=c1, timestamp="2026-11-26T22:27:29Z", ref=ref),
             dict(activity_type="branch_creation", before=z, after=c0, timestamp="2026-11-26T22:25:58Z", ref=ref)]
    redone = clean + [dict(activity_type="branch_deletion", before=c1, after=z, timestamp="2026-11-26T23:00:00Z", ref=ref),
                      dict(activity_type="branch_creation", before=z, after="e" * 40, timestamp="2026-11-26T23:05:00Z", ref=ref)]
    forced = clean + [dict(activity_type="force_push", before=c1, after="f" * 40, timestamp="2026-11-26T23:00:00Z", ref=ref)]
    checks, out = [], {}

    def run(label, items, commit):
        try:
            return "ok " + A.announce_time(items, commit, "evidence/combined-draw")
        except SystemExit as e:
            return str(e)
    out["clean"] = run("clean", clean, c0)
    out["redone"] = run("redone", redone, "e" * 40)
    out["forced"] = run("forced", forced, c0)
    out["not_the_creation"] = run("other", clean, c1)
    e = (HERE / "analysis.py").exists()
    ok = all([check(checks, "a clean creation gives its time", out["clean"], "ok 2026-11-26T22:25:58Z", HERE / "analysis.py", e),
              check(checks, "deleted and created again: refused", out["redone"], "was rewritten or deleted (branch_deletion",
                    HERE / "analysis.py", e),
              check(checks, "a force push: refused", out["forced"], "was rewritten or deleted (force_push", HERE / "analysis.py", e),
              check(checks, "not the creation's commit: refused", out["not_the_creation"],
                    "is not the branch_creation that pushed the announce commit", HERE / "analysis.py", e)])
    out["checks"] = checks
    return ok, out


def case_draw_canonical(w):
    """The owner's draw defect: one signed drand value must give one list of seeds. On draw_seeds.draw, with the
    published quicknet round 1000000 (the offline stand-in) and the pinned EXCLUDED.json:
    - the lowercase value gives exactly the seeds draw_seeds.py gave at ef374ccd (the old file, from git), at the
      stand-in sizes, at DRAW_SIZES and at DRAW_SIZES_REHEARSAL;
    - the same value as its 32 bytes gives identical seeds; written in upper case, mixed case, with spaces, or with a
      0x prefix, it is refused (ValueError), never drawn with other seeds; a round given as a string is refused;
    - every permutation of the sizes dict gives byte-identical draws;
    - the evidence for the fixed order: a value is found for which the OLD draw gives different seeds for two orders
      of the same sizes (the groups collide), and the new draw gives one list for both."""
    import importlib.util
    import itertools
    sys.path.insert(0, str(HERE))
    import draw_seeds as D
    old_src = sh("git", "-C", HERE, "show", "ef374ccd:research/layered-networks/draw_seeds.py").stdout
    of = w.wd / "draw_seeds_ef374ccd.py"
    of.write_text(old_src)
    spec = importlib.util.spec_from_file_location("draw_seeds_old", of)
    O = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(O)
    ex = json.loads((HERE / "EXCLUDED.json").read_text())
    v = "b22aad4794f7451896f7a371aa46106fd84d919f3f569acd5b2fddf1d1440af3"
    sizes = dict(standin=dict(NOT1=2, ANDOR3=1, XOR3=1), campaign=dict(NOT1=60, ANDOR3=32, XOR3=37),
                 rehearsal=dict(NOT1=6, ANDOR3=6, XOR3=6))
    checks, out = [], {}
    same_as_before = {k: D.draw(v, 1000000, ex, n)["groups"] == O.draw(v, 1000000, ex, n)["groups"] for k, n in sizes.items()}
    out["lowercase_same_as_ef374ccd"] = same_as_before
    out["bytes_same"] = D.draw(bytes.fromhex(v), 1000000, ex, sizes["campaign"])["groups"] == D.draw(v, 1000000, ex, sizes["campaign"])["groups"]
    writings = dict(upper=v.upper(), mixed="".join(c.upper() if i % 2 else c for i, c in enumerate(v)),
                    spaced=" ".join(v[i:i + 2] for i in range(0, 64, 2)), prefixed="0x" + v)
    refused = {}
    for k, x in writings.items():
        try:
            D.draw(x, 1000000, ex, sizes["standin"])
            refused[k] = False
        except ValueError:
            refused[k] = True
    try:
        D.draw(v, "1000000", ex, sizes["standin"])
        refused["round_as_string"] = False
    except ValueError:
        refused["round_as_string"] = True
    out["other_writings_refused"] = refused
    perms = {}
    for k, n in sizes.items():
        outs = {D.canon(D.draw(v, 1000000, ex, dict(p))) for p in itertools.permutations(n.items())}
        perms[k] = len(outs) == 1
    out["permutations_identical"] = perms
    found = None
    for i in range(400):
        x = hashlib_sha(f"order evidence {i}")
        n1 = dict(NOT1=60, ANDOR3=32, XOR3=37)
        n2 = dict(XOR3=37, ANDOR3=32, NOT1=60)
        if O.draw(x, 1000000, ex, n1)["groups"] != O.draw(x, 1000000, ex, n2)["groups"]:
            found = dict(value=x, old_differs=True,
                         new_identical=D.draw(x, 1000000, ex, n1)["groups"] == D.draw(x, 1000000, ex, n2)["groups"])
            break
    out["order_evidence"] = found
    import beacon_chain
    import beacon_verify
    br = dict(round=1000000, randomness=v, signature="83ad29e4c409f9470fc2ef02f90214df49e02b441a1a241a82d622d9f608ef98"
              "fd8b11a029f1bee9d9e83b45088abe72")
    out["beacon_verify"] = dict(published=beacon_verify.verify(beacon_chain.QUICKNET, br).get("ok"),
                                padded=beacon_verify.verify(beacon_chain.QUICKNET, dict(br, signature="00" + br["signature"])).get("ok"))
    e = (HERE / "draw_seeds.py").exists()
    ok = all([check(checks, "lowercase: the seeds of ef374ccd", json.dumps(same_as_before, sort_keys=True),
                    '"campaign": true, "rehearsal": true, "standin": true', HERE / "draw_seeds.py", e),
              check(checks, "other writings refused", json.dumps(refused, sort_keys=True),
                    '"mixed": true, "prefixed": true, "round_as_string": true, "spaced": true, "upper": true',
                    HERE / "draw_seeds.py", e),
              check(checks, "every permutation of the sizes identical", json.dumps(perms, sort_keys=True),
                    '"campaign": true, "rehearsal": true, "standin": true', HERE / "draw_seeds.py", e),
              check(checks, "the order evidence", json.dumps(found), '"old_differs": true, "new_identical": true',
                    HERE / "draw_seeds.py", e),
              check(checks, "beacon_verify: the published signature verifies, the zero-padded one is refused",
                    json.dumps(out["beacon_verify"], sort_keys=True), '"padded": false, "published": true',
                    HERE / "beacon_verify.py", (HERE / "beacon_verify.py").exists())]) and out["bytes_same"]
    out["checks"] = checks
    return ok, out


def case_analysis_two_rehearsals(w):
    """The owner's rule after rehearsal 1 (2026-11-27): the campaign's list must hold the seeds of BOTH rehearsals and
    their noise seeds 10 S + 0..3, rehearsal 1 checked against its own freeze (analysis.REHEARSAL1). Called on
    analysis.check_rehearsal_seeds, offline, with rehearsal 1's published files (tests/fixtures/rehearsal1: its DRAW.json
    b8aaefd9, DRAW_ANNOUNCE.txt and EXCLUDED_PUBLISHED.json) and, for rehearsal 2, a stand-in draw on the published
    quicknet round 20000000 (6/6/6 over the pinned EXCLUDED.json):
    - both, with the full list: accepted, both checked (recomputed, signature verified);
    - rehearsal 1 absent in campaign mode: refused; rehearsal 2 absent: refused;
    - one rehearsal 1 seed, or one of its noise seeds, missing from the list: refused, naming it;
    - rehearsal 1's DRAW.json changed (re-serialized, the same content): refused by its pinned sha256;
    - rehearsal 1 with another list than its published one: refused;
    - rehearsal 1's announce later than the campaign's: refused."""
    import datetime
    import hashlib
    import importlib.util
    spec = importlib.util.spec_from_file_location("analysis_under_test", ANALYSIS)
    A = importlib.util.module_from_spec(spec)
    sys.path.insert(0, str(Path(ANALYSIS).parent))
    spec.loader.exec_module(A)
    import beacon_chain
    import beacon_verify
    import draw_seeds as D
    fx = HERE / "tests" / "fixtures" / "rehearsal1"
    ex_f = HERE / "EXCLUDED.json"
    ex = json.loads(ex_f.read_text())
    r1 = json.loads((fx / "DRAW.json").read_text())
    br = dict(round=20000000, randomness="f39c98df5525968e6622e0c63edb3d1f9c5607cf780db78abdded36e4b3dba95",
              signature="96892582a33552a7b67ba44ef09c3ccd535bbebe760c93ecf45be8958d0c0f06390c6d19d7bf492eb806af7eef6b125c")
    t0 = beacon_verify.round_time(beacon_chain.QUICKNET, br["round"]) - beacon_verify.DELAY_S
    push = datetime.datetime.fromtimestamp(t0, datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    sizes = dict(NOT1=6, ANDOR3=6, XOR3=6)
    a2 = w.wd / "ANNOUNCE_r2.txt"
    a2.write_text(f"format layered-draw-announce/1\nmode rehearsal\nexcluded_sha256 {hashlib.sha256(ex_f.read_bytes()).hexdigest()}\n"
                  "sizes NOT1=6 ANDOR3=6 XOR3=6\n")
    d2 = D.draw(br["randomness"], br["round"], ex, dict(sizes))
    f2 = w.wd / "DRAW_r2.json"
    f2.write_bytes(D.canon(dict(d2, beacon_round=br, announce=dict(branch=A.ANNOUNCE_BRANCH["rehearsal"], commit="0" * 40,
                                                                    push_utc=push))))
    s1 = sorted(s for v in r1["groups"].values() for s in v)
    s2 = sorted(s for v in d2["groups"].values() for s in v)
    full = sorted(set(ex["seeds"]) | set(s1) | set(s2) | {10 * s + j for s in s1 + s2 for j in range(4)})

    def listed(label, seeds):
        x = dict(ex, seeds=seeds, count=len(seeds), seeds_sha256=hashlib.sha256(D.canon(seeds)).hexdigest())
        f = w.wd / f"EXCLUDED_two_{label}.json"
        f.write_bytes(D.canon(x))
        return str(f)
    later = (datetime.datetime.now(datetime.timezone.utc) + datetime.timedelta(days=1)).strftime("%Y-%m-%dT%H:%M:%SZ")
    base = dict(rehearsal_draw=str(f2), rehearsal_announce=str(a2), rehearsal1_draw=str(fx / "DRAW.json"),
                rehearsal1_excluded=str(fx / "EXCLUDED_PUBLISHED.json"), rehearsal1_announce=str(fx / "DRAW_ANNOUNCE.txt"))
    resaved = w.wd / "DRAW_r1_resaved.json"
    resaved.write_text(json.dumps(r1, indent=1, sort_keys=True) + "\n")
    other_list = listed("other", sorted(set(ex["seeds"]) | {1}))

    def call(kw, campaign_push=later):
        try:
            r = A.check_rehearsal_seeds(dict(kw), dict(announce=dict(push_utc=campaign_push)), w.wd / "two_out", None,
                                        False, "campaign")
            return "accepted: " + json.dumps({k: dict(recomputed=v["recomputed"], signature_verified=v["signature_verified"],
                                                      seeds=v["seeds"]) for k, v in r.items()}, sort_keys=True)
        except SystemExit as e:
            return str(e)
    (w.wd / "two_out").mkdir(exist_ok=True)
    cases = [
        ("both, the full list: accepted", dict(base, excluded=listed("full", full)),
         '"rehearsal1": {"recomputed": true, "seeds": 18, "signature_verified": true}'),
        ("rehearsal 1 absent: refused", dict({k: v for k, v in base.items() if not k.startswith("rehearsal1_")},
                                             excluded=listed("full", full)), "rehearsal1_draw= (rehearsal1's published DRAW.json) is required"),
        ("rehearsal 2 absent: refused", dict({k: v for k, v in base.items() if not k.startswith("rehearsal_")},
                                             excluded=listed("full", full)), "rehearsal_draw= (rehearsal2's published DRAW.json) is required"),
        ("a rehearsal 1 seed missing: refused", dict(base, excluded=listed("no_s1", [s for s in full if s != s1[0]])),
         f"lacks rehearsal1 seeds [{s1[0]}]"),
        ("a rehearsal 1 noise seed missing: refused", dict(base, excluded=listed("no_n1", [s for s in full if s != 10 * s1[1] + 3])),
         f"noise seeds [{10 * s1[1] + 3}]"),
        ("rehearsal 1's DRAW.json re-serialized: refused", dict(base, rehearsal1_draw=str(resaved), excluded=listed("full", full)),
         "the published rehearsal 1 draw is b8aaefd9f107"),
        ("rehearsal 1 with another list: refused", dict(base, rehearsal1_excluded=other_list, excluded=listed("full", full)),
         "not the one DRAW_ANNOUNCE.txt names"),
    ]
    checks, out = [], {}
    oks = []
    for label, kw, needle in cases:
        got = call(kw)
        out[label] = got
        oks.append(check(checks, label, got, needle, w.wd / "two_out", True))
    # rehearsal mode (rehearsal 2's own analysis): its list must hold rehearsal 1's 18 seeds and 72 noise seeds
    r2list = sorted(set(ex["seeds"]) | set(s1) | {10 * s + j for s in s1 for j in range(4)})

    def call_r2(lst):
        try:
            r = A.check_rehearsal_seeds(dict(rehearsal1_draw=str(fx / "DRAW.json"), rehearsal1_excluded=str(fx / "EXCLUDED_PUBLISHED.json"),
                                             rehearsal1_announce=str(fx / "DRAW_ANNOUNCE.txt"), excluded=lst),
                                        dict(announce=dict(push_utc=later)), w.wd / "two_out", None, False, "rehearsal")
            return "accepted: " + json.dumps(sorted(r))
        except SystemExit as e:
            return str(e)
    for label, lst, needle in (
            ("rehearsal mode: rehearsal 2's list with rehearsal 1's seeds: accepted", listed("r2_full", r2list), 'accepted: ["rehearsal1"]'),
            ("rehearsal mode: rehearsal 2's list missing one rehearsal 1 noise seed: refused",
             listed("r2_no_n1", [s for s in r2list if s != 10 * s1[2] + 1]), f"rehearsal 2's excluded= list lacks rehearsal1 seeds [] and noise seeds [{10 * s1[2] + 1}]"),
            ("rehearsal mode: rehearsal 1 absent: refused", None, "rehearsal mode: rehearsal1_draw=")):
        if lst is None:
            try:
                A.check_rehearsal_seeds(dict(excluded=listed("r2_full", r2list)), dict(announce=dict(push_utc=later)),
                                        w.wd / "two_out", None, False, "rehearsal")
                got = "accepted"
            except SystemExit as e:
                got = str(e)
        else:
            got = call_r2(lst)
        out[label] = got
        oks.append(check(checks, label, got, needle, w.wd / "two_out", True))
    got = call(dict(base, excluded=listed("full", full)), campaign_push="2026-11-27T15:00:00Z")
    out["rehearsal 1's announce later than the campaign's: refused"] = got
    oks.append(check(checks, "rehearsal 1's announce later than the campaign's: refused", got,
                     "rehearsal1's announce (2026-11-27T15:14:37Z) is not earlier", w.wd / "two_out", True))
    return all(oks), dict(checks=checks, results=out, rehearsal1_seeds=s1, rehearsal2_standin_seeds=s2)


def hashlib_sha(s):
    import hashlib
    return hashlib.sha256(s.encode()).hexdigest()


def case_draw_plans_command(w):
    """The audit's X2, through the real command: a DRAW.json file (the stand-in quicknet round 1000000 at 60/32/37 and
    at 6/6/6, written as the coordinator writes it, with beacon_round and announce) split by `plan_split3.py DRAW.json
    campaign_template.json OUTDIR`, as the procedure does; every PLAN_K<nn>.json must be byte for byte the plan
    analysis.py expects (plan_split.canon of expected_plans of the recomputed draw), which is what campaign mode
    matches a root's PLAN_INPUT.json against. And plan_split3.split gives byte-identical plans for every key order of
    draw["groups"]."""
    import importlib.util
    import itertools
    sys.path.insert(0, str(HERE))
    import draw_seeds as D
    import plan_split as PS
    import plan_split3 as P3
    spec = importlib.util.spec_from_file_location("analysis_p", HERE / "analysis.py")
    A = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(A)
    ex = json.loads((HERE / "EXCLUDED.json").read_text())
    v = "b22aad4794f7451896f7a371aa46106fd84d919f3f569acd5b2fddf1d1440af3"
    br = dict(round=1000000, randomness=v, signature="83ad29e4c409f9470fc2ef02f90214df49e02b441a1a241a82d622d9f608ef98"
              "fd8b11a029f1bee9d9e83b45088abe72")
    tmpl = json.loads((HERE / "campaign_template.json").read_text())
    checks, out = [], {}
    for label, n in (("campaign", A.DRAW_SIZES), ("rehearsal", A.DRAW_SIZES_REHEARSAL)):
        d = D.draw(v, 1000000, ex, dict(n))
        f = w.wd / f"DRAW_plans_{label}.json"
        f.write_bytes(D.canon(dict(d, beacon_round=br, announce=dict(branch="test", commit="0" * 40,
                                                                     push_utc="2023-09-27T08:19:24Z"))))
        od = w.wd / f"plans_cmd_{label}"
        shutil.rmtree(od, ignore_errors=True)
        r = sh(PY, "-B", HERE / "plan_split3.py", f, HERE / "campaign_template.json", od)
        expected, _ = A.expected_plans(d)
        match = {k: (od / f"PLAN_{k}.json").exists() and (od / f"PLAN_{k}.json").read_bytes() == PS.canon(p)
                 for k, p in expected.items()}
        perms = len({b"".join(PS.canon(p) for p in P3.split(dict(d, groups={g: d["groups"][g] for g in perm}), tmpl, 12)[0])
                     for perm in itertools.permutations(d["groups"])}) == 1
        out[label] = dict(rc=r.returncode, plans_match=match, every_key_order_identical=perms)
        checks.append(dict(check=f"{label}: the 12 plan files are the expected plans", matched=json.dumps(match)
                           if all(match.values()) and len(match) == 12 else None, target=str(f), target_exists=f.exists()))
        checks.append(dict(check=f"{label}: one split for every key order", matched="identical" if perms else None,
                           target=str(f), target_exists=f.exists()))
    out["checks"] = checks
    return all(c["matched"] for c in checks) and all(x["rc"] == 0 for k, x in out.items() if k != "checks"), out


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
    run("analysis_announce", case_analysis_announce)
    run("draw_canonical", case_draw_canonical)
    run("draw_plans_command", case_draw_plans_command)
    run("analysis_two_rehearsals", case_analysis_two_rehearsals)
    run("analysis_own_check", case_analysis_own_check)
    run("sigterm_driver_only", case_sigterm_driver_only)
    run("sigkill_driver_only", case_sigkill_driver_only)
    run("k3_budget_stop", case_k3_budget_stop)
    r = run("home_run", case_home)
    if r and len(r) > 2:
        run("differing_duplicate", case_differing_duplicate, r[2])
        run("duplicate_after_later_seals", case_duplicate_after_later_seals, r[2])
        run("duplicate_forged_line", case_duplicate_forged_line, r[2])
        run("analysis_refuses", case_analysis_refuses_test_root, r[2]["root"])
        run("analysis_tampered", case_analysis_tampered, r[2])
        run("analysis_forged_pins", case_analysis_forged_pins, r[2]["root"])
        run("analysis_d8_not_run", case_analysis_d8_not_run, r[2])
        run("analysis_d9_copies", case_analysis_d9_copies, r[2])
        run("analysis_d10_manifest", case_analysis_d10_manifest, r[2])
        run("analysis_hardening", case_analysis_hardening, r[2])
    run("partial_guard_and_resume", case_partial_guard)
    ok = all(v["ok"] for v in report.values())
    report["all_pass"] = ok
    (w.wd / "TEST_C.json").write_text(json.dumps(report, indent=1, sort_keys=True) + "\n")
    return ok


if __name__ == "__main__":
    sys.exit(0 if main(*sys.argv[1:]) else 1)
