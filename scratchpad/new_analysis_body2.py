

# ================================================================================================ 2. seals (analyze3, analyze10)

def seal_files(R, name):
    """B2 and B1: the seal is exactly seal/<name>.json beside MANIFEST.json and SHA256SUMS, and seal.verify holds.
    Returns (rel path of the sealed prediction or None, why or None)."""
    import seal as sealmod
    d = R.path / name / "seal"
    if not d.is_dir():
        return None, "no seal folder"
    names = sorted(p.name for p in d.iterdir())
    if names != sorted(["MANIFEST.json", "SHA256SUMS", f"{name}.json"]):
        return None, f"the seal folder holds {names}, not exactly MANIFEST.json, SHA256SUMS and {name}.json"
    with contextlib.redirect_stdout(io.StringIO()):
        ok = sealmod.verify(d, quiet=True)
    if not ok:
        return None, "seal.verify fails on the seal folder"
    for f in ("MANIFEST.json", f"{name}.json"):
        R.file(f"{name}/seal/{f}")
    return f"{name}/seal/{name}.json", None


def regenerate(R, name, plan, status, kernel_build, seal_rel):
    d = R.path / name
    p10 = json.loads(R.bytes(seal_rel))                        # analyze10's check comes first
    names6, kernel = "stage_d6.py" in p10.get("code", {}), "kernel" in p10
    if names6 and not kernel:
        return False, "the sealed prediction names stage_d6.py but has no kernel field"
    if kernel and not names6:
        return False, "the sealed prediction has a kernel field but does not name stage_d6.py"
    if not R.exists(f"{name}/D/record.json"):
        return False, "no stage-D record"
    sealed = R.bytes(seal_rel)
    pred = json.loads(sealed)
    script = next((s for s in SCRIPTS if s in pred.get("code", {})), None)
    if script is None:
        return False, "the sealed prediction names no stage-D script"
    spec = HERE / plan["groups"][status["group"]]["spec"]
    with tempfile.TemporaryDirectory() as t:
        t = Path(t)
        for f in ("record.json", "overlay_d.json"):
            shutil.copyfile(R.file(f"{name}/D/{f}"), t / f)
        args = [PY, "-B", str(HERE / script), "predict", str(spec), str(t), f"rule={pred.get('testError_rule', 'one-port')}"]
        if (d / "inv" / "inverter_gate.json").exists():
            (t / "inv").mkdir()
            shutil.copyfile(R.file(f"{name}/inv/inverter_gate.json"), t / "inv" / "inverter_gate.json")
            args.append(f"inverters={t / 'inv' / 'inverter_gate.json'}")
        env = {k: os.environ[k] for k in REGEN_ENV if k in os.environ}       # B11: a minimal environment
        env["LAYERED_KERNEL_BUILD"] = str(kernel_build)
        if status.get("env_sha256"):
            env["LAYERED_ENV_SHA256"] = status["env_sha256"]
        r = subprocess.run(args, cwd=HERE, capture_output=True, text=True, env=env)
        if r.returncode or not (t / "prediction.json").exists():
            return False, "regeneration failed: " + r.stderr.strip().replace(str(t), "<scratch>")[-300:]
        again = (t / "prediction.json").read_bytes()
    if again != sealed:
        a, b = json.loads(again), pred
        keys = sorted(k for k in set(a) | set(b) if a.get(k) != b.get(k))
        return False, f"regenerated prediction differs from the seal in {keys}"
    return True, None


def safe(branch):
    return str(branch).replace("/", "__")


def push_times(remote, branch, src, outdir):
    """B7: GitHub's recorded push times (every activity item saved in OUTDIR/activity/), or the local bare log in
    test mode."""
    if src == "github":
        owner_repo = str(remote).rstrip("/").removesuffix(".git").split("github.com/")[-1]
        r = subprocess.run(["gh", "api", "-X", "GET", f"repos/{owner_repo}/activity", "-f", f"ref=refs/heads/{branch}",
                            "-f", "per_page=100", "--paginate"], capture_output=True, text=True, check=True)
        items = SP.activity_pages(r.stdout)
        a = Path(outdir) / "activity"
        a.mkdir(exist_ok=True)
        (a / f"{safe(branch)}.json").write_bytes(canon(dict(repository=owner_repo, ref=f"refs/heads/{branch}", items=items)))
        return SP.github_times(items)
    return SP.times(remote, branch, src)


def seal_log(R, name, plan, status, logs, times_src, campaign, outdir):
    sp_ = plan.get("seal_push")
    if not sp_:
        return False, dict(why="the plan has no seal_push")
    if sp_.get("dry"):
        return False, dict(why="dry seal push (nothing was pushed)")
    key = (str(sp_["remote"]), sp_["branch"])
    if key not in logs:
        with tempfile.TemporaryDirectory() as w:
            try:
                lines = SP.log_lines(sp_["remote"], sp_["branch"], w)
                tm = push_times(sp_["remote"], sp_["branch"], times_src, outdir)
                logs[key] = (lines, tm, None)
            except Exception as e:
                if campaign:                              # A1(i): never reinterpreted; rerun the analysis later
                    refuse(f"campaign mode: the seal log or its push times cannot be read ({sp_['branch']}): {e!r}"[:500])
                logs[key] = ([], {}, repr(e))
    lines, tm, err = logs[key]
    if err:
        return False, dict(why=f"the seal log cannot be read: {err}")
    want = sha(R.path / name / "seal" / "SHA256SUMS")
    mine = [x for x in lines if x["instance"] == name]
    if len(mine) != 1:                                    # B3: exactly one line per instance
        return False, dict(why=f"{len(mine)} lines for this instance in the seal log, not exactly one",
                           logged=[x["seal_sha256"] for x in mine])
    x = mine[0]
    if x["seal_sha256"] != want:
        return False, dict(why="the logged seal sha256 is not this seal's", logged=[x["seal_sha256"]])
    pushed = tm.get(x["commit"])
    if pushed is None:
        if campaign:
            refuse(f"campaign mode: no recorded push time for {x['commit']} ({sp_['branch']}, {name})")
        return False, dict(why="no recorded push time for the commit that logged the seal", commit=x["commit"])
    n0 = status["steps"].get("N0", {}).get("started")
    if n0 is None:
        return True, dict(pushed_utc=pushed, stage_n_start=None, note="no stage N started", commit=x["commit"])
    margin = (parse_utc(n0) - parse_utc(pushed)).total_seconds()
    detail = dict(pushed_utc=pushed, stage_n_start=n0, margin_s=round(margin, 3), commit=x["commit"])
    if margin <= 0:
        return False, dict(detail, why="the seal was pushed after stage N started")
    return True, detail


def same_n0(Ra, a, Rb, b):
    out = {}
    for f in ("noisy_record.json", "trace.digest.json"):
        if Ra.exists(f"{a}/{f}") and Rb.exists(f"{b}/{f}"):
            out[f] = strip(Ra.json(f"{a}/{f}")) == strip(Rb.json(f"{b}/{f}"))
        else:
            out[f] = None
    if Ra.exists(f"{a}/input.spice") and Rb.exists(f"{b}/input.spice"):
        out["input.spice"] = Ra.bytes(f"{a}/input.spice") == Rb.bytes(f"{b}/input.spice")
    return out


def seal_defect(r, level):
    """A1(ii), the owner's rule: a seal defect makes an agreement count for nothing; a completed refutation (a
    differing comparison, or a run stopped by its own check) stays refuted, flagged."""
    x = r.get(level) or {}
    if x.get("counted") and x.get("refuted"):
        r[level] = dict(x, seal_defect=True)
    elif x.get("counted"):
        r[level] = dict(counted=False, not_sealed=True)


def layer_seals(M, times_src, kernel_build, th, campaign, rule, outdir):
    rows, observed, failed, controls, envs, defects = [], [], [], dict(U=[], duplicate=[], S=[], cross_machine_duplicates=[]), {}, []
    logs, by_inst = {}, {}
    for machine, m in M.items():
        R, plan = m["R"], m["plan"]
        if R is None:                                    # D8: a machine of the expected plans with no root
            for name, group, seed in home_instances(plan):
                rows.append(dict(instance=name, group=group, seed=seed, machine=machine, not_run=True,
                                 why="no root for this machine", K0=dict(counted=False), K3=dict(counted=False)))
            continue
        envs[machine] = env_section(R)
        res = analyze_root(R, plan, machine, campaign)
        for r in res["instances"]:
            r["machine"] = machine
            if r.get("stage_d") is not None:
                status = R.json(f"{r['instance']}/status.json")
                seal_rel, why0 = seal_files(R, r["instance"])
                if seal_rel is None:
                    ok1, why1 = False, why0
                else:
                    ok1, why1 = regenerate(R, r["instance"], plan, status, kernel_build, seal_rel)
                    dp = f"{r['instance']}/D/prediction.json"
                    if ok1 and (not R.exists(dp) or R.bytes(dp) != R.bytes(seal_rel)):
                        ok1, why1 = False, "D/prediction.json differs from its seal (the sealed prediction is the one read)"
                    if campaign:                              # B6
                        p = json.loads(R.bytes(seal_rel))
                        if "stage_d6.py" not in p.get("code", {}) or p.get("testError_rule") != rule:
                            refuse(f"campaign mode: {machine} {r['instance']}: the sealed prediction does not name "
                                   f"stage_d6.py with the template's testError_rule {rule!r}")
                if seal_rel is None:
                    ok2, det2 = False, dict(why="no valid seal")
                else:
                    ok2, det2 = seal_log(R, r["instance"], plan, status, logs, times_src, campaign, outdir)
                r["seal"] = dict(regenerated_identical=ok1, regeneration_why=why1, log_ok=ok2, log=det2)
                if not (ok1 and ok2):
                    defects.append(dict(machine=machine, instance=r["instance"], regenerated=why1 or "identical",
                                        log=det2.get("why") or "ok"))
                    for level in ("K0", "K3"):
                        seal_defect(r, level)
            rows.append(r)
            if not r.get("not_run"):
                by_inst[r["instance"]] = (machine, r)
        observed += [dict(o, machine=machine) for o in res["observed_only"]]
        failed += [dict(f, machine=machine) for f in res["run_failed"]]
        for c in ("U", "duplicate", "S"):
            controls[c] += [dict(x, machine=machine) for x in res["controls"][c]]
    for machine, m in M.items():
        if m["R"] is None:
            continue
        for dx in sorted(m["R"].path.glob("DUPX_*")):
            name = dx.name[len("DUPX_"):]
            entry = dict(instance=name, duplicate_machine=machine)
            if name not in by_inst:
                entry["why"] = "original instance not in the analysed OUTROOTs"
            else:
                om = by_inst[name][0]
                entry.update(original_machine=om, **{f"{k_}_identical": v for k_, v in
                                                     same_n0(M[om]["R"], f"{name}/N0", m["R"], f"{dx.name}/N0").items()})
            controls["cross_machine_duplicates"].append(entry)
    groups = {}
    allgroups = sorted({g for m in M.values() for g in m["plan"]["groups"]})
    for g in allgroups:
        rs = [r for r in rows if r["group"] == g]
        out = dict(instances=len(rs), eligible_K0=sum(1 for r in rs if (r.get("stage_d") or {}).get("eligible_K0")),
                   room_K3=sum(1 for r in rs if (r.get("stage_d") or {}).get("room_K3")))
        for level in ("K0", "K3"):
            counted = [r for r in rs if (r.get(level) or {}).get("counted")]
            ref = sorted(r["instance"] for r in counted if r[level]["refuted"])
            out[level] = dict(counted=len(counted), refuted_instances=ref, threshold=th[level][g],
                              verdict=word(len(counted), bool(ref), th[level][g]),
                              not_sealed=sorted(r["instance"] for r in rs if (r.get(level) or {}).get("not_sealed")))
        mr = [r for r in rs if r.get("max_rule_comparison")]
        out["max_rule_comparison_counts_for_nothing"] = dict(
            eligible_K0=sum(1 for r in mr if r["max_rule_comparison"]["eligible_K0"]),
            room_K3=sum(1 for r in mr if r["max_rule_comparison"]["room_K3"]),
            room_only_under_one_port=sorted(r["instance"] for r in mr if r["stage_d"]["room_K3"] and not r["max_rule_comparison"]["room_K3"]))
        groups[g] = out
    rows.sort(key=lambda r: (r["group"], r["seed"]))
    if times_src.startswith("lsremote:"):
        lp = Path(times_src.split(":", 1)[1])
        src_desc = dict(source="lsremote (coordinator's ls-remote log; first-seen times, upper bounds of the push times)",
                        log=lp.name, log_sha256=sha(lp) if lp.exists() else None)
    else:
        src_desc = dict(source={"github": "GitHub repository activity API (push timestamps; push and branch_creation "
                                          "items only; every item saved in activity/)",
                                "bare": "local bare repository post-receive log"}.get(times_src, times_src))
    return rt(dict(times_source=src_desc, machines=len(M),
                   env={m: (None if e is None else dict(static_sha256=e["static_sha256"], env_json_sha256=e["env_json_sha256"]))
                        for m, e in envs.items()},
                   groups=groups, family=family_of(groups), seal_defects=defects, observed_only=observed, run_failed=failed,
                   controls=controls, instances=rows, thresholds=dict(K0=th["K0"], K3=th["K3"])))


# ================================================================================================ 3–6

def regroup(res, threshold_of):
    for g, v in res["groups"].items():
        rs = [r for r in res["instances"] if r["group"] == g]
        for level in ("K0", "K3"):
            counted = [r for r in rs if (r.get(level) or {}).get("counted")]
            ref = sorted(r["instance"] for r in counted if r[level]["refuted"])
            v[level].update(counted=len(counted), refuted_instances=ref,
                            verdict=word(len(counted), bool(ref), threshold_of(g, level)),
                            not_sealed=sorted(r["instance"] for r in rs if (r.get(level) or {}).get("not_sealed")))
    res["family"] = family_of(res["groups"])


def completed_rounds(r, level):
    """The rounds of a counted level whose comparison completed (a run stopped by its own check included): N0 at K0;
    at K3 the completed noisy rounds (all three for a held instance, at least the refuting one for a refuted one)."""
    if level == "K0":
        return [0]
    comps = r.get("comparisons") or {}
    return [n for n in (1, 2, 3) if (comps.get(f"C{n}") or {}).get("verdict") in ("agrees", "refuted")
            or (comps.get(f"C{n}") or {}).get("stopped_by_own_check")]


def layer_stage_n_seal_log(res, M, th):
    for r in res["instances"]:
        if r.get("not_run"):
            continue
        R = M[r["machine"]]["R"]
        commit = ((r.get("seal") or {}).get("log") or {}).get("commit")
        for level in ("K0", "K3"):
            if not (r.get(level) or {}).get("counted"):
                continue
            bad = []
            for n in completed_rounds(r, level):
                f = f"{r['instance']}/N{n}/SEAL_LOG.json"
                got = (R.json(f) or {}).get("commit") if R.exists(f) else None
                if got is None or got != commit:
                    bad.append(f"N{n}: SEAL_LOG.json {'missing' if got is None else got[:12]} vs log {str(commit)[:12]}")
            if bad:
                seal_defect(r, level)
                res["seal_defects"].append(dict(machine=r["machine"], instance=r["instance"], stage_n_seal_log=bad))
    regroup(res, lambda g, level: th[level][g])
    return rt(res)


def layer_thresholds(res, tf, th):
    for g, v in res["groups"].items():
        for level in ("K0", "K3"):
            t = th[level][g]
            v[level].update(threshold=t, verdict=word(v[level]["counted"], bool(v[level]["refuted_instances"]), t))
    res["family"] = family_of(res["groups"])
    res.update(thresholds=dict(file=Path(tf).name, sha256=sha(tf), K0=th["K0"], K3=th["K3"]))
    return rt(res)


def layer_record_seal_log(res, M):
    for r in res["instances"]:
        if r.get("not_run"):
            continue
        R, plan = M[r["machine"]]["R"], M[r["machine"]]["plan"]
        branch = (plan.get("seal_push") or {}).get("branch")
        commit = ((r.get("seal") or {}).get("log") or {}).get("commit")
        for level in ("K0", "K3"):
            if not (r.get(level) or {}).get("counted"):
                continue
            bad = []
            for n in completed_rounds(r, level):
                f = f"{r['instance']}/N{n}/noisy_record.json"
                sl = (R.json(f) or {}).get("seal_log") if R.exists(f) else None
                if not sl or sl.get("commit") != commit or sl.get("branch") != branch:
                    bad.append(f"N{n}: record seal_log {sl} vs log {str(commit)[:12]} on {branch}")
            if bad:
                seal_defect(r, level)
                res["seal_defects"].append(dict(machine=r["machine"], instance=r["instance"], record_seal_log=bad))
    th = res["thresholds"]
    regroup(res, lambda g, level: th[level][g])
    useal = []
    for machine, m in M.items():
        if m["R"] is None:
            continue
        for f in sorted(m["R"].path.glob("U_*/U/untrained_record.json")):
            rel = str(f.relative_to(m["R"].path))
            useal.append(dict(machine=machine, instance=f.parent.parent.name[2:], seal_log=m["R"].json(rel).get("seal_log")))
    res["controls"]["U_seal_log"] = useal
    return rt(res)


def load_checker(path):
    spec = importlib.util.spec_from_file_location("check_duplicate_analysis", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def judge(chk, a, b):
    out = io.StringIO()
    with contextlib.redirect_stdout(out):
        ok = bool(chk.main(str(a), str(b)))
    return ok, out.getvalue().splitlines()


def layer_duplicates(res, M, controls_dir):
    where = {r["instance"]: r["machine"] for r in res["instances"] if not r.get("not_run") and not r.get("unverified")}
    xs = []
    for machine, m in M.items():
        if m["R"] is None:
            continue
        R = m["R"]
        for dx in sorted(R.path.glob("DUPX_*")):
            name = dx.name[len("DUPX_"):]
            e = dict(instance=name, duplicate_machine=machine)
            if name not in where:
                e["why"] = "original instance not in the analysed OUTROOTs"
                xs.append(e)
                continue
            om = where[name]
            OR = M[om]["R"]
            e["original_machine"] = om
            ctl = Path(controls_dir) if controls_dir else \
                Path(OR.json("PLAN.json")["noise_tree"]) / "research" / "layered-networks"
            cp = ctl / "tests" / "check_duplicate.py"
            e["checker"] = dict(file="tests/check_duplicate.py", sha256=sha(cp) if cp.exists() else None)
            for d_, R_ in ((OR.path / name / "N0", OR), (dx / "N0", R)):     # what check_duplicate reads (B8)
                for f in sorted(d_.iterdir()) if d_.is_dir() else []:
                    if f.is_file() and f.name in ("noisy_record.json", "trace.digest.json", "trace.raw", "input.spice"):
                        R_.file(str(f.relative_to(R_.path)))
            if cp.exists():
                ident, lines = judge(load_checker(cp), OR.path / name / "N0", dx / "N0")
                e.update(identical=ident, checker_lines=lines)
            else:
                e.update(identical=None, why="check_duplicate.py not found")
            sc = R.json(f"{dx.name}/seal_check.json")
            if sc is not None:
                sc.pop("seal_dir", None)
                e["seal_check"] = sc
            sf = R.json(f"{dx.name}/seal_fetch.json")
            if sf is not None:
                sf.pop("remote", None)
                e["seal_fetch"] = sf
            cd = R.json(f"{dx.name}/N0/comparison.json")
            if cd is not None:
                co = OR.json(f"{name}/N0/comparison.json")
                e["comparison"] = dict(verdict=cd.get("verdict"), equals_original=co is not None and strip(cd) == strip(co))
            else:
                e["comparison"] = None
            xs.append(e)
    res["controls"]["cross_machine_duplicates_v3"] = res["controls"].pop("cross_machine_duplicates", [])
    res["controls"]["cross_machine_duplicates"] = xs
    # A7: the expected controls against the present ones
    exp_u, exp_d = [], []
    for machine, m in M.items():
        plan = m["plan"]
        for g in sorted(plan.get("U_groups") or []):
            u = [x for x in res["controls"]["U"] if x["machine"] == machine and
                 any(r["instance"] == x["instance"] and r["group"] == g for r in res["instances"])]
            exp_u.append(dict(machine=machine, group=g, present=bool(u), instance=u[0]["instance"] if u else None,
                              passed=(u[0]["holds"] is True) if u else None,
                              why=None if u else ("no root" if m["R"] is None else "not run (no U folder: no eligible "
                                                  "instance of the group, or the run stopped)")))
        for x in plan.get("remote_duplicates") or []:
            d = [e for e in xs if e["duplicate_machine"] == machine and e["instance"] == x["home_instance"]]
            exp_d.append(dict(machine=machine, instance=x["home_instance"], home_machine=x["home_machine"],
                              present=bool(d), passed=(d[0].get("identical") is True) if d else None,
                              why=None if d else ("no root" if m["R"] is None else "not run (no DUPX folder)")))
    summ = lambda xs_: dict(expected=len(xs_), present=sum(1 for x in xs_ if x["present"]),
                            passed=sum(1 for x in xs_ if x["passed"] is True),
                            failed=sum(1 for x in xs_ if x["present"] and x["passed"] is not True))
    res["expected_controls"] = dict(U=exp_u, remote_duplicates=exp_d,
                                    summary=dict(U=summ(exp_u), remote_duplicates=summ(exp_d)))
    return rt(res)


# ================================================================================================ 7. D4 (analyze8)

def is_audited(R, name):
    f = f"{name}/D/fit_d.json"
    if not R.exists(f):
        return False
    cells = R.json(f).get("cells", [])
    return any(((c.get("budgets") or {}).get("K0") or {}).get("D4_source") == SOLO for c in cells)


def layer_d4(res, M):
    live = lambda r: not r.get("not_run") and not r.get("unverified")
    inst_dir = lambda r: M[r["machine"]]["R"].path / r["instance"]
    spec_of = lambda r: HERE / M[r["machine"]]["plan"]["groups"][r["group"]]["spec"]
    rows, frozen = res["instances"], D4.FROZEN
    groups, flags = {}, {}
    for g in sorted({r["group"] for r in rows}):
        rs = sorted((r for r in rows if r["group"] == g and live(r)), key=lambda r: (r["machine"], r["instance"]))
        aud = [r for r in rs if is_audited(M[r["machine"]]["R"], r["instance"])]
        planned = sorted((m_, f"{tag_of(m['plan'], g)}_{s}") for m_, m in M.items() if g in m["plan"]["groups"]
                         for s in m["plan"]["groups"][g].get("d4_audit") or [])
        present = sorted((r["machine"], r["instance"]) for r in aud)
        ls = []
        for r in aud:
            R = M[r["machine"]]["R"]
            for f in sorted((inst_dir(r) / "D").glob("*.json")):
                R.file(str(f.relative_to(R.path)))
            for c, by_g in sorted(D4.audited_lines(inst_dir(r) / "D").items()):
                for grp, v in sorted(by_g.items()):
                    ls.append(dict(machine=r["machine"], instance=r["instance"], cell=c, group=grp, value=str(v),
                                   value_float=float(v), above_frozen=v > frozen))
        star = max((F(x["value"]) for x in ls), default=None)
        sec = dict(planned=[list(x) for x in planned], audited=[r["instance"] for r in aud],
                   planned_not_audited=[list(x) for x in planned if x not in present],
                   audited_not_planned=[list(x) for x in present if x not in planned],
                   note=None if aud else "no D4 audit in this group",
                   lines=ls, frozen_d4_stage=str(frozen),
                   D4_star=None if star is None else str(star), D4_star_float=None if star is None else float(star),
                   exceeds=bool(star is not None and star > frozen), regated=[], premise_flagged_D4=dict(K0=[], K3=[]))
        if sec["exceeds"]:
            for r in rs:
                if r in aud or r.get("stage_d") is None:
                    continue
                reg = D4.regate(spec_of(r), inst_dir(r), star)
                if not reg["reproduces_sealed"]:                  # A8
                    refuse(f"{r['machine']} {r['instance']}: the D4 regate at the frozen value does not reproduce the "
                           f"sealed gate ({reg['sealed']})")
                sec["regated"].append(dict(machine=r["machine"], instance=r["instance"], **{
                    k: reg[k] for k in ("reproduces_sealed", "sealed", "regated", "gate_holds_K0", "gate_holds_K3",
                                        "newly_failing_K0", "newly_failing_K3")}))
                for level in ("K0", "K3"):
                    if (r.get(level) or {}).get("counted") and not reg[f"gate_holds_{level}"]:
                        sec["premise_flagged_D4"][level].append(r["instance"])
                        flags.setdefault((r["machine"], r["instance"]), {})[level] = reg
        groups[g] = sec
    for r in res["instances"]:
        for level in flags.get((r["machine"], r["instance"]), {}):
            if r[level].get("refuted"):
                r[level] = dict(r[level], premise_flagged_D4=True)
                continue
            r[level] = dict(r[level], counted=False, premise_flagged_D4=True)
    th = res["thresholds"]
    for g, v in res["groups"].items():
        rs = [r for r in res["instances"] if r["group"] == g]
        for level in ("K0", "K3"):
            counted = [r for r in rs if (r.get(level) or {}).get("counted")]
            ref = sorted(r["instance"] for r in counted if r[level].get("refuted"))
            v[level].update(counted=len(counted), refuted_instances=ref, verdict=word(len(counted), bool(ref), th[level][g]),
                            premise_flagged_D4=sorted(r["instance"] for r in rs if (r.get(level) or {}).get("premise_flagged_D4")))
    for level in ("K0", "K3"):
        vs = [res["groups"][g][level]["verdict"] for g in res["groups"]]
        res["family"][level] = "refuted" if "refuted" in vs else "established" if vs and all(x == "established" for x in vs) else "worded per group"
    res["d4_audit"] = dict(rule="proportional D4 (see analyze8.py)", assumption=ASSUMPTION, groups=groups)
    return rt(res)
