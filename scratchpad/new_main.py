def main(mode, outdir, *args):
    if sys.flags.optimize:                                 # A5
        refuse("Python runs with -O (sys.flags.optimize): run analysis.py without it")
    if mode not in MODES:
        refuse(f"mode {mode!r} is none of {', '.join(MODES)}")
    strict = mode != "test"                                # campaign and rehearsal: every campaign-mode refusal
    args = [str(a) for a in args]
    kw = {}
    for a in args:                                          # A4
        if "=" in a:
            k, v = a.split("=", 1)
            if k not in KEYS:
                refuse(f"unknown argument {a!r} (keys: {', '.join(KEYS)}; a root path cannot contain '=')")
            if k in kw:
                refuse(f"argument {k} given twice")
            kw[k] = v
    roots = [Path(a).resolve() for a in args if "=" not in a]
    if not roots:
        refuse("no root")
    if len(set(roots)) != len(roots):                       # D9
        refuse(f"a root is given more than once: {sorted(str(r) for r in roots if roots.count(r) > 1)}")
    for r in roots:
        if not r.is_dir():
            refuse(f"{r} is not a folder")
    out = Path(outdir).resolve()
    for r in roots:
        if out == r or r in out.parents:
            refuse(f"OUTDIR {out} lies inside the root {r}")
    if out.exists() and (not out.is_dir() or any(out.iterdir())):     # B10
        refuse(f"OUTDIR {out} exists and is not an empty folder")
    drivers = {f"root_{k}": root_driver(r) for k, r in enumerate(roots, start=1)}
    times = kw.get("times", "github")
    tf = Path(kw.get("thresholds", str(HERE / "thresholds.json"))).resolve()
    controls = kw.get("controls")
    pc = CP.pins_check()
    if strict:
        if CP.pins_refusal(pc):
            refuse(f"{mode} mode: " + CP.pins_refusal(pc))
        pinned = {p: h for fs in json.loads(CP.PINS.read_text())["groups"].values() for p, h in fs.items()}
        if tf != (HERE / "thresholds.json").resolve() or pinned.get("research/layered-networks/thresholds.json") != sha(tf):
            refuse(f"{mode} mode reads the pinned thresholds.json only")
        if times != "github":                                          # B7
            refuse(f"{mode} mode: times must be github, not {times!r}")
        noise_commit = json.loads(CP.FROZEN_TEMPLATE.read_text())["noise_commit"]
        trees = [p for p, h in CP.worktrees() if h == noise_commit and CP.git_head(p)[1]]
        if not trees:
            refuse(f"{mode} mode: no clean worktree at the template's noise_commit {noise_commit[:12]}")
        want = (Path(trees[0]) / "research" / "layered-networks").resolve()
        if controls is not None and Path(controls).resolve() != want:
            refuse(f"{mode} mode: controls must be the noise tree at {noise_commit[:12]} ({want})")
        controls = str(want)
        bad = [m for m, d in drivers.items() if d != dict(driver_sha256=sha(HERE / "campaign.py"),
                                                          template_sha256=CP.FROZEN_TEMPLATE_SHA256, mode="CAMPAIGN")]
        if bad:
            refuse(f"roots not run by this campaign.py on the frozen template in campaign mode: {bad}")
        bad = [f"root_{k}" for k, r in enumerate(roots, start=1) if root_pins(r) != pc["pins_sha256"]]
        if bad:
            refuse(f"roots whose driver checked another FREEZE_PINS.json than this tree's ({pc['pins_sha256'][:12]}): {bad}")
        if "draw" not in kw:
            refuse(f"{mode} mode: draw=DRAW.json is required")
    th = json.loads(tf.read_text())
    tips = None
    if "tips" in kw:
        tips = dict(file=Path(kw["tips"]).name, sha256=sha(kw["tips"]), tips=json.loads(Path(kw["tips"]).read_text()))
    # D10: every manifest line of every root, before anything is read
    Rs = [Root(r) for r in roots]
    bad = {str(R.path): R.walk() for R in Rs}
    bad = {k: v for k, v in bad.items() if v}
    if bad:
        refuse("files that differ from their manifests, or are missing: " + json.dumps(bad)[:4000])
    # D8, D9: the machines
    out.mkdir(parents=True, exist_ok=True)
    draw_info, notice, template_rule, sizes = None, [], None, None
    M = {}
    if "draw" in kw:
        draw, draw_info, dn = check_draw(kw, mode, out)
        sizes = draw_info["sizes"]
        if dn:
            notice.append(dn)
        expected, tmpl = expected_plans(draw)
        template_rule = tmpl["testError_rule"]
        by = {}
        for R in Rs:
            k = match_plan(R, expected, strict)
            if k in by:
                refuse(f"two roots on machine {k}: {by[k].path} and {R.path}")
            by[k] = R
        for k, p in expected.items():
            M[k] = dict(R=by.get(k), plan=rt(p))
    else:
        for k, R in enumerate(Rs, start=1):
            plan = R.json("PLAN.json") or R.json("PLAN_INPUT.json")
            if plan is None:
                refuse(f"{R.path}: no PLAN.json")
            M[f"machine_{k}"] = dict(R=R, plan=plan)
        notice.append("no draw: the expected plans are each root's own PLAN.json (test mode, no draw=)")
    if strict and template_rule is None:
        refuse(f"{mode} mode: no expected plans")
    seen = {}
    for k, m in M.items():
        if m["R"] is None:
            continue
        check_folders(m["R"], m["plan"])
        for name, g, s in home_instances(m["plan"]):
            if (m["R"].path / name / "status.json").exists():
                if (g, s) in seen:
                    refuse(f"the home instance {g} {s} is in more than one root: {seen[(g, s)]} and {k}")
                seen[(g, s)] = k
    if mode == "rehearsal":
        notice.insert(0, "REHEARSAL: not the campaign; its outcomes count for no claim")
    before = sums_of(roots)
    build = kernel_library(out)
    res = layer_seals(M, times, build, th, strict, template_rule, out)
    res = layer_stage_n_seal_log(res, M, th)
    res = layer_thresholds(res, tf, th)
    res = layer_record_seal_log(res, M)
    res = layer_duplicates(res, M, controls)
    res = layer_d4(res, M)
    res = layer_counts(res, sizes)
    after = sums_of(roots)
    if after != before:
        refuse(f"a root's SHA256SUMS changed during the analysis: {before} -> {after}")
    notice += res.pop("machines_attention", [])
    detail = {}
    for k, m in M.items():
        R = m["R"]
        if R is None:
            detail[k] = dict(root=None)
            continue
        rr = R.json("RESULT.json") if R.finished else R.json("RESULT_INSTANCES.json") if R.instances_done else None
        detail[k] = dict(root=str(R.path), finished=R.finished, instances_done=R.instances_done,
                         job_errors=(rr or {}).get("job_errors"), stopped_for_disk=(rr or {}).get("stopped_for_disk"),
                         files_verified=len(R.verified), files_anchored_by_status=sorted(R.anchored),
                         files_read=len(R.reads), files_read_unmanifested=sorted(x for x in R.reads
                                                                                 if x not in R.verified and x not in R.anchored))
    pre = "REHEARSAL: " if mode == "rehearsal" else ""
    for g, v in res["groups"].items():                    # A8 and the rehearsal, in the verdict lines
        note = ((res.get("d4_audit") or {}).get("groups") or {}).get(g, {}).get("note")
        for lv in ("K0", "K3"):
            v[lv]["verdict"] = pre + v[lv]["verdict"] + (f" ({note})" if note else "")
    res["family"] = {lv: pre + x for lv, x in res["family"].items()}
    res.update(format=FORMAT, analysis_sha256=sha(__file__), mode=mode.upper(),
               NOTICE=notice, draw=draw_info, machines_detail=detail, tips=tips,
               unmanifested_rule=UNMANIFESTED, own_check_rule=dict(prefix="failed: ", simulator_end=list(SIMULATOR_END)),
               stage_d_script_rule=RULE10, kernel_sources_sha256=CP.KERNEL_SOURCES, root_drivers=drivers,
               roots_sha256sums=dict(before=before, after=after), pins=pc)
    (out / "RESULTS.json").write_bytes(canon(res))
    listed = [out / "RESULTS.json"] + (sorted((out / "activity").glob("*.json")) if (out / "activity").exists() else [])
    (out / "SHA256SUMS").write_text("".join(f"{sha(p)}  {p.relative_to(out)}\n" for p in listed))
    print(json.dumps(dict(results_sha256=sha(out / "RESULTS.json"), mode=res["mode"], notice=notice,
                          counts={g: {lv: {k: (x[k]["n"] if isinstance(x[k], dict) else x[k]) for k in ("counted",) + ROWS}
                                      for lv, x in v.items()} for g, v in res["counts"].items()}), indent=1))
    return True


