

# ================================================================================================ 8. counts (analyze9)

def never_run(r, lv):
    steps = r.get("steps") or {}
    need = [k for k in (ORDER[:7] if lv == "K0" else ORDER) if not (k == "inverters" and r["group"] == "ANDOR3")]
    miss = next((k for k in need if k not in steps), None)
    return dict(step=miss, status="not run")


def layer_counts(res, sizes):
    failed = {}
    for f in res.get("run_failed", []):
        levels = ("K0", "K3") if f["level"] == "stage D" else (f["level"],)
        for lv in levels:
            failed.setdefault((f.get("machine"), f["instance"], lv), f.get("first_failing"))
    out = {}
    for g in sorted(res["groups"]):
        rs = sorted((r for r in res["instances"] if r["group"] == g), key=lambda r: (r["machine"], r["instance"]))
        out[g] = {}
        for lv in ("K0", "K3"):
            row = {k: [] for k in ROWS}
            for r in rs:
                x = r.get(lv) or {}
                name = r["instance"]
                if r.get("not_run"):
                    row["not_run"].append(dict(instance=name, machine=r["machine"], why=r.get("why")))
                elif x.get("counted") and x.get("refuted") and x.get("stopped_by_own_check"):
                    row["refuted_stopped_by_own_check"].append(name)
                elif x.get("counted") and x.get("refuted"):
                    row["refuted"].append(name)
                elif x.get("counted"):
                    row["held"].append(name)
                elif x.get("premise_flagged_D4"):
                    row["premise_flagged_D4"].append(name)
                elif x.get("not_sealed"):
                    row["not_sealed"].append(dict(instance=name, verdicts={
                        k: (c or {}).get("verdict") for k, c in sorted((r.get("comparisons") or {}).items())}))
                elif (r["machine"], name, lv) in failed:
                    ff = failed[(r["machine"], name, lv)] or never_run(r, lv)
                    row["not_completed"].append(dict(instance=name, step=ff.get("step"), status=ff.get("status")))
                else:
                    row["no_prediction"].append(name)
            n = {k: len(v) for k, v in row.items()}
            if sum(n.values()) != len(rs):
                refuse(f"the counts of {g} {lv} do not sum to its instances: {n} vs {len(rs)}")
            if sizes is not None and len(rs) != sizes[g]:
                refuse(f"{g} has {len(rs)} instances in the analysis, not the drawn size {sizes[g]}")
            out[g][lv] = dict(instances=len(rs), counted=n["held"] + n["refuted"] + n["refuted_stopped_by_own_check"],
                              **{k: dict(n=n[k], list=row[k]) for k in ROWS})
    res["counts"] = out
    for g, v in res["counts"].items():
        for lv in ("K0", "K3"):
            if v[lv]["counted"] != res["groups"][g][lv]["counted"]:
                refuse(f"the counts of {g} {lv} differ from the verdict's: {v[lv]['counted']} vs "
                       f"{res['groups'][g][lv]['counted']}")
    return rt(res)


# ================================================================================================ the checks around it

def root_driver(root):
    """(driver sha256, template sha256, mode) a root records, or Nones for a root of the old chain."""
    env = json.loads((Path(root) / "ENV.json").read_text()) if (Path(root) / "ENV.json").exists() else {}
    c = env.get("campaign") or {}
    return dict(driver_sha256=c.get("driver_sha256"), template_sha256=c.get("template_sha256"), mode=c.get("mode"))


def root_pins(root):
    """The FREEZE_PINS.json sha256 a root's driver checked (TEMPLATE_CHECK.json pins.pins_sha256), or None."""
    f = Path(root) / "TEMPLATE_CHECK.json"
    return (json.loads(f.read_text()).get("pins") or {}).get("pins_sha256") if f.exists() else None


def sums_of(roots):
    out = {}
    for k, root in enumerate(roots, start=1):
        files = sorted(p for p in Path(root).rglob("SHA256SUMS*")
                       if not any(x in NOT_WALKED for x in p.relative_to(root).parts))
        out[f"root_{k}"] = hashlib.sha256("".join(f"{sha(p)}  {p.relative_to(root)}\n" for p in files).encode()).hexdigest()
    return out


def kernel_library(outdir):
    r = E3.lean_resolution()                               # the real toolchain binary, not elan's proxy
    if r.get("sha256") != E3.LEAN_SHA256:
        refuse(f"the lean binary is not the pinned one ({E3.LEAN_SHA256[:12]}): {r.get('sha256')}")
    have = {f"{m}.lean": sha(CP.LEAN_DIR / f"{m}.lean") for m in CP.KERNEL_MODULES}
    if have != CP.KERNEL_SOURCES:
        refuse("the kernel's Lean sources differ from the pinned ones")
    return CP.build_kernel(outdir)


def check_draw(path, sizes, campaign):
    """B16 and D8: DRAW.json recomputed from its own beacon and round, the pinned EXCLUDED.json and the pinned sizes;
    the beacon round's signature verified against the pinned chain."""
    import beacon_chain
    import beacon_verify
    import draw_seeds
    b = Path(path).read_bytes()
    try:
        d = json.loads(b)
    except ValueError as e:
        refuse(f"DRAW.json is not JSON: {e}")
    br = d.get(DRAW_EXTRA_KEY)
    if not isinstance(br, dict) or set(br) != {"round", "signature", "randomness"}:
        refuse(f"DRAW.json has no {DRAW_EXTRA_KEY} {{round, signature, randomness}}")
    if not isinstance(d.get("beacon"), str) or not isinstance(d.get("round"), int):
        refuse("DRAW.json has no beacon string and round integer")
    ex = json.loads((HERE / "EXCLUDED.json").read_text())
    with contextlib.redirect_stdout(io.StringIO()):
        try:
            again = draw_seeds.draw(d["beacon"], d["round"], ex, dict(sizes))
        except AssertionError as e:
            refuse(f"the draw cannot be recomputed: {e}")
    want = draw_seeds.canon(dict(again, **{DRAW_EXTRA_KEY: br}))
    if b != want:
        refuse("DRAW.json is not draw_seeds.draw of its beacon and round on the pinned EXCLUDED.json at the pinned "
               f"sizes {sizes} (with its {DRAW_EXTRA_KEY} added), byte for byte")
    if br["round"] != d["round"] or br["randomness"].lower() != d["beacon"].lower():
        refuse(f"DRAW.json: the beacon is not the randomness of round {d['round']}")
    if not beacon_chain.check():
        refuse("the pinned quicknet chain does not check")
    v = beacon_verify.verify(beacon_chain.QUICKNET, br)
    if not v.get("ok"):
        refuse(f"DRAW.json: the beacon round does not verify against the pinned quicknet key: {v}")
    return d, dict(sha256=hashlib.sha256(b).hexdigest(), beacon=d["beacon"], round=d["round"], sizes=dict(sizes),
                   machines=MACHINES, excluded_sha256=d["excluded_sha256"], signature_verified=True)


def expected_plans(draw):
    import plan_split3
    t = json.loads(CP.FROZEN_TEMPLATE.read_text())
    plans, _ = plan_split3.split(draw, t, MACHINES)
    return {f"K{k:02d}": p for k, p in enumerate(plans, start=1)}, t


def match_plan(R, expected):
    """D8, B5: the root's PLAN_INPUT.json is byte for byte one expected plan; PLAN.json and PLAN_RESOLVED.json are
    that plan plus PLAN_LOCAL_KEYS, equal to TEMPLATE_CHECK.json's trees."""
    import plan_split
    b = R.bytes("PLAN_INPUT.json")
    if b is None:
        refuse(f"{R.path}: no PLAN_INPUT.json")
    hit = [k for k, p in expected.items() if plan_split.canon(p) == b]
    if len(hit) != 1:
        refuse(f"{R.path}: PLAN_INPUT.json is none of the expected plans of the draw")
    k = hit[0]
    plan = R.json("PLAN.json")
    if plan is None or R.bytes("PLAN_RESOLVED.json") != R.bytes("PLAN.json"):
        refuse(f"{R.path}: PLAN.json missing, or PLAN_RESOLVED.json differs from it")
    if {x: plan[x] for x in plan if x not in PLAN_LOCAL_KEYS} != rt(expected[k]) or set(PLAN_LOCAL_KEYS) - set(plan):
        refuse(f"{R.path}: PLAN.json is not the expected plan {k} plus {PLAN_LOCAL_KEYS}")
    tc = R.json("TEMPLATE_CHECK.json") or {}
    trees = tc.get("trees") or {}
    if {x: str(plan[x]) for x in PLAN_LOCAL_KEYS} != {x: str(trees.get(x)) for x in PLAN_LOCAL_KEYS}:
        refuse(f"{R.path}: PLAN.json's {PLAN_LOCAL_KEYS} differ from TEMPLATE_CHECK.json's trees")
    return k


def main(mode, outdir, *args):
    if sys.flags.optimize:                                 # A5
        refuse("Python runs with -O (sys.flags.optimize): run analysis.py without it")
    if mode not in ("campaign", "test"):
        refuse(f"mode {mode!r} is neither campaign nor test")
    campaign = mode == "campaign"
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
    rehearsal = kw.get("rehearsal")
    if rehearsal not in (None, "1"):
        refuse(f"rehearsal={rehearsal!r}: only rehearsal=1")
    sizes = DRAW_SIZES_REHEARSAL if rehearsal == "1" else DRAW_SIZES
    drivers = {f"root_{k}": root_driver(r) for k, r in enumerate(roots, start=1)}
    times = kw.get("times", "github")
    tf = Path(kw.get("thresholds", str(HERE / "thresholds.json"))).resolve()
    controls = kw.get("controls")
    pc = CP.pins_check()
    if campaign:
        if CP.pins_refusal(pc):
            refuse("campaign mode: " + CP.pins_refusal(pc))
        pinned = {p: h for fs in json.loads(CP.PINS.read_text())["groups"].values() for p, h in fs.items()}
        if tf != (HERE / "thresholds.json").resolve() or pinned.get("research/layered-networks/thresholds.json") != sha(tf):
            refuse("campaign mode reads the pinned thresholds.json only")
        if times != "github":                                          # B7
            refuse(f"campaign mode: times must be github, not {times!r}")
        if "draw" not in kw:
            refuse("campaign mode: draw=DRAW.json is required")
        noise_commit = json.loads(CP.FROZEN_TEMPLATE.read_text())["noise_commit"]
        trees = [p for p, h in CP.worktrees() if h == noise_commit and CP.git_head(p)[1]]
        if not trees:
            refuse(f"campaign mode: no clean worktree at the template's noise_commit {noise_commit[:12]}")
        want = (Path(trees[0]) / "research" / "layered-networks").resolve()
        if controls is not None and Path(controls).resolve() != want:
            refuse(f"campaign mode: controls must be the noise tree at {noise_commit[:12]} ({want})")
        controls = str(want)
        bad = [m for m, d in drivers.items() if d != dict(driver_sha256=sha(HERE / "campaign.py"),
                                                          template_sha256=CP.FROZEN_TEMPLATE_SHA256, mode="CAMPAIGN")]
        if bad:
            refuse(f"roots not run by this campaign.py on the frozen template in campaign mode: {bad}")
        bad = [f"root_{k}" for k, r in enumerate(roots, start=1) if root_pins(r) != pc["pins_sha256"]]
        if bad:
            refuse(f"roots whose driver checked another FREEZE_PINS.json than this tree's ({pc['pins_sha256'][:12]}): {bad}")
    elif rehearsal == "1" and "draw" not in kw:
        refuse("rehearsal=1 needs draw=")
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
    draw_info, notice, template_rule = None, [], None
    M = {}
    if "draw" in kw:
        draw, draw_info = check_draw(kw["draw"], sizes, campaign)
        expected, tmpl = expected_plans(draw)
        template_rule = tmpl["testError_rule"]
        by = {}
        for R in Rs:
            k = match_plan(R, expected)
            if k in by:
                refuse(f"two roots on machine {k}: {by[k].path} and {R.path}")
            by[k] = R
        for k, p in expected.items():
            M[k] = dict(R=by.get(k), plan=rt(p))
            if k not in by:
                notice.append(f"no root: {k} (its instances are not run)")
    else:
        for k, R in enumerate(Rs, start=1):
            plan = R.json("PLAN.json") or R.json("PLAN_INPUT.json")
            if plan is None:
                refuse(f"{R.path}: no PLAN.json")
            M[f"machine_{k}"] = dict(R=R, plan=plan)
        notice.append("no draw: the expected plans are each root's own PLAN.json (test mode, no draw=)")
    if campaign and template_rule is None:
        refuse("campaign mode: no expected plans")
    seen = {}
    for k, m in M.items():
        if m["R"] is None:
            continue
        check_folders(m["R"], m["plan"])
        if not m["R"].finished:
            notice.append(f"root not finished: {k}")
        for name, g, s in home_instances(m["plan"]):
            if (m["R"].path / name / "status.json").exists():
                if (g, s) in seen:
                    refuse(f"the home instance {g} {s} is in more than one root: {seen[(g, s)]} and {k}")
                seen[(g, s)] = k
    if rehearsal == "1":
        notice.insert(0, "REHEARSAL: not the campaign; its outcomes count for no claim")
    before = sums_of(roots)
    out.mkdir(parents=True, exist_ok=True)
    build = kernel_library(out)
    res = layer_seals(M, times, build, th, campaign, template_rule, out)
    res = layer_stage_n_seal_log(res, M, th)
    res = layer_thresholds(res, tf, th)
    res = layer_record_seal_log(res, M)
    res = layer_duplicates(res, M, controls)
    res = layer_d4(res, M)
    res = layer_counts(res, sizes if "draw" in kw else None)
    after = sums_of(roots)
    if after != before:
        refuse(f"a root's SHA256SUMS changed during the analysis: {before} -> {after}")
    detail = {}
    for k, m in M.items():
        R = m["R"]
        if R is None:
            detail[k] = dict(root=None)
            continue
        rr = R.json("RESULT.json") if R.finished else R.json("RESULT_INSTANCES.json") if R.instances_done else None
        detail[k] = dict(root=str(R.path), finished=R.finished, instances_done=R.instances_done,
                         job_errors=(rr or {}).get("job_errors"), stopped_for_disk=(rr or {}).get("stopped_for_disk"),
                         files_verified=len(R.verified), files_read=len(R.reads),
                         files_read_unmanifested=sorted(x for x in R.reads if x not in R.verified))
    pre = "REHEARSAL: " if rehearsal == "1" else ""
    for g, v in res["groups"].items():                    # A8 and the rehearsal, in the verdict lines
        note = ((res.get("d4_audit") or {}).get("groups") or {}).get(g, {}).get("note")
        for lv in ("K0", "K3"):
            v[lv]["verdict"] = pre + v[lv]["verdict"] + (f" ({note})" if note else "")
    res["family"] = {lv: pre + x for lv, x in res["family"].items()}
    res.update(format=FORMAT, analysis_sha256=sha(__file__),
               mode=("REHEARSAL " if rehearsal == "1" else "") + ("CAMPAIGN" if campaign else "TEST"),
               NOTICE=notice, draw=draw_info, machines_detail=detail, tips=tips,
               unmanifested_rule=UNMANIFESTED, own_check_rule=dict(prefix="failed: ", simulator_end=list(SIMULATOR_END)),
               stage_d_script_rule=RULE10, kernel_sources_sha256=CP.KERNEL_SOURCES, root_drivers=drivers,
               roots_sha256sums=dict(before=before, after=after), pins=pc)
    (out / "RESULTS.json").write_bytes(canon(res))
    listed = [out / "RESULTS.json"] + sorted((out / "activity").glob("*.json")) if (out / "activity").exists() else [out / "RESULTS.json"]
    (out / "SHA256SUMS").write_text("".join(f"{sha(p)}  {p.relative_to(out)}\n" for p in listed))
    print(json.dumps(dict(results_sha256=sha(out / "RESULTS.json"), mode=res["mode"], notice=notice,
                          counts={g: {lv: {k: (x[k]["n"] if isinstance(x[k], dict) else x[k]) for k in ("counted",) + ROWS}
                                      for lv, x in v.items()} for g, v in res["counts"].items()}), indent=1))
    return True


if __name__ == "__main__":
    if len(sys.argv) < 4:
        sys.exit(__doc__)
    sys.exit(0 if main(*sys.argv[1:]) else 1)
