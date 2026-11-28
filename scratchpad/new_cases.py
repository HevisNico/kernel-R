

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
    - A2 a round stopped by its own check (noisy_record status "failed: ...", the comparison recomputed): K3 refuted, in
      its own row; and a simulator end is not;
    - A1(ii) that refutation with a defective seal (D/prediction.json changed): still refuted, flagged seal_defect;
    - B1/B2 an extra file in the seal folder: a seal defect (held → not sealed);
    - B9 a root without DONE: analysed, "root not finished" at the top;
    - A7 the expected U control, present and passed;
    - B16/D8 a draw that is not draw_seeds.draw of its beacon refuses; a real one (quicknet round 1000000, its
      signature verified) goes on and refuses the root's plan as none of the expected plans; one changed signature
      byte refuses."""
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

    def stopped(label, status, seal_changed=False):
        r = copy_root(base, w.wd / f"root_h_{label}")
        d = r / "NOT1_6212"
        rec = json.loads((d / "N2" / "noisy_record.json").read_text())
        rec["status"] = status
        (d / "N2" / "noisy_record.json").write_text(json.dumps(rec, indent=1, default=str) + "\n")
        recompare(d, 2)
        if seal_changed:
            p = json.loads((d / "D" / "prediction.json").read_text())
            p["env_note"] = "changed (test)"
            (d / "D" / "prediction.json").write_text(json.dumps(p, indent=1, sort_keys=True) + "\n")
        reseal(r)
        return r

    ra = stopped("a2", "failed: the tail leak must be set before it starts")
    a, res = run_analysis(w, "h_a2", ra, "times=bare")
    cnt = ((res or {}).get("counts") or {}).get("NOT1", {}).get("K3", {})
    lst = (cnt.get("refuted_stopped_by_own_check") or {}).get("list")
    oks.append(a.returncode == 0 and check(checks, "A2: stopped by its own check is refuted, own row", json.dumps(lst),
                                           '["NOT1_6212"]', ra, ra.exists())
               and res["groups"]["NOT1"]["K3"]["verdict"].startswith("refuted"))
    out["A2"] = dict(rc=a.returncode, stderr=a.stderr.strip()[-300:], K3=cnt, verdict=(res or {}).get("groups", {}).get("NOT1", {}).get("K3", {}).get("verdict"))
    rs = stopped("a2sim", "failed: the simulator ended during: tran 1n 2n")
    a, res = run_analysis(w, "h_a2sim", rs, "times=bare")
    cnt = ((res or {}).get("counts") or {}).get("NOT1", {}).get("K3", {})
    nc = [x["instance"] for x in (cnt.get("not_completed") or {}).get("list", [])]
    oks.append(a.returncode == 0 and check(checks, "A2: a simulator end is not completed, not refuted", json.dumps(nc),
                                           '["NOT1_6212"]', rs, rs.exists()))
    out["A2_simulator_end"] = dict(rc=a.returncode, K3=cnt)
    r1 = stopped("a1", "failed: the tail leak must be set before it starts", seal_changed=True)
    a, res = run_analysis(w, "h_a1", r1, "times=bare")
    row = next((x for x in (res or {}).get("instances", []) if x["instance"] == "NOT1_6212"), {})
    oks.append(a.returncode == 0 and check(checks, "A1(ii): refuted with a defective seal, flagged", json.dumps(row.get("K3")),
                                           '"seal_defect": true', r1, r1.exists())
               and row["K3"].get("refuted") is True and row["K3"].get("counted") is True
               and (row.get("K0") or {}).get("not_sealed") is True)
    out["A1ii"] = dict(rc=a.returncode, K0=row.get("K0"), K3=row.get("K3"), seal=row.get("seal"))

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
    import draw_seeds
    br = dict(round=1000000, randomness="b22aad4794f7451896f7a371aa46106fd84d919f3f569acd5b2fddf1d1440af3",
              signature="83ad29e4c409f9470fc2ef02f90214df49e02b441a1a241a82d622d9f608ef98fd8b11a029f1bee9d9e83b45088abe72")
    ex = json.loads((HERE / "EXCLUDED.json").read_text())
    good = dict(draw_seeds.draw(br["randomness"], 1000000, ex, dict(NOT1=60, ANDOR3=32, XOR3=37)), beacon_round=br)
    gd = w.wd / "DRAW_good.json"
    gd.write_bytes(draw_seeds.canon(good))
    bad = dict(good, groups=dict(good["groups"], NOT1=[6212] + good["groups"]["NOT1"][1:]))
    bd = w.wd / "DRAW_forged.json"
    bd.write_bytes(draw_seeds.canon(bad))
    sg = dict(good, beacon_round=dict(br, signature=br["signature"][:-2] + ("00" if br["signature"][-2:] != "00" else "11")))
    sd = w.wd / "DRAW_badsig.json"
    sd.write_bytes(draw_seeds.canon(sg))
    refused("B16: a forged draw", "DRAW.json is not draw_seeds.draw of its beacon and round", base, "times=bare",
            f"draw={bd}", target=bd)
    refused("B16: one changed signature byte", "the beacon round does not verify", base, "times=bare", f"draw={sd}",
            target=sd)
    refused("B16/D8: a verified draw, the root's plan is none of the expected plans", "PLAN_INPUT.json is none of the "
            "expected plans of the draw", base, "times=bare", f"draw={gd}", target=gd)
    out["checks"] = checks
    return all(oks), out
