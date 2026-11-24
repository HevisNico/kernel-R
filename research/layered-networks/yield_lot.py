"""The yield lot (YIELD_LOT_RULE.md): the per-machine plans, the report and the sizing rule. Development only.

  yield_lot.py plans TEMPLATE.json OUTDIR [m=12]          OUTDIR/PLAN_K<nn>.json (stage D only), OUTDIR/LOT.json
  yield_lot.py report OUTDIR ROOT [ROOT ...]              OUTDIR/YIELD.json: k/n with 90 % Wilson intervals per group
  yield_lot.py size YIELD.json OUT.json [ceiling=280] [machines=12]    the campaign sizes by YIELD_LOT_RULE_2.md §4
                                                     (machines only sets the window, 280 / (4 m) h; the sizes do not
                                                     depend on it; fewer than 8 machines: postponed)
"""
import json
import math
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import plan_split as PS  # noqa: E402

Z = 1.6449
SEEDS = dict(
    ANDOR3=[6102, 6104, 6106, 6108, 6110, 6123, 6125, 6129, 6130, 6131, 6133, 6135, 6136, 6137, 6143, 6144, 6147, 6150,
            6151, 6152, 6153, 6154, 6155, 6156],
    XOR3=[6157, 6158, 6159, 6164, 6165, 6166, 6173, 6174, 6175, 6177, 6178, 6179, 6180, 6181, 6182, 6185, 6187, 6190,
          6192, 6193, 6196, 6202, 6203, 6204],
    NOT1=[6212, 6213, 6217, 6218, 6219, 6220, 6223, 6225])
THRESHOLD = dict(K0=20, K3=5)
CAP = 80
NOT1_SIZE, NOT1_FALLBACK = 60, 40


def canon(obj):
    return (json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True) + "\n").encode()


def wilson(k, n, z=Z):
    if n == 0:
        return (0.0, 1.0)
    p = k / n
    den = 1 + z * z / n
    c = (p + z * z / (2 * n)) / den
    h = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / den
    return (max(0.0, c - h), min(1.0, c + h))


def stage_d_cost(g):
    c = PS.COST[g]
    return c["gate"] + c["D"]


def plans(template, m=12):
    assert sorted(set(s for v in SEEDS.values() for s in v)) == sorted(s for v in SEEDS.values() for s in v)
    items = sorted(((g, s) for g, v in SEEDS.items() for s in v), key=lambda x: (-stage_d_cost(x[0]), x[0], x[1]))
    load, where = [0.0] * m, {}
    for g, s in items:
        k = min(range(m), key=lambda i: (load[i], i))
        load[k] += stage_d_cost(g)
        where[(g, s)] = k
    out = []
    for k in range(m):
        p = json.loads(json.dumps(template))
        p.update(what=f"yield lot (YIELD_LOT_RULE.md), stage D only, machine K{k + 1:02d} of {m}; dev seeds, count for nothing",
                 steps_until="D", controls=dict(duplicate={}), rounds=3)
        p.pop("seal_push", None)
        p["groups"] = {g: dict(spec=PS.SPECS[g], seeds=[s for s in v if where[(g, s)] == k]) for g, v in SEEDS.items()
                       if any(where[(g, s)] == k for s in v)}
        out.append(p)
    return out, dict(machines=m, expected_core_h=[round(x / 60, 2) for x in load], total_core_h=round(sum(load) / 60, 2))


def report(roots):
    rows = {g: [] for g in SEEDS}
    for root in roots:
        for st in sorted(Path(root).glob("*/status.json")):
            s = json.loads(st.read_text())
            pf = st.parent / "D" / "prediction.json"
            p = json.loads(pf.read_text()) if pf.exists() else None
            fail = next(({"step": k, "status": v["status"]} for k, v in sorted(s["steps"].items()) if v["status"] != "done"), None)
            rows[s["group"]].append(dict(instance=st.parent.name, measured=bool(p and p["measured"]),
                                         eligible_K0=bool(p and p["eligible_K0"]), room_K3=bool(p and p["room_K3"]),
                                         first_failing_step=fail,
                                         failing={c["cell"]: dict(K0=(c.get("K0") or {}).get("failing"), K3=(c.get("K3") or {}).get("failing"),
                                                                  why_not_measured=c["why_not_measured"]) for c in (p["cells"] if p else [])}))
    out = {}
    for g, rs in rows.items():
        n = len(rs)
        k0 = sum(r["eligible_K0"] for r in rs)
        k3 = sum(r["room_K3"] for r in rs)
        clauses = {}
        for r in rs:
            for c, f in r["failing"].items():
                for lvl in ("K0", "K3"):
                    for cl in f[lvl] or []:
                        key = f"{lvl} {c} {cl.split(' (slack')[0]}"
                        clauses[key] = clauses.get(key, 0) + 1
        out[g] = dict(n=n, planned=len(SEEDS[g]), measured=sum(r["measured"] for r in rs),
                      eligible_K0=dict(k=k0, n=n, rate=k0 / n if n else None, wilson90=wilson(k0, n)),
                      room_K3=dict(k=k3, n=n, rate=k3 / n if n else None, wilson90=wilson(k3, n)),
                      failing_clauses=dict(sorted(clauses.items())), instances=sorted(rs, key=lambda r: r["instance"]))
    return out


def expected_cost(g, n, r3):
    c = PS.COST[g]
    per = c["gate"] + c["D"] + c["N0"] + r3 * 3 * c["noisy"]
    audits = (n // 6) * c["d4"]
    controls = c["N0"] + c["N0"]                     # U (about one N0) and the duplicate's N0
    return (n * per + audits + controls) / 60


def size(yld, ceiling=280.0, machines=12):
    if machines < 8:
        raise SystemExit(f"refused: {machines} machines; below 8 the campaign is postponed")
    y = {g: yld[g] for g in SEEDS}
    req, r3 = {}, {}
    for g in ("ANDOR3", "XOR3"):
        L0, L3 = y[g]["eligible_K0"]["wilson90"][0], y[g]["room_K3"]["wilson90"][0]
        n0 = math.ceil(THRESHOLD["K0"] / L0) if L0 > 0 else math.inf
        n3 = math.ceil(THRESHOLD["K3"] / L3) if y[g]["room_K3"]["k"] > 0 and L3 > 0 else math.inf
        req[g] = dict(N0=n0, N3=n3)
        r3[g] = y[g]["room_K3"]["rate"] or 0.0
    r3["NOT1"] = y["NOT1"]["room_K3"]["rate"] or 0.0
    N = {"NOT1": NOT1_SIZE}
    declared = []
    for g in ("ANDOR3", "XOR3"):
        if req[g]["N3"] == math.inf:
            declared.append(f"{g}: K3 not expected to be established (k3 = 0 in the lot)")
            want = req[g]["N0"]
        elif req[g]["N3"] > CAP:
            declared.append(f"{g}: K3 not expected to be established (N3 = {req[g]['N3']} > {CAP})")
            want = req[g]["N0"]
        else:
            want = max(req[g]["N0"], req[g]["N3"])
        N[g] = min(int(want) if want != math.inf else CAP, CAP)
    total = lambda: sum(expected_cost(g, N[g], r3[g]) for g in N)
    steps = [("XOR3", req["XOR3"]["N0"]), ("ANDOR3", req["ANDOR3"]["N0"])]
    for g, floor in steps:
        while total() > ceiling and N[g] > floor:
            N[g] -= 1
    turn = 0
    while total() > ceiling and (N["XOR3"] > 1 or N["ANDOR3"] > 1):
        g = ("XOR3", "ANDOR3")[turn % 2]
        if N[g] > 1:
            N[g] -= 1
        turn += 1
    for g in ("ANDOR3", "XOR3"):
        if req[g]["N3"] != math.inf and req[g]["N3"] <= CAP and N[g] < req[g]["N3"]:
            declared.append(f"{g}: K3 not expected to be established (cut to {N[g]} < N3 = {req[g]['N3']})")
        if N[g] < req[g]["N0"]:
            declared.append(f"{g}: K0 not expected to be established (cut to {N[g]} < N0 = {req[g]['N0']})")
    exp = {g: dict(N=N[g], expected_K0=round(N[g] * (y[g]["eligible_K0"]["rate"] or 0), 1),
                   expected_K3=round(N[g] * (y[g]["room_K3"]["rate"] or 0), 1), core_h=round(expected_cost(g, N[g], r3[g]), 1))
           for g in N}
    return dict(format="layered-sizes/2", ceiling_core_h=ceiling, machines=machines, window_h=round(ceiling / (4 * machines), 3),
                thresholds=THRESHOLD,
                requirements={g: {k: (None if v == math.inf else v) for k, v in r.items()} for g, r in req.items()},
                sizes=exp, total_core_h=round(total(), 1), declared_in_advance=sorted(set(declared)))


if __name__ == "__main__":
    c, *a = sys.argv[1:] or ["help"]
    if c == "plans":
        tmpl, outdir, *rest = a
        m = int(dict(x.split("=") for x in rest).get("m", 12))
        ps, summ = plans(json.loads(Path(tmpl).read_text()), m)
        Path(outdir).mkdir(parents=True, exist_ok=True)
        for k, p in enumerate(ps, start=1):
            (Path(outdir) / f"PLAN_K{k:02d}.json").write_bytes(canon(p))
        (Path(outdir) / "LOT.json").write_bytes(canon(dict(seeds=SEEDS, **summ)))
        print(json.dumps(summ))
    elif c == "report":
        outdir, *roots = a
        r = report(roots)
        Path(outdir).mkdir(parents=True, exist_ok=True)
        (Path(outdir) / "YIELD.json").write_bytes(canon(r))
        print(json.dumps({g: (v["eligible_K0"]["k"], v["room_K3"]["k"], v["n"]) for g, v in r.items()}))
    elif c == "size":
        yf, out, *rest = a
        kw = dict(x.split("=") for x in rest)
        r = size(json.loads(Path(yf).read_text()), float(kw.get("ceiling", 280)), int(kw.get("machines", 12)))
        Path(out).write_bytes(canon(r))
        print(json.dumps(r, indent=1))
    else:
        sys.exit(__doc__)
