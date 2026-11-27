"""One PLAN.json per machine from the drawn seeds (CAMPAIGN_PLAN_DRAFT.md §6–§7; PREDICTION draft, 2026-11-24).
Development only.

  plan_split.py DRAW.json TEMPLATE.json OUTDIR [m=12]       OUTDIR/PLAN_K01.json .. PLAN_K<m>.json, OUTDIR/SPLIT.json

- m machines, 8 ≤ m ≤ 12 (asserted). TEMPLATE.json gives the fields every plan shares (overlay, rule, trees and
  commits, rounds, stagen); each machine's `seal_push` branch is `evidence/combined-seals-K<nn>`.
- **Expected core-hours per instance** (COST, CPU-min, from the dry run and the validations [K], with the noisy rounds
  weighted by the expected room rate [G]): expected = gate + D + N0 + p_room × 3 × noisy round, plus the D4 audit's
  solo scans on audited instances.
- **The D4 audits**: every 6th instance of each group in draw order (positions 6, 12, 18, …) runs its stage D with its
  own solo scans (`groups[g]["d4_audit"]`).
- **Balancing**: longest-processing-time first. The instances in decreasing expected cost (ties by group, then draw
  order) each go to the machine with the least expected load so far (ties to the lowest number).
- **U**: per group, on the machine that holds the group's first drawn seed (`U_groups`). There it runs on that
  machine's first eligible instance of the group in seed order.
- **The duplicate**: per group, the group's first drawn instance has its N0 run again on another machine, the least
  loaded one other than its own (`remote_duplicates`). analyze3.py compares the two.
- Deterministic: the same inputs give the same files.
"""
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))

COST = dict(  # CPU-min per item [K: dry run 9804-9806, validations 9801/9803]; p_room [G: K3 rates of plan §3 with the one-port rule]
    NOT1=dict(gate=2.5, D=3.7, N0=1.5, noisy=2.0, p_room=0.79, d4=0.7),
    ANDOR3=dict(gate=0.0, D=50.0, N0=30.0, noisy=40.0, p_room=0.27, d4=45.0),
    XOR3=dict(gate=11.5, D=57.0, N0=42.0, noisy=62.0, p_room=0.25, d4=30.0),
)
SPECS = dict(NOT1="specs/not1.json", ANDOR3="specs/andor3.json", XOR3="specs/xor3.json")


def canon(obj):
    return (json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True) + "\n").encode()


def expected(g, audited):
    c = COST[g]
    return c["gate"] + c["D"] + c["N0"] + c["p_room"] * 3 * c["noisy"] + (c["d4"] if audited else 0.0)


def ordered_groups(draw):
    """The draw's groups in draw_seeds.GROUP_ORDER, never in the order of a dict's keys (a DRAW.json read back has
    them sorted, the draw in memory in its own order): one draw gives one split."""
    import draw_seeds
    gs = draw["groups"]
    if set(gs) - set(draw_seeds.GROUP_ORDER):
        raise ValueError(f"groups {sorted(set(gs) - set(draw_seeds.GROUP_ORDER))} are not of {draw_seeds.GROUP_ORDER}")
    return [(g, gs[g]) for g in draw_seeds.GROUP_ORDER if g in gs]


def split(draw, template, m=12):
    if not 8 <= m <= 12:
        raise ValueError(f"m = {m}: the plan allows 8 to 12 machines")
    groups = ordered_groups(draw)
    names = [g for g, _ in groups]
    items = []
    for g, seeds in groups:
        for pos, s in enumerate(seeds, start=1):
            audited = pos % 6 == 0
            items.append(dict(group=g, seed=s, pos=pos, audited=audited, cost=expected(g, audited)))
    order = sorted(items, key=lambda x: (-x["cost"], names.index(x["group"]), x["pos"]))
    load = [0.0] * m
    where = {}
    for x in order:
        k = min(range(m), key=lambda i: (load[i], i))
        load[k] += x["cost"]
        where[(x["group"], x["seed"])] = k
    plans = []
    for k in range(m):
        p = json.loads(json.dumps(template))
        p["what"] = f"campaign machine K{k + 1:02d} of {m}"
        p["groups"] = {}
        for g, seeds in groups:
            mine = [s for s in seeds if where[(g, s)] == k]
            if mine:
                aud = [x["seed"] for x in items if x["group"] == g and x["audited"] and where[(g, x["seed"])] == k]
                p["groups"][g] = dict(spec=SPECS[g], seeds=mine, d4_audit=aud)
        p["seal_push"] = dict(template.get("seal_push", {}), branch=f"evidence/combined-seals-K{k + 1:02d}")
        p["U_groups"], p["remote_duplicates"], p["controls"] = [], [], dict(duplicate={})
        plans.append(p)
    dup_load = list(load)
    for g, seeds in groups:
        first = seeds[0]
        home = where[(g, first)]
        plans[home]["U_groups"].append(g)
        other = min((i for i in range(m) if i != home), key=lambda i: (dup_load[i], i))
        plans[other]["remote_duplicates"].append(dict(group=g, spec=SPECS[g], seed=first))
        dup_load[other] += COST[g]["N0"]
    summary = dict(format="layered-split/1", machines=m, draw_sha256=None,
                   expected_core_h=[round(x / 60, 2) for x in dup_load],
                   max_core_h=round(max(dup_load) / 60, 2), total_core_h=round(sum(dup_load) / 60, 2),
                   per_machine={f"K{k + 1:02d}": dict(groups={g: len(v["seeds"]) for g, v in plans[k]["groups"].items()},
                                                      U_groups=plans[k]["U_groups"],
                                                      remote_duplicates=[f"{x['group']} {x['seed']}" for x in plans[k]["remote_duplicates"]],
                                                      d4_audit=sum(len(v["d4_audit"]) for v in plans[k]["groups"].values()))
                                for k in range(m)}, cost_model=COST)
    return plans, summary


def main(draw_path, template_path, outdir, *rest):
    m = int(dict(a.split("=") for a in rest).get("m", 12))
    draw = json.loads(Path(draw_path).read_text())
    template = json.loads(Path(template_path).read_text())
    plans, summary = split(draw, template, m)
    import hashlib
    summary["draw_sha256"] = hashlib.sha256(Path(draw_path).read_bytes()).hexdigest()
    out = Path(outdir)
    out.mkdir(parents=True, exist_ok=True)
    for k, p in enumerate(plans, start=1):
        (out / f"PLAN_K{k:02d}.json").write_bytes(canon(p))
    (out / "SPLIT.json").write_bytes(canon(summary))
    print(json.dumps(dict(machines=m, max_core_h=summary["max_core_h"], total_core_h=summary["total_core_h"],
                          per_machine=summary["expected_core_h"]), indent=1))
    return True


if __name__ == "__main__":
    sys.exit(0 if main(*sys.argv[1:]) else 1)
