"""The yield lot's inverter K3 room, regated under noise4's allowance (read-only; the audit, relayed 2026-11-25).
Development only.

Every stored lot gate file is read from the 12 branches evidence/yield-lot-K<nn>: results/K<nn>/<inst>/inv/n<j>/gates/
GATE_<seed>.json. Its K0 measures are regated twice with noise4.py's own functions (noise4.verdict, and the gate's
mirror at kit d599300 via noise4.gate_module):
- under the noise.json allowance, which must reproduce the stored K3 verdict;
- under noise4's allowance.
An instance has K3 room when it is eligible at K0, its R cells have room at K3 (D/prediction.json, unchanged by
noise4), and every inverter's K3 holds. Nothing is simulated.

  recount_noise4_lot.py NOISE_TREE_LAYERED_DIR REPO OUT.json
  (NOISE_TREE_LAYERED_DIR: research/layered-networks of research/layered-networks 458bc7a6; REPO: a clone with the 12
   yield-lot branches fetched as refs/remotes/origin/evidence/yield-lot-K<nn>)
"""
import json, subprocess, sys
from fractions import Fraction as F
from pathlib import Path
NZ = Path(sys.argv[1]); REPO = sys.argv[2]
sys.path.insert(0, str(NZ))
import noise4 as N4
g = N4.gate_module("d599300")
cfg = json.loads(N4.show("d599300", f"{N4.INV}/config.json"))
d, grid = g.design(cfg), F(cfg["gate"]["early_grid"])
t = {n: F(v) for n, v in cfg["gate"]["timing"].items()}
k_old = {n: F(v) for n, v in N4.BUDGET["allowance_K3_noise_json"].items()}
k_new = N4.allowance()
git = lambda *a: subprocess.run(["git", "-C", REPO, *a], capture_output=True, text=True, check=True).stdout
rows, reproduced = [], True
for k in range(1, 13):
    ref = f"origin/evidence/yield-lot-K{k:02d}"
    base_path = f"research/layered-networks/dev/yield_lot/results/K{k:02d}/"
    files = git("ls-tree", "-r", "--name-only", ref, base_path).split()
    insts = sorted({f[len(base_path):].split("/")[0] for f in files if "/D/prediction.json" in f})
    for inst in insts:
        grp, seed = inst.split("_")
        pred = json.loads(git("show", f"{ref}:{base_path}{inst}/D/prediction.json"))
        gates = sorted(f for f in files if f.startswith(f"{base_path}{inst}/inv/") and f.endswith(f"/gates/GATE_{seed}.json"))
        inv = []
        for gf in gates:
            G = json.loads(git("show", f"{ref}:{gf}"))
            base = {n: F(v) for n, v in G["measures"]["K0"].items() if n != "early"}
            v0, m0 = N4.verdict(g, d, base, k_old, t, grid)
            v1, m1 = N4.verdict(g, d, base, k_new, t, grid)
            same = v0["Premises"] == G["kernel"]["K3"]
            reproduced &= same
            inv.append(dict(gate=gf.split("/inv/")[1], eligible_K0=G["eligible_K0"], K3_stored=G["kernel"]["K3"],
                            K3_noise_json=v0["Premises"], K3_noise4=v1["Premises"], reproduced=same,
                            failing_noise4=[p for p, b in v1.items() if not b],
                            min_margin_noise4=min(m1.values()) if m1 else None))
        cells_room = all(not (c.get("K3") or {}).get("failing") for c in pred["cells"]) and pred["measured"]
        inv_k0 = all(x["eligible_K0"] for x in inv)
        rows.append(dict(machine=f"K{k:02d}", instance=inst, group=grp, eligible_K0=pred["eligible_K0"], room_K3_lot=pred["room_K3"],
                         inverters=inv, cells_room_K3=cells_room,
                         room_K3_noise4=pred["eligible_K0"] and cells_room and inv_k0 and all(x["K3_noise4"] for x in inv) if inv else pred["room_K3"]))
summ = {}
for grp in ("NOT1", "XOR3", "ANDOR3"):
    rs = [r for r in rows if r["group"] == grp]
    summ[grp] = dict(n=len(rs), room_K3_lot=sum(r["room_K3_lot"] for r in rs), room_K3_noise4=sum(r["room_K3_noise4"] for r in rs),
                     gained=[r["instance"] for r in rs if r["room_K3_noise4"] and not r["room_K3_lot"]],
                     lost=[r["instance"] for r in rs if r["room_K3_lot"] and not r["room_K3_noise4"]],
                     inverters=sum(len(r["inverters"]) for r in rs),
                     inverter_K3_noise_json=sum(x["K3_noise_json"] for r in rs for x in r["inverters"]),
                     inverter_K3_noise4=sum(x["K3_noise4"] for r in rs for x in r["inverters"]))
out = dict(reproduced_stored_K3=reproduced, allowance_noise_json=N4.BUDGET["allowance_K3_noise_json"],
           allowance_noise4=N4.BUDGET["allowance_K3"], groups=summ, rows=rows)
Path(sys.argv[3]).write_text(json.dumps(out, indent=1, default=str) + "\n")
print(json.dumps({k: v for k, v in out.items() if k != "rows"}, indent=1, default=str))
