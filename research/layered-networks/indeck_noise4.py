"""The kit's in-deck inverter gate with the K3 allowance of noise4_budget.json (the owner's decision of 2026-11-25,
relayed by the coordinator). Development only. New file; the kit (research/inverter-instances, invinst) is unchanged.

  indeck_noise4.py KIT_PKG BUDGET.json OUTDIR --deck DECK --seed S [--inverters ...]

Runs `python -m invinst.indeck OUTDIR --deck DECK --seed S ...` in KIT_PKG (research/circuit/inverter/instances),
with noise4_gate/ first on PYTHONPATH and LAYERED_K3_BUDGET, LAYERED_KIT_PKG set: in the parent and in every per-inverter
job, the kit's unchanged gate receives K0's allowance as before and, at K3, the budget's allowance_K3
(delta 2506/10^6, eta 2597/10^6 in x at 458bc7a). Afterwards every gate file under OUTDIR/*/gates must record exactly
that K3 allowance, else exit 1. Writes OUTDIR/K3_BUDGET.json: the budget's sha256, its allowance_K3, and the check.
"""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent


def main(pkg, budget, outdir, *rest):
    pkg, budget, outdir = Path(pkg).resolve(), Path(budget).resolve(), Path(outdir).resolve()
    b = json.loads(budget.read_text())
    env = dict(os.environ, PYTHONPATH=str(HERE / "noise4_gate") + os.pathsep + os.environ.get("PYTHONPATH", ""),
               LAYERED_K3_BUDGET=str(budget), LAYERED_KIT_PKG=str(pkg))
    r = subprocess.run([sys.executable, "-m", "invinst.indeck", str(outdir), *rest], cwd=pkg, env=env)
    from fractions import Fraction as F
    want = {k: F(v) for k, v in b["allowance_K3"].items()}
    seen, bad = [], []
    for f in sorted(outdir.rglob("*.json")):
        try:
            d = json.loads(f.read_text())
        except ValueError:
            continue
        al = d.get("allowance") if isinstance(d, dict) else None
        if isinstance(al, dict) and "K3" in al:
            seen.append(str(f.relative_to(outdir)))
            if {k: F(v) for k, v in al["K3"].items()} != want:        # exact fractions (the gate reduces them)
                bad.append(dict(file=str(f.relative_to(outdir)), K3=al["K3"]))
    ok = r.returncode == 0 and bool(seen) and not bad
    (outdir / "K3_BUDGET.json").write_text(json.dumps(dict(
        budget_file=budget.name, budget_sha256=hashlib.sha256(budget.read_bytes()).hexdigest(), allowance_K3={k: str(v) for k, v in want.items()},
        gate_files_checked=seen, mismatches=bad, ok=ok), indent=1, sort_keys=True) + "\n")
    print(json.dumps(dict(ok=ok, checked=len(seen), mismatches=bad, indeck_exit=r.returncode)))
    return ok


if __name__ == "__main__":
    sys.exit(0 if main(*sys.argv[1:]) else 1)
