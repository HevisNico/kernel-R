"""The runs of stage P and their order on the two machines.

  python3 -I p_plan.py             print the two queues
  python3 -I p_plan.py manifest    write p_manifest.json: the hash of every input and the queues

Scope: full (SCOPE_P.json: f = 1.096). The queues are those of ../AMENDMENT_2.md, with the seven
secondary runs of ../AMENDMENT_3.md at the end of each, and without the run with resistance
(../AMENDMENT_4.md).

A run is made by a runner of research/circuit, unchanged:
  circuit   ../../circuit/run.py                                    cell runs and refresh runs
  cert      ../../circuit/certification/cert_run.py                 ramp, read, leak scan of the calibration, noisy test run
  uncond    ../../circuit/certification-unconditional/uncond_run.py leak scan and noiseless gain run of a cell
"""
import hashlib
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
CIRCUIT = HERE.parent.parent / "circuit"
LARGE, SMALL = [6065, 6002, 6074, 6051], [6082, 6003, 6031, 6030]
CELLS = dict(A=[6065, 6031, 6074, 6082], B=[6030, 6002, 6003, 6051])
CALIBRATION = dict(A=[5001, 5003, 5005, 5007], B=[5002, 5004, 5006, 5008])
LEAK_CALIBRATION = [5001, 5002]
NOISE_ID = 700000                   # noise identifier of the noisy test run of cell SEED: 700000 + SEED


def circuit(name, kind, *args):
    return dict(name=name, tool="circuit", kind=kind, args=list(args), section="tt", seed=None, noise=False)


def cert(name, stage, mode, seed=None, noise=False):
    return dict(name=name, tool="cert", stage=stage, mode=mode, section="tt_mm" if seed else "tt", seed=seed, noise=noise,
                noise_id=NOISE_ID + seed if noise else None)


def uncond(name, stage, mode, seed):
    return dict(name=name, tool="uncond", stage=stage, mode=mode, section="tt_mm", seed=seed, noise=False)


NOMINAL = dict(
    A=[circuit("nom_cell", "cell", "rel=1"), cert("nom_ramp", "preflight", "ramp"), cert("nom_read", "preflight", "read"),
       cert("nom_leak", "preflight", "leak")],
    B=[circuit("nom_refresh", "refresh", "100", "rlk=1e11", "rel=1"), circuit("nom_cell125", "cell", "temp=125", "rel=1"),
       circuit("nom_refresh125", "refresh", "60", "temp=125", "rel=1")])


def calibration_unit(seed):
    unit = [cert(f"c{seed}_train", "calibration", "train", seed), cert(f"c{seed}_ramp", "calibration", "ramp", seed)]
    if seed in LEAK_CALIBRATION:
        unit.append(cert(f"c{seed}_leak", "calibration", "leak", seed))
    return unit


def cell_unit(seed):
    return [cert(f"t{seed}_ramp", "characterization", "ramp", seed), cert(f"t{seed}_read", "characterization", "read", seed),
            uncond(f"u{seed}_leak", "scan", "leak", seed), uncond(f"u{seed}_train", "gain", "train", seed),
            cert(f"t{seed}_train", "test", "train", seed, noise=True)]


def queues():
    """machine -> ordered list of runs. Each run carries its analysis: primary or secondary."""
    out = {}
    for m in ("A", "B"):
        q = [dict(r, analysis="primary") for r in NOMINAL[m]]
        for cal, cell in zip(CALIBRATION[m], CELLS[m]):
            q += [dict(r, analysis="primary") for r in calibration_unit(cal) + cell_unit(cell)]
        q += [dict(r, name="s_" + r["name"], analysis="secondary") for r in NOMINAL[m]]
        out[m] = q
    return out


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


INPUTS = ["circuit/cell.spice", "circuit/blocks.spice", "circuit/run.py", "circuit/analyze.py", "circuit/campaign.py", "circuit/noise.json",
          "circuit/spiceinit.txt", "circuit/bridge_check/runtime/spinit", "circuit/certification/cert_run.py",
          "circuit/certification/cert_analyze.py", "circuit/certification/calibration.json",
          "circuit/certification-unconditional/uncond_run.py", "circuit/certification-unconditional/uncond_early.py",
          "circuit/certification-unconditional/uncond_analyze.py", "circuit/certification-unconditional/uncond_amend1.py",
          "circuit/repetition/fakepid.c", "reusable-controller/physical/asymmetric_check.py",
          "sky130-layout/phase1/netlist.py", "sky130-layout/phase1/p_shim/ngspice", "sky130-layout/phase1/p_areas.csv",
          "sky130-layout/phase1/p_caps_primary.csv", "sky130-layout/phase1/p_caps.csv", "sky130-layout/phase1/p_plan.py",
          "sky130-layout/phase1/p_run.py", "sky130-layout/phase1/SCOPE_P.json"]


def manifest(ngspice="/usr/bin/ngspice", models=None):
    models = models or CIRCUIT / "pdk"
    commit = subprocess.run(["git", "-C", str(models), "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
    q = queues()
    return dict(stage="P", scope="full", prediction_sha256=digest(HERE.parent / "PREDICTION.md"),
                ngspice_path=ngspice, ngspice_sha256=digest(ngspice), pdk_commit=commit,
                inputs={p: digest(HERE.parent.parent / p) for p in INPUTS},
                queues={m: [r["name"] for r in q[m]] for m in q}, runs={r["name"]: r for m in q for r in q[m]})


if __name__ == "__main__":
    import os
    if len(sys.argv) > 1 and sys.argv[1] == "manifest":
        m = manifest(os.environ.get("P1_NGSPICE", "/usr/bin/ngspice"), Path(os.environ["MODELS"]) if os.environ.get("MODELS") else None)
        (HERE / "p_manifest.json").write_text(json.dumps(m, indent=1) + "\n")
        print("p_manifest.json written:", {k: len(v) for k, v in m["queues"].items()}, "runs")
    else:
        for m, q in queues().items():
            print("machine", m, f"({len(q)} runs):", " ".join(r["name"] for r in q))
