"""Run list of the repetition campaign, from frozen.json. No simulation is run.

  rep_plan.py   -> manifest.json
"""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
REPEATS = 20


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    cert = json.loads((ROOT / "certification" / "manifest.json").read_text())
    frozen = json.loads((HERE / "frozen.json").read_text())
    m = {k: cert[k] for k in ("ngspice_path", "ngspice_version", "ngspice_sha256", "pdk_commit", "temperature_C", "source_sha256")}
    m = dict(kind="repetition campaign, rules in PREDICTION.md", **m)
    m["code_sha256"] = {"certification/cert_run.py": digest(ROOT / "certification" / "cert_run.py"),
                        "certification-unconditional/uncond_run.py": digest(ROOT / "certification-unconditional" / "uncond_run.py"),
                        "certification-unconditional/uncond_early.py": digest(ROOT / "certification-unconditional" / "uncond_early.py"),
                        "repetition/fakepid.c": digest(HERE / "fakepid.c"), "repetition/frozen.json": digest(HERE / "frozen.json")}
    m["added_signals"] = ["@m.x1.xmout.msky130_fd_pr__nfet_01v8[id]", "@m.x2.xmout.msky130_fd_pr__nfet_01v8[id]", "v(x1.nzi)", "v(x2.nzi)"]
    nominal = dict(section="tt", seed=None, noise=False, noise_id=None)
    accel = [dict(name=f"a_{tag}", mode="train", periods=22, tmax="200n", klu=klu, binary=binary, **nominal)
             for tag, klu, binary in (("base", False, False), ("klu", True, False), ("bin", False, True), ("klu_bin", True, True))]
    step = []
    for case, section, seed in (("nom", "tt", None), ("c5001", "tt_mm", 5001), ("c5002", "tt_mm", 5002)):
        for mode, periods in (("train", 22), ("leak", 41)):
            for tmax in ("400n", "200n", "100n", "50n"):
                step.append(dict(name=f"s_{case}_{mode}_{tmax}", mode=mode, periods=periods, tmax=tmax, section=section, seed=seed, noise=False, noise_id=None))
    preflight = [dict(name="p_trunc", mode="train", periods=6, section="tt", seed=None, noise=False, noise_id=900000),
                 dict(name="p_noise_a", mode="train", periods=4, section="tt", seed=None, noise=True, noise_id=900001),
                 dict(name="p_noise_b", mode="train", periods=4, section="tt", seed=None, noise=True, noise_id=900001),
                 dict(name="p_noise_c", mode="train", periods=4, section="tt", seed=None, noise=True, noise_id=900002)]
    cells = {}
    for p in frozen["ports"]:
        cells.setdefault(p["seed"], []).append([p["port"], p["m"]])
    repeat = []
    for rep in range(REPEATS):
        for seed in sorted(cells):
            last = max((m_ + 1) if port == 1 else (11 + m_) for port, m_ in cells[seed])   # period of read m of the last port
            repeat.append(dict(name=f"r{rep:02d}_t{seed}", rep=rep, machine="A" if rep % 2 == 0 else "B", mode="train", periods=last + 1,
                               section="tt_mm", seed=seed, noise=True, noise_id=(seed - 6000) * 100 + rep + 1, ports=sorted(cells[seed])))
    m["stages"] = dict(accel=accel, step=step, preflight=preflight, repeat=repeat)
    (HERE / "manifest.json").write_text(json.dumps(m, indent=1) + "\n")
    print({k: len(v) for k, v in m["stages"].items()}, "periods of the repetitions:", sum(r["periods"] for r in repeat),
          "distinct noise ids:", len({r["noise_id"] for r in repeat}))


if __name__ == "__main__":
    main()
