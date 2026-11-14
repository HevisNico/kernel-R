"""Gathers the per-port measures of the instances into MEASURES.json: what each pulse did, and the hashes of the
decks and waveforms, which are not in Git. Phase 1, exploratory.

  collect.py DATA OUT.json SEED...

DATA holds `scan-<seed>-<cell><port>/result.json` (cellscan.py), `train-<seed>-quiet|noise/result.json`
(noisechar.py, 26 reads per port) and `short-<seed>-<k>/result.json` (noisechar.py with noise, 10 reads per
port, one simulator process each). No number is derived here: `constants.py` does that from MEASURES.json alone.
"""
import json
from pathlib import Path
import sys

KEEP = ("date_s", "kind", "fire", "latency", "protected_until_units", "protected_at_start", "step_mV", "error_phase_units")


def pulse(o, port):
    r = {k: o[k] for k in KEEP if k in o}
    r["u_before_mV"], r["u_after_mV"] = o[f"u{port}_before_V"] * 1e3, o[f"u{port}_after_V"] * 1e3
    return r


def main():
    data, out, seeds = Path(sys.argv[1]), Path(sys.argv[2]), sys.argv[3:]
    instances = {}
    for seed in seeds:
        scans = {}
        for name in ("a1", "a2", "b1", "b2"):
            r = json.loads((data / f"scan-{seed}-{name}" / "result.json").read_text())
            assert (r["seed"], r["cell"], str(r["port"])) == (int(seed), name[0], name[1])
            scans[name] = dict(pulses=[pulse(o, name[1]) for o in r["pulses"]], other_cell=r["idle"], wall_s=r["wall_s"],
                               deck_sha256=r["deck_sha256"], raw_sha256=r["raw_sha256"])
        def train(path, noise):
            r = json.loads(path.read_text())
            assert r["seed"] == int(seed) and r["deck"]["noise"] == noise and not r["still_queued_at_the_horizon"] and not r["calendar"]["edges"]
            assert all(o["delivered"] for o in r["occurrences"])
            return dict(run=path.parent.name, ports={name: [pulse(o, name[1]) for o in r["occurrences"] if f"{o['cell']}{o['port']}" == name] for name in scans},
                        calendar=r["calendar"]["name"], fires=len(r["fires"]), wall_s=r["wall_s"], simulated_s=r["calendar"]["horizon"] * 20e-6,
                        deck_sha256=r["deck_sha256"], raw_sha256=r["raw_sha256"])

        quiet = train(data / f"train-{seed}-quiet" / "result.json", False)
        noisy = [train(data / f"train-{seed}-noise" / "result.json", True)]
        noisy += [train(path, True) for path in sorted(data.glob(f"short-{seed}-*/result.json"))]
        instances[seed] = dict(section="tt_mm", seed=int(seed), scans=scans, quiet_train=quiet, noisy_trains=noisy)
    out.write_text(json.dumps(dict(what="per-port measures of the development instances of phase 1; see collect.py", instances=instances), indent=1) + "\n")


if __name__ == "__main__":
    main()
