"""One run of campaign 4, as the launch kit starts it.

  run4.py --out DIR --ngspice BIN --pdk DIR --id ID --seed S|none --kind cal --guard on|off
  run4.py ... --kind extract --cell a --state hold --port 1|none --isolation 0|1 --reuse-trip 0|1 --instances I
  run4.py ... --kind extract --state all --reuse-trip 0|1 --seed none   the single-run extraction (rehearsal, nominal cell)
  run4.py ... --kind network --needs 4,4,4,4 --control skew|untrained|none --noise none|device|injected
              [--round n --extraction FILE --extraction-sha256 HEX] [--scale 0 (rehearsal, nominal cell)]

Written in DIR: what the simulation recorded of itself (`result.json`, or `part.json` for an extraction part),
`record.json` (what was asked, that the run reached its last date, the SHA-256 of its files, the simulator's peak
memory) and `noise.sha256`, the fingerprint of the noise the run drew: the SHA-256 of its samples under the device
model, of its first trnoise values under the injected model, of zeros without noise, and of the text "no transient
noise" for an extraction. No word, output or score is computed or printed here.

Seed guard (PREDICTION.md, Noise-model extraction): a mismatch seed is accepted only if it is one of 7501 to
7500 + I (I from --instances, which the manifests take from BEFORE_M.md) and the run is inside a launch of the
kit (its folder holds the record the kit wrote for it, status `started`, in the STATE.json of the folder above).
The nominal cell (no seed) is for the rehearsal.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import resource
import sys
import time

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE / "noise"))
import c4                                               # noqa: E402
import noisemodel                                       # noqa: E402
import plans4                                           # noqa: E402
import session4                                         # noqa: E402
from session4 import net, measure                       # noqa: E402

NOISE_SAMPLES = 64
NO_NOISE = hashlib.sha256(b"no transient noise").hexdigest()


def inside_kit(out):
    state = Path(out).parent / "STATE.json"
    if not state.exists():
        return False
    s = json.loads(state.read_text())
    return s.get("status") == "running" and any(r.get("id") == Path(out).name and r.get("status") == "started" for r in s.get("records", []))


def guard(seed, instances, out):
    if seed is None:
        return
    assert instances >= 1 and c4.FIRST_SEED <= seed < c4.FIRST_SEED + instances, f"seed {seed} is not one of 7501 to 7500 + {instances}"
    assert inside_kit(out), "a mismatch seed of campaign 4 runs only inside a launch of the kit"


def trnoise_fingerprint(tr, cells):
    names = [v for c in cells for v in [f"v(x{c}.nzm)"] + [f"v(x{c}.x{p}.{n})" for p in net.PORTS for n in ("nzo", "nzc")]]
    grid = net.NOISE_STEP * np.arange(1, NOISE_SAMPLES + 1)
    values = np.rint(np.column_stack([np.interp(grid, tr.t, tr.v[v]) for v in names]) * 1e9).astype("<i8")
    return hashlib.sha256(np.ascontiguousarray(values).tobytes()).hexdigest()


def unlink_pdk_links(folder):
    for p in sorted(Path(folder).rglob("pdk")):
        if p.is_symlink():
            p.unlink()


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def run(a):
    began = time.time()
    out = Path(a.out)
    seed = None if a.seed == "none" else int(a.seed)
    guard(seed, a.instances, out)
    section = "tt" if seed is None else c4.SECTION
    rec = dict(id=a.id, kind=a.kind, section=section, seed=seed)
    if a.kind == "extract":
        import devnoise, pilot
        pilot.ALLOWED_SEEDS = (seed,) if seed is not None else ()
        devnoise.REUSE_TRIP = bool(a.reuse_trip)
        out.mkdir(parents=True, exist_ok=True)
        if a.state == "all":
            assert seed is None, "the single-run extraction is for the rehearsal on the nominal cell only"
            devnoise.extract(out / "work", out / "extraction.json", section, seed, list(c4.CELLS), a.ngspice, a.pdk, list(noisemodel.MODEL_STATES))
            unlink_pdk_links(out)
            rec.update(state="all", reuse_trip=bool(a.reuse_trip), reached_its_last_date=True, files={"extraction.json": sha(out / "extraction.json")})
        else:
            port = None if a.port == "none" else int(a.port)
            part = devnoise.extract_part(out / "work", out / "part.json", section, seed, list(c4.CELLS), a.cell, a.state, port,
                                         bool(a.isolation), a.ngspice, a.pdk)
            unlink_pdk_links(out)
            rec.update(cell=a.cell, state=a.state, port=port, isolation=bool(a.isolation), reuse_trip=bool(a.reuse_trip),
                       outputs=len(part["outputs"]), reached_its_last_date=True, files={"part.json": sha(out / "part.json")})
        mark = NO_NOISE
    else:
        if a.kind == "cal":
            plan, reads = plans4.calibration()
            text = net.deck(cells=c4.CELLS, section=section)
            noise_id = shim = None
            info = dict(model="none")
            guard_off = a.guard == "off"
            rec.update(guard=a.guard, reads=reads)
        else:
            needs = tuple(int(x) for x in a.needs.split(","))
            control = None if a.control == "none" else a.control
            plan, slots = plans4.network(needs, control)
            guard_off, noise_id, shim, files = False, None, None, []
            horizon = session4.at(plan["horizon"]) + 50e-6
            if a.noise == "device":
                extraction = json.loads(Path(a.extraction).read_text())
                assert sha(a.extraction) == a.extraction_sha256, "not the extraction PREDICTED.json records"
                noisemodel.use_codemodel()
                (out / "samples").mkdir(parents=True)
                ns = c4.noise_seed(seed, a.round)
                position = c4.POSITIONS[f"n{a.round}"]
                assert a.scale == "1" or seed is None, "the zero-amplitude run is for the rehearsal on the nominal cell only"
                text, files, info = noisemodel.device_text(net.deck(cells=c4.CELLS, section=section), extraction, c4.CELLS, ns,
                                                           c4.instance_key(seed), position, horizon, out / "samples" / "nz", a.scale)
                info["extraction_sha256"] = a.extraction_sha256
            elif a.noise == "injected":
                out.mkdir(parents=True, exist_ok=True)
                shim, shim_info = noisemodel.shim(out)
                noise_id = c4.noise_seed(seed, a.round)
                text = net.deck(cells=c4.CELLS, section=section, noise=True)
                info = dict(model="injected", noise_seed=noise_id, imposed_process_number=noise_id, shim=shim_info)
            else:
                text = net.deck(cells=c4.CELLS, section=section)
                info = dict(model="none")
            rec.update(needs=list(needs), control=control, round=a.round if a.noise != "none" else None, slots=len(slots))
        result, tr = session4.play(out / "evidence", plan, text, a.ngspice, a.pdk, seed=seed, guard_off=guard_off, noise_id=noise_id, shim=shim)
        (out / "evidence" / "pdk").unlink()
        reached = bool(tr.t[-1] >= result["horizon_s"] - 1e-9)
        if info["model"] == "device":
            mark, each = noisemodel.samples_sha256(files)
            info["samples_sha256"], info["samples_files_sha256"] = mark, each
            for f in files:
                f.unlink()
            (out / "samples").rmdir()
        else:
            mark = trnoise_fingerprint(tr, c4.CELLS)
        if shim is not None:
            Path(shim).unlink()
        ev = out / "evidence"
        rec.update(noise=info, reached_its_last_date=reached, horizon_s=result["horizon_s"], waveform_ends_s=result["waveform_ends_s"],
                   points=result["points"], files={x: sha(ev / x) for x in ("input.spice", "session.log", "trace.raw", "result.json")})
    rec.update(noise_fingerprint=mark, wall_s=time.time() - began,
               peak_rss_MB=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss / 1024)
    (out / "noise.sha256").write_text(mark + "\n")
    (out / "record.json").write_text(json.dumps(rec, indent=1) + "\n")
    assert rec["reached_its_last_date"], "the waveform ends before the last date of the run"
    return rec


def main():
    p = argparse.ArgumentParser(description=__doc__)
    for name in ("out", "ngspice", "pdk"):
        p.add_argument("--" + name, type=Path, required=True)
    p.add_argument("--id", required=True)
    p.add_argument("--kind", choices=("cal", "extract", "network"), required=True)
    p.add_argument("--seed", required=True)
    p.add_argument("--instances", type=int, default=0)
    p.add_argument("--guard", choices=("on", "off"))
    p.add_argument("--cell", choices=c4.CELLS)
    p.add_argument("--state", choices=noisemodel.MODEL_STATES + ("all",))
    p.add_argument("--port", default="none")
    p.add_argument("--isolation", type=int, default=0)
    p.add_argument("--reuse-trip", type=int, default=0)
    p.add_argument("--needs")
    p.add_argument("--control", default="none", choices=("none", "skew", "untrained"))
    p.add_argument("--noise", default="none", choices=("none", "device", "injected"))
    p.add_argument("--round", type=int, default=0)
    p.add_argument("--extraction")
    p.add_argument("--extraction-sha256")
    p.add_argument("--scale", default="1", choices=("1", "0"))
    r = run(p.parse_args())
    print(json.dumps(dict(id=r["id"], kind=r["kind"], reached_its_last_date=r["reached_its_last_date"], wall_s=round(r["wall_s"]))))


if __name__ == "__main__":
    main()
