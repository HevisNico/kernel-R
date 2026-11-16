"""Campaign 4: the two noise models a noisy network run can use, chosen by BEFORE_M.json, not by this code.

- **device**: the noise study's device model (VALIDATION_CRITERIA.md, commit 5a24d10, section 1, items 2 to 6; its
  PROTOCOL.md for the validation's own runs). Per instance, the sources are built from the instance's merged
  extraction: per cell, the union of the devices kept at hold, window, fire and pulse, each with the A, B, ef and
  nodes of the state of its largest share; per port, the shot term 2qI (I = 173 nA) between dq and the stored node;
  sorted by name, devices first, then the shot terms. Each drives, through a VCCS of gain g = sqrt(A / 2 NT) / 1 mV,
  a node whose samples are `noise/noisegen.samples(noise_seed, index, n, A/g^2, B/g^2, ef,
  slow=(instance_key, k))`, the first sample 0, read by XSPICE `filesource` instances of 8 sources each, with
  `xtrtol=7`. This is the code of the noise study's `validation/vrun.py` (`model_sources`, `add_sources`) and
  `phase0/cost3.py` (`filesource`) at its released commit 74e93b4, copied here; only the paths differ.
- **injected**: the default of amendment 1, point 6 (the injected model of research/circuit/noise.py, as in
  campaigns 1 to 3): `trnoise` sources, seeded by the simulator's process number, which the run imposes with the
  `fakepid` shim of research/circuit/repetition (`noise_id` of net.Session), the noise seed as that number.
"""
import hashlib
import json
import math
from pathlib import Path
import subprocess
import sys

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE / "noise"))
sys.path.insert(0, str(HERE.parent / "network-circuit"))
import net                                              # noqa: E402
import noisegen                                         # noqa: E402  (noise/noisegen.py, the copy at 74e93b4)

CODEMODEL = "/usr/lib/x86_64-linux-gnu/ngspice/analog.cm"
ANALOG_CM_SHA256 = "98c7c296dfd04e81f568db91c8261a07f00d8d63e63e5cc1d331451ccda30941"
XTRTOL = "7"
FS_GROUP = 8
Q, IPK = 1.602176634e-19, 5e-12 * 0.5 * math.log(4) / 20e-6
MODEL_STATES = ("hold", "window", "fire", "pulse")
SHIM_SOURCE = HERE.parent / "circuit" / "repetition" / "fakepid.c"


def model_sources(extraction, cells):
    """The sources of the device model of an instance, from its merged extraction (a dict)."""
    best = {}
    for o in extraction["outputs"]:
        if o.get("error") or o["state"] not in MODEL_STATES or o["cell"] not in cells:
            continue
        for k in o["kept"]:
            if k["kind"] == "res":
                continue
            if k["device"] not in best or k["share"] > best[k["device"]]["share"]:
                best[k["device"]] = dict(k, state=o["state"])
    devs = [dict(name=d, nodes=best[d]["nodes"], A=best[d]["white_A2_Hz"], B=best[d]["flicker_B"],
                 alpha=best[d]["alpha"], state=best[d]["state"]) for d in sorted(best)]
    shots = [dict(name=f"shot.x{c}.x{p}", nodes=[f"x{c}.x{p}.dq", f"x{c}.vmem{p}"], A=2 * Q * IPK, B=0.0, alpha=1.0)
             for c in sorted(cells) for p in net.PORTS]
    return devs + shots


def columns(sources, noise_seed, instance_key, position, t_s):
    n = int(math.ceil(t_s / noisegen.NT)) + 2
    cols, gains = [], []
    for k, s in enumerate(sources):
        g = math.sqrt(s["A"] / (2 * noisegen.NT)) / 1e-3
        x = noisegen.samples(noise_seed, k, n, s["A"] / g ** 2, s["B"] / g ** 2, s["alpha"], slow=(instance_key, position))
        x[0] = 0.0
        cols.append(x)
        gains.append(g)
    return cols, gains


def write_samples(cols, stem):
    """The samples files of a run, FS_GROUP sources each; returns their paths in order."""
    assert str(stem) == str(stem).lower(), "ngspice lowercases the file name of a filesource: the path must be lowercase"
    t = np.arange(len(cols[0])) * noisegen.NT
    files = []
    for g in range(0, len(cols), FS_GROUP):
        f = Path(f"{stem}.{g // FS_GROUP}")
        np.savetxt(f, np.column_stack([t] + list(cols[g:g + FS_GROUP])), fmt="%.9g")
        files.append(f)
    return files


def deck_lines(sources, gains, stem, scale="1"):
    lines = []
    for k, (s, g) in enumerate(zip(sources, gains)):
        lines += [f"rnzp{k} nzp{k} 0 1k noisy=0", f"gnzp{k} {s['nodes'][0]} {s['nodes'][1]} nzp{k} 0 {g:.10g}"]
    for g in range(0, len(sources), FS_GROUP):
        m = len(sources[g:g + FS_GROUP])
        nodes = " ".join(f"%v(nzp{g + k})" for k in range(m))
        ones, zeros = " ".join([scale] * m), " ".join(["0"] * m)
        lines += [f"anz{g // FS_GROUP} [{nodes}] fsnz{g // FS_GROUP}",
                  f'.model fsnz{g // FS_GROUP} filesource (file="{stem}.{g // FS_GROUP}" amploffset=[{zeros}] amplscale=[{ones}] '
                  f"timeoffset=0 timescale=1 timerelative=false amplstep=false)"]
    return lines


def samples_sha256(files):
    """The SHA-256 of a run's samples: of the concatenation of its files, in order, and of each file."""
    h = hashlib.sha256()
    each = {}
    for f in files:
        b = Path(f).read_bytes()
        h.update(b)
        each[Path(f).name] = hashlib.sha256(b).hexdigest()
    return h.hexdigest(), each


def device_text(text, extraction, cells, noise_seed, instance_key, position, t_s, stem, scale="1"):
    """The deck with the device model's sources, the samples files written; returns (text, files, info)."""
    sources = model_sources(extraction, cells)
    cols, gains = columns(sources, noise_seed, instance_key, position, t_s)
    files = write_samples(cols, stem)
    lines = deck_lines(sources, gains, stem, scale)
    info = dict(model="device", sources=len(sources), source_names=[s["name"] for s in sources], noise_seed=noise_seed,
                instance_key=instance_key, position=position, samples_t_s=t_s, scale=scale)
    return text.replace("\n.end\n", "\n" + "\n".join(lines) + "\n.end\n"), files, info


def regenerate_sha256(extraction, cells, info, stem):
    """The analysis's check: the samples of a run, regenerated from its record, and their SHA-256 (files deleted)."""
    sources = model_sources(extraction, cells)
    assert [s["name"] for s in sources] == info["source_names"]
    cols, _ = columns(sources, info["noise_seed"], info["instance_key"], info["position"], info["samples_t_s"])
    files = write_samples(cols, stem)
    whole, _ = samples_sha256(files)
    for f in files:
        f.unlink()
    return whole


def use_codemodel():
    """Make every net.Session of this process load the XSPICE code models at start-up, with xtrtol = 7, as the noise
    study's cost3.py does (the code model is loaded before the deck, as ngspice requires)."""
    assert hashlib.sha256(Path(CODEMODEL).read_bytes()).hexdigest() == ANALOG_CM_SHA256, "not the pinned analog.cm"
    copy = net.shutil.copyfile

    def with_codemodel(src, dst, *a, **k):
        r = copy(src, dst, *a, **k)
        if Path(dst).name == ".spiceinit":
            with open(dst, "a") as f:
                f.write(f"codemodel {CODEMODEL}\nset xtrtol={XTRTOL}\n")
        return r
    net.shutil.copyfile = with_codemodel


def shim(folder):
    """The preloaded library that imposes the simulator's process number (injected model), built from fakepid.c into
    the run's folder; its SHA-256 and that of its source are recorded."""
    so = Path(folder) / "fakepid.so"
    subprocess.run(["gcc", "-shared", "-fPIC", "-O2", "-o", str(so), str(SHIM_SOURCE)], check=True)
    return so, dict(source_sha256=hashlib.sha256(SHIM_SOURCE.read_bytes()).hexdigest(),
                    library_sha256=hashlib.sha256(so.read_bytes()).hexdigest())
