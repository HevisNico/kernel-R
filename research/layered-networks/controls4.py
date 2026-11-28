"""The versioned stage-N entry point, version 4: controls3's sealed stage N and untrained run, with the simulator's
trace written as controls2 writes it. Development only. New file: noise3.py, controls3.py and controls2.py stay as
pushed.

Why: noise3.stagen (so controls3 stagen) never wrote trace.raw or trace.digest.json, so tests/check_duplicate.py
reported every controls3 duplicate as differing on the missing trace. Here the stage-N run writes OUT/trace.raw at its
end with controls2.write_trace (ngspice `write`, then the digests in OUT/trace.digest.json), before the session closes.
Everything else is noise3's stage N: noise2's R-cell noise, the C5 inverters' budgeted noise, controls2's skew slots,
the same record (OUT/noisy_record.json) with the seal.
A noisy run also saves each inverter's three noise nodes (xn<j>.nzm, nzh<x>, nzj<x>) so that the injected sources
can be read from the trace. That adds vectors to trace.raw and changes nothing in the record.

  controls4.py stagen    SPEC OUT SEED ROUND seal_log=<40-hex> seal_branch=<branch> [scale=1] [overlay=FILE]
  controls4.py untrained SPEC OUT SEED       seal_log=<40-hex> seal_branch=<branch> [overlay=FILE]

Refusal and seal: as controls3 (exit 2 before any session; "seal_log": {commit, branch} in the record).
"""
import hashlib
import json
import os
from pathlib import Path
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import controls2  # noqa: E402
import controls3  # noqa: E402
import instrument  # noqa: E402
import noise2  # noqa: E402
import noise3  # noqa: E402
import run as runmod  # noqa: E402
import spec as specmod  # noqa: E402


def stagen(spec_path, out, seed, rnd, scale=1.0, overlay=None, extra=None, log=print):
    """noise3.stagen, with the noise nodes saved in a noisy run and the trace written before the session closes."""
    s, cfg, out = specmod.load(spec_path), noise3._cfg(overlay), Path(out)
    rnd = int(rnd)
    cells, invs = instrument.deckmod.names(s)
    ns = noise2.noise_seed(seed, rnd) if rnd > 0 else None
    t0 = time.time()
    orig = instrument.deck_text
    saved_env = {k: os.environ.get(k) for k in ("LD_PRELOAD", "FAKEPID")}
    if ns is not None:
        instrument.deck_text = lambda s_, c_: noise3.inverter_lines(noise2.noisy_text(orig(s_, c_), cells, scale), invs, scale)
        os.environ.update(LD_PRELOAD=str(noise2.shim(HERE / "build")), FAKEPID=str(ns))
    try:
        net = noise3.Net3(s, cfg, out, int(seed), windows=ns is not None)
    finally:
        instrument.deck_text = orig
        for k, v in saved_env.items():
            if v is None:
                os.environ.pop(k, None)
            else:
                os.environ[k] = v
    if ns is not None:
        net.ses.saved = net.ses.saved + [n for x in invs for n in (f"x{x}.nzm", f"nzh{x}", f"nzj{x}")]
    status, lessons, words, tests, skews = "done", [], {}, [], []
    try:
        lessons, words, tests = noise2.train_and_test(net, s, cfg, log)
        for k, i in controls2.both_cells(s):
            r = controls2.skew_slot(net, s, k, i)
            net.inverter_x.append({})
            skews.append(len(net.slots) - 1)
            log(f"skew c{k}_{i}: {'FIRE' if r['reads'][0]['emission'] is not None else 'silent'}")
    except Exception as e:
        status = f"failed: {e}"
        log(status)
    finally:
        controls2.write_trace(net)
        cpu = runmod.cpu_of(net.ses.p.pid)
        net.ses.close()
    text = (out / "input.spice").read_text()
    rec = dict(tag=s["tag"], seed=int(seed), round=rnd, noise_seed=ns, noise_scale=float(scale) if ns else 0.0,
               noise_model="noise3: noise2 R cells + C5 inverter comparator and mirrors (K3 gate budget)",
               status=status, input_spice_sha256=hashlib.sha256(text.encode()).hexdigest(),
               cost=dict(wall_s=time.time() - t0, cpu_s=cpu),
               words={f"{k}/{i}/{g}": w for (k, i, g), w in words.items()}, lessons=lessons, tests=tests, skews=skews,
               slots=net.slots, inverter_x=net.inverter_x, **(extra or {}))
    (out / "noisy_record.json").write_text(json.dumps(rec, indent=1, default=str) + "\n")
    return rec


def main(argv):
    if not argv or argv[0] not in ("stagen", "untrained"):
        print(__doc__)
        return 2
    cmd, *a = argv
    kw = dict(x.split("=", 1) for x in a if "=" in x)
    pos = [x for x in a if "=" not in x]
    seal, why = controls3.seal(kw)
    if why:
        print(why)
        return 2
    if cmd == "stagen":
        if len(pos) != 4:
            print("refused: stagen needs SPEC OUT SEED ROUND")
            return 2
        r = stagen(*pos, scale=float(kw.get("scale", 1)), overlay=kw.get("overlay"), extra=dict(seal_log=seal))
        print(json.dumps(dict(status=r["status"], noise_seed=r["noise_seed"], seal_log=r["seal_log"], cost=r["cost"]), indent=1))
        return 0 if r["status"] == "done" else 1
    return controls3.main(argv)                             # untrained: controls2's, which writes its trace already


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
