"""The versioned stage-N entry point, version 5: controls4's stage N (noise3's sealed stage N, the trace written,
the inverters' noise nodes saved in a noisy run) and untrained run, with one added option. Development only. New file:
controls4.py stays as pushed.

Option save_ref=1 (off by default), for one noisy round of the pre-freeze dry run: the trace also holds each
inverter's comparator reference, xn<j>.vrefm (before the noise) and xn<j>.vrefmn (the comparator's input, after bvrm,
rvrm and cvrm), so that the comparator noise level can be read where the comparator sees it
(tests/check_ref_level.py). Saving vectors adds no time point; the record then carries "saved_ref" and is otherwise the
same. With the option off, the run is controls4's (so its record is controls3's). Refused (exit 2) on a round-0 run,
which has no comparator noise, and for any value other than 0 or 1.

  controls5.py stagen    SPEC OUT SEED ROUND seal_log=<40-hex> seal_branch=<branch> [scale=1] [overlay=FILE] [save_ref=1]
  controls5.py untrained SPEC OUT SEED       seal_log=<40-hex> seal_branch=<branch> [overlay=FILE]

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


def stagen(spec_path, out, seed, rnd, scale=1.0, overlay=None, extra=None, log=print, save_ref=False):
    """controls4.stagen (the noise nodes saved in a noisy run, the trace written before the session closes).
    save_ref: also save each inverter's comparator reference (vrefm, vrefmn); a noisy round only."""
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
    ref = [n for x in invs for n in (f"x{x}.vrefm", f"x{x}.vrefmn")] if save_ref and ns is not None else []
    net.ses.saved = net.ses.saved + ref
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
               slots=net.slots, inverter_x=net.inverter_x, **(dict(saved_ref=ref) if ref else {}), **(extra or {}))
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
        save_ref = kw.get("save_ref", "0")
        if save_ref not in ("0", "1"):
            print("refused: save_ref must be 0 or 1")
            return 2
        if save_ref == "1" and int(pos[3]) <= 0:
            print("refused: save_ref=1 needs a noisy round (ROUND > 0)")
            return 2
        r = stagen(*pos, scale=float(kw.get("scale", 1)), overlay=kw.get("overlay"), extra=dict(seal_log=seal),
                   save_ref=save_ref == "1")
        print(json.dumps(dict(status=r["status"], noise_seed=r["noise_seed"], seal_log=r["seal_log"], cost=r["cost"]), indent=1))
        return 0 if r["status"] == "done" else 1
    return controls3.main(argv)                             # untrained: controls2's, which writes its trace already


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
