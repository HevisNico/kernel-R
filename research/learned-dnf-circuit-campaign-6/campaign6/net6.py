"""Campaign 6's network runner (PREDICTION.md 4), as the launch kit starts it. New code: campaign 5's run4.run network
branch (run without noise, noisy run under the injected model, untrained control run), called through the same frozen
functions (plans4.network, net.deck, noisemodel.shim, session4.play, run4.trnoise_fingerprint), writing the same deck
and the same record key for key, plus one key `campaign6`. run4.run itself cannot run campaign 6's seeds: its guard
accepts only campaign 5's. This runner's guard is c6.guard_seed, before any deck is written (test_campaign6.NetCopy
shows the equivalence with a fake simulator; the guard's refusals are tested without one).

  net6.py STAGE OUT ID SEED NEEDS CONTROL NOISE ROUND NGSPICE PDK
      NEEDS a,b,c1,c2; CONTROL skew | untrained | none; NOISE none | injected; ROUND 0, or 1 to 3 for a noisy run
"""
import json
from pathlib import Path
import resource
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import c6                                               # noqa: E402
import c4                                               # noqa: E402
import noisemodel                                       # noqa: E402  (campaign 5, frozen: the shim of the imposed process number)
import plans4                                           # noqa: E402
import run4                                             # noqa: E402  (campaign 5, frozen: trnoise_fingerprint, sha)
import session4                                         # noqa: E402
from session4 import net                                # noqa: E402


def network(stage, out, rid, seed_text, needs, control, noise, rnd, ngspice, pdk):
    c6.require_debug()
    began = time.time()
    out = Path(out)
    assert noise in ("none", "injected"), "refused: the injected model only (PREDICTION.md 4; campaign 5, section 6)"
    seed = c6.guard_seed(seed_text, stage, out)
    assert stage not in c6.MEASURE_REHEARSAL, "refused: the measure rehearsal has no network run"
    assert (noise == "none") == (rnd == 0), "a noisy run has a round from 1 to 3, a run without noise none"
    assert control in (None, "skew", "untrained")
    section = "tt" if seed is None else c4.SECTION
    rec = dict(id=rid, kind="network", section=section, seed=seed, stage=None)        # run4.run's order
    plan, slots = plans4.network(tuple(needs), control)
    guard_off, noise_id, shim = False, None, None
    if noise == "injected":
        out.mkdir(parents=True, exist_ok=True)
        shim, shim_info = noisemodel.shim(out)
        noise_id = c6.noise_seed(seed, rnd)
        text = net.deck(cells=c4.CELLS, section=section, noise=True)
        info = dict(model="injected", noise_seed=noise_id, imposed_process_number=noise_id, shim=shim_info)
    else:
        text = net.deck(cells=c4.CELLS, section=section)
        info = dict(model="none")
    rec.update(needs=list(needs), control=control, round=rnd if noise != "none" else None, slots=len(slots))
    result, tr = session4.play(out / "evidence", plan, text, ngspice, pdk, seed=seed, guard_off=guard_off, noise_id=noise_id, shim=shim)
    (out / "evidence" / "pdk").unlink()
    reached = bool(tr.t[-1] >= result["horizon_s"] - 1e-9)
    mark = run4.trnoise_fingerprint(tr, c4.CELLS)
    if shim is not None:
        Path(shim).unlink()
    ev = out / "evidence"
    rec.update(noise=info, reached_its_last_date=reached, horizon_s=result["horizon_s"], waveform_ends_s=result["waveform_ends_s"],
               points=result["points"], files={x: run4.sha(ev / x) for x in ("input.spice", "session.log", "trace.raw", "result.json")})
    rec.update(noise_fingerprint=mark, wall_s=time.time() - began,
               peak_rss_MB=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss / 1024)
    rec["campaign6"] = c6.run_header(seed, None, "network", stage)                  # the only added key
    (out / "noise.sha256").write_text(mark + "\n")
    (out / "record.json").write_text(json.dumps(rec, indent=1) + "\n")
    assert rec["reached_its_last_date"], "the waveform ends before the last date of the run"
    return rec


def main(argv=None):
    a = sys.argv[1:] if argv is None else argv
    stage, out, rid, seed_text, needs, control, noise, rnd, ngspice, pdk = a
    rec = network(stage, out, rid, seed_text, [int(x) for x in needs.split(",")], None if control == "none" else control, noise, int(rnd),
                  Path(ngspice), Path(pdk))
    print(json.dumps(dict(id=rec["id"], reached_its_last_date=rec["reached_its_last_date"], wall_s=round(rec["wall_s"]))))


if __name__ == "__main__":
    main()
