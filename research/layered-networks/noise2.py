"""The injected noise model on the layered decks, and the noisy run (training and tests, no scans). Development only.

Sources of the method (read, not imported or wrapped):
- the noise sources: research/network-circuit/net.py `deck(noise=True)` (evidence/function-family-campaign-predicted
  d7e4fcc2, lines 85-96). Each R-cell port's three zero sources vnzc, vnzo, vnzi and the cell's vnzm become trnoise
  sources with the amplitudes of research/circuit/noise.json `params`, input-referred, from the blocks' small-signal
  noise analyses (research/circuit/noise.py): comparator window (vncw, vncf), integrator op-amp (vnow, vnof), mirror
  shot (inmw), FIRE comparator (vnmw, vnmf), sampled every tnz = 0.4 us;
- the noise seed: ngspice 42 seeds its trnoise generator from getpid() when it starts, and the preloaded shim
  research/circuit/repetition/fakepid.c makes getpid() return FAKEPID. The noisy run of round n of seed S has
  FAKEPID = 10 x S + n (campaign 6 PREDICTION.md §4, campaign (a) PREDICTION.md §4);
- the constants against which the measured noise is compared: decision 5, b = 0.111 mV between runs, w = 0.094 mV
  within a run, d = 0.009 mV per dose (research/learned-dnf-circuit/DECISIONS.md; measured in campaign 3,
  network-circuit-ring-campaign-3 REPORT.md M5, analyze.py lines 253-257 and 377-380).
The inverters keep their noise sources at zero: net.py injects into R cells only, and the C5 instances were
characterised without noise.

  noise2.py run SPEC OUT SEED ROUND [scale=1] [overlay=FILE]   ROUND 0 = noise off (no shim, dc 0 sources)
  noise2.py bwd SPEC OFF_DIR NOISY_DIR...                       measured b, w, d against the noise-off run
"""
import contextlib
import hashlib
import json
import os
from pathlib import Path
import statistics
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import instrument  # noqa: E402
import run as runmod  # noqa: E402
import spec as specmod  # noqa: E402

CIRCUIT = (HERE / ".." / "circuit").resolve()
NOISE = json.loads((CIRCUIT / "noise.json").read_text())["params"]
DECISION5_mV = dict(b=0.111, w=0.094, d=0.009)
SHIM_SRC = CIRCUIT / "repetition" / "fakepid.c"
SOURCES = (("vnzc", "vncw", "vncf"), ("vnzo", "vnow", "vnof"), ("vnzi", "inmw", None), ("vnzm", "vnmw", "vnmf"))


def noise_seed(seed, rnd):
    return 10 * int(seed) + int(rnd)


def noisy_text(text, cells, scale=1.0):
    """The flattened deck with each R cell's zero sources turned into net.py's trnoise sources (times `scale`)."""
    lines, n = text.splitlines(), 0
    for i, l in enumerate(lines):
        for name, white, flicker in SOURCES:
            for c in cells:
                if l.startswith(f"v.x{c}.") and f".{name} " in l and l.endswith(" 0 dc 0"):
                    w = NOISE[white] * scale
                    f = (NOISE[flicker] * scale) if flicker else 0.0
                    lines[i] = f"{l} trnoise({w:.16g} {NOISE['tnz']:.16g} {1 if flicker else 0} {f:.16g})"
                    n += 1
    assert n == 7 * len(cells), f"expected 7 noise sources per R cell, found {n}"
    return "\n".join(lines) + "\n"


def shim(build):
    so = Path(build) / "fakepid.so"
    if not so.exists() or so.stat().st_mtime < SHIM_SRC.stat().st_mtime:
        so.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(["gcc", "-shared", "-fPIC", "-O2", "-o", str(so), str(SHIM_SRC)], check=True)
    return so


@contextlib.contextmanager
def noisy_deck(cells, scale, env):
    """instrument.deck_text replaced by its noisy version, and the shim in the environment, for one CalNetwork."""
    orig = instrument.deck_text
    saved = {k: os.environ.get(k) for k in env}
    instrument.deck_text = lambda s, cfg: noisy_text(orig(s, cfg), cells, scale)
    os.environ.update(env)
    try:
        yield
    finally:
        instrument.deck_text = orig
        for k, v in saved.items():
            if v is None:
                os.environ.pop(k, None)
            else:
                os.environ[k] = v


def train_and_test(net, s, cfg, log):
    """instrument.cal_run's lesson and test calendar (the same loop), without the scans."""
    calc = cfg["calendar"]
    lessons, words, tests = [], {}, []
    for l in range(len(s["layers"])):
        k = l + 1
        for g in range(2):
            for stim, members in net.partitions(l, g):
                x = specmod.line_pattern(s, stim)
                state = {i: dict(r=0, run=0, word="") for i in members}
                while state:
                    cells = set(state)
                    r_ = net.slot("lesson", x, k, {k: cells}, {f"c{k}_{i}" for i in cells},
                                  dict(layer=k, group=g, cells=sorted(cells), stimulus=sorted(stim)))
                    idx = len(net.slots) - 1
                    for i in sorted(cells):
                        r = next(r for r in r_["reads"] if r["layer"] == k and r["index"] == i)
                        f = r["emission"] is not None
                        st = state[i]
                        lessons.append(dict(layer=k, cell=i, group=g, round=st["r"], slot=idx))
                        st["word"] += "F" if f else "s"
                        st["run"] = st["run"] + 1 if f else 0
                        st["r"] += 1
                        if st["run"] >= calc["hold"] or st["r"] >= calc["max_rounds"]:
                            words[(k, i, g)] = st["word"]
                            log(f"lesson layer {k} cell {i} group {g}: {st['word']}")
                            del state[i]
    for x in specmod.patterns(s["m"]):
        r_ = net.slot("test", specmod.rails(s, x), len(s["layers"]), {}, set(), dict(pattern=[int(b) for b in x]))
        tests.append(len(net.slots) - 1)
        top = r_["reads"][-1]
        log(f"test {''.join(str(int(b)) for b in x)}: out {'FIRE' if top['emission'] is not None else 'silent'}")
    return lessons, words, tests


def run(spec_path, out, seed, rnd, scale=1.0, overlay=None, log=print):
    import lcal2
    s = specmod.load(spec_path)
    cfg = lcal2.config(overlay)[0] if overlay else json.loads((HERE / "config.json").read_text())
    out = Path(out)
    rnd = int(rnd)
    cells, _ = instrument.deckmod.names(s)
    ns = noise_seed(seed, rnd) if rnd > 0 else None
    env = {} if ns is None else dict(LD_PRELOAD=str(shim(HERE / "build")), FAKEPID=str(ns))
    t0 = time.time()
    if ns is None:
        net = instrument.CalNetwork(s, cfg, out, int(seed))
    else:
        with noisy_deck(cells, float(scale), env):
            net = instrument.CalNetwork(s, cfg, out, int(seed))
    status = "done"
    lessons, words, tests = [], {}, []
    try:
        lessons, words, tests = train_and_test(net, s, cfg, log)
    except Exception as e:
        status = f"failed: {e}"
        log(status)
    finally:
        cpu = runmod.cpu_of(net.ses.p.pid)
        net.ses.close()
    text = (out / "input.spice").read_text()
    rec = dict(tag=s["tag"], seed=int(seed), round=rnd, noise_seed=ns, noise_scale=float(scale) if ns else 0.0,
               status=status, input_spice_sha256=hashlib.sha256(text.encode()).hexdigest(),
               cost=dict(wall_s=time.time() - t0, cpu_s=cpu),
               words={f"{k}/{i}/{g}": w for (k, i, g), w in words.items()}, lessons=lessons, tests=tests, slots=net.slots)
    (out / "noisy_record.json").write_text(json.dumps(rec, indent=1, default=str) + "\n")
    return rec


# --------------------------------------------------------------------------------------------- measured b, w, d

def bwd(spec_path, off_dir, noisy_dirs):
    """Per port and noisy run, x_t = u_noisy(t) - u_off(t) over the slots matched to the noise-off run (by kind, info
    and occurrence), for each cell while its read outcomes agree with the noise-off run's.
      b: the run offset, mean_t x_t (rms over port-runs), the analogue of campaign 3's M5 run offset;
      w: the scatter within the run, sd_t x_t (rms), the analogue of M5's within-run scatter;
      d: per dose, the spread of the dose step, (du_noisy - du_off) at each write of the port (rms).
    Campaign 3 read b and w from FIRE latencies through a slope; these are read on the stored voltage directly."""
    off = json.loads((Path(off_dir) / "noisy_record.json").read_text())
    offs, scat, dose, latency = [], [], [], []
    per_run = []
    def keyed(slots):
        seen, out = {}, {}
        for i, sl in enumerate(slots):
            k = (sl["kind"], json.dumps(sl.get("info"), sort_keys=True))
            seen[k] = seen.get(k, 0) + 1
            out[k + (seen[k],)] = i
        return out

    def outcome(sl, c):
        return [x["emission"] is not None for x in sl["reads"] if f"c{x['layer']}_{x['index']}" == c]

    for d in noisy_dirs:
        r = json.loads((Path(d) / "noisy_record.json").read_text())
        ko, kn = keyed(off["slots"]), keyed(r["slots"])
        pairs = sorted((ko[k], kn[k]) for k in ko if k in kn)          # matched by kind, info and occurrence
        lat = []
        for c in off["slots"][0]["u"]:
            # cell c is compared while its read outcomes agree, up to and including its first differing outcome
            # (a different FIRE/silence changes its writes from the next slot on)
            pc = []
            for i, j in pairs:
                pc.append((i, j))
                if outcome(off["slots"][i], c) != outcome(r["slots"][j], c):
                    break
            for i, j in pc:
                for x, y in zip(off["slots"][i]["reads"], r["slots"][j]["reads"]):
                    if f"c{x['layer']}_{x['index']}" == c and x.get("latch") is not None and y.get("latch") is not None:
                        lat.append((y["latch"] - r["slots"][j]["T"]) - (x["latch"] - off["slots"][i]["T"]))
            for p in (0, 1):
                xs = [(r["slots"][j]["u"][c][p] - off["slots"][i]["u"][c][p]) * 1e3 for i, j in pc
                      if off["slots"][i]["u"].get(c) is not None and r["slots"][j]["u"].get(c) is not None]
                if len(xs) < 3:
                    continue
                offs.append(statistics.mean(xs))
                scat.append(statistics.stdev(xs))
                for (i0, j0), (i1, j1) in zip(pc, pc[1:]):
                    if i1 != i0 + 1 or j1 != j0 + 1:
                        continue                            # a dose step only between consecutive slots of both runs
                    du_off = off["slots"][i1]["u"][c][p] - off["slots"][i0]["u"][c][p]
                    du_n = r["slots"][j1]["u"][c][p] - r["slots"][j0]["u"][c][p]
                    if du_off < -0.5e-3:                     # a write (one dose is about 2.7 mV at 2x)
                        dose.append((du_n - du_off) * 1e3)
        latency.append(lat)
        per_run.append(dict(dir=str(d), noise_seed=r["noise_seed"], matched_slots=len(pairs), slots=len(r["slots"]),
                            latch_shift_ns=dict(n=len(lat), mean=statistics.mean(lat) if lat else None,
                                                sd=statistics.stdev(lat) if len(lat) > 1 else None),
                            words_equal=r["words"] == off["words"],
                            tests_equal=[r["slots"][j]["reads"][-1]["emission"] is not None for j in r["tests"]] ==
                                        [off["slots"][i]["reads"][-1]["emission"] is not None for i in off["tests"]]))
    rms = lambda v: (statistics.mean(x * x for x in v) ** 0.5) if v else None
    allat = [x for l in latency for x in l]
    return dict(b_mV=rms(offs), w_mV=rms(scat), d_mV=rms(dose), port_runs=len(offs), doses=len(dose),
                latch_shift_ns_rms=rms(allat), latch_reads=len(allat), model_mV=DECISION5_mV, runs=per_run)


if __name__ == "__main__":
    cmd, *a = sys.argv[1:]
    if cmd == "run":
        kw = dict(x.split("=", 1) for x in a[4:])
        r = run(*a[:4], scale=float(kw.get("scale", 1)), overlay=kw.get("overlay"))
        print(json.dumps(dict(status=r["status"], noise_seed=r["noise_seed"], words=r["words"], cost=r["cost"]), indent=1))
    elif cmd == "bwd":
        print(json.dumps(bwd(a[0], a[1], a[2:]), indent=1))
    else:
        sys.exit(__doc__)
