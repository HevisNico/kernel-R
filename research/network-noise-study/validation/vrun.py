"""Validation of the device-noise model: the runs (see PROTOCOL.md). Each call is one simulator run.

  vrun.py frozen  OUT.json INSTANCE STATE CELL PORT T_S ROUND MODEL|injected      V3/V4/V5: frozen-deck transient
  vrun.py preset  OUT.json INSTANCE ROUND|zero                                   V6: 50 us of the instance deck
  vrun.py seeding OUT.json INSTANCE ROUND|quiet                                  V8: 1 ms of the instance deck
  vrun.py train   OUT_DIR  INSTANCE ROUND|quiet|zero|injected                    section 3, V5, V7: a train

INSTANCE is nominal, 7101, 7102 or 7103 (no other seed is accepted). CELL is a, b or `all` (hold: every output of
the two-cell deck at once); PORT is 1, 2 or `-`. ROUND is the noise round of amendment 1. The model of an instance
is read from DEVNOISE_<instance>.json of this folder (the validation's extraction).
"""
import hashlib, json, math, os, re, shutil, subprocess, sys, time
from pathlib import Path
import numpy as np

HERE = Path(__file__).resolve().parent
P0 = HERE.parent / "phase0"
sys.path.insert(0, str(HERE.parent.parent / "network-circuit"))
sys.path.insert(0, str(P0))
import net, router              # noqa: E402
import model, pilot, noisegen   # noqa: E402
from cost3 import filesource, CODEMODEL, XTRTOL   # noqa: E402

NGSPICE = Path("/usr/bin/ngspice")
PDK = HERE.parent.parent / "circuit" / "pdk"
Q, IPK = 1.602176634e-19, 5e-12 * 0.5 * math.log(4) / 20e-6         # the shot terms: 2qI at the peak of bip
MODEL_STATES = ("hold", "window", "fire", "pulse")
INSTANCES = {"nominal": ("tt", None, 90000), "7101": ("tt_mm", 7101, 7101), "7102": ("tt_mm", 7102, 7102),
             "7103": ("tt_mm", 7103, 7103)}
FS_DIR = Path(os.environ.get("VAL_SAMPLES", "/tmp/claude-0/-home-user-kernel-r/ea58e5f1-2e9f-519d-96f6-6fc1ac9f458a/scratchpad/val/samples"))


def noise_seed(instance, rnd):
    """Amendment 1, item 1."""
    _, seed, _ = INSTANCES[instance]
    assert int(rnd) >= (1 if seed is None else 3)
    return 90000 + int(rnd) if seed is None else 1000 * seed + int(rnd)


def position(instance, rnd):
    """The run's position k in the instance's list of runs (PROTOCOL.md): round 1 (nominal) or 3 (7101-7103) is k = 0."""
    return int(rnd) - (1 if INSTANCES[instance][1] is None else 3)


def model_sources(instance, cells):
    """The model of an instance (criteria, section 1, items 2 and 3): per cell, the union of the devices kept at the
    four states, each with A, B, ef and nodes from the state of its largest share; per port, the shot term. Sorted
    by name, devices first, then the shot terms."""
    ex = json.loads((HERE / f"DEVNOISE_{instance}.json").read_text())
    best = {}
    for o in ex["outputs"]:
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


def add_sources(text, sources, instance, rnd, t_s, work, scale="1"):
    """The filesource sources of the model for one run; the samples files are hashed and deleted after the run by
    `finish`. The first sample of every source is 0 (PROTOCOL.md: the operating point is that of the deck without the
    model, V8)."""
    seed = noise_seed(instance, rnd)
    key = INSTANCES[instance][2]
    n = int(math.ceil(t_s / noisegen.NT)) + 2
    cols, lines = [], []
    for k, s in enumerate(sources):
        g = math.sqrt(s["A"] / (2 * noisegen.NT)) / 1e-3
        x = noisegen.samples(seed, k, n, s["A"] / g ** 2, s["B"] / g ** 2, s["alpha"], slow=(key, position(instance, rnd)))
        x[0] = 0.0
        cols.append(x)
        lines += [f"rnzp{k} nzp{k} 0 1k noisy=0", f"gnzp{k} {s['nodes'][0]} {s['nodes'][1]} nzp{k} 0 {g:.10g}"]
    FS_DIR.mkdir(parents=True, exist_ok=True)
    stem = FS_DIR / f"{Path(work).name}.samples.txt"
    assert str(stem) == str(stem).lower(), "ngspice lowercases the file name of a filesource: the path must be lowercase"
    lines += filesource("nz", cols, stem, scale)
    files = sorted(FS_DIR.glob(stem.name + ".*"))
    return text.replace("\n.end\n", "\n" + "\n".join(lines) + "\n.end\n"), files, seed


def finish(files):
    out = {}
    for f in files:
        out[f.name] = hashlib.sha256(f.read_bytes()).hexdigest()
        f.unlink()
    return out


ANALOG_CM_SHA256 = "98c7c296dfd04e81f568db91c8261a07f00d8d63e63e5cc1d331451ccda30941"
_CHECKED = []


def environment():
    """The pinned environment (criteria: each hash checked before the runs), once per process."""
    if not _CHECKED:
        assert pilot.sim.digest(NGSPICE) == pilot.sim.NGSPICE_SHA256, "not the pinned ngspice 42 binary"
        assert subprocess.check_output(["git", "-C", str(PDK.resolve()), "rev-parse", "HEAD"], text=True).strip() == pilot.sim.PDK_COMMIT
        assert np.__version__ == "2.3.5", np.__version__
        assert hashlib.sha256(Path(CODEMODEL).read_bytes()).hexdigest() == ANALOG_CM_SHA256, "not the pinned analog.cm"
        _CHECKED.append(True)


def spice(work, text, timeout=None):
    environment()
    work = Path(work)
    work.mkdir(parents=True, exist_ok=False)
    (work / "pdk").symlink_to(PDK.resolve(), target_is_directory=True)
    init = (HERE.parent.parent / "circuit" / "spiceinit.txt").read_text() + f"codemodel {CODEMODEL}\nset xtrtol={XTRTOL}\n"
    (work / ".spiceinit").write_text(init)
    (work / "deck.spice").write_text(text)
    env = dict(os.environ, SPICE_SCRIPTS=str(pilot.sim.SPINIT.parent))
    t0 = time.time()
    p = subprocess.run([str(NGSPICE), "-b", "deck.spice"], cwd=work, env=env, capture_output=True, text=True, timeout=timeout)
    (work / "log.txt").write_text(p.stdout + p.stderr)
    low = (p.stdout + p.stderr).lower()
    bad = any(s in low for s in ("aborted", "timestep too small", "transient op failed", "fatal error"))
    return p.stdout, time.time() - t0, bad


def control(text, lines):
    return text.replace("\n.end\n", "\n.control\nset numdgt=16\n" + "\n".join(lines) + "\nquit\n.endc\n.end\n")


def frozen(out, instance, state, cell, port, t_s, rnd, kind):
    """V3/V4 (kind: model) and V5 (kind: injected): one transient of the frozen deck. hold: nominal one cell, the
    development instances every output of the two-cell deck at once (cell `all`); window, fire, pulse: the isolated
    cell of the extraction, its comparator held at the extraction's trip value."""
    section, seed, _ = INSTANCES[instance]
    cells = ("a",) if instance == "nominal" and state == "hold" else ("a", "b")
    focus = (cells[0], 1) if cell == "all" else (cell, None if port == "-" else int(port))
    original = net.deck
    if kind == "injected":
        net.deck = lambda **kw: original(**dict(kw, noise=True))
    try:
        text, _ = model.analysis_deck(section, cells, state, focus=focus)
    finally:
        net.deck = original
    if cell == "all":
        outs = [model.out_expr(state, c, p) for c in cells for p in net.PORTS]
        mcells = cells
    else:
        text = model.isolate(text, focus[0], cells)
        outs = [model.out_expr(state, focus[0], focus[1])]
        mcells = (focus[0],)
        ex = json.loads((HERE / f"DEVNOISE_{instance}.json").read_text())
        o = next(o for o in ex["outputs"] if o["state"] == state and o["cell"] == focus[0] and o.get("port") == focus[1])
        if o["trip"] is not None:
            src = {"window": "vfrc", "fire": "vfrcq"}[state]
            text, n = re.subn(rf"^{src} (\S+) 0 dc \S+$", lambda m: f"{src} {m.group(1)} 0 dc {o['trip']:.15g}", text, flags=re.M)
            assert n == 1
    work = Path(out).with_suffix("")
    files, nseed = [], None
    if kind != "injected":
        text, files, nseed = add_sources(text, model_sources(instance, mcells), instance, rnd, t_s, work)
    names = [re.sub(r"[^a-z0-9]", "_", o) for o in outs]
    ctl = pilot.seeded(seed) + [f"tran 0.2u {t_s:.9g} 0 200n", "write tran.raw " + " ".join(outs),
                                "linearize " + " ".join(outs), "wrdata out.txt " + " ".join(outs)]
    stdout, wall, bad = spice(work, control(text, ctl))
    hashes = finish(files)
    raw = work / "tran.raw"
    raw_sha = hashlib.sha256(raw.read_bytes()).hexdigest() if raw.exists() else None
    if raw.exists():
        raw.unlink()
    d = np.loadtxt(work / "out.txt")
    np.save(work / "y.npy", d[:, 1::2])                 # one column per output, every 0.2 us from 0
    (work / "out.txt").unlink()
    summary = {o: summarize(d[:, 2 * i + 1], 0.2e-6) for i, o in enumerate(outs)}
    Path(out).write_text(json.dumps(dict(machine=os.environ.get("VAL_MACHINE"), run="frozen", instance=instance, state=state, cell=cell, port=port, kind=kind,
                                         round=rnd, noise_seed=nseed, position=position(instance, rnd) if kind != "injected" else None,
                                         t_s=t_s, dt_s=0.2e-6, outputs=outs, aborted=bad, wall_s=wall,
                                         samples_sha256=hashes, raw_sha256=raw_sha,
                                         y_sha256=hashlib.sha256((work / "y.npy").read_bytes()).hexdigest(),
                                         points=int(len(d)), y_file=str(work / "y.npy"),
                                         summary=summary)) + "\n")


LAGS = (0.36e-3, 2e-3, 5e-3, 10e-3, 19e-3)       # V4
READ = 40e-6
GRID = [10 ** (k / 3) for k in range(0, 20)]      # V3: the third-decade grid


def summarize(y, dt):
    """What V3, V4 and V5 use of one output of one draw (PROTOCOL.md), so that a draw needs no waveform: the mean;
    per lag, the sum of squared drifts of the 40 us reads and their count; the Hann periodogram's mean over each
    band of the grid; its integral from 25 Hz to 1 kHz."""
    w = np.hanning(len(y))
    P = 2 * dt * np.abs(np.fft.rfft((y - y.mean()) * w)) ** 2 / np.sum(w ** 2)
    fr = np.fft.rfftfreq(len(y), dt)
    m = int(round(READ / dt))
    reads = y[: len(y) // m * m].reshape(-1, m).mean(axis=1)
    drift = {}
    for lag in LAGS:
        k = int(round(lag / READ))
        d = reads[k:] - reads[:-k]
        drift[f"{lag:g}"] = dict(sum_sq=float(np.sum(d ** 2)), n=int(len(d)))
    bands = []
    for lo, hi in zip(GRID[:-1], GRID[1:]):
        b = (fr >= lo) & (fr < hi)
        bands.append(dict(lo=lo, hi=hi, bins=int(b.sum()), P_mean=float(P[b].mean()) if b.any() else None))
    mb = (fr >= 25) & (fr <= 1000)
    return dict(points=int(len(y)), dt_s=dt, mean_V=float(y.mean()), drift=drift, bands=bands,
                band_25_1000_V2=float(np.trapezoid(P[mb], fr[mb])))


def instance_deck(instance):
    section, seed, _ = INSTANCES[instance]
    return net.deck(cells=("a", "b"), section=section), seed


def preset(out, instance, rnd):
    """V6: 50 us of the instance deck from t = 0, all sources on (or at zero amplitude: `zero`, the same run without
    noise), v(vmem) - v(sum) of each port at 3.1 us, 1 us after the preset ends."""
    text, seed = instance_deck(instance)
    work = Path(out).with_suffix("")
    zero = rnd == "zero"
    text, files, nseed = add_sources(text, model_sources(instance, ("a", "b")), instance, 3 if zero and seed else (1 if zero else rnd),
                                     50e-6, work, scale="0" if zero else "1")
    meas = [f"meas tran m{c}{p} find v(x{c}.vmem{p}) at=3.1u" for c in "ab" for p in net.PORTS] + \
           [f"meas tran s{c}{p} find v(x{c}.x{p}.sum) at=3.1u" for c in "ab" for p in net.PORTS]
    stdout, wall, bad = spice(work, control(text, pilot.seeded(seed) + ["tran 0.1u 50u 0 200n",
                                                                      "write tran.raw " + " ".join(f"v(x{c}.vmem{p}) v(x{c}.x{p}.sum)" for c in "ab" for p in net.PORTS)] + meas))
    raw = work / "tran.raw"
    raw_sha = hashlib.sha256(raw.read_bytes()).hexdigest() if raw.exists() else None
    got = lambda k: float(re.search(rf"^{k}\s*=\s*(\S+)", stdout, re.M | re.I).group(1))
    u = {f"{c}{p}": got(f"m{c}{p}") - got(f"s{c}{p}") for c in "ab" for p in net.PORTS}
    Path(out).write_text(json.dumps(dict(machine=os.environ.get("VAL_MACHINE"), run="preset", instance=instance, round=None if zero else rnd, noise_seed=None if zero else nseed,
                                         position=None if zero else position(instance, rnd), aborted=bad, wall_s=wall,
                                         samples_sha256=finish(files), raw_sha256=raw_sha, u_V=u)) + "\n")


def seeding(out, instance, rnd):
    """V8: the operating point (every node, 16 digits) and 1 ms of the instance deck with the model (or `quiet`:
    without it), the stored voltages written in full."""
    text, seed = instance_deck(instance)
    work = Path(out).with_suffix("")
    files, nseed = [], None
    if rnd != "quiet":
        text, files, nseed = add_sources(text, model_sources(instance, ("a", "b")), instance, rnd, 1e-3, work)
    outs = [f"v(x{c}.vmem{p})" for c in "ab" for p in net.PORTS]
    ctl = pilot.seeded(seed) + ["op", "print all > op.txt", "tran 0.2u 1m 0 200n", "write tran.raw " + " ".join(outs),
                                "linearize " + " ".join(outs), "wrdata out.txt " + " ".join(outs)]
    stdout, wall, bad = spice(work, control(text, ctl))
    op = (work / "op.txt").read_text()
    d = np.loadtxt(work / "out.txt")
    Path(out).write_text(json.dumps(dict(machine=os.environ.get("VAL_MACHINE"), run="seeding", instance=instance, round=rnd, noise_seed=nseed,
                                         position=None if rnd == "quiet" else position(instance, rnd), aborted=bad, wall_s=wall,
                                         samples_sha256=finish(files), op_sha256=hashlib.sha256(op.encode()).hexdigest(), op=op,
                                         raw_sha256=hashlib.sha256((work / "tran.raw").read_bytes()).hexdigest(),
                                         outputs=outs, y=d[:, 1::2].tolist())) + "\n")
    np.save(work / "y.npy", d[:, 1::2])
    (work / "out.txt").unlink()


def train(outdir, instance, rnd):
    """Section 3, V5, V7: the train of `noisechar.py` (10 reads per port, 18 units), two cells, through the router:
    `quiet` (no source), `zero` (the model's sources at zero amplitude), `injected` (the trnoise sources of campaigns
    1 to 3, seeded by the simulator's process number), or a round (the model)."""
    import shutil as _sh
    sys.path.insert(0, str(HERE.parent.parent / "network-circuit" / "phase1"))
    import noisechar
    section, seed, _ = INSTANCES[instance]
    cal = noisechar.calendar(10)
    horizon = router.ORIGIN + cal["horizon"] * net.TU + 50e-6
    info = {}
    original = net.deck
    if rnd not in ("quiet", "injected"):
        def deck(**kw):
            t = original(**kw)
            t, info["files"], info["seed"] = add_sources(t, model_sources(instance, ("a", "b")), instance,
                                                         (3 if seed else 1) if rnd == "zero" else rnd, horizon, Path(outdir),
                                                         scale="0" if rnd == "zero" else "1")
            return t
        net.deck = deck
        copy = _sh.copyfile

        def with_codemodel(src, dst, *a, **k):
            r = copy(src, dst, *a, **k)
            if Path(dst).name == ".spiceinit":
                with open(dst, "a") as f:
                    f.write(f"codemodel {CODEMODEL}\nset xtrtol={XTRTOL}\n")
            return r
        net.shutil.copyfile = with_codemodel
    environment()
    r = router.run(Path(outdir), cal, NGSPICE, PDK, seed=seed, section=section, noise=rnd == "injected")
    meta = dict(machine=os.environ.get("VAL_MACHINE"), run="train", instance=instance, round=rnd, noise_seed=info.get("seed") if rnd not in ("quiet", "zero", "injected") else None,
                position=position(instance, rnd) if rnd not in ("quiet", "zero", "injected") else None,
                samples_sha256=finish(info.get("files", [])), word=router.word(r), wall_s=r["wall_s"])
    (Path(outdir) / "meta.json").write_text(json.dumps(meta) + "\n")
    print(json.dumps(meta))


if __name__ == "__main__":
    a = sys.argv[1:]
    assert a[2] in INSTANCES, "only the nominal cell and 7101-7103"
    if a[0] == "frozen":
        frozen(a[1], a[2], a[3], a[4], a[5], float(a[6]), a[7] if a[8] != "injected" else None, a[8])
    elif a[0] == "preset":
        preset(a[1], a[2], a[3] if a[3] == "zero" else int(a[3]))
    elif a[0] == "seeding":
        seeding(a[1], a[2], a[3] if a[3] == "quiet" else int(a[3]))
    elif a[0] == "train":
        train(a[1], a[2], a[3] if a[3] in ("quiet", "zero", "injected") else int(a[3]))
