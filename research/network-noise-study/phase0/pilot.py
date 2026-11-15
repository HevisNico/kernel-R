"""Phase 0, feasibility, no claim: a noise model drawn from the device models, on one operating point of the cell.

  pilot.py extract WORK OUT.json SECTION SEED|none NGSPICE PDK [hold|preset]
  pilot.py tran    WORK OUT.json MODEL.json device|injected|quiet T_S DRAWS NGSPICE PDK
  pilot.py op      WORK OUT.json SECTION SEED NGSPICE PDK        (the mismatch check)

The deck is the network deck of `../../network-circuit/net.py` with one cell, `a`, frozen in the **hold** state:
no pulse, and the preset switch of each integrator replaced by a noiseless 1e14 ohm resistor, so that the stored
voltage keeps a DC solution (through the preset loop, whose loop gain falls to one at about 0.5 Hz) and is free in
the band that matters. The
resistors that only belong to the bench (the 10 k filters of the controls, the 1 k injection resistors) are made
noiseless; every transistor and the design resistors keep the noise of their model.

`extract` runs `.noise` at v(xa.vmem1) with per-device output, ranks the devices by their share of the output noise
power over BAND, and for the devices that make up COVER of it finds the noise current of the device: the output
density of its thermal and flicker parts divided by |H|, H the transfer from a unit current between its two
channel terminals to the output (one AC analysis per device). It writes, per device, the white density A (A^2/Hz)
and the flicker coefficient B (S = B / f^alpha, alpha from the model card).

`tran` runs DRAWS transients of T_S seconds of the same frozen deck, each in its own simulator process, with
  device   : one current source per selected device, between its channel terminals, white + 1/f^alpha
             (trnoise, amplitudes from the calibration of GENERATOR.json), and nothing else;
  injected : the four sources of `../../circuit/noise.json`, as in every campaign so far;
  quiet    : no source (the numerical floor),
and writes the mean periodogram of v(xa.vmem1) and the drift of a 40 us average over a time lag.
"""
import json, math, os, re, shutil, subprocess, sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import numpy as np

HERE = Path(__file__).resolve().parent
NETWORK = HERE.parent.parent / "network-circuit"
CIRCUIT = HERE.parent.parent / "circuit"
sys.path.insert(0, str(NETWORK))
import net                                    # noqa: E402
import sim                                    # noqa: E402  (../../sky130-supervisor-closure/sim.py, via net)

NT = 0.4e-6                                   # sample time of every noise source, as in the campaigns
BAND = (10.0, 1.25e6)                         # the band of the ranking: from below 1/run to the sample band
COVER = 0.99                                  # devices kept: the largest shares, until they make 99 % of the power
OUT_NODE = "v(xa.vmem1)"
BENCH = ("rsen", "rrst", "rpreb", "rrsti", "rvcmn", "rvrs", "rvrm", "rnzc", "rnzo", "rnzi", "rnzm")
ALPHA = {"nfet_01v8": 0.84, "pfet_01v8": 1.0, "pfet_01v8_lvt": 0.88}      # ef of the model cards, tt
READ = 40e-6                                  # a read of the stored voltage is its mean over 40 us (run.py)
LAGS = (0.36e-3, 2e-3, 5e-3, 10e-3, 19e-3)    # 18 units, and spans up to a train of 26 reads


def hold_deck(section, injected=False, state="hold"):
    """state "hold": as described above. state "preset": the deck unchanged, whose DC solution is the preset (the
    preset switch is closed at time 0): the operating point whose noise the stored voltage samples at the end of the
    preset."""
    t = net.deck(cells=("a",), section=section, noise=injected)
    for port in ("1", "2") if state == "hold" else ():    # the preset switch becomes a noiseless 1e14 ohm resistor
        t = net.swap(t, f"s.xa.x{port}.srst xa.x{port}.sum xa.x{port}.drv xa.x{port}.rsti 0 swr",
                     f"r.hold{port} xa.x{port}.sum xa.x{port}.drv 1e14 noisy=0")
    t = net.swap(t, "\nvcm vcm 0 {vcm}\n", "\nvcm vcm 0 {vcm} ac 1\n")     # an input for the noise command only
    out = []
    for line in t.splitlines():
        name = line.split(" ", 1)[0]
        if name.startswith("r.") and name.rsplit(".", 1)[-1] in BENCH:
            line += " noisy=0"
        out.append(line)
    return "\n".join(out) + "\n"


def vec(d, kind):
    """The name of the output noise density of a device in the noise1 plot."""
    return f"onoise_r.{d}" if kind == "res" else f"onoise.m.{d}.msky130_fd_pr__{kind}"


def devices(text):
    """name -> (node a, node b, kind) for every transistor (drain, source) and every resistor of the deck."""
    out = {}
    for line in text.splitlines():
        f = line.split()
        if not f:
            continue
        m = re.search(r"sky130_fd_pr__(\w+)", line)
        if f[0].startswith("xa.") and m:
            out[f[0]] = (f[1], f[3], m.group(1))
        elif f[0].startswith("r."):
            out[f[0][2:]] = (f[1], f[2], "res")
    return out


def spice(work, text, ngspice, pdk):
    work.mkdir(parents=True, exist_ok=False)
    (work / "pdk").symlink_to(Path(pdk).resolve(), target_is_directory=True)
    shutil.copyfile(CIRCUIT / "spiceinit.txt", work / ".spiceinit")
    (work / "deck.spice").write_text(text)
    env = dict(os.environ, SPICE_SCRIPTS=str(sim.SPINIT.parent))
    p = subprocess.run([ngspice, "-b", "deck.spice"], cwd=work, env=env, capture_output=True, text=True)
    (work / "log.txt").write_text(p.stdout + p.stderr)
    return p.stdout


def raw_ascii(path):
    """Variables and real values of an ASCII raw file of ngspice (one plot)."""
    lines = Path(path).read_text().splitlines()
    nv = int(next(l for l in lines if l.startswith("No. Variables:")).split(":")[1])
    npts = int(next(l for l in lines if l.startswith("No. Points:")).split(":")[1])
    i = lines.index("Variables:")
    names = [lines[i + 1 + k].split()[1] for k in range(nv)]
    vals = [x for l in lines[lines.index("Values:") + 1:] for x in l.split()]
    data = np.zeros((npts, nv))
    pos = 0
    for p in range(npts):
        pos += 1                                       # point index
        for k in range(nv):
            data[p, k] = float(vals[pos].split(",")[0]); pos += 1
    return {n: data[:, k] for k, n in enumerate(names)}


OP_NODES = ("xa.vmem1", "xa.x1.sum", "xa.x1.xop.o1", "xa.x1.xop.o1m", "xa.x1.xcmps.o1m", "xa.xcmpm.o1m")


def op_lines():
    return ["op"] + [f"echo OP {n} $&v({n})" for n in OP_NODES]


def read_op(stdout):
    return {l.split()[1]: float(l.split()[2]) for l in stdout.splitlines() if l.startswith("OP ")}


ALLOWED_SEEDS = (7101, 7102, 7103)        # the development instances; every other seed is refused (7501-7520: campaign 4)


def seeded(seed):
    assert seed is None or seed in ALLOWED_SEEDS, f"seed {seed} is not a development instance of the noise study"
    return [f"setseed {seed}", "reset"] if seed is not None else []


def extract(work, out, section, seed, ngspice, pdk, state="hold"):
    text = hold_deck(section, state=state)
    devs = devices(text)
    body = text.replace("\n.end\n", "\n")
    ctl = [".control", "set numdgt=16", "set filetype=ascii"] + seeded(seed) + op_lines() + [
        f"noise {OUT_NODE} vcm dec 20 1 1e8 1", "setplot noise1", "write noise.raw all", "quit", ".endc", ".end"]
    stdout = spice(work / "noise", body + "\n".join(ctl) + "\n", ngspice, pdk)
    r = raw_ascii(work / "noise" / "noise.raw")
    f = r["frequency"]
    band = (f >= BAND[0]) & (f <= BAND[1])
    total = r["onoise_spectrum"] ** 2
    integ = lambda s: float(np.trapezoid(s[band], f[band]))
    p_total = integ(total)
    share = {}
    for d, (_, _, kind) in devs.items():
        key = vec(d, kind)
        if key in r:
            share[d] = integ(r[key] ** 2) / p_total
    order = sorted(share, key=share.get, reverse=True)
    keep, acc = [], 0.0
    for d in order:
        if acc >= COVER:
            break
        keep.append(d); acc += share[d]
    # transfer from a unit current between the two terminals of each kept device to the output
    inj = [f"iinj{k} {devs[d][0]} {devs[d][1]} dc 0 ac 0" for k, d in enumerate(keep)]
    ctl = [".control", "set numdgt=16", "set filetype=ascii"] + seeded(seed) + op_lines()
    for k in range(len(keep)):
        ctl += [f"alter @iinj{k}[acmag]=1", "ac dec 20 1 1e8", f"let h{k} = mag({OUT_NODE})",
                f"write h{k}.raw h{k}", f"alter @iinj{k}[acmag]=0"]
    ctl += ["quit", ".endc", ".end"]
    stdout2 = spice(work / "ac", body + "\n".join(inj + ctl) + "\n", ngspice, pdk)
    model = []
    for k, d in enumerate(keep):
        h = list(raw_ascii(work / "ac" / f"h{k}.raw").values())[1]
        a, b, kind = devs[d]
        key = vec(d, kind)
        if kind == "res":
            th, fl, alpha = r[key + "_thermal"] ** 2 / h ** 2, np.zeros_like(h), 1.0
        else:
            th, fl, alpha = r[key + ".id"] ** 2 / h ** 2, r[key + ".1overf"] ** 2 / h ** 2, ALPHA[kind]
        rest = (r[key] ** 2 - r[key + ("_thermal" if kind == "res" else ".id")] ** 2
                - (0 if kind == "res" else r[key + ".1overf"] ** 2))
        other = float(integ(np.maximum(rest, 0)) / integ(r[key] ** 2))    # gate, body resistance: not modelled
        sel = band & (h > 1e-3 * h[band].max())        # where the device reaches the output
        A = float(np.median(th[sel]))
        B = float(np.median(fl[sel] * f[sel] ** alpha))
        flat_th = float(np.percentile(th[sel], 95) / max(np.percentile(th[sel], 5), 1e-300))
        flat_fl = float(np.percentile(fl[sel] * f[sel] ** alpha, 95) / max(np.percentile(fl[sel] * f[sel] ** alpha, 5), 1e-300)) if B > 0 else None
        model.append(dict(device=d, kind=kind, nodes=[a, b], share=share[d], other_parts=other, alpha=alpha, white_A2_Hz=A, flicker_B=B,
                          spread_white_p95_p5=flat_th, spread_flicker_p95_p5=flat_fl,
                          corner_Hz=(B / A) ** (1 / alpha) if A > 0 and B > 0 else None))
        print(f"{d:40s} {kind:14s} share {share[d]:.4f}  A {A:.3e}  B {B:.3e}  spread {flat_th:.2f} {flat_fl}")
    unranked = 1.0 - sum(share.values())          # switches and anything else without a device vector here
    res = dict(section=section, seed=seed, state=state, unranked_share=unranked, output=OUT_NODE, band_Hz=BAND, cover=COVER, op=read_op(stdout),
               op_ac=read_op(stdout2), devices_in_deck=len(devs), devices_ranked=len(share), kept=len(keep),
               covered=acc, onoise_V2_Hz=dict(f=f.tolist(), total=total.tolist()), model=model)
    out.write_text(json.dumps(res, indent=1) + "\n")


def calibration():
    g = json.loads((HERE / "GENERATOR.json").read_text())
    c = {}
    for a, v in g["alphas"].items():
        rows = [b for b in v["bands"] if 1e3 <= b["band_Hz"][0] < 5e5]     # where the estimate is tight
        c[float(a)] = float(np.mean([b["c_flicker"] for b in rows]))
    return c


def device_sources(model):
    c = calibration()
    out = []
    for k, m in enumerate(model["model"]):
        g = math.sqrt(m["white_A2_Hz"] / (2 * NT)) / 1e-3          # gain such that the white part is 1 mV rms
        na = 1e-3
        namp = math.sqrt(m["flicker_B"] / c[m["alpha"]]) / g if m["flicker_B"] > 0 else 0.0
        a, b = m["nodes"]
        out += [f"vnzd{k} nzd{k} 0 dc 0 trnoise({na:.10g} {NT:g} {m['alpha'] if namp else 0:g} {namp:.10g})",
                f"rnzd{k} nzd{k} 0 1k noisy=0", f"gnzd{k} {a} {b} nzd{k} 0 {g:.10g}"]
    return out


def one_tran(work, text, ngspice, pdk, tstop, seed):
    ctl = [".control", "set numdgt=16"] + seeded(seed) + op_lines() + [
        f"save {OUT_NODE}", f"tran {NT:g} {tstop:g} 0 200n", f"linearize {OUT_NODE}", f"wrdata out.txt {OUT_NODE}",
        "quit", ".endc", ".end"]
    import time
    t0 = time.time()
    stdout = spice(work, text.replace("\n.end\n", "\n") + "\n".join(ctl) + "\n", ngspice, pdk)
    wall = time.time() - t0
    x = np.loadtxt(work / "out.txt")[:, 1]
    return x, wall, read_op(stdout)


def tran(work, out, model_path, mode, tstop, draws, ngspice, pdk):
    model = json.loads(Path(model_path).read_text())
    text = hold_deck(model["section"], injected=mode == "injected")
    if mode == "device":
        text = text.replace("\n.end\n", "\n" + "\n".join(device_sources(model)) + "\n.end\n")
    with ThreadPoolExecutor(4) as ex:
        res = list(ex.map(lambda i: one_tran(work / f"{mode}{i:02d}", text, ngspice, pdk, tstop, model["seed"]), range(draws)))
    skip = int(50e-6 / NT)                                   # the first 50 us: the start of the transient
    xs = [x[skip:] for x, _, _ in res]
    n = min(len(x) for x in xs)
    xs = np.array([x[:n] for x in xs])
    w = np.hanning(n)
    fr = np.fft.rfftfreq(n, NT)
    psd = np.mean([2 * NT * abs(np.fft.rfft((x - x.mean()) * w)) ** 2 / np.sum(w ** 2) for x in xs], 0)
    k = int(READ / NT)
    reads = np.array([np.convolve(x, np.ones(k) / k, mode="valid") for x in xs])
    drift = {}
    for lag in LAGS:
        L = int(round(lag / NT))
        if L < reads.shape[1]:
            d = reads[:, L:] - reads[:, :-L]
            drift[f"{lag:g}"] = float(np.sqrt(np.mean(d ** 2)))
    # the same from the .noise spectrum: Var = int S(f) sinc^2(pi f READ) 4 sin^2(pi f lag) df
    f0, s0 = np.array(model["onoise_V2_Hz"]["f"]), np.array(model["onoise_V2_Hz"]["total"])
    ff = np.logspace(0, 8, 20001)
    ss = np.interp(np.log(ff), np.log(f0), s0)
    drift_noise = {f"{lag:g}": float(np.sqrt(np.trapezoid(ss * np.sinc(ff * READ) ** 2 * 4 * np.sin(np.pi * ff * lag) ** 2, ff)))
                   for lag in LAGS}
    bands = []
    edges = 10 ** np.arange(1, 6.2, 1 / 3)
    for lo, hi in zip(edges[:-1], edges[1:]):
        m = (fr >= lo) & (fr < hi)
        if m.sum() < 2:
            continue
        ref = np.interp(np.log(fr[m]), np.log(f0), s0)
        ratio = float(np.mean(psd[m]) / np.mean(ref))
        se = float(np.std([np.mean(2 * NT * abs(np.fft.rfft((x - x.mean()) * w))[m] ** 2 / np.sum(w ** 2)) for x in xs])
                   / np.sqrt(len(xs)) / np.mean(ref))
        bands.append(dict(band_Hz=[float(lo), float(hi)], bins=int(m.sum()), tran_over_noise=ratio, se=se))
    out_res = dict(mode=mode, tstop_s=tstop, draws=draws, wall_s=[w_ for _, w_, _ in res], op=[o for _, _, o in res],
                   sources=len(model["model"]) if mode == "device" else (4 if mode == "injected" else 0),
                   rms_V=float(np.sqrt(np.mean(xs.var(1)))), drift_rms_V=drift, drift_from_noise_V=drift_noise,
                   run_mean_sd_V=float(np.std(xs.mean(1), ddof=1)), bands=bands)
    for b in bands:
        print(f"{b['band_Hz'][0]:10.1f} {b['band_Hz'][1]:10.1f}  tran/.noise {b['tran_over_noise']:.3f} +- {b['se']:.3f}")
    print("drift", drift, "from .noise", drift_noise, "wall", out_res["wall_s"])
    Path(out).write_text(json.dumps(out_res, indent=1) + "\n")


def op_check(work, out, section, seed, ngspice, pdk):
    """The operating point of the hold deck under a mismatch seed, twice, and the first point of the network deck."""
    text = hold_deck(section).replace("\n.end\n", "\n")
    res = {}
    for k in range(2):
        ctl = [".control", "set numdgt=16"] + seeded(seed) + op_lines() + ["quit", ".endc", ".end"]
        res[f"hold_{k}"] = read_op(spice(work / f"op{k}", text + "\n".join(ctl) + "\n", ngspice, pdk))
    plain = net.deck(cells=("a",), section=section).replace("\n.end\n", "\n")
    ctl = [".control", "set numdgt=16"] + seeded(seed) + op_lines() + ["quit", ".endc", ".end"]
    res["network_deck"] = read_op(spice(work / "opnet", plain + "\n".join(ctl) + "\n", ngspice, pdk))
    print(json.dumps(res, indent=1))
    Path(out).write_text(json.dumps(dict(section=section, seed=seed, op=res), indent=1) + "\n")


if __name__ == "__main__":
    cmd, a = sys.argv[1], sys.argv[2:]
    seed = lambda s: None if s == "none" else int(s)
    if cmd == "extract":
        extract(Path(a[0]), Path(a[1]), a[2], seed(a[3]), a[4], a[5], *(a[6:7] or ["hold"]))
    elif cmd == "tran":
        tran(Path(a[0]), Path(a[1]), a[2], a[3], float(a[4]), int(a[5]), a[6], a[7])
    elif cmd == "op":
        op_check(Path(a[0]), Path(a[1]), a[2], seed(a[3]), a[4], a[5])
