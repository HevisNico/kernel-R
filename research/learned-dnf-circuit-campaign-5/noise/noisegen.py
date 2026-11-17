"""Phase 0, feasibility, no claim: noise samples drawn outside the simulator, from a noise seed fixed by rule.

  noisegen.py psd OUT.json DRAWS             the spectrum of the generator itself, against its target (no simulator)
  noisegen.py seeds WORK OUT.json NGSPICE PDK
      on instance 7101 (two cells), the same deck with the device sources of the hold point under the noise seeds
      71011, 71012 and 71011 again: operating points, and whether the stored voltages are the same or differ

Why: `trnoise` draws from a generator that ngspice 42 seeds from its own process number. `setseed`, the `seed`
option and `rndseed` do not change it (`../../circuit/DESIGN.md`, "Noise"), so the noise of a run cannot be fixed
in advance. Here every noise source is a PWL source whose samples are computed with numpy from
  numpy.random.default_rng(numpy.random.SeedSequence([noise_seed, source_index]))
and written into the deck. The simulator draws no random number for the noise, so the mismatch sample set by
`setseed` is untouched by construction; the same noise seed gives the same run, and two seeds give two draws.

The rule proposed for campaign 4: noise seed = 10 x instance seed + round (round 1, 2, 3, ...), and source_index =
the position of the source in the sorted list of its device names. Each sample is held at a date k NT, with
NT = 0.4 us as in the campaigns; between samples the source is linear, as `trnoise` is. Sample 0 (at time 0) is 0,
as with `trnoise`, so that the operating point does not depend on the noise.

A source is white (density A, one-sided, in the unit of the source squared per Hz) plus 1/f^alpha (B / f^alpha),
the parameters of `model.py`. The 1/f^alpha part is made by shaping a white Gaussian sequence in the frequency
domain over a sequence twice the run long (so that its lowest frequency is below 1 / run), its mean set to zero.
"""
import hashlib, json, math, sys
from pathlib import Path
import numpy as np

NT = 0.4e-6
T_CAMPAIGN = 1e5          # s: the declared span of the slow part, so its lowest frequency is 1e-5 Hz
RUN_GAP = 1000.0          # s: the virtual start of run k of an instance (its position in the instance's run list,
                          # from 0, every run of the instance counted, measures and network runs) is k x RUN_GAP
PER_DECADE = 20           # components of the slow part per decade


def slow_part(instance_key, index, t, B, alpha, f_hi):
    """The 1/f^alpha part from 1/T_CAMPAIGN up to f_hi, at the virtual times t, as a sum of components
    a cos + b sin on log-spaced bands, a and b Gaussian with the variance of B/f^alpha over their band. One realization
    per instance and source (keyed by instance_key, not by the noise seed of the run): the runs of an instance share
    it, each at its own virtual time, so that two runs of an instance differ by what 1/f noise does over RUN_GAP."""
    f_lo = 1.0 / T_CAMPAIGN
    if B <= 0 or f_hi <= f_lo:
        return np.zeros_like(t)
    k = max(1, int(math.ceil(PER_DECADE * math.log10(f_hi / f_lo))))
    edges = f_lo * (f_hi / f_lo) ** (np.arange(k + 1) / k)
    if alpha == 1.0:
        var = B * np.log(edges[1:] / edges[:-1])
    else:
        var = B * (edges[1:] ** (1 - alpha) - edges[:-1] ** (1 - alpha)) / (1 - alpha)
    fc = np.sqrt(edges[1:] * edges[:-1])
    rng = np.random.default_rng(np.random.SeedSequence([int(instance_key), int(index), 1]))
    a, b = rng.standard_normal(k) * np.sqrt(var), rng.standard_normal(k) * np.sqrt(var)
    w = 2 * np.pi * np.outer(t, fc)
    return np.cos(w) @ a + np.sin(w) @ b


def samples(noise_seed, index, n, A, B=0.0, alpha=1.0, slow=None):
    """n + 1 samples at 0, NT, ..., n NT of a source with one-sided density A + B / f^alpha.
    The 1/f^alpha part is shaped over m >= 2 (n + 1) samples: it holds the frequencies from 1/(m NT) up. With
    slow = (instance_key, run_position), the part from 1/T_CAMPAIGN to 1/(2 m NT) is added from slow_part, at the
    virtual times run_position x RUN_GAP + k NT; without it, nothing slower than about 1/(2 T_run) is present."""
    rng = np.random.default_rng(np.random.SeedSequence([int(noise_seed), int(index)]))
    x = rng.standard_normal(n + 1) * math.sqrt(A / (2 * NT))
    if B > 0:
        m = 1 << int(math.ceil(math.log2(2 * (n + 1))))
        f = np.fft.rfftfreq(m, NT)
        s = np.zeros_like(f)
        s[1:] = B / f[1:] ** alpha
        z = (rng.standard_normal(len(f)) + 1j * rng.standard_normal(len(f))) * np.sqrt(s * m / (4 * NT))
        z[0] = 0
        if m % 2 == 0:
            z[-1] = z[-1].real * math.sqrt(2)
        y = np.fft.irfft(z, m)[: n + 1]
        x = x + y
        if slow is not None:
            key, pos = slow
            t = pos * RUN_GAP + np.arange(n + 1) * NT
            x = x + slow_part(key, index, t, B, alpha, 0.5 / (m * NT))
    x[0] = 0.0
    return x


def pwl(name, node, values, gain_unit="v"):
    """A PWL voltage source on its own node, one sample per NT, with continuation lines."""
    pts = " ".join(f"{k * NT:.6e} {v:.6e}" for k, v in enumerate(values))
    return f"{name} {node} 0 pwl({pts})"


def fingerprint(values):
    return hashlib.sha256(np.round(np.asarray(values) * 1e9).astype(np.int64).tobytes()).hexdigest()


def psd_check(out, draws, first_seed=1000):
    """The generator against its target: A = 1e-12, B = 1e-8 at alpha 0.84, 0.88, 1.0; 40 ms; DRAWS seeds from
    first_seed. Also the slow part: the variance of one run's value and of the difference between two runs RUN_GAP
    apart, over DRAWS instance keys, against the integral of B/f^alpha over its band."""
    n = int(40e-3 / NT)
    res = {}
    for alpha in (0.84, 0.88, 1.0):
        A, B = 1e-12, 1e-8
        P = []
        for d in range(draws):
            x = samples(first_seed + d, 0, n, A, B, alpha)[1:]
            fr = np.fft.rfftfreq(len(x), NT)
            P.append(2 * NT / len(x) * abs(np.fft.rfft(x - x.mean())) ** 2)
        P = np.mean(P, 0)
        # the target seen through linear interpolation between samples is the sampled sequence's own spectrum:
        # compare the sequence (not the interpolated waveform) with A + B / f^alpha
        rows = []
        edges = 10 ** np.arange(1.5, 6.2, 0.5)
        for lo, hi in zip(edges[:-1], edges[1:]):
            m = (fr >= lo) & (fr < hi)
            tgt = A + B / fr[m] ** alpha
            rows.append(dict(band_Hz=[float(lo), float(hi)], bins=int(m.sum()), ratio=float(np.mean(P[m]) / np.mean(tgt))))
        m_ = 1 << int(math.ceil(math.log2(2 * (n + 1))))
        f_hi = 0.5 / (m_ * NT)
        v1, v2 = [], []
        for d in range(draws):
            y = slow_part(first_seed + d, 0, np.array([0.0, RUN_GAP]), B, alpha, f_hi)
            v1.append(y[0]); v2.append(y[1] - y[0])
        ff = np.logspace(math.log10(1 / T_CAMPAIGN), math.log10(f_hi), 40001)
        slow = dict(f_hi_Hz=f_hi, var_ratio=float(np.var(v1) / np.trapezoid(B / ff ** alpha, ff)),
                    diff_var_ratio=float(np.var(v2) / np.trapezoid(B / ff ** alpha * 4 * np.sin(np.pi * ff * RUN_GAP) ** 2, ff)))
        res[f"{alpha:g}"] = dict(bands=rows, slow=slow)
        print(alpha, [round(r["ratio"], 3) for r in rows], {k: round(v, 3) for k, v in slow.items()})
    Path(out).write_text(json.dumps(dict(draws=draws, first_seed=first_seed, nt_s=NT, run_s=40e-3, numpy=np.__version__,
                                         t_campaign_s=T_CAMPAIGN, run_gap_s=RUN_GAP, results=res), indent=1) + "\n")


if __name__ == "__main__":
    if sys.argv[1] == "psd":
        psd_check(sys.argv[2], int(sys.argv[3]))


def device_lines(text, model_devices, noise_seed, n, cells):
    """PWL sources and VCCS for the given devices, one per (cell, port, device) of the deck, sorted by name.
    model_devices: {suffix: (A, B, alpha)}, suffix as in 'xop.xm3' (per port) or 'xcmpm.xm1' (per cell)."""
    nodes = {}
    for line in text.splitlines():
        f = line.split()
        if f and "sky130_fd_pr__" in line:
            nodes[f[0]] = (f[1], f[3])
    names = sorted(d for d in nodes if any(d.endswith("." + s) and d.split(".")[0] in [f"x{c}" for c in cells]
                                           for s in model_devices))
    out, prints = [], {}
    for k, d in enumerate(names):
        A, B, alpha = next(v for s, v in model_devices.items() if d.endswith("." + s))
        g = math.sqrt(A / (2 * NT)) / 1e-3                      # the white part of the node is 1 mV rms
        x = samples(noise_seed, k, n, A / g ** 2, B / g ** 2, alpha)
        out += [pwl(f"vnzp{k}", f"nzp{k}", x), f"rnzp{k} nzp{k} 0 1k noisy=0", f"gnzp{k} {nodes[d][0]} {nodes[d][1]} nzp{k} 0 {g:.10g}"]
        prints[d] = fingerprint(x)
    return out, prints


def seeds_check(work, out, ngspice, pdk):
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    import pilot
    from pilot import net
    cells, seed, tstop = ("a", "b"), 7101, 1e-3
    n = int(round(tstop / NT)) + 2
    m = json.loads((Path(__file__).resolve().parent / "MODEL_nominal.json").read_text())
    devs = {d["device"].split(".", 2)[2]: (d["white_A2_Hz"], d["flicker_B"], d["alpha"]) for d in m["model"]}
    base = net.deck(cells=cells, section="tt_mm")
    probes = [f"x{c}.vmem{p}" for c in cells for p in net.PORTS]
    ops = ["xa.x1.xcmps.o1m", "xa.xcmpm.o1m", "xb.x2.xcmps.o1m", "xb.xcmpm.o1m", "xa.x1.xop.o1", "xb.x2.xop.o1m"]
    res = {}
    for tag, ns in (("none", None), ("71011", 71011), ("71012", 71012), ("71011_again", 71011)):
        if ns is None:
            text, prints = base, {}
        else:
            lines, prints = device_lines(base, devs, ns, n, cells)
            text = base.replace("\n.end\n", "\n" + "\n".join(lines) + "\n.end\n")
        ctl = [".control", "set numdgt=16"] + pilot.seeded(seed) + ["op"] + [f"echo OP {x} $&v({x})" for x in ops + probes] + [
            "save " + " ".join(f"v({x})" for x in probes), f"tran {NT:g} {tstop:g} 0 200n",
            "linearize " + " ".join(f"v({x})" for x in probes), "wrdata out.txt " + " ".join(f"v({x})" for x in probes),
            "quit", ".endc", ".end"]
        import time
        t0 = time.time()
        stdout = pilot.spice(Path(work) / tag, text.replace("\n.end\n", "\n") + "\n".join(ctl) + "\n", ngspice, pdk)
        wall = time.time() - t0
        y = np.loadtxt(Path(work) / tag / "out.txt")[:, 1::2]
        res[tag] = dict(noise_seed=ns, op=pilot.read_op(stdout), wall_s=wall, sources=len(prints),
                        source_fingerprints=prints, waveform_sha256=hashlib.sha256(np.round(y * 1e12).astype(np.int64).tobytes()).hexdigest(),
                        rms_from_quiet_uV=None, y=y)
    q = res["none"]["y"]
    for tag in res:
        res[tag]["rms_from_quiet_uV"] = [float(v) for v in 1e6 * np.sqrt(np.mean((res[tag]["y"] - q) ** 2, 0))]
    a, b, c = res["71011"]["y"], res["71012"]["y"], res["71011_again"]["y"]
    summary = dict(
        same_op_all=all(res[t]["op"] == res["none"]["op"] for t in res),
        same_waveform_same_seed=bool(np.array_equal(a, c)),
        rms_difference_two_seeds_uV=[float(v) for v in 1e6 * np.sqrt(np.mean((a - b) ** 2, 0))],
        correlation_two_seeds=[float(np.corrcoef(a[:, i] - q[:, i], b[:, i] - q[:, i])[0, 1]) for i in range(a.shape[1])])
    for t in res:
        del res[t]["y"]
    Path(out).write_text(json.dumps(dict(instance=seed, cells=cells, tstop_s=tstop, probes=probes, runs=res, summary=summary), indent=1) + "\n")
    print(json.dumps(summary, indent=1))
    for t in res:
        print(t, res[t]["wall_s"], res[t]["rms_from_quiet_uV"], res[t]["waveform_sha256"][:16])


if __name__ == "__main__" and sys.argv[1] == "seeds":
    seeds_check(sys.argv[2], sys.argv[3], sys.argv[4], sys.argv[5])
