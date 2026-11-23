"""One inverter instance with SKY130 mismatch: decks, runs and stand-alone measures.

Development work, not a preregistered campaign. The cell is the inverter cell of ../inverter.py (iteration 2),
unchanged, except for the model section: `tt_mm` in place of `tt`, and a mismatch sample drawn by ngspice's
`setseed S` then `reset`, before the analysis, as run.py's `_mm` sections do. One seed is one instance. Noise
sources stay at zero (the noise allowance enters the K3 verdict of the gate as an added threshold error).

Every run of one instance uses the same netlist text (only the independent sources differ), so the device sample
is the same in every run; each log records a fingerprint of the operating point of the FIRE comparator, and
measure() refuses an instance whose fingerprints differ.

Runs, all from the same deck text except the sources:
  R1 absent   help on, input absent, reset on, 1.3 time units, step <= 5 ns
  R2 present  help on, input present, reset on, 1.3, 5 ns
  R3 leak +   help on, input absent, no reset, 4.0, 20 ns: leak above rest, fitted on [1, 4]
  R4 leak -   help off, input present, no reset, 4.0, 20 ns: leak below rest, fitted on [0.5, 4]
  R5 static   the main capacitor node is driven by an ideal slow ramp through the FIRE level: the static
              threshold, and the comparator and latch delays at a known slope
Usage: python instance.py SEED OUTDIR     (writes OUTDIR/SEED/MEASURE.json)
"""
import hashlib, json, math, subprocess, sys, time
from pathlib import Path
import numpy as np

HERE = Path(__file__).resolve().parent
CELL = HERE.parent                                   # research/circuit/inverter
sys.path.insert(0, str(CELL))
import inverter as I                                 # the pushed cell, imported, not modified

TU, T0, UNIT, VR0, VUNIT, LEVEL = I.TU, I.T0, I.UNIT, I.VR0, I.VUNIT, I.LEVEL
d = I.DESIGN
UNIT_PER_S = TU / UNIT
SECTION = __import__("os").environ.get("INV_SECTION", "tt_mm")   # "tt" only for the nominal sanity check
FINGER = ("v(ibm)", "@m.xcmpm.xm1.msky130_fd_pr__pfet_01v8_lvt[vth]", "@m.xcmpm.xm2.msky130_fd_pr__pfet_01v8_lvt[vth]",
          "@m.xmh1.msky130_fd_pr__nfet_01v8[vth]", "@m.xmj1.msky130_fd_pr__pfet_01v8[vth]")
FINGER_TOL = 1e-4   # volts: vth moves slightly with the bias, which differs between runs; a new draw moves it by mV
RAMP = dict(v_hi=0.85, v_lo=0.75, lead_tu=0.2, ramp_tu=2.0)   # R5: 1.25 -> 0.85 V in 0.2 tu, then 0.85 -> 0.75 V in 2 tu


def deck(seed, present, help_on=True, reset=True, forced=False):
    text = I.netlist(present=present, help_on=help_on, reset=reset)
    old = '.lib "pdk/models/sky130.lib.spice" tt\n'
    assert old in text
    text = text.replace(old, f'.lib "pdk/models/sky130.lib.spice" {SECTION}\n')
    if forced:   # R5: the main capacitor stays, an ideal source drives its node through a 1 ohm resistor
        s = lambda x: f"{T0 + x * TU:.12g}"
        r = RAMP
        pwl = (f"0 {VR0} {s(0)} {VR0} {s(r['lead_tu'])} {r['v_hi']} {s(r['lead_tu'] + r['ramp_tu'])} {r['v_lo']}")
        text = text.replace("\n.option temp=27\n", f"\nvforce vfn 0 pwl({pwl})\nrforce vfn vq 1\n.option temp=27\n")
    return text


def run(folder, seed, text, tstop, maxstep):
    folder.mkdir(parents=True, exist_ok=True)
    pdk = folder / "pdk"
    if not pdk.exists():
        pdk.symlink_to(CELL.parent / "pdk", target_is_directory=True)
    (folder / "blocks.spice").write_text((CELL.parent / "blocks.spice").read_text())
    (folder / ".spiceinit").write_text((CELL.parent / "spiceinit.txt").read_text())
    control = f"""
.control
setseed {seed}
reset
op
echo FINGER {' '.join(f'$&{n}' for n in FINGER)}
set wr_singlescale
set wr_vecnames
option numdgt=12
tran 1n {tstop:.12g} 0 {maxstep}
wrdata trace.txt v(vq) i(vah) i(vaj) v(p) v(cmpm) v(khelp) v(kinb) v(krst)
quit
.endc
"""
    deckt = text.replace("\n.end\n", control + ".end\n")
    (folder / "input.spice").write_text(deckt)
    t0 = time.time()
    out = subprocess.run(["ngspice", "-b", "input.spice"], cwd=folder, capture_output=True, text=True, timeout=3600)
    wall = time.time() - t0
    log = out.stdout + out.stderr
    (folder / "ngspice.log").write_text(log)
    if out.returncode or not (folder / "trace.txt").exists() or "aborted" in log or "too small" in log:
        raise RuntimeError(f"{folder.name}: ngspice failed\n" + log[-3000:])
    finger = [l.split()[1:] for l in out.stdout.splitlines() if l.startswith("FINGER")]
    data = np.loadtxt(folder / "trace.txt", skiprows=1)
    c = dict(t=data[:, 0], vq=data[:, 1], H=data[:, 2] * UNIT_PER_S, J=data[:, 3] * UNIT_PER_S, p=data[:, 4],
             cmp=data[:, 5])
    c["x"] = (VR0 - c["vq"]) / VUNIT
    files = {f: sha(folder / f) for f in ("input.spice", "trace.txt", "ngspice.log")}
    return c, dict(files=files, wall_s=wall, finger=finger[0] if finger else None, points=int(len(c["t"])))


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


u = lambda t: (t - T0) / TU


def integ(c, y, a_tu, b_tu):
    return I.integral(c["t"], y, T0 + a_tu * TU, T0 + b_tu * TU) / TU


def first_cross(t, y, level, after, rising=True):
    """Date of the first crossing of `level` by y after `after`, linearly interpolated; None if none."""
    sel = np.nonzero(t >= after)[0]
    yy = y[sel]
    hit = np.nonzero(yy >= level if rising else yy <= level)[0]
    if not len(hit):
        return None
    k = sel[hit[0]]
    if k == 0:
        return float(t[0])
    y0, y1 = y[k - 1], y[k]
    return float(t[k - 1] + (level - y0) * (t[k] - t[k - 1]) / (y1 - y0)) if y1 != y0 else float(t[k])


def cmp_flip(c, after):
    """First change of state of the FIRE comparator output after `after` (mid-rail crossing, either sense)."""
    t, y = c["t"], c["cmp"]
    k0 = np.argmax(t >= after)
    rising = y[k0] < 0.9
    return first_cross(t, y, 0.9, after, rising=rising)


def help_window(c):
    H, t = c["H"], c["t"]
    H0 = np.where((t >= T0 + d["h"] * TU) & (t < T0 + (d["h"] + d["hl"]) * TU), d["H0"], 0.0)
    err = np.abs(H - H0)
    grid = np.linspace(0, d["D"], 201)
    prefix = [integ(c, err, 0, b) for b in grid[1:]]
    return dict(help_charge_window=integ(c, H, d["h"], d["h"] + d["hl"]), help_L1_error_max_prefix=max(prefix))


def leak_fit(c, a_tu, b_tu):
    """x = x_inf + c exp(-k (t - a)) by least squares (k on a grid of 1e-5), and the plain log-linear fit."""
    sel = (c["t"] >= T0 + a_tu * TU) & (c["t"] <= T0 + b_tu * TU)
    tt, xx = u(c["t"][sel]), c["x"][sel]
    if np.any(xx == 0) or np.any(np.sign(xx) != np.sign(xx[0])):
        raise RuntimeError("x changes sign in the fit window")
    slope = np.polyfit(tt, np.log(np.abs(xx)), 1)[0]
    best = None
    for k in np.linspace(0.40, 0.60, 20001):
        A = np.vstack([np.ones_like(tt), np.exp(-k * (tt - a_tu))]).T
        coef, res, *_ = np.linalg.lstsq(A, xx, rcond=None)
        r = float(np.sum((A @ coef - xx) ** 2))
        if best is None or r < best[0]:
            best = (r, k, coef)
    return dict(rate_loglin=float(-slope), rate_offset=float(best[1]), asymptote_x=float(best[2][0]),
                fit_rms=float(math.sqrt(best[0] / len(tt))))


def measure(seed, outdir):
    t_start = time.time()
    root = Path(outdir) / str(seed)
    meta = {}
    c1, meta["R1"] = run(root / "R1_absent", seed, deck(seed, False), T0 + 1.3 * TU, "5n")
    c2, meta["R2"] = run(root / "R2_present", seed, deck(seed, True), T0 + 1.3 * TU, "5n")
    c3, meta["R3"] = run(root / "R3_leak_help", seed, deck(seed, False, reset=False), T0 + 4.0 * TU, "20n")
    c4, meta["R4"] = run(root / "R4_leak_inhib", seed, deck(seed, True, help_on=False, reset=False), T0 + 4.0 * TU, "20n")
    r = RAMP
    c5, meta["R5"] = run(root / "R5_static", seed, deck(seed, False, help_on=False, reset=False, forced=True),
                         T0 + (r["lead_tu"] + r["ramp_tu"] + 0.1) * TU, "5n")
    fingers = {k: v["finger"] for k, v in meta.items()}
    ref = fingers["R1"]   # the help mirror's diode carries no current in R4 and R5: its vth is compared on R1-R3 only
    same_sample = None not in fingers.values() and all(
        abs(float(a) - float(b)) <= FINGER_TOL for k, v in fingers.items()
        for j, (a, b) in enumerate(zip(v, ref)) if not (j == 3 and k in ("R4", "R5")))

    m = {}
    slot = lambda c: (c["t"] >= T0) & (c["t"] <= T0 + d["D"] * TU)
    # threshold: static trip point on the ideal ramp (R5)
    t_cmp5 = cmp_flip(c5, T0 + r["lead_tu"] * TU * 0.5)
    t_p5 = first_cross(c5["t"], c5["p"], 0.9, T0)
    x_trip = float(np.interp(t_cmp5, c5["t"], c5["x"])) if t_cmp5 else None
    ramp_slope = (r["v_hi"] - r["v_lo"]) / VUNIT / r["ramp_tu"]          # units of x per time unit
    m["actual_level_x"] = x_trip
    m["delta"] = abs(x_trip - LEVEL) if x_trip is not None else None
    m["delta_signed"] = x_trip - LEVEL if x_trip is not None else None
    m["static_ramp_slope_x_per_tu"] = ramp_slope
    m["static_latch_delay_tu"] = u(t_p5) - u(t_cmp5) if (t_p5 and t_cmp5) else None
    # R1: firing without inhibition
    t_cross1 = first_cross(c1["t"], c1["x"], x_trip, T0) if x_trip is not None else None
    t_lvl1 = first_cross(c1["t"], c1["x"], LEVEL, T0)
    t_cmp1 = cmp_flip(c1, T0)
    t_p1 = first_cross(c1["t"], c1["p"], 0.9, T0)
    m["emit_absent_tu"] = u(t_p1) if t_p1 else None
    m["cross_actual_level_tu"] = u(t_cross1) if t_cross1 else None
    m["cross_level_tu"] = u(t_lvl1) if t_lvl1 else None
    m["comparator_delay_tu"] = u(t_cmp1) - u(t_cross1) if (t_cmp1 and t_cross1) else None
    m["latch_delay_tu"] = u(t_p1) - u(t_cross1) if (t_p1 and t_cross1) else None
    m["x_slope_at_cross_per_tu"] = float(np.interp(t_cross1 + 1e-9, c1["t"], np.gradient(c1["x"], u(c1["t"])))) if t_cross1 else None
    m["delta_dynamic"] = float(np.interp(t_cmp1, c1["t"], c1["x"])) - LEVEL if t_cmp1 else None
    m["x_max_absent"] = float(c1["x"][slot(c1)].max())
    m["eta_J_off_charge_L1"] = integ(c1, np.abs(c1["J"]), 0, d["D"])
    hw1 = help_window(c1)
    # R2: silence under inhibition
    s2 = slot(c2)
    m["fired_present"] = bool((c2["p"][s2] > 0.9).any())
    m["emit_present_tu"] = u(first_cross(c2["t"], c2["p"], 0.9, T0)) if m["fired_present"] else None
    m["x_max_present"] = float(c2["x"][s2].max())
    m["x_min_present"] = float(c2["x"][s2].min())
    m["Q_by_tau"] = integ(c2, np.maximum(c2["J"], 0), 0, d["tau"])
    m["eta_m_wrong_sign_L1"] = integ(c2, np.maximum(-c2["J"], 0), 0, d["D"])
    m["inhibitory_after_tau_L1"] = integ(c2, np.abs(c2["J"]), d["tau"] + 0.005, d["D"])
    m["vq_max_present"] = float(c2["vq"][s2].max())
    hw2 = help_window(c2)
    m["eta_H"] = max(hw1["help_L1_error_max_prefix"], hw2["help_L1_error_max_prefix"])
    m["help_charge_window"] = [hw1["help_charge_window"], hw2["help_charge_window"]]
    # initial error: x at the slot start, and x after the reset (the next slot's start)
    after = lambda c: float(np.interp(T0 + (d["D"] + d["reset_len"] + 0.05) * TU, c["t"], c["x"]))
    at0 = lambda c: float(np.interp(T0, c["t"], c["x"]))
    m["x_slot_start"] = [at0(c1), at0(c2)]
    m["x_after_reset"] = [after(c1), after(c2)]
    m["eps0"] = max(abs(v) for v in m["x_slot_start"] + m["x_after_reset"])
    # leak on both sides of rest
    m["leak_above"] = leak_fit(c3, 1.0, 4.0)
    m["leak_below"] = leak_fit(c4, 0.5, 4.0)
    a_up, a_dn = m["leak_above"]["rate_offset"], m["leak_below"]["rate_offset"]
    m["a_actual"] = a_up            # the side the uninhibited response rises on
    m["a_prime"] = a_dn             # the side the inhibited response sits on
    m["leak_asymmetry"] = abs(a_up - a_dn)
    m["same_sample"] = same_sample
    m["fingerprints"] = fingers
    m["machine_s"] = {k: v["wall_s"] for k, v in meta.items()}
    m["machine_s_total"] = time.time() - t_start
    out = dict(seed=seed, section=SECTION, design=d, level_x=LEVEL, ramp=RAMP, measures=m,
               files={k: v["files"] for k, v in meta.items()},
               code={n: sha(p) for n, p in (("instance.py", HERE / "instance.py"), ("inverter.py", CELL / "inverter.py"),
                                            ("blocks.spice", CELL.parent / "blocks.spice"),
                                            ("spiceinit.txt", CELL.parent / "spiceinit.txt"))})
    (root / "MEASURE.json").write_text(json.dumps(out, indent=1, sort_keys=True))
    return out


if __name__ == "__main__":
    o = measure(int(sys.argv[1]), sys.argv[2])
    print(json.dumps(o["measures"], indent=1, sort_keys=True))
