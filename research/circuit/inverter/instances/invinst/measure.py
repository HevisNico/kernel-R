"""Stand-alone measure of one inverter instance: five runs, every quantity the inverter theorems need.

Runs (config "runs"): R1 input absent, R2 present (both with help and reset, one slot); R3 and R4 the leak above and
below rest (no reset); R5 the main node driven by an ideal slow ramp through the FIRE level (static threshold).
All five decks have the same text except their independent sources, so the device sample is the same; each log
records a fingerprint and the instance is marked `same_sample = false` if any differs by more than the tolerance.

Sign conventions are those of the Lean hypotheses: help H = current out of the main capacitor (raises x),
inhibitory J = current into it (lowers x). Inhibitory J is split pointwise: J+ is `inhibitory` (inhibitorySign holds
by construction), J- is booked into `wrongSign` (ηm), as CircuitInverter.lean requires.
"""
import json, math, time
from pathlib import Path
import numpy as np
from . import cell, sim


def _cols(c, raw):
    tu, unit, t0 = c["tu_s"], cell.unit_coulombs(c), c["settle_s"]
    k = tu / unit
    out = dict(t=raw["t"], H=raw["ih"] * k, J=raw["ij"] * k, p=raw["p"], cmp=raw["cmp"], vq=raw["vq"])
    out["x"] = (c["vr0_V"] - raw["vq"]) / c["vunit_V"]
    out["u"] = (raw["t"] - t0) / tu
    return out


def integral(c, y, a, b):
    """Trapezoidal integral over slot time [a, b] (time units), end points interpolated."""
    u = c["u"]
    grid = np.concatenate(([a], u[(u > a) & (u < b)], [b]))
    return float(np.trapezoid(np.interp(grid, u, y), grid))


def first_cross(u, y, level, after, rising=True):
    idx = np.nonzero(u >= after)[0]
    hit = np.nonzero(y[idx] >= level if rising else y[idx] <= level)[0]
    if not len(hit):
        return None
    k = idx[hit[0]]
    if k == 0 or y[k] == y[k - 1]:
        return float(u[k])
    return float(u[k - 1] + (level - y[k - 1]) * (u[k] - u[k - 1]) / (y[k] - y[k - 1]))


def comparator_flip(c, after):
    k = int(np.argmax(c["u"] >= after))
    return first_cross(c["u"], c["cmp"], 0.9, after, rising=c["cmp"][k] < 0.9)


def help_error(c, cfg):
    H0 = np.where((c["u"] >= cfg["h"]) & (c["u"] < cfg["h"] + cfg["hl"]), cfg["H0"], 0.0)
    err = np.abs(c["H"] - H0)
    return max(integral(c, err, 0, b) for b in np.linspace(0, cfg["D"], 201)[1:])


def leak_fit(c, a, b):
    """x = x_inf + c exp(-k (t - a)), least squares, k on a grid of 1e-5 in [0.40, 0.60]."""
    sel = (c["u"] >= a) & (c["u"] <= b)
    tt, xx = c["u"][sel], c["x"][sel]
    if np.any(xx == 0) or np.any(np.sign(xx) != np.sign(xx[0])):
        raise RuntimeError("x changes sign in the fit window")
    best = None
    for k in np.linspace(0.40, 0.60, 20001):
        A = np.vstack([np.ones_like(tt), np.exp(-k * (tt - a))]).T
        coef = np.linalg.lstsq(A, xx, rcond=None)[0]
        r = float(np.sum((A @ coef - xx) ** 2))
        if best is None or r < best[0]:
            best = (r, k, coef)
    return dict(rate=float(best[1]), asymptote_x=float(best[2][0]), fit_rms=float(math.sqrt(best[0] / len(tt))))


def measure(cfg, seed, outdir, section=None, ngspice="ngspice"):
    """Measure instance `seed` (section tt_mm with its draw; section given: that section, no draw)."""
    t_start = time.time()
    c = cfg["cell"]
    sec = section or cfg["mismatch"]["section"]
    draw = None if section else seed
    root = Path(outdir) / str(seed)
    cols, recs = {}, {}
    for name, r in cfg["runs"].items():
        deck = cell.netlist(c, present=r["present"], help_on=r["help"], reset=r["reset"], section=sec, ramp=r.get("ramp"))
        raw, recs[name] = sim.run(root / name, draw, deck, c["settle_s"] + r["length_tu"] * c["tu_s"], r["maxstep"],
                                  ngspice=ngspice)
        cols[name] = _cols(c, raw)
    tol = cfg["fingerprint_tol_V"]
    ref = recs["R1_absent"]["finger"]
    same = all(rec["finger"] is not None for rec in recs.values()) and all(
        abs(a - b) <= tol for name, rec in recs.items() for j, (a, b) in enumerate(zip(rec["finger"], ref))
        if not (j == 3 and not cfg["runs"][name]["help"]))          # the help diode carries no current without help
    r1, r2, r3, r4, r5 = (cols[n] for n in cfg["runs"])
    D, level = c["D"], c["level_x"]
    slot = lambda q: (q["u"] >= 0) & (q["u"] <= D)
    m = dict(same_sample=same)
    # 8. threshold error: static trip point on the ideal ramp (R5)
    ramp = cfg["runs"]["R5_static"]["ramp"]
    t5 = comparator_flip(r5, ramp["lead_tu"] / 2)
    m["actual_level_x"] = float(np.interp(t5, r5["u"], r5["x"])) if t5 is not None else None
    m["delta"] = abs(m["actual_level_x"] - level) if t5 is not None else None
    m["static_ramp_slope"] = (ramp["v_hi"] - ramp["v_lo"]) / c["vunit_V"] / ramp["ramp_tu"]
    # R1: firing without inhibition; 7. ηJ
    tc = first_cross(r1["u"], r1["x"], m["actual_level_x"], 0) if t5 is not None else None
    tf = comparator_flip(r1, 0)
    te = first_cross(r1["u"], r1["p"], 0.9, 0)
    m["contact_tu"] = tc
    m["emit_absent_tu"] = te
    m["comparator_delay_tu"] = tf - tc if (tf is not None and tc is not None) else None
    m["latch_delay_tu"] = te - tc if (te is not None and tc is not None) else None
    m["delta_dynamic"] = float(np.interp(tf, r1["u"], r1["x"])) - level if tf is not None else None
    m["x_max_absent"] = float(r1["x"][slot(r1)].max())
    m["etaJ"] = integral(r1, np.abs(r1["J"]), 0, c["h"] + c["hl"])       # offCharge over [0, deadline]
    m["etaJ_slot"] = integral(r1, np.abs(r1["J"]), 0, D)
    # R2: silence; 4. ηm; 6. Q
    s2 = slot(r2)
    m["fired_present"] = bool((r2["p"][s2] > 0.9).any())
    m["x_max_present"] = float(r2["x"][s2].max())
    m["Q"] = integral(r2, np.maximum(r2["J"], 0), 0, c["tau"])
    m["etaM"] = integral(r2, np.maximum(-r2["J"], 0), 0, D)
    m["vq_max_present"] = float(r2["vq"][s2].max())
    # 3. ηH on every prefix, both decisive runs; negative help enters here
    m["etaH"] = max(help_error(r1, c), help_error(r2, c))
    m["help_negative_L1"] = max(integral(q, np.maximum(-q["H"], 0), 0, D) for q in (r1, r2))
    # 2. ε₀: state at the slot start and after the reset (the next slot's start)
    at = lambda q, x: float(np.interp(x, q["u"], q["x"]))
    m["x_slot_start"] = [at(r1, 0), at(r2, 0)]
    m["x_after_reset"] = [at(r1, D + c["reset_len"] + 0.05), at(r2, D + c["reset_len"] + 0.05)]
    m["eps0"] = max(abs(v) for v in m["x_slot_start"] + m["x_after_reset"])
    # 1. leaks on both sides of rest
    m["leak_above"] = leak_fit(r3, *cfg["runs"]["R3_leak_above"]["fit_tu"])
    m["leak_below"] = leak_fit(r4, *cfg["runs"]["R4_leak_below"]["fit_tu"])
    m["slot_duration_tu"] = D + c["reset_len"]                        # 15.
    m["state_extent"] = state_extent(cfg, root, (m["leak_above"]["rate"] + m["leak_below"]["rate"]) / 2)
    m["machine_s"] = {n: rec["wall_s"] for n, rec in recs.items()}
    m["machine_s_total"] = time.time() - t_start
    out = dict(seed=seed, section=sec, drawn=draw is not None, cell=c, measures=m,
               runs={n: dict(files=rec["files"], finger=rec["finger"], points=rec["points"]) for n, rec in recs.items()})
    (root / "MEASURE.json").write_text(json.dumps(out, indent=1, sort_keys=True))
    return out


def state_extent(cfg, root, a_ref):
    """X candidates for the varying-leak lemma, from the kept traces of one instance (no new simulation).

    Returns, for R2 (input present) on [0, D] and for R1 (input absent) on [0, D] and on [0, h + hl]:
    max |x| and max |x - r|, with r the box reference leakyResponse a_ref 0 box in closed form."""
    c = cfg["cell"]
    h, hl, H0, D = c["h"], c["hl"], c["H0"], c["D"]

    def ref(u):
        y = np.clip(u - h, 0.0, hl)
        peak_part = H0 * (1 - np.exp(-a_ref * y)) / a_ref
        return np.where(u <= h + hl, peak_part, peak_part * np.exp(-a_ref * (u - h - hl)))

    out = {}
    for name in ("R1_absent", "R2_present"):
        data = np.loadtxt(Path(root) / name / "trace.txt", skiprows=1)
        q = _cols(c, dict(t=data[:, 0], vq=data[:, 1], ih=data[:, 2], ij=data[:, 3], p=data[:, 4], cmp=data[:, 5]))
        for tag, end in (("slot", D), ("deadline", h + hl)):
            sel = (q["u"] >= 0) & (q["u"] <= end)
            out[f"{name}_{tag}_abs_x"] = float(np.abs(q["x"][sel]).max())
            out[f"{name}_{tag}_abs_x_minus_ref"] = float(np.abs(q["x"][sel] - ref(q["u"][sel])).max())
    return out
