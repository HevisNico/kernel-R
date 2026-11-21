"""Runs of the one-cell inverter and the contract quantities of INVERTER_DESIGN.md section 3.4 (subset).

Writes MEASURES.json: every number, the design, and the sha256 of every trace and deck.
"""
import json, math
import numpy as np
import inverter as I

d = I.DESIGN
TU, T0 = I.TU, I.T0
u = lambda t: (t - T0) / TU                      # slot time in time units
UNIT_PER_S = TU / I.UNIT                         # amperes -> units of x per time unit


def load(name, present, tstop_tu, maxstep, **kw):
    folder, data = I.run(name, I.netlist(present=present, **kw), T0 + tstop_tu * TU, maxstep)
    t = data[:, 0]
    cols = dict(t=t, vq=data[:, 1], H=data[:, 2] * UNIT_PER_S, J=data[:, 3] * UNIT_PER_S, p=data[:, 4])
    cols["x"] = (I.VR0 - cols["vq"]) / I.VUNIT
    files = {f: I.sha(folder / f) for f in ("input.spice", "trace.txt", "ngspice.log")}
    return cols, files


def integ(c, y, a_tu, b_tu):
    return I.integral(c["t"], y, T0 + a_tu * TU, T0 + b_tu * TU) / TU    # in units (time integral in time units)


def fire_date(c, after_tu=0.0):
    sel = (c["p"] > 0.9) & (c["t"] >= T0 + after_tu * TU)
    return float(u(c["t"][np.argmax(sel)])) if sel.any() else None


def help_window(c):
    H, t = c["H"], c["t"]
    H0 = np.where((t >= T0 + d["h"] * TU) & (t < T0 + (d["h"] + d["hl"]) * TU), d["H0"], 0.0)
    err = np.abs(H - H0)
    grid = np.linspace(0, d["D"], 201)
    prefix = [integ(c, err, 0, b) for b in grid[1:]]
    inside = (t >= T0 + (d["h"] + 0.02) * TU) & (t < T0 + (d["h"] + d["hl"] - 0.02) * TU)
    outside = ((t >= T0) & (t < T0 + d["h"] * TU)) | ((t > T0 + (d["h"] + d["hl"]) * TU) & (t <= T0 + d["D"] * TU))
    return dict(
        help_charge_window=integ(c, H, d["h"], d["h"] + d["hl"]),
        help_charge_nominal=d["H0"] * d["hl"],
        help_L1_error_max_prefix=max(prefix),
        help_L1_error_outside_window=integ(c, np.where(outside, np.abs(H), 0.0), 0, d["D"]),
        help_current_inside_mean=float(H[inside].mean()), help_current_inside_min=float(H[inside].min()),
        help_current_inside_max=float(H[inside].max()),
    )


def leak_fit(c, a_tu, b_tu):
    """Fit x(t) = x(a) exp(-k (t - a)) by least squares on log|x| over [a, b] (time units)."""
    sel = (c["t"] >= T0 + a_tu * TU) & (c["t"] <= T0 + b_tu * TU)
    tt, xx = u(c["t"][sel]), c["x"][sel]
    if np.any(xx == 0) or np.any(np.sign(xx) != np.sign(xx[0])):
        raise RuntimeError("x changes sign in the fit window")
    slope, _ = np.polyfit(tt, np.log(np.abs(xx)), 1)
    resid = np.log(np.abs(xx)) - np.polyval(np.polyfit(tt, np.log(np.abs(xx)), 1), tt)
    best = None                                    # second fit, with a constant offset: x = x_inf + c exp(-k (t - a))
    for k in np.linspace(0.40, 0.60, 20001):
        A = np.vstack([np.ones_like(tt), np.exp(-k * (tt - a_tu))]).T
        coef = np.linalg.lstsq(A, xx, rcond=None)[0]
        r = float(np.sum((A @ coef - xx) ** 2))
        if best is None or r < best[0]:
            best = (r, k, coef)
    return dict(rate_per_tu=float(-slope), x_start=float(xx[0]), x_end=float(xx[-1]),
                window_tu=[a_tu, b_tu], log_residual_max=float(np.abs(resid).max()),
                rate_with_offset_per_tu=float(best[1]), offset_asymptote_x=float(best[2][0]),
                offset_fit_rms=float(np.sqrt(best[0] / len(tt))))


out = dict(design=d, nominal_leak_per_tu=0.5, unit_coulombs=I.UNIT, level_x=I.LEVEL, runs={}, files={})

# R1: input absent, help on, reset on.
c, f = load("R1_absent", False, 1.3, "5n"); out["files"]["R1_absent"] = f
J = c["J"]
out["runs"]["R1_absent"] = dict(
    fire_date_tu=fire_date(c), x_max_slot=float(c["x"][(c["t"] >= T0) & (c["t"] <= T0 + d["D"] * TU)].max()),
    off_charge_L1=integ(c, np.abs(J), 0, d["D"]),
    off_charge_signed=integ(c, J, 0, d["D"]),
    wrong_sign_charge_L1=integ(c, np.maximum(-J, 0), 0, d["D"]),
    x_after_reset=float(np.interp(T0 + (d["D"] + d["reset_len"] + 0.05) * TU, c["t"], c["x"])),
    **help_window(c))

# R2: input present, help on, reset on.
c, f = load("R2_present", True, 1.3, "5n"); out["files"]["R2_present"] = f
J = c["J"]; slot = (c["t"] >= T0) & (c["t"] <= T0 + d["D"] * TU)
out["runs"]["R2_present"] = dict(
    fired_in_slot=bool((c["p"][slot] > 0.9).any()), fire_date_tu=fire_date(c),
    x_max_slot=float(c["x"][slot].max()), x_min_slot=float(c["x"][slot].min()),
    vq_max_slot=float(c["vq"][slot].max()),
    inhibitory_charge_by_tau=integ(c, np.maximum(J, 0), 0, d["tau"]),
    inhibitory_charge_nominal=d["J0"] * d["tau"],
    inhibitory_current_end_of_window=float(np.interp(T0 + (d["tau"] - 0.01) * TU, c["t"], J)),
    wrong_sign_charge_L1=integ(c, np.maximum(-J, 0), 0, d["D"]),
    inhibitory_charge_after_tau_L1=integ(c, np.abs(J), d["tau"] + 0.005, d["D"]),
    x_after_reset=float(np.interp(T0 + (d["D"] + d["reset_len"] + 0.05) * TU, c["t"], c["x"])),
    **help_window(c))

# R3: leak with x above rest (help only, no inhibition, no reset): fit after the help window.
c, f = load("R3_leak_help", False, 4.0, "20n", reset=False); out["files"]["R3_leak_help"] = f
out["runs"]["R3_leak_help"] = leak_fit(c, 1.0, 4.0)

# R4: leak with x below rest (inhibition only, no help, no reset): fit after the input window.
c, f = load("R4_leak_inhib", True, 4.0, "20n", help_on=False, reset=False); out["files"]["R4_leak_inhib"] = f
r4 = leak_fit(c, 0.5, 4.0)
r4["inhibitory_charge_by_tau"] = integ(c, np.maximum(c["J"], 0), 0, d["tau"])
r4["vq_max"] = float(c["vq"].max())
out["runs"]["R4_leak_inhib"] = r4

for name in ("inverter.py", "measure.py", "blocks.spice", "spiceinit.txt"):
    out["files"][name] = I.sha(I.HERE / name)
(I.HERE / "MEASURES.json").write_text(json.dumps(out, indent=1, sort_keys=True))
print(json.dumps(out["runs"], indent=1, sort_keys=True))
