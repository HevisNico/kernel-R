"""Version 2 of measure.measure: the same five runs and the same quantities, with the deck's simulator directives
taken from the layered network (config_netopts.json, through netdeck.netlist). measure.py stays as pushed: every
helper below is imported from it; only measure() is restated, with its one deck line changed.
"""
import json, time
from pathlib import Path
import numpy as np
from . import netdeck, sim
from .measure import _cols, integral, first_cross, comparator_flip, help_error, leak_fit, state_extent  # noqa: F401


def measure(cfg, netopts, seed, outdir, section=None, ngspice="ngspice"):
    """Measure instance `seed` at the network's directives (`netopts`): tt_mm with its draw; with `section`, the nominal
    section of `netopts`, no draw (any section given selects the nominal one)."""
    t_start = time.time()
    c = cfg["cell"]
    sec = section or cfg["mismatch"]["section"]
    draw = None if section else seed
    root = Path(outdir) / str(seed)
    cols, recs = {}, {}
    for name, r in cfg["runs"].items():
        deck = netdeck.netlist(c, netopts, present=r["present"], help_on=r["help"], reset=r["reset"], nominal=draw is None,
                               ramp=r.get("ramp"))
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
    out = dict(seed=seed, section=sec, drawn=draw is not None, cell=c, measures=m, netopts=netopts,
               runs={n: dict(files=rec["files"], finger=rec["finger"], points=rec["points"]) for n, rec in recs.items()})
    (root / "MEASURE.json").write_text(json.dumps(out, indent=1, sort_keys=True))
    return out
