"""The per-instance Lean gate, from one MEASURE.json.

The family gates' pattern (research/function-family, family_predict.lean_gate): an exact Python mirror of the Lean
premises gives the verdicts; the generated file asserts them by `decide +kernel`; if it fails to compile, the other
(K0, K3) combinations are tried without per-premise theorems, and the one that compiles is the kernel's verdict.

K0 (eligibility): the measured values, rounded outward. K3 (room): K0 plus K3_sigmas standard deviations of the
frozen cell's noise (research/circuit/noise.json): the FIRE comparator's input noise on δ; the shot noise of the two
mirrors, integrated over the slot, on each charge budget and taken from Q.
"""
import json, math, os, subprocess
from fractions import Fraction as F
from pathlib import Path

PKG = Path(__file__).resolve().parents[1]
NOISE = Path(__file__).resolve().parents[3] / "noise.json"
OPEN_PREMISES = [
    "[I] one constant actual leak: actualLaw of inhibited_silence_leaks / uninhibited_first_crossing_leaks needs "
    "actual = leakyResponse a ... with ONE a; the cell's leak depends on the side of rest (two measured rates), so "
    "the theorem's hypothesis is not met. The gate checks both rates lie in [a' - alpha, a' + alpha], which is the "
    "numeric content of a varying-leak lemma (|a(t) - a'| <= alpha) that is not proved yet.",
    "the real bridge from these Rat premises to the real hypotheses (BRIDGE_INTERFACE.md): not written yet.",
    "the latch: the contact-to-latch delay is a measured constant, not a proved bound.",
]
NAMES = ("aLo", "aHi", "aRef", "alpha", "eps0", "etaH", "etaM", "etaJ", "delta", "Q", "latchLo", "latchHi", "emit", "early")


class Rounding:
    def __init__(self, den):
        self.den = den

    def up(self, x):
        return F(math.ceil(x * self.den), self.den)

    def down(self, x):
        return F(math.floor(x * self.den), self.den)

    def near(self, x):
        return F(round(x * self.den), self.den)


def allowance(cfg, K):
    if K == 0:
        return dict(delta=F(0), eta=F(0))
    c, noise = cfg["cell"], json.loads(NOISE.read_text())
    r = Rounding(cfg["gate"]["rational_denominator"])
    s_cmp = noise["fire_comparator"]["total_input_uV"] * 1e-6 / c["vunit_V"]
    p = noise["params"]
    s_q = math.sqrt(2) * p["inmw"] * math.sqrt(c["D"] * c["tu_s"] * p["tnz"]) / (c["cq_F"] * c["vunit_V"])
    return dict(delta=r.up(K * s_cmp), eta=r.up(K * s_q))


# ------------------------------------------------------------------ the mirror: the Lean definitions, over fractions
def expLo(x):
    return 1 - x + x * x / 2 - x ** 3 / 6 + x ** 4 / 24 - x ** 5 / 120


def expHi(x):
    return expLo(x) + x ** 6 / 720


def premises(d, m, k, t):
    refU = lambda y: d["H0"] * (1 - expLo(m["aRef"] * y)) / m["aRef"]
    refL = lambda y: d["H0"] * (1 - expHi(m["aRef"] * y)) / m["aRef"]
    lt = m["alpha"] * (d["D"] * d["H0"] * d["hl"])
    dl = m["delta"] + k["delta"]
    Bs = m["eps0"] + m["etaH"] + m["etaM"] + k["eta"]
    Bf = m["eps0"] + m["etaH"] + m["etaJ"] + k["eta"]
    sm = d["level"] + expLo((m["aRef"] + m["alpha"]) * d["D"]) * (m["Q"] - k["eta"]) - (refU(d["hl"]) + Bs + dl + lt)
    fm = refL(d["hl"]) - (d["level"] + Bf + dl + lt)
    v = dict(
        Order=(0 <= d["tau"] <= d["h"] and 0 < d["hl"] and d["h"] + d["hl"] <= d["D"] and 0 <= m["aLo"] <= m["aHi"]
               and m["aRef"] > 0 and m["alpha"] >= 0 and m["aRef"] - m["alpha"] <= m["aLo"] and m["aHi"] <= m["aRef"] + m["alpha"]
               and m["Q"] - k["eta"] >= 0 and d["H0"] > 0
               and all(m[n] >= 0 for n in ("eps0", "etaH", "etaM", "etaJ", "delta")) and k["delta"] >= 0 and k["eta"] >= 0
               and 0 <= m["early"] < d["hl"] and 0 <= m["latchLo"] <= m["latchHi"]),
        SilenceBefore=Bs + dl + lt < d["level"],
        SilenceAfter=sm > 0,
        FiringBefore=refU(m["early"]) + Bf + dl + lt < d["level"],
        FiringAfter=fm > 0,
        Timing=(0 <= t["window"] <= t["emitEarly"] < t["emitLate"] and t["window"] == d["tau"]
                and t["emitEarly"] <= d["h"] + m["early"] + m["latchLo"] and d["h"] + d["hl"] + m["latchHi"] <= t["emitLate"]
                and t["emitEarly"] < m["emit"] <= t["emitLate"]))
    v["Premises"] = all(v.values())
    return v, dict(silence_margin=sm, firing_margin=fm, leak_term=lt)


def best_early(d, m, k, t, grid):
    """The largest early date on the grid with FiringBefore (the narrowest proved crossing interval)."""
    e, best = F(0), F(0)
    while e < d["hl"]:
        if not premises(d, dict(m, early=e), k, t)[0]["FiringBefore"]:
            break
        best, e = e, e + grid
    return best


def design(cfg):
    c = cfg["cell"]
    return {n: F(str(c[n])) for n in ("tau", "h", "hl", "H0", "D")} | dict(level=F(str(c["level_x"])))


def measures(cfg, x):
    r = Rounding(cfg["gate"]["rational_denominator"])
    lo, hi = sorted([x["leak_above"]["rate"], x["leak_below"]["rate"]])
    aLo, aHi = r.down(lo), r.up(hi)
    aRef = (aLo + aHi) / 2
    return dict(aLo=aLo, aHi=aHi, aRef=aRef, alpha=(aHi - aLo) / 2, eps0=r.up(x["eps0"]), etaH=r.up(x["etaH"]),
                etaM=r.up(x["etaM"]), etaJ=r.up(x["etaJ"]), delta=r.up(x["delta"]), Q=r.down(x["Q"]),
                latchLo=r.down(x["latch_delay_tu"]), latchHi=r.up(x["latch_delay_tu"]), emit=r.near(x["emit_absent_tu"]))


# ------------------------------------------------------------------ the Lean file
def q(x):
    x = F(x)
    return f"({x.numerator} : Rat)" if x.denominator == 1 else f"({x.numerator} / {x.denominator} : Rat)"


def lean_file(seed, d, t, ms, ks, verdicts, per, fe=None):
    L = ["import InverterInstanceCheck", "",
         f"/-! The kernel gate of inverter instance {seed} (SKY130 tt_mm, its seed), written by",
         "research/circuit/inverter/instances/invinst/gate.py from its MEASURE.json. Each theorem asserts a verdict of",
         "the Python mirror by `decide +kernel`; the file compiles only if the kernel agrees with every one. -/", "",
         "namespace LearnedCoincidence.MonotoneDNF.InverterInstance.Gate", "",
         "open LearnedCoincidence.MonotoneDNF.InverterInstance", "",
         f"def design : Design := ⟨{', '.join(q(d[n]) for n in ('tau', 'h', 'hl', 'H0', 'D', 'level'))}⟩",
         f"def timing : InverterTiming := ⟨{q(t['window'])}, {q(t['emitEarly'])}, {q(t['emitLate'])}⟩", ""]
    for K in ("K0", "K3"):
        L += [f"def m_{seed}_{K} : Measures := ⟨{', '.join(q(ms[K][n]) for n in NAMES)}⟩",
              f"def k_{K} : Allowance := ⟨{q(ks[K]['delta'])}, {q(ks[K]['eta'])}⟩", ""]
    for K in ("K0", "K3"):
        v, args = verdicts[K], f"design m_{seed}_{K} k_{K}"
        L += [f"theorem check_{seed}_{K} : check {args} timing = {str(v['Premises']).lower()} := by decide +kernel", ""]
        if per:
            for p in ("Order", "SilenceBefore", "SilenceAfter", "FiringBefore", "FiringAfter"):
                L.append(f"theorem {p}_{seed}_{K} : decide ({p} {args}) = {str(v[p]).lower()} := by decide +kernel")
            L += [f"theorem Timing_{seed}_{K} : decide (Timing design m_{seed}_{K} timing) = {str(v['Timing']).lower()} := by decide +kernel", ""]
        if v["Premises"]:
            L += [f"theorem premises_{seed}_{K} : Premises {args} timing := check_sound check_{seed}_{K}", "",
                  f"theorem inverterRead_{seed}_{K} : InverterRead timing (absentRead m_{seed}_{K}) ∧ InverterRead timing presentRead :=",
                  f"  inverterRead_of_premises premises_{seed}_{K}", ""]
    if fe is not None:
        L += [f"theorem FrontEndFits_{seed} : decide (FrontEndFits timing {q(fe['epsilon'])} {q(fe['skew'])}) = "
              f"{str(fe['verdict']).lower()} := by decide +kernel", ""]
    return "\n".join(L + ["end LearnedCoincidence.MonotoneDNF.InverterInstance.Gate", ""])


def gate(cfg, meas, out_dir, build, timeout=1800):
    seed, x = meas["seed"], meas["measures"]
    d = design(cfg)
    t = {n: F(v) for n, v in cfg["gate"]["timing"].items()}
    grid = F(cfg["gate"]["early_grid"])
    ks = {"K0": allowance(cfg, 0), "K3": allowance(cfg, cfg["gate"]["K3_sigmas"])}
    out = Path(out_dir)
    out.mkdir(parents=True, exist_ok=True)
    res = dict(seed=seed, kernel=None, attempts=[], measured=x["delta"] is not None and x["emit_absent_tu"] is not None)
    fcfg = cfg["gate"]["front_end"]
    fe = None
    if fcfg["skew"] is not None and fcfg["epsilon"] is not None:
        eps, skew = F(fcfg["epsilon"]), F(fcfg["skew"])
        fe = dict(epsilon=eps, skew=skew, verdict=0 <= eps and t["window"] + eps <= skew and t["emitLate"] - t["emitEarly"] <= skew)
    res["front_end_fits"] = "not checked: skew or epsilon not set" if fe is None else fe["verdict"]
    res["observed"] = dict(same_sample=x["same_sample"], silent_present=not x["fired_present"],
                           fired_absent=x["emit_absent_tu"] is not None)
    if res["measured"]:
        base = measures(cfg, x)
        ms, mirror, margins = {}, {}, {}
        for K in ("K0", "K3"):
            ms[K] = dict(base, early=best_early(d, base, ks[K], t, grid))
            mirror[K], mg = premises(d, ms[K], ks[K], t)
            margins[K] = {n: float(v) for n, v in mg.items()}
        res.update(mirror=mirror, margins=margins, measures={K: {n: str(v) for n, v in ms[K].items()} for K in ms})
        first = (mirror["K0"]["Premises"], mirror["K3"]["Premises"])
        tries = [(first, True)] + [((a, b), False) for a in (True, False) for b in (True, False) if (a, b) != first]
        env = dict(os.environ, GATE_BUILD=str(build))
        for n, ((v0, v3), per) in enumerate(tries):
            vv = {"K0": mirror["K0"] if per else {"Premises": v0}, "K3": mirror["K3"] if per else {"Premises": v3}}
            name = f"Inverter_{seed}" + ("" if n == 0 else f"_try{n}")
            f = out / f"{name}.lean"
            f.write_text(lean_file(seed, d, t, ms, ks, vv, per, fe))
            p = subprocess.run(["bash", str(PKG / "lean" / "check.sh"), str(f)], capture_output=True, text=True,
                               env=env, timeout=timeout)
            (out / f"{name}.log").write_text(p.stdout + p.stderr)
            res["attempts"].append(dict(file=f.name, asserted=dict(K0=v0, K3=v3), per_premise=per, passed=p.returncode == 0))
            if p.returncode == 0:
                res["kernel"] = dict(K0=v0, K3=v3)
                res["kernel_agrees_with_mirror"] = n == 0
                break
    obs = all(res["observed"].values())
    fits = fe is None or fe["verdict"]          # an unset front end is reported, not counted against the instance
    res["eligible_K0"] = bool(res["kernel"] and res["kernel"]["K0"] and obs and fits)
    res["room_K3"] = bool(res["kernel"] and res["kernel"]["K3"] and obs and fits)
    res["open_premises"] = OPEN_PREMISES
    res["verdict_status"] = "conditional on open_premises: not a proof that the instance meets the theorems"
    res["allowance"] = {K: {n: str(v) for n, v in ks[K].items()} for K in ks}
    res["timing"] = {n: str(v) for n, v in t.items()}
    (out / f"GATE_{seed}.json").write_text(json.dumps(res, indent=1, sort_keys=True))
    return res
