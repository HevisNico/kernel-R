"""The per-instance Lean gate of one inverter instance, from its MEASURE.json.

Development work, not preregistered. Mirrors the family gates (research/function-family, emit.py and
family_predict.lean_gate): the Python mirror computes each verdict exactly over fractions, the generated Lean file
asserts the mirror's verdicts by `decide +kernel`, and if it fails to compile the other verdict combinations are
tried; the one that compiles is the kernel's verdict.

K0 (eligibility): the measured values, outward rounded. K3 (room): K0 plus three standard deviations of the frozen
cell's noise (noise.json): the FIRE comparator's input noise on the threshold error, the shot noise of the two
mirrors integrated over the slot on every charge budget and taken from Q.

Usage: python emit.py MEASURE.json OUTDIR [--lean-build DIR]   -> OUTDIR/Inverter_<seed>.lean, OUTDIR/GATE_<seed>.json
"""
import json, math, os, subprocess, sys
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
NOISE = json.loads((HERE.parent.parent / "noise.json").read_text())
DEN = 10 ** 6
# campaign dates of the inverter (development choices, time units): window = tau, emission in (emitEarly, emitLate]
TIMING = dict(window=F(1, 4), emitEarly=F(2, 5), emitLate=F(13, 20))
EARLY_GRID = F(1, 1000)


def up(x):
    return F(math.ceil(x * DEN), DEN)


def down(x):
    return F(math.floor(x * DEN), DEN)


def allowance(K, d):
    if K == 0:
        return dict(delta=F(0), eta=F(0))
    tu, unit = 20e-6, 2.5e-12
    s_cmp = NOISE["fire_comparator"]["total_input_uV"] * 1e-6 / 0.5           # units of x
    p = NOISE["params"]
    s_q = math.sqrt(2) * p["inmw"] * math.sqrt(d["D"] * tu * p["tnz"]) / unit     # two mirrors, over the slot
    return dict(delta=up(K * s_cmp), eta=up(K * s_q))


# ------------------------------------------------------------------ the mirror (same formulas as the Lean file)
def expLo(x):
    return 1 - x + x * x / 2 - x ** 3 / 6 + x ** 4 / 24 - x ** 5 / 120


def expHi(x):
    return expLo(x) + x ** 6 / 720


def premises(d, m, k, t):
    refU = lambda y: d["H0"] * (1 - expLo(m["aLo"] * y)) / m["aLo"]
    refL = lambda y: d["H0"] * (1 - expHi(m["aHi"] * y)) / m["aHi"]
    dl = m["delta"] + k["delta"]
    Bs = m["eps0"] + m["etaH"] + m["etaM"] + k["eta"]
    Bf = m["eps0"] + m["etaH"] + m["etaJ"] + k["eta"]
    sm = d["level"] + expLo(m["aHi"] * d["D"]) * (m["Q"] - k["eta"]) - (refU(d["hl"]) + Bs + dl)
    fm = refL(d["hl"]) - (d["level"] + Bf + dl)
    order = (0 <= d["tau"] <= d["h"] and 0 < d["hl"] and d["h"] + d["hl"] <= d["D"] and 0 < m["aLo"] <= m["aHi"]
             and all(m[n] >= 0 for n in ("eps0", "etaH", "etaM", "etaJ", "delta")) and k["delta"] >= 0 and k["eta"] >= 0
             and 0 <= m["early"] < d["hl"] and 0 <= m["latchLo"] <= m["latchHi"])
    v = dict(
        Order=order,
        SilenceBefore=Bs + dl < d["level"],
        SilenceAfter=sm > 0,
        FiringBefore=refU(m["early"]) + Bf + dl < d["level"],
        FiringAfter=fm > 0,
        Timing=(0 <= t["window"] <= t["emitEarly"] < t["emitLate"] and t["window"] == d["tau"]
                and t["emitEarly"] <= d["h"] + m["early"] + m["latchLo"] and d["h"] + d["hl"] + m["latchHi"] <= t["emitLate"]
                and t["emitEarly"] < m["emit"] <= t["emitLate"]))
    v["Premises"] = all(v.values())
    return v, dict(silence_margin=sm, firing_margin=fm)


def best_early(d, m, k):
    """The largest early on the grid with FiringBefore (so the proved crossing interval is the narrowest)."""
    e, best = F(0), None
    while e < d["hl"]:
        mm = dict(m, early=e)
        if premises(d, mm, k, TIMING)[0]["FiringBefore"]:
            best = e
        else:
            break
        e += EARLY_GRID
    return best if best is not None else F(0)


def measures(meas):
    x = meas["measures"]
    a = sorted([x["a_actual"], x["a_prime"]])
    return dict(aLo=down(a[0]), aHi=up(a[1]), eps0=up(x["eps0"]), etaH=up(x["eta_H"]), etaM=up(x["eta_m_wrong_sign_L1"]),
                etaJ=up(x["eta_J_off_charge_L1"]), delta=up(x["delta"]), Q=down(x["Q_by_tau"]),
                latchLo=down(x["latch_delay_tu"]), latchHi=up(x["latch_delay_tu"]), emit=F(round(x["emit_absent_tu"] * DEN), DEN))


def design(meas):
    g = meas["design"]
    return dict(tau=F(str(g["tau"])), h=F(str(g["h"])), hl=F(str(g["hl"])), H0=F(str(g["H0"])), D=F(str(g["D"])),
                level=F(str(meas["level_x"])))


# ------------------------------------------------------------------ the Lean file
def q(x):
    x = F(x)
    s = f"({x.numerator} : Rat)" if x.denominator == 1 else f"({x.numerator} / {x.denominator} : Rat)"
    return s


def lean_file(seed, d, ms, ks, verdicts, per=True):
    L = ["import InverterInstanceCheck", "",
         f"/-! The kernel gate of inverter instance {seed} (SKY130 tt_mm, its seed), written by",
         "research/circuit/inverter/instances/emit.py from its MEASURE.json. Each theorem asserts a verdict of the",
         "Python mirror by `decide +kernel`; the file compiles only if the kernel agrees with every one. -/", "",
         "namespace LearnedCoincidence.MonotoneDNF.InverterInstance.Gate", "", "open LearnedCoincidence.MonotoneDNF.InverterInstance", "",
         f"def design : Design := ⟨{', '.join(q(d[n]) for n in ('tau', 'h', 'hl', 'H0', 'D', 'level'))}⟩",
         f"def timing : InverterTiming := ⟨{q(TIMING['window'])}, {q(TIMING['emitEarly'])}, {q(TIMING['emitLate'])}⟩", ""]
    names = ("aLo", "aHi", "eps0", "etaH", "etaM", "etaJ", "delta", "Q", "latchLo", "latchHi", "emit", "early")
    for K in ("K0", "K3"):
        m, k = ms[K], ks[K]
        L += [f"def m_{seed}_{K} : Measures := ⟨{', '.join(q(m[n]) for n in names)}⟩",
              f"def k_{K} : Allowance := ⟨{q(k['delta'])}, {q(k['eta'])}⟩", ""]
    for K in ("K0", "K3"):
        v = verdicts[K]
        args = f"design m_{seed}_{K} k_{K}"
        L += [f"theorem check_{seed}_{K} : check {args} timing = {str(v['Premises']).lower()} := by decide +kernel", ""]
        if per:
            for p in ("Order", "SilenceBefore", "SilenceAfter", "FiringBefore", "FiringAfter"):
                L += [f"theorem {p}_{seed}_{K} : decide ({p} {args}) = {str(v[p]).lower()} := by decide +kernel"]
            L += [f"theorem Timing_{seed}_{K} : decide (Timing design m_{seed}_{K} timing) = {str(v['Timing']).lower()} := by decide +kernel", ""]
        if v["Premises"]:
            L += [f"/-- The premises, hence the abstract inverter law on both observed reads. -/",
                  f"theorem premises_{seed}_{K} : Premises {args} timing := check_sound check_{seed}_{K}", "",
                  f"theorem inverterRead_{seed}_{K} : InverterRead timing (absentRead m_{seed}_{K}) ∧ InverterRead timing presentRead :=",
                  f"  inverterRead_of_premises premises_{seed}_{K}", ""]
    L += ["end LearnedCoincidence.MonotoneDNF.InverterInstance.Gate", ""]
    return "\n".join(L)


def gate(meas_path, out_dir, build):
    meas = json.loads(Path(meas_path).read_text())
    seed = meas["seed"]
    d = design(meas)
    base = measures(meas)
    ks = {f"K{K}": allowance(K, meas["design"]) for K in (0, 3)}
    ms, mirror, margins = {}, {}, {}
    for K in ("K0", "K3"):
        ms[K] = dict(base, early=best_early(d, base, ks[K]))
        mirror[K], mg = premises(d, ms[K], ks[K], TIMING)
        margins[K] = {n: float(v) for n, v in mg.items()}
    out = Path(out_dir)
    out.mkdir(parents=True, exist_ok=True)
    tries = [((mirror["K0"]["Premises"], mirror["K3"]["Premises"]), True)]
    tries += [((a, b), False) for a in (True, False) for b in (True, False) if (a, b) != tries[0][0]]
    res = dict(seed=seed, mirror=mirror, margins=margins, attempts=[], kernel=None,
               measures={K: {n: str(v) for n, v in ms[K].items()} for K in ms},
               allowance={K: {n: str(v) for n, v in ks[K].items()} for K in ks}, timing={n: str(v) for n, v in TIMING.items()},
               measured_same_sample=meas["measures"]["same_sample"], observed_silent=not meas["measures"]["fired_present"],
               observed_fired=meas["measures"]["emit_absent_tu"] is not None)
    for n, ((v0, v3), per) in enumerate(tries):
        vv = {"K0": dict(mirror["K0"]) if per else {"Premises": v0}, "K3": dict(mirror["K3"]) if per else {"Premises": v3}}
        name = f"Inverter_{seed}" + ("" if n == 0 else f"_try{n}")
        f = out / f"{name}.lean"
        f.write_text(lean_file(seed, d, ms, ks, vv, per))
        env = dict(os.environ, GATE_BUILD=str(build))
        p = subprocess.run(["bash", str(HERE / "lean" / "check.sh"), str(f)], capture_output=True, text=True, env=env, timeout=1800)
        (out / f"{name}.log").write_text(p.stdout + p.stderr)
        res["attempts"].append(dict(file=f.name, asserted=dict(K0=v0, K3=v3), per_checker=per, passed=p.returncode == 0))
        if p.returncode == 0:
            res["kernel"] = dict(K0=v0, K3=v3)
            res["kernel_agrees_with_mirror"] = n == 0
            break
    res["eligible_K0"] = bool(res["kernel"] and res["kernel"]["K0"] and res["measured_same_sample"]
                              and res["observed_silent"] and res["observed_fired"])
    res["room_K3"] = bool(res["eligible_K0"] and res["kernel"]["K3"])
    (out / f"GATE_{seed}.json").write_text(json.dumps(res, indent=1, sort_keys=True, default=str))
    return res


if __name__ == "__main__":
    b = sys.argv[sys.argv.index("--lean-build") + 1] if "--lean-build" in sys.argv else None
    if b is None:
        raise SystemExit("--lean-build DIR is required (a folder with the compiled library, or an empty one)")
    r = gate(sys.argv[1], sys.argv[2], b)
    print(json.dumps({k: r[k] for k in ("seed", "kernel", "eligible_K0", "room_K3", "margins")}, indent=1, default=str))
