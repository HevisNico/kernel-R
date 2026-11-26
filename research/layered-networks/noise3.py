"""noise2's injected model plus the noise the C5 inverter's K3 gate budgets, in the layered noisy runs. Development only.
New file: noise2.py, controls2.py, instrument.py and run.py are imported, not changed.

What the inverter's K3 gate budgets (research/inverter-instances invinst/gate.py `allowance()`, K3 = 3 sigma of
research/circuit/noise.json), and how it is injected here, as the inverter-kit worker specified:
1. The FIRE comparator's input noise, on the threshold (delta). sigma = fire_comparator.total_input_uV = 335.029 uV =
   sqrt(316.637^2 + 109.480^2), i.e. 6.70e-4 in x. Injected on the comparator's reference: the inverter's existing zero
   source `v.xn<j>.vnzm` becomes `trnoise(vnmw tnz 1 vnmf)`, the line of research/circuit/certification/cert_run.py
   for the frozen cell (and noise2's for the R cells).
2. The shot charge of the two mirrors, help (xmh1/xmh2) and inhibitory (xmj1/xmj2), booked on the charge budgets (eta)
   and taken from Q: sigma_q = sqrt(2) inmw sqrt(D tu tnz) / (cq vunit) = 7.84e-4 in x, both integrated over the WHOLE
   slot [0, D] whatever the switches do. Injected exactly so: two independent trnoise sources of inmw (white, per tnz
   sample, no flicker), each on its own node with 1 kohm (as the frozen cell's vnzi), summed by a behavioural current
   source into the charge node xn<j>.vq, gated by a window that is 1 on [T, T + D tu] of each slot and 0 elsewhere (a
   per-slot pulse `vkw<x>` set with the inverter's other gates). Outside the window no mirror noise reaches vq, as in
   the budget.
Not budgeted, not injected: the latch, the reset gate, the leak resistor and the comparator bias.

Seed: noise2's, FAKEPID = 10 x S + n for the whole run (R cells and inverters), recorded.
For the comparison with the budget, each inverter's vq is saved and, in every slot, x = (vr0 - vq)/vunit is read at
T + tau (before help and before any FIRE) and at T + D (the end of the noise window): OUT/noisy_record.json carries
them in `inverter_x` (one entry per slot, outside the slot records, so that the slots keep their layout).

  noise3.py stagen SPEC OUT SEED ROUND [scale=1] [overlay=FILE]   noise2's training and tests, controls2's skews
  noise3.py budget SPEC OFF_DIR NOISY_DIR...                      the measured inverter perturbation against 3 sigma
"""
import hashlib
import json
import math
import os
from pathlib import Path
import statistics
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import controls2  # noqa: E402
import instrument  # noqa: E402
import noise2  # noqa: E402
import run as runmod  # noqa: E402
import spec as specmod  # noqa: E402

NOISE_JSON = json.loads((noise2.CIRCUIT / "noise.json").read_text())
P = NOISE_JSON["params"]
SIGMA_CMP_V = NOISE_JSON["fire_comparator"]["total_input_uV"] * 1e-6


def budget_sigmas(cfg):
    c, tu = cfg["inverter"], cfg["stimulus"]["tu_s"]
    unit = 5e-12 * 0.5                                     # cq * vunit, as deck.rinv
    return dict(delta_x=SIGMA_CMP_V / 0.5, eta_x=math.sqrt(2) * P["inmw"] * math.sqrt(c["D"] * tu * P["tnz"]) / unit)


def inverter_lines(text, invs, scale):
    lines, n = text.splitlines(), 0
    for i, l in enumerate(lines):
        for x in invs:
            if l == f"v.x{x}.vnzm x{x}.nzm 0 dc 0":
                lines[i] = f"{l} trnoise({P['vnmw'] * scale:.16g} {P['tnz']:.16g} 1 {P['vnmf'] * scale:.16g})"
                n += 1
    assert n == len(invs), f"expected one vnzm per inverter, found {n}"
    end = lines.index(".end")
    extra = []
    for x in invs:
        w = P["inmw"] * scale
        extra += [f"* the two mirrors' shot noise of {x}, gated to [T, T + D tu] (noise3.py)",
                  f"vkw{x} kw{x} 0 pulse(0 0 1 1n 1n 1u 2)",
                  f"vnzh{x} nzh{x} 0 dc 0 trnoise({w:.16g} {P['tnz']:.16g} 0 0)", f"rnzh{x} nzh{x} 0 1k",
                  f"vnzj{x} nzj{x} 0 dc 0 trnoise({w:.16g} {P['tnz']:.16g} 0 0)", f"rnzj{x} nzj{x} 0 1k",
                  f"bnz{x} x{x}.vq 0 i = (v(nzh{x}) + v(nzj{x})) * v(kw{x})"]
    return "\n".join(lines[:end] + extra + lines[end:]) + "\n"


class Net3(instrument.CalNetwork):
    """CalNetwork with the inverters' noise window set per slot and their vq read at T + tau and T + D."""

    def __init__(self, s, cfg, out, seed, windows=True):
        self.windows = windows
        super().__init__(s, cfg, out, seed)
        self.ses.saved = self.ses.saved + [f"x{x}.vq" for x in self.invs]
        self.inverter_x = []

    def inverter(self, x, T_ns, present):
        super().inverter(x, T_ns, present)
        if not self.windows:
            return
        d, tu = self.cfg["inverter"], self.cfg["stimulus"]["tu_s"]
        self.ses.alter_pulse(f"vkw{x}", [0, 1, T_ns * 1e-9, "1n", "1n", d["D"] * tu - 1e-9, 2])

    def _x_at(self, x, t):
        self.n_meas += 1
        name = f"q{self.n_meas}"
        self.ses.cmd(f"meas tran {name} find v(x{x}.vq) at={t:.12g}")
        v = float(self.ses.cmd(f"print {name}").strip().split("=")[-1])
        return (1.25 - v) / 0.5                            # x = (vr0 - vq) / vunit

    def slot(self, kind, lines, top, allowed, ungated, info):
        rec = super().slot(kind, lines, top, allowed, ungated, info)
        d, tu = self.cfg["inverter"], self.cfg["stimulus"]["tu_s"]
        T = rec["T"] * 1e-9
        self.inverter_x.append({x: dict(x_tau=self._x_at(x, T + d["tau"] * tu), x_D=self._x_at(x, T + d["D"] * tu - 2e-9))
                                for x in self.invs} if self.invs and rec["inv"] else {})
        return rec


def _cfg(overlay):
    import lcal2
    return lcal2.config(overlay)[0] if overlay else json.loads((HERE / "config.json").read_text())


def stagen(spec_path, out, seed, rnd, scale=1.0, overlay=None, extra=None, log=print):
    s, cfg, out = specmod.load(spec_path), _cfg(overlay), Path(out)
    rnd = int(rnd)
    cells, invs = instrument.deckmod.names(s)
    ns = noise2.noise_seed(seed, rnd) if rnd > 0 else None
    t0 = time.time()
    orig = instrument.deck_text
    saved_env = {k: os.environ.get(k) for k in ("LD_PRELOAD", "FAKEPID")}
    if ns is not None:
        instrument.deck_text = lambda s_, c_: inverter_lines(noise2.noisy_text(orig(s_, c_), cells, scale), invs, scale)
        os.environ.update(LD_PRELOAD=str(noise2.shim(HERE / "build")), FAKEPID=str(ns))
    try:                                                    # noise off: the pushed deck unchanged (vq only saved)
        net = Net3(s, cfg, out, int(seed), windows=ns is not None)
    finally:
        instrument.deck_text = orig
        for k, v in saved_env.items():
            if v is None:
                os.environ.pop(k, None)
            else:
                os.environ[k] = v
    status, lessons, words, tests, skews = "done", [], {}, [], []
    try:
        lessons, words, tests = noise2.train_and_test(net, s, cfg, log)
        for k, i in controls2.both_cells(s):
            r = controls2.skew_slot(net, s, k, i)
            net.inverter_x.append({})
            skews.append(len(net.slots) - 1)
            log(f"skew c{k}_{i}: {'FIRE' if r['reads'][0]['emission'] is not None else 'silent'}")
    except Exception as e:
        status = f"failed: {e}"
        log(status)
    finally:
        cpu = runmod.cpu_of(net.ses.p.pid)
        net.ses.close()
    text = (out / "input.spice").read_text()
    rec = dict(tag=s["tag"], seed=int(seed), round=rnd, noise_seed=ns, noise_scale=float(scale) if ns else 0.0,
               noise_model="noise3: noise2 R cells + C5 inverter comparator and mirrors (K3 gate budget)",
               status=status, input_spice_sha256=hashlib.sha256(text.encode()).hexdigest(),
               cost=dict(wall_s=time.time() - t0, cpu_s=cpu),
               words={f"{k}/{i}/{g}": w for (k, i, g), w in words.items()}, lessons=lessons, tests=tests, skews=skews,
               slots=net.slots, inverter_x=net.inverter_x, **(extra or {}))
    (out / "noisy_record.json").write_text(json.dumps(rec, indent=1, default=str) + "\n")
    return rec


def budget(spec_path, off_dir, noisy_dirs, overlay="config_inverter_c5.json"):
    """Per inverter and slot, dx = x_noisy - x_off at T + tau and at T + D, over the slots matched by kind, info and
    occurrence (noise2.bwd's matching), against the gate's sigmas: at T + D the mirrors' charge alone (sigma_q, about
    0.8 of it after the leak over D); the comparator noise is on the threshold, not on x."""
    off = json.loads((Path(off_dir) / "noisy_record.json").read_text())
    sig = budget_sigmas(_cfg(overlay))

    def keyed(r):
        seen, out = {}, {}
        for i, sl in enumerate(r["slots"]):
            k = (sl["kind"], json.dumps(sl.get("info"), sort_keys=True))
            seen[k] = seen.get(k, 0) + 1
            out[k + (seen[k],)] = i
        return out
    dtau, dD, dlat = [], [], []
    for d in noisy_dirs:
        r = json.loads((Path(d) / "noisy_record.json").read_text())
        ko, kn = keyed(off), keyed(r)
        for k in ko:
            if k not in kn:
                continue
            i, j = ko[k], kn[k]
            a, b = off["inverter_x"][i], r["inverter_x"][j]
            for x in a:
                if x in b:
                    dtau.append(b[x]["x_tau"] - a[x]["x_tau"])
                    jj = int(x[1:])
                    va, vb = off["slots"][i]["inv"][jj], r["slots"][j]["inv"][jj]
                    if va["arrival"] is not None:          # input present: silent, x(D) is the charge the gate bounds
                        dD.append(b[x]["x_D"] - a[x]["x_D"])
                    elif va["latch"] is not None and vb["latch"] is not None:
                        dlat.append((vb["latch"] - r["slots"][j]["T"]) - (va["latch"] - off["slots"][i]["T"]))
    sd = lambda v: statistics.pstdev(v) if len(v) > 1 else None
    rms = lambda v: (sum(t * t for t in v) / len(v)) ** 0.5 if v else None
    return dict(sigma_budget=dict(delta_x=sig["delta_x"], eta_x=sig["eta_x"], K3_delta_x=3 * sig["delta_x"],
                                  K3_eta_x=3 * sig["eta_x"]),
                dx_tau=dict(n=len(dtau), rms=rms(dtau), sd=sd(dtau), max_abs=max(map(abs, dtau)) if dtau else None),
                dx_D_silent=dict(n=len(dD), rms=rms(dD), sd=sd(dD), max_abs=max(map(abs, dD)) if dD else None),
                latch_shift_ns_firing=dict(n=len(dlat), rms=rms(dlat), max_abs=max(map(abs, dlat)) if dlat else None))


if __name__ == "__main__":
    cmd, *a = sys.argv[1:]
    kw = dict(x.split("=", 1) for x in a if "=" in x)
    pos = [x for x in a if "=" not in x]
    if cmd == "stagen":
        r = stagen(*pos[:4], scale=float(kw.get("scale", 1)), overlay=kw.get("overlay"))
        print(json.dumps(dict(status=r["status"], noise_seed=r["noise_seed"], words=r["words"], cost=r["cost"]), indent=1))
    elif cmd == "budget":
        print(json.dumps(budget(pos[0], pos[1], pos[2:], kw.get("overlay", "config_inverter_c5.json")), indent=1))
    else:
        sys.exit(__doc__)
