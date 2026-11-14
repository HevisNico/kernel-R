"""Phase-1 qualification measurements on the supervised two-port cell. Exploratory, not registered.

  qualify.py threshold CONFIG PORT OUT    service threshold of one port: bracket between a correct read and an incorrect one
  qualify.py reads CONFIG OUT V1 V2       the three reads at preset stored voltages (mV): port 1, port 2, joint

Both end with NGSPICE PDK, then any of the words: `junction` (junction areas on every transistor, see
JUNCTION_AREAS.md), `zero-areas` (the same expanded deck with areas at zero: the identity test),
`instrumented` (the ammeter of the write current of the first runs).

CONFIG is a name of configs.json. OUT is a new folder outside the repository; it receives the deck,
the simulator log, the raw waveform and result.json. No leakage jump is simulated here.
"""
import json
from pathlib import Path
import sys
import time

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import extract
import sim

CONFIGS = json.loads((HERE / "configs.json").read_text())
LEAK_PER_MV = 4.42e-10          # conductance (S) that loses about 1 mV in a window of 169.5 us; refined on the run itself
CF = 30e-12


OPTIONS = ("instrumented", "junction", "zero-areas")
AMMETER = "instrumented" in sys.argv       # the first qualification runs measured the write current; see sim.py
JUNCTION = "areas" if "junction" in sys.argv else "zero" if "zero-areas" in sys.argv else None


def session(cfg, out, slots, ngspice, pdk, **deck_args):
    c = CONFIGS[cfg]
    return sim.Session(out, sim.deck(section=c["section"], temperature=c["temperature_C"], ammeter=AMMETER, junction=JUNCTION, **deck_args),
                       ngspice, pdk, seed=c["seed"], stop_s=slots * sim.SLOT)


def threshold(cfg, port, out, ngspice, pdk, coarse=0.25e-3, bracket=20e-6, limit=900):
    """Brackets the service threshold of one port between a correct read and an incorrect one, by bisection.

    A period is 440 us: slot k is a read, a clock-only cycle or nothing; slot k+1 may carry an imposed leak. The
    stored voltage rises when the reserve falls: by itself (the junctions, at high temperature) and under the
    imposed leak; it falls by one dose at a silent read or a clock-only cycle. The supervisor of this scan steers
    it to the middle of the bracket, reads, and halves the bracket. Every decision uses voltages measured in the
    run; the bracket is made of measured values only."""
    s = session(cfg, out, limit, ngspice, pdk)
    me, state, log = f"v(vmem{port})", dict(k=2, scale=LEAK_PER_MV, drift=0.0), []

    def period(kind, delta=0.0):
        """Returns (correct read?, latency, stored voltage before slot k, stored voltage at the end of the period)."""
        k = state["k"]
        a, b = k * sim.SLOT, (k + 1) * sim.SLOT
        s.run_to(a + 0.5e-6)
        pre = s.mean(me, a - 40e-6, a - 1e-6)
        s.set(f"vsel{port}", 0 if kind == "idle" else 1)
        s.set(f"vamp{port}", 1 if kind == "read" else 0)
        s.run_to(b + 0.5e-6)
        fired, latency = None, None
        if kind == "read":
            fired = float(s.cmd(f"meas tran f{k} max v(p) from={a + 3.5e-6:.12g} to={b - 2e-6:.12g}").split("=")[1].split()[0]) > 0.9
            if fired:
                when = float(s.cmd(f"meas tran w{k} when v(p)=0.9 rise=1 from={a + 3.5e-6:.12g} to={b - 2e-6:.12g}").split("=")[1].split()[0])
                latency = (when - a - sim.T0) / sim.TU
        before = s.mean(me, a + 160e-6, a + 200e-6)
        s.set(f"vsel{port}", 0)
        if delta > 0:
            s.set("vgl", delta * 1e3 * state["scale"])
            s.run_to(b + 170e-6)
            s.set("vgl", 0)
        s.run_to(b + 219e-6)
        after = s.mean(me, b + 180e-6, b + 218e-6)
        imposed = (after - before) - 0.543 * state["drift"]          # the drift of the 239 us between the two means is not the leak's
        if delta > 0 and imposed > 0.2 * delta:
            state["scale"] *= delta / imposed                         # calibrate the leak on what it did
        if kind == "idle" and delta == 0:
            state["drift"] = after - pre                              # what one period does by itself
        ok = bool(fired and latency <= 1.0) if kind == "read" else None
        log.append(dict(slot=k, kind=kind, read=kind == "read", delta_mV=delta * 1e3, fired=fired, latency=latency, correct=ok, pre_read_V=pre, after_V=after))
        state["k"] = k + 2
        return ok, latency, pre, after

    _, _, _, v = period("idle")                             # the drift of one period, before anything else
    for _ in range(30):                                     # silent reads train the port
        ok, _, pre, v = period("read")
        if ok:
            break
    else:
        s.kill()
        raise RuntimeError("no correct read after thirty reads")
    trained = len(log) - 2                                  # reads before the first correct one
    correct, incorrect = pre, None                          # highest stored voltage read correctly, lowest read incorrectly
    for _ in range(40):                                     # coarse descent
        ok, _, pre, v = period("read", coarse)
        if not ok:
            incorrect = pre
            break
        correct = pre
    assert incorrect is not None and incorrect > correct, "no incorrect read in the coarse descent"
    for _ in range(16):                                     # bisection
        if incorrect - correct <= bracket:
            break
        target = (correct + incorrect) / 2
        for _ in range(40):
            gap, drift = target - v, max(state["drift"], 0.0)
            if gap < drift - 2e-6:                          # one period alone would pass the target: take a dose first
                _, _, _, v = period("dose")
            elif gap <= 2 * drift + 0.05e-3:                # last step: the drift and a small leak
                _, _, _, v = period("idle", max(gap - drift, 0.0))
                break
            else:                                           # come to one drift and 0.05 mV under the target
                _, _, _, v = period("idle", min(gap - 2 * drift - 0.05e-3, 1.2e-3))
        else:
            s.kill()
            raise RuntimeError("the stored voltage did not reach the target")
        ok, _, pre, v = period("read")
        if ok:
            correct = max(correct, pre)
        else:
            incorrect = min(incorrect, pre)
    s.run_to(state["k"] * sim.SLOT + 0.5e-6)
    raw = s.close()
    return dict(config=cfg, port=port, log=log, slots=state["k"], raw=str(raw), trained_after_reads=trained, drift_V_per_period=state["drift"],
                bracket_V=[correct, incorrect])


def reads(cfg, out, v1_mV, v2_mV, ngspice, pdk):
    """Presets the two stored voltages, then reads port 1, port 2 and both, one read per 440 us."""
    s = session(cfg, out, 9, ngspice, pdk, vinit1=v1_mV * 1e-3, vinit2=v2_mV * 1e-3)
    plan = {2: (1, 0), 4: (0, 1), 6: (1, 1)}
    for k in range(2, 8):
        s.run_to(k * sim.SLOT + 0.5e-6)
        a = plan.get(k, (0, 0))
        for p in (1, 2):
            s.set(f"vsel{p}", a[p - 1])
            s.set(f"vamp{p}", 1)
    s.run_to(8 * sim.SLOT + 0.5e-6)
    raw = s.close()
    return dict(config=cfg, preset_mV=[v1_mV, v2_mV], raw=str(raw), slots=8)


def main():
    kind, cfg, out = sys.argv[1], sys.argv[2], None
    args = [a for a in sys.argv if a not in OPTIONS]
    ngspice, pdk = Path(args[-2]), Path(args[-1])
    began = time.time()
    if kind == "threshold":
        port, out = int(sys.argv[3]), Path(sys.argv[4])
        result = threshold(cfg, port, out, ngspice, pdk)
    else:
        out = Path(sys.argv[3])
        result = reads(cfg, out, float(sys.argv[4]), float(sys.argv[5]), ngspice, pdk)
    d = extract.read_raw(result["raw"])
    result.update(kind=kind, ammeter=AMMETER, junction=JUNCTION, wall_s=time.time() - began, points=int(len(d)), raw_sha256=sim.digest(result["raw"]),
                  deck_sha256=sim.digest(out / "input.spice"), raw=Path(result["raw"]).name,
                  records=[extract.slot_record(d, k) for k in range(2, result["slots"])])
    (out / "result.json").write_text(json.dumps(result, indent=1) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k not in ("records", "log")}))


if __name__ == "__main__":
    main()
