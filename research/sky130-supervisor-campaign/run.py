"""One run of the SKY130 supervisor campaign, as PREDICTION.md defines it. Started by the launch kit only.

  run.py --out DIR --ngspice BIN --pdk DIR --id NAME --scenario NAME --config NAME --mode supervised|self
         --noise 0|1 --jump SIEMENS --version 0|2 --seed N [--services 24] [--jump-period 8]

The deck, the simulator session, the kernel and the bounds are those of the qualification
(`../sky130-supervisor-closure`), unchanged: this file adds the leakage jump, the mode without
supervisor, and a smaller evidence. DIR receives, and nothing else:

  input.spice    the deck (its model library line carries the path of the PDK on this machine)
  .spiceinit     the simulator options of ../circuit/spiceinit.txt
  session.log    every command sent to the simulator and every answer
  head.raw       the first 30 us, with the noise sources: what the fingerprint is computed from
  noise.sha256   the fingerprint of the noise drawn by this run
  trace.raw      the whole run: FIRE output, stored node, summing node and write node of each port
  result.json    parameters, decisions of each period, measures of each slot; written last

A run that is cut leaves what it had written. It is never started again.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

import numpy as np

HERE = Path(__file__).resolve().parent
CLOSURE = HERE.parent / "sky130-supervisor-closure"
sys.path.insert(0, str(CLOSURE))
import extract
import kernel as K
import sim

BOUNDS_SHA256 = "1d01ce86e1af8c3ceb1c2bdf415bff15445d45fe162e9b9ed3d3a1c58dcf7b70"
G0 = 1e-11                      # the reference leak, in siemens
JUMP_PERIOD = 8
SERVICES = 24
PREPARATION_LIMIT = 40
READS = (("port1", (1, 0)), ("port2", (0, 1)), ("joint", (1, 1)))
OBS = (60e-6, 20e-6)            # the observation window: from 60 us to 20 us before the start of the slot
HEAD_S = 30e-6
HEAD = ["v(nzm)", "v(x1.nzo)", "v(x2.nzo)", "v(x1.nzi)", "v(x2.nzi)", "v(x1.nzc)", "v(x2.nzc)"]
TRACE = ["v(p)", "v(vmem1)", "v(vmem2)", "v(x1.sum)", "v(x2.sum)", "v(x1.si)", "v(x2.si)"]
LIBRARY = '.lib "pdk/models/sky130.lib.spice" '


def bounds_of(config, version):
    """Threshold and kernel bounds of each port, from the file pushed before the confirmation of the qualification."""
    path = CLOSURE / "BOUNDS_JUNCTION.json"
    assert sim.digest(path) == BOUNDS_SHA256, "not the bounds of the preregistration"
    table = json.loads(path.read_text())
    design = table["designs"][config][str(version)]
    assert design["well_formed"] and all(p["holds_the_reference_leak"] for p in design["ports"]), "no bounds for this configuration and version"
    return [t["u_service_V"] for t in table["thresholds"][config]], [K.Bounds(**p["bounds"]) for p in design["ports"]]


class Session(sim.Session):
    """The session of the qualification, in a folder that holds no link: the deck names the PDK by its path."""

    def __init__(self, folder, text, ngspice, pdk, seed, stop_s, max_step="200n"):
        self.folder = Path(folder)
        self.folder.mkdir(parents=True, exist_ok=False)
        assert text.count(LIBRARY) == 1 and "\n.include" not in text
        shutil.copyfile(sim.CIRCUIT / "spiceinit.txt", self.folder / ".spiceinit")
        (self.folder / "input.spice").write_text(text.replace(LIBRARY, f'.lib "{Path(pdk).resolve()}/models/sky130.lib.spice" '))
        assert sim.digest(ngspice) == sim.NGSPICE_SHA256, "not the pinned ngspice 42 binary"
        assert subprocess.check_output(["git", "-C", str(Path(pdk).resolve()), "rev-parse", "HEAD"], text=True).strip() == sim.PDK_COMMIT
        assert os.environ.get("SPICE_SCRIPTS") == str(sim.SPINIT.parent), "the launcher must give the committed simulator start file"
        assert "LD_PRELOAD" not in os.environ
        self.log = (self.folder / "session.log").open("w")
        self.p = subprocess.Popen([str(ngspice), "-p", "input.spice"], cwd=self.folder, stdin=subprocess.PIPE,
                                  stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, bufsize=1)
        self.n, self.started, self.max_step, self.stop_s = 0, False, max_step, stop_s
        self.cmd("set numdgt=16")
        self.cmd(f"setseed {seed}")
        self.cmd("reset")
        self.cmd("save " + " ".join(sorted(set(HEAD + TRACE))))

    def write(self, name, signals):
        self.cmd("set filetype=binary")
        self.cmd(f"write {name} " + " ".join(signals))
        return self.folder / name

    def close(self):
        raw = self.write("trace.raw", TRACE)
        self.p.stdin.write("quit\n")
        self.p.stdin.flush()
        try:
            self.p.wait(timeout=60)
        finally:
            self.log.close()
        return raw


def read_raw(path):
    """Points of a waveform of this campaign, in the columns of the qualification; a vector that was not saved is NaN."""
    blob = Path(path).read_bytes()
    head, _, body = blob.partition(b"Binary:\n")
    lines = head.decode("ascii", "replace").splitlines()
    nvar = int(next(l for l in lines if l.startswith("No. Variables:")).split(":")[1])
    npts = int(next(l for l in lines if l.startswith("No. Points:")).split(":")[1])
    names = [l.split("\t")[2] for l in lines[lines.index("Variables:") + 1:][:nvar]]
    assert any(l.startswith("Flags:") and "real" in l for l in lines) and names[0] == "time" and len(body) == 8 * nvar * npts, "unexpected raw file"
    saved = np.frombuffer(body, dtype="<f8").reshape(npts, nvar)
    assert np.isfinite(saved).all() and np.all(np.diff(saved[:, 0]) >= 0) and set(names[1:]) <= set(sim.SIGNALS)
    d = np.full((npts, len(sim.SIGNALS) + 1), np.nan)
    d[:, 0] = saved[:, 0]
    for i, name in enumerate(names[1:], 1):
        d[:, extract.COL[name]] = saved[:, i]
    return d


def slot_record(d, k):
    """What the waveform shows in slot k: FIRE, writes, and the capacitor voltage of each port before and after. The windows are those of the qualification."""
    start = k * sim.SLOT
    fires = extract.rises(d, "v(p)", start + 3.5e-6, start + sim.SLOT - 2e-6)
    r = dict(slot=k, fires=len(fires), fire_latency=(fires[0] - start - sim.T0) / sim.TU if fires else None)
    for p in (1, 2):
        u = lambda lo, hi: extract.mean(d, f"v(vmem{p})", lo, hi) - extract.mean(d, f"v(x{p}.sum)", lo, hi)
        r[f"writes{p}"] = len(extract.rises(d, f"v(x{p}.si)", start + 3.5e-6, start + sim.SLOT - 2e-6))
        r[f"u{p}_pre_pulse"] = u(start - 40e-6, start - 1e-6)
        r[f"u{p}_obs"] = u(start + 160e-6, start + 200e-6)
    return r


def decide(mode, bounds, carry, refused, report, period):
    """The action of each port in the maintenance slot of a service period, and what the kernel computed."""
    actions, detail = [], []
    for p in (0, 1):
        if mode == "self":                                  # no supervisor: the kernel is not consulted
            actions.append(K.WAIT)
            detail.append(None)
        elif refused[p] is not None:                        # after a refusal nothing is guaranteed: the rule of the preparation
            actions.append(K.prepare(bounds[p], report[p]))
            detail.append(None)
        else:
            action, lo, hi, nxt = K.step(bounds[p], carry[p], report[p])
            detail.append(dict(lower=lo, upper=hi, carry=carry[p], next_carry=nxt, answer=action))
            carry[p] = nxt
            if action == K.REFUSE:
                refused[p] = period
                action = K.prepare(bounds[p], report[p])
            actions.append(action)
    return actions, detail


def leak_at(period, jump, jump_period):
    return G0 if period is None or period < jump_period else jump


def run(a):
    config = json.loads((CLOSURE / "configs.json").read_text())[a.config]
    assert a.mode in ("supervised", "self") and a.noise in (0, 1) and a.version in (0, 2)
    assert config["seed"] is None or config["seed"] == a.seed, "a mismatch instance is its seed"
    v_service, bounds = bounds_of(a.config, a.version)
    text = sim.deck(section=config["section"], temperature=config["temperature_C"], noise=bool(a.noise), leak_S=G0, junction="areas")
    total = 2 + PREPARATION_LIMIT + 2 * a.services + 1
    began = time.time()
    s = Session(a.out, text, a.ngspice, a.pdk, a.seed, stop_s=total * sim.SLOT)
    s.run_to(HEAD_S)
    fingerprint = extract.noise_fingerprint(read_raw(s.write("head.raw", HEAD)))
    (a.out / "noise.sha256").write_text(fingerprint + "\n")
    events, carry, refused, entered = [], [None, None], [None, None], None
    k, n, leak_now = 2, 0, G0

    def controls(pairs):
        for p in (0, 1):
            s.set(f"vsel{p + 1}", pairs[p][0])
            s.set(f"vamp{p + 1}", pairs[p][1])

    while True:
        start = k * sim.SLOT
        s.run_to(start + 0.5e-6)
        obs = [s.mean(f"v(vmem{p + 1})", start - OBS[0], start - OBS[1]) - s.mean(f"v(x{p + 1}.sum)", start - OBS[0], start - OBS[1]) for p in (0, 1)]
        report = [K.to_units(v_service[p] - obs[p]) for p in (0, 1)]
        if entered is None:
            certificates = [K.entry(bounds[p], report[p]) for p in (0, 1)]
            if None not in certificates:
                entered, carry = k, certificates
            elif k - 2 >= PREPARATION_LIMIT:
                events.append(dict(slot=k, phase="preparation", observed_V=obs, report=report, action=["none", "none"], note="no entry certificate within the limit"))
                break
            else:
                actions = [K.prepare(bounds[p], report[p]) for p in (0, 1)]
                events.append(dict(slot=k, phase="preparation", observed_V=obs, report=report, action=actions))
                controls([(1, 0) if x == K.MAINTENANCE else (0, 0) for x in actions])
                k += 1
                continue
        if n == a.services:
            events.append(dict(slot=k, phase="end", observed_V=obs, report=report))
            controls([(0, 0), (0, 0)])                      # nothing is requested after the last observation
            break
        g = leak_at(n, a.jump, a.jump_period)               # set after the observation: the kernel is not told
        if g != leak_now:
            s.set("vgl", g)
            leak_now = g
        actions, detail = decide(a.mode, bounds, carry, refused, report, n)
        events.append(dict(slot=k, phase="maintenance", period=n, observed_V=obs, report=report, action=actions, kernel=detail, leak_S=leak_now))
        controls([(1, 0) if x == K.MAINTENANCE else (0, 0) for x in actions])
        s.run_to((k + 1) * sim.SLOT + 0.5e-6)
        name, ports = READS[n % 3]
        events.append(dict(slot=k + 1, phase="read", period=n, read=name))
        controls([(ports[0], 1), (ports[1], 1)])
        k, n = k + 2, n + 1
    s.run_to(k * sim.SLOT + 1e-6)
    raw = s.close()
    d = read_raw(raw)
    assert d[-1, 0] >= k * sim.SLOT
    result = dict(id=a.id, scenario=a.scenario, config=a.config, mode=a.mode, noise=bool(a.noise), version=a.version, seed=a.seed,
                  section=config["section"], temperature_C=config["temperature_C"], reference_leak_S=G0, jump_S=a.jump, jump_period=a.jump_period,
                  services_requested=a.services, services_run=n, entered_at_slot=entered, refused_at_period=refused, last_slot=k - 1,
                  ended_at_the_last_slot_of_its_plan=True, v_service_V=v_service, bounds=[vars(b) for b in bounds], events=events,
                  records=[slot_record(d, j) for j in range(2, k)], noise_fingerprint=fingerprint, points=int(len(d)), wall_s=time.time() - began,
                  deck_sha256=hashlib.sha256(text.encode()).hexdigest(), files={x: sim.digest(a.out / x) for x in ("input.spice", "head.raw", "trace.raw")})
    (a.out / "result.json").write_text(json.dumps(result, indent=1) + "\n")
    return result


def main():
    p = argparse.ArgumentParser(description=__doc__)
    for name in ("out", "ngspice", "pdk"):
        p.add_argument("--" + name, type=Path, required=True)
    for name in ("id", "scenario", "config", "mode"):
        p.add_argument("--" + name, required=True)
    p.add_argument("--noise", type=int, required=True)
    p.add_argument("--jump", type=float, required=True)
    p.add_argument("--version", type=int, required=True)
    p.add_argument("--seed", type=int, required=True)
    p.add_argument("--services", type=int, default=SERVICES)
    p.add_argument("--jump-period", type=int, default=JUMP_PERIOD)
    r = run(p.parse_args())
    print(json.dumps(dict(id=r["id"], services=r["services_run"], entered_at_slot=r["entered_at_slot"], wall_s=round(r["wall_s"]))))


if __name__ == "__main__":
    main()
