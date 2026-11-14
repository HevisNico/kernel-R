"""One supervised sequence on the two-port cell: the kernel in the loop. Phase-1 qualification tool.

The simulator is stopped at the start of every slot of 220 us. The supervisor then reads, for each
port, the voltage across its storage capacitor (stored node minus summing node), as a mean over a
window of 40 us that ended 20 us before, turns it into a report of reserve, and asks the kernel what
to do in the slot that begins. The noise of the integrator moves the two nodes together, so this
difference does not see it; the stored node alone does.

  preparation   slot after slot, a clock-only cycle on each port that has its headroom, until both
                ports have their entry certificate. No read is requested; nothing here is a service.
  service       period n is a maintenance slot (the kernel's action on each port) followed by a read
                slot. The reads cycle: port 1, port 2, both. The report of period n+1 is taken after
                the read of period n.

The imposed leak follows `leak`, a list of (first service period, conductance in siemens); the
first entry also holds during the preparation. In this qualification it is constant; no jump is
simulated here.
"""
import hashlib
import json
from pathlib import Path
import sys
import time

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import extract
import kernel as K
import sim

READS = (("port1", (1, 0)), ("port2", (0, 1)), ("joint", (1, 1)))
OBS = (60e-6, 20e-6)            # the observation window: from 60 us to 20 us before the start of the slot
NOISE = ["v(nzm)", "v(x1.nzo)", "v(x2.nzo)", "v(x1.nzi)", "v(x2.nzi)", "v(x1.nzc)", "v(x2.nzc)"]


def run(out, section, temperature, seed, v_service, bounds, leak, services, ngspice, pdk, noise=False, prep_limit=40, max_step="200n", ammeter=False, junction=None):
    """v_service[p] is the capacitor voltage (stored node minus summing node, V) of the service threshold of port p+1; bounds[p] its kernel bounds."""
    total = 2 + prep_limit + 2 * services + 1
    s = sim.Session(out, sim.deck(section=section, temperature=temperature, noise=noise, leak_S=leak[0][1], ammeter=ammeter, junction=junction), ngspice, pdk,
                    seed=seed, stop_s=total * sim.SLOT, max_step=max_step)
    began = time.time()
    events, carry, entered, refused = [], [None, None], None, [None, None]
    k, n, leak_now = 2, 0, leak[0][1]

    def controls(actions):
        for p in (0, 1):
            sel, amp = actions[p]
            s.set(f"vsel{p + 1}", sel)
            s.set(f"vamp{p + 1}", amp)

    def reports(slot):
        start = slot * sim.SLOT
        obs = [s.mean(f"v(vmem{p + 1})", start - OBS[0], start - OBS[1]) - s.mean(f"v(x{p + 1}.sum)", start - OBS[0], start - OBS[1]) for p in (0, 1)]
        return obs, [K.to_units(v_service[p] - obs[p]) for p in (0, 1)]

    while True:
        s.run_to(k * sim.SLOT + 0.5e-6)
        g = [value for first, value in leak if first <= n][-1] if entered is not None else leak[0][1]
        if g != leak_now:
            s.set("vgl", g)
            leak_now = g
        obs, rep = reports(k)
        if entered is None:
            certificates = [K.entry(bounds[p], rep[p]) for p in (0, 1)]
            if None not in certificates:
                entered, carry = k, certificates
            elif k - 2 >= prep_limit:
                events.append(dict(slot=k, phase="preparation", observed_V=obs, report=rep, action=["none", "none"], note="no entry certificate within the limit"))
                break
            else:
                act = [K.prepare(bounds[p], rep[p]) for p in (0, 1)]
                events.append(dict(slot=k, phase="preparation", observed_V=obs, report=rep, action=act))
                controls([(1, 0) if a == K.MAINTENANCE else (0, 0) for a in act])
                k += 1
                continue
        if n == services:
            events.append(dict(slot=k, phase="end", observed_V=obs, report=rep))
            break
        # maintenance slot of service period n
        act, detail = [], []
        for p in (0, 1):
            if refused[p] is not None:                      # after a refusal nothing is guaranteed; keep the preparation rule
                a = K.prepare(bounds[p], rep[p])
                detail.append(dict(lower=None, upper=None, carry=None))
            else:
                a, lo, hi, nxt = K.step(bounds[p], carry[p], rep[p])
                detail.append(dict(lower=lo, upper=hi, carry=carry[p], next_carry=nxt))
                carry[p] = nxt
                if a == K.REFUSE:
                    refused[p] = n
            act.append(a)
        events.append(dict(slot=k, phase="maintenance", period=n, observed_V=obs, report=rep, action=act, kernel=detail, leak_S=leak_now))
        controls([(1, 0) if a == K.MAINTENANCE else (0, 0) for a in act])
        # read slot of service period n
        s.run_to((k + 1) * sim.SLOT + 0.5e-6)
        name, ports = READS[n % 3]
        events.append(dict(slot=k + 1, phase="read", period=n, read=name))
        controls([(ports[0], 1), (ports[1], 1)])
        k, n = k + 2, n + 1
    s.run_to(k * sim.SLOT + 100e-6)
    raw = s.close()
    d = extract.read_raw(raw)
    i1 = int(np.searchsorted(d[:, 0], 2 * sim.SLOT))
    noise_bytes = np.ascontiguousarray(d[:i1][:, [extract.COL[x] for x in NOISE]]).tobytes()
    result = dict(section=section, temperature_C=temperature, seed=seed, noise=noise, observer="capacitor", ammeter=ammeter, junction=junction, v_service_V=list(v_service),
                  bounds=[vars(b) for b in bounds], leak=leak, services_requested=services, services_run=n,
                  entered_at_slot=entered, refused_at_period=refused, events=events, wall_s=time.time() - began,
                  points=int(len(d)), raw=raw.name, raw_sha256=sim.digest(raw), deck_sha256=sim.digest(Path(out) / "input.spice"),
                  noise_sha256=hashlib.sha256(noise_bytes).hexdigest(), noise_fingerprint=extract.noise_fingerprint(d), records=[extract.slot_record(d, j) for j in range(2, k)])
    (Path(out) / "result.json").write_text(json.dumps(result, indent=1) + "\n")
    return result


def main():
    """supervise.py BOUNDS_JSON CONFIG LEAK_S SERVICES OUT NGSPICE PDK [noise] [instrumented] [junction | zero-areas]"""
    table, cfg, leak_s, services, out, ngspice, pdk = sys.argv[1:8]
    row = json.loads(Path(table).read_text())[cfg]
    c = json.loads((HERE / "configs.json").read_text())[cfg]
    bounds = [K.Bounds(**row["bounds"][p]) for p in (0, 1)]
    r = run(Path(out), c["section"], c["temperature_C"], c["seed"], row["v_service_V"], bounds, [(0, float(leak_s))], int(services),
            Path(ngspice), Path(pdk), noise="noise" in sys.argv[8:], ammeter="instrumented" in sys.argv[8:],
            junction="areas" if "junction" in sys.argv[8:] else "zero" if "zero-areas" in sys.argv[8:] else None)
    print(json.dumps(dict(config=cfg, leak_S=float(leak_s), services=r["services_run"], entered_at_slot=r["entered_at_slot"],
                          refused=r["refused_at_period"], wall_s=round(r["wall_s"]), points=r["points"])))


if __name__ == "__main__":
    main()
