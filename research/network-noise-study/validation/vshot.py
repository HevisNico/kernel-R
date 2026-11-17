"""Validation: the shot terms' part of the reference density (amendment 1, item 2), from the same AC as the device
transfers of devnoise.py: per output of the four states, |H|² from a unit current between `dq` and the stored node
of each port of the cell, in the isolated cell deck at the extraction's operating point (and trip value).

  vshot.py WORK SHOT_<instance>.json INSTANCE
"""
import json, re, sys
from pathlib import Path
import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import vrun                         # noqa: E402
from vrun import model, net, INSTANCES, NGSPICE, PDK, Q, IPK, MODEL_STATES     # noqa: E402
import devnoise                     # noqa: E402


def main(work, out, instance):
    section, seed, _ = INSTANCES[instance]
    cells = ("a", "b")
    ex = json.loads((HERE / f"DEVNOISE_{instance}.json").read_text())
    res = []
    for o in ex["outputs"]:
        if o["state"] not in MODEL_STATES:
            continue
        c, p, state = o["cell"], o.get("port"), o["state"]
        text, _ = model.analysis_deck(section, cells, state, focus=(c, p))
        iso = model.isolate(text, c, cells)
        if o["trip"] is not None:
            src = {"window": "vfrc", "fire": "vfrcq"}[state]
            iso = re.sub(rf"^{src} (\S+) 0 dc \S+$", lambda m: f"{src} {m.group(1)} 0 dc {o['trip']:.15g}", iso, flags=re.M)
        names = [f"shot.x{c}.x{q}" for q in net.PORTS]
        nodes = [(f"x{c}.x{q}.dq", f"x{c}.vmem{q}") for q in net.PORTS]
        H, fails = devnoise.transfers(Path(work) / f"{state}_{c}{p or ''}", iso, names, nodes, model.out_expr(state, c, p),
                                      seed, state, c, p, str(NGSPICE), str(PDK))
        f = np.array(o["onoise"]["f"])
        full = np.logspace(0, 8, 161)                 # devnoise.FREQ: dec 20 1 1e8
        S = 2 * Q * IPK * sum(np.asarray(h) ** 2 for h in H)
        res.append(dict(state=state, cell=c, port=p, output=o["output"], ac_dc_failures=fails,
                        f=f.tolist(), shot_V2_Hz=np.interp(np.log(f), np.log(full), S).tolist()))
        print(state, c, p, fails, float(np.sqrt(np.trapezoid(S, full))), flush=True)
    Path(out).write_text(json.dumps(dict(instance=instance, I_A=IPK, outputs=res), indent=1) + "\n")


if __name__ == "__main__":
    main(*sys.argv[1:4])
