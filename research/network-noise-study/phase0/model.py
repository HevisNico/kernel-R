"""Phase 0, feasibility, no claim: the per-instance generator of a noise model drawn from the device models.

  model.py extract WORK OUT.json SECTION SEED|none CELLS NGSPICE PDK [STATE ...]

CELLS is a comma-separated list of cell names, the cells of the deck of the instance (for example a,b): the mismatch
sample of a seed belongs to the whole deck, so the extraction runs on that deck, with its seed (`setseed`, `reset`),
never on a cell taken alone. Every cell is frozen in the same state; each port or cell in turn is the output.

States (default: all five) and the output of each:
  hold    the stored voltage v(x<c>.vmem<p>), preset ended, no pulse (as in pilot.py)
  preset  the voltage across the integrating capacitor, v(x<c>.vmem<p>) - v(x<c>.x<p>.sum), preset switch closed:
          what the end of the preset freezes. The out-of-band part is reported, not modelled
  window  the first stage of the window comparator of the port, v(x<c>.x<p>.xcmps.o1), with the sensor node held by
          an ideal source, set by a DC sweep to where that comparator trips (the precharge cannot do it: below about
          0.65 V the discharge holds the sensor node at 0.4 V). The sensor's own noise is shorted here; it is not
          part of a decision point, and its sampled part is item V6
  fire    the first stage of the FIRE comparator of the cell, v(x<c>.xcmpm.o1), with vr0 set where it trips
  pulse   the main charge v(x<c>.vq), the port admitted and its mirror at the peak current of a pulse

What every analysis deck changes, against the network deck: the bench resistors are noiseless; `vcm` gets `ac 1`, the
input that the noise command requires; and every internal node of a NAND stack gets a noiseless 1e-12 S to ground.
Phase 0 found that with both transistors of a stack off, such a node is held only by leakage, and the small-signal
matrix is then near singular below about 30 Hz (FEASIBILITY.md, section 3). In `hold`, `window`, `fire` and `pulse`
the preset switches are noiseless 1e14 ohm resistors.

For each state and output it keeps the devices that make 99 % of the output noise power over 10 Hz to 1.25 MHz and
writes their white density A and flicker coefficient B (S = A + B / f^ef), as in pilot.py.
"""
import json, re, sys
from pathlib import Path
import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import pilot                                   # noqa: E402
from pilot import net, raw_ascii, spice, seeded, vec, ALPHA, BENCH, BAND, COVER   # noqa: E402

STATES = ("hold", "preset", "window", "fire", "pulse")
STACK = re.compile(r"\.n[12]$")


def analysis_deck(section, cells, state, focus=None):
    """The frozen deck. `focus` is (cell, port) for `pulse`: the port that is admitted."""
    t = net.deck(cells=cells, section=section)
    if state != "preset":
        for c in cells:
            for p in net.PORTS:
                t = net.swap(t, f"s.x{c}.x{p}.srst x{c}.x{p}.sum x{c}.x{p}.drv x{c}.x{p}.rsti 0 swr",
                             f"r.hold{c}{p} x{c}.x{p}.sum x{c}.x{p}.drv 1e14 noisy=0")
    t = net.swap(t, "\nvcm vcm 0 {vcm}\n", "\nvcm vcm 0 {vcm} ac 1\n")
    if state == "window":                      # the sensor node is held where the comparator trips (see balance)
        c, p = focus
        t = t.replace("\n.end\n", f"\nvfrc x{c}.x{p}.vs 0 dc 0.6\n.end\n")
    if state == "pulse":
        c, p = focus
        t = net.swap(t, f"vks{c}{p} ks{c}{p} 0 pulse(0 1 {net.NEVER} 1n 1n {net.TU - 1e-9:.12g} 2)", f"vks{c}{p} ks{c}{p} 0 dc 1")
        t = net.swap(t, f"vts{c}{p} ts{c}{p} 0 dc {net.NEVER}", f"vts{c}{p} ts{c}{p} 0 dc 0")
    out, nodes = [], set()
    for line in t.splitlines():
        f = line.split()
        name = f[0] if f else ""
        if name.startswith("r.") and name.rsplit(".", 1)[-1] in BENCH:
            line += " noisy=0"
        if f and "sky130_fd_pr__" in line:
            nodes.update(n for n in f[1:5] if STACK.search(n))
        out.append(line)
    cond = [f"r.cond{k} {n} 0 1e12 noisy=0" for k, n in enumerate(sorted(nodes))]
    text = "\n".join(out) + "\n"
    return text.replace("\n.end\n", "\n" + "\n".join(cond) + "\n.end\n"), len(cond)


def devices(text):
    out = {}
    for line in text.splitlines():
        f = line.split()
        if not f:
            continue
        m = re.search(r"sky130_fd_pr__(\w+)", line)
        if m and f[0].startswith("x"):
            out[f[0]] = (f[1], f[3], m.group(1))
        elif f[0].startswith("r.") and "noisy=0" not in line:
            out[f[0][2:]] = (f[1], f[2], "res")
    return out


def outputs(state, cells):
    if state in ("hold", "preset", "window", "pulse"):
        return [(c, p) for c in cells for p in net.PORTS]
    return [(c, None) for c in cells]


def out_expr(state, c, p):
    return {"hold": f"v(x{c}.vmem{p})", "preset": f"v(x{c}.vmem{p},x{c}.x{p}.sum)", "window": f"v(x{c}.x{p}.xcmps.o1)",
            "fire": f"v(x{c}.xcmpm.o1)", "pulse": f"v(x{c}.vq)"}[state]


def balance(state, c, p):
    """Control lines that set the shared source where the comparator of (c, p) trips, before the noise analysis."""
    if state == "window":
        src, lo, hi, node = "vfrc", 0.54, 0.66, f"x{c}.x{p}.xcmps.o2"
    elif state == "fire":
        src, lo, hi, node = "vr0", 0.74, 0.86, f"x{c}.xcmpm.o2"
    else:
        return []
    return [f"dc {src} {lo} {hi} 0.0005", f"meas dc vtrip when v({node})=0.9", f"echo TRIP $&vtrip",
            f"alter {src} dc = $&vtrip"]


def one_output(work, text, devs, seed, state, c, p, ngspice, pdk):
    out = out_expr(state, c, p)
    pre = [".control", "set numdgt=16", "set filetype=ascii"] + seeded(seed) + balance(state, c, p) + ["op"]
    body = text.replace("\n.end\n", "\n")
    stdout = spice(work / "noise", body + "\n".join(pre + [f"noise {out} vcm dec 20 1 1e8 1", "setplot noise1",
                                                         "write noise.raw all", "quit", ".endc", ".end"]) + "\n", ngspice, pdk)
    trip = next((float(l.split()[1]) for l in stdout.splitlines() if l.startswith("TRIP ")), None)
    if not (work / "noise" / "noise.raw").exists():
        return dict(state=state, cell=c, port=p, output=out, error="no noise result", trip=trip)
    r = raw_ascii(work / "noise" / "noise.raw")
    if "onoise_spectrum" not in r:
        return dict(state=state, cell=c, port=p, output=out, error="no noise plot", trip=trip)
    f = r["frequency"]
    band = (f >= BAND[0]) & (f <= BAND[1])
    integ = lambda s: float(np.trapezoid(s[band], f[band]))
    total = r["onoise_spectrum"] ** 2
    p_total = integ(total)
    share = {d: integ(r[vec(d, k)] ** 2) / p_total for d, (_, _, k) in devs.items() if vec(d, k) in r}
    keep, acc = [], 0.0
    for d in sorted(share, key=share.get, reverse=True):
        if acc >= COVER:
            break
        keep.append(d); acc += share[d]
    inj = [f"iinj{k} {devs[d][0]} {devs[d][1]} dc 0 ac 0" for k, d in enumerate(keep)]
    ctl = list(pre)
    for k in range(len(keep)):
        ctl += [f"alter @iinj{k}[acmag]=1", "ac dec 20 1 1e8", f"let h{k} = mag({out})", f"write h{k}.raw h{k}",
                f"alter @iinj{k}[acmag]=0"]
    spice(work / "ac", body + "\n".join(inj + ctl + ["quit", ".endc", ".end"]) + "\n", ngspice, pdk)
    kept = []
    for k, d in enumerate(keep):
        h = list(raw_ascii(work / "ac" / f"h{k}.raw").values())[1]
        a, b, kind = devs[d]
        key = vec(d, kind)
        if kind == "res":
            th, fl, alpha = r[key + "_thermal"] ** 2 / h ** 2, np.zeros_like(h), 1.0
        else:
            th, fl, alpha = r[key + ".id"] ** 2 / h ** 2, r[key + ".1overf"] ** 2 / h ** 2, ALPHA[kind]
        sel = band & (h > 1e-2 * h[band].max())
        A, B = float(np.median(th[sel])), float(np.median(fl[sel] * f[sel] ** alpha))
        spread = lambda y: float(np.percentile(y, 95) / max(np.percentile(y, 5), 1e-300))
        kept.append(dict(device=d, kind=kind, nodes=[a, b], share=share[d], alpha=alpha, white_A2_Hz=A, flicker_B=B,
                         spread_white=spread(th[sel]), spread_flicker=spread(fl[sel] * f[sel] ** alpha) if B > 0 else None))
    parts = {}
    for lo, hi in ((1, BAND[0]), BAND, (BAND[1], 1e8)):
        m = (f >= lo) & (f <= hi)
        parts[f"{lo:g}-{hi:g}"] = float(np.sqrt(np.trapezoid(total[m], f[m])))
    return dict(state=state, cell=c, port=p, output=out, trip=trip, rms_V=parts, covered=acc, kept=kept,
                top_share=max(share.values()) if share else None,
                onoise=dict(f=f[::4].tolist(), total=total[::4].tolist()))


def extract(work, out, section, seed, cells, ngspice, pdk, states):
    res = dict(section=section, seed=seed, cells=cells, band_Hz=BAND, cover=COVER, outputs=[])
    for state in states:
        for c, p in outputs(state, cells):
            text, ncond = analysis_deck(section, cells, state, focus=(c, p))
            devs = devices(text)
            r = one_output(work / f"{state}_{c}{p or ''}", text, devs, seed, state, c, p, ngspice, pdk)
            r["conditioned_nodes"] = ncond
            res["outputs"].append(r)
            ks = r.get("kept", [])
            print(state, c, p, r.get("error", ""), "trip", r.get("trip"), "rms", {k: round(v * 1e6, 1) for k, v in r.get("rms_V", {}).items()},
                  "kept", len(ks), [(x["device"], round(x["share"], 3), round(x["spread_white"], 3)) for x in ks[:4]], flush=True)
            Path(out).write_text(json.dumps(res, indent=1) + "\n")


if __name__ == "__main__":
    a = sys.argv[2:]
    if sys.argv[1] == "extract":
        extract(Path(a[0]), Path(a[1]), a[2], None if a[3] == "none" else int(a[3]), tuple(a[4].split(",")), a[5], a[6],
                a[7:] or list(STATES))
