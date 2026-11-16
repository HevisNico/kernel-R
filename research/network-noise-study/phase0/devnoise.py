"""Phase 0: the per-instance extraction without the operating point of a whole-cell noise analysis.

  devnoise.py extract [--full] WORK OUT.json SECTION SEED|none CELLS NGSPICE PDK [STATE ...]
  devnoise.py idcheck WORK OUT.json      the drain-current check of an extraction, from its logs

`--full` runs the same method without isolating the cell (V2c's reference, on the nominal cell and 7102).

Why: in the frozen decks of model.py, the operating point that ngspice's `noise` command solves for itself fails
(gmin stepping, then source stepping) on almost every state and instance, nominal included, where `op` and `ac`
converge. Its result is then computed about another point: at `pulse` the same op-amp transistor, at the same
operating point in `op` (gm 6.561e-5 S, id 4.865 uA in both states on 7102), came out 1.17 to 1.71 times noisier than
at `hold`, the same factor for every device of an output. So the noise analysis of a whole cell is not used.

The method, for each cell (isolated as in model.isolate: the other cells' transistors grounded, their mismatch draws
kept) and each frozen state of model.py:
  1. `op` of the isolated cell (after the trip sweep where there is one): every node voltage;
  2. the noise current of every non-logic transistor of the cell at its own operating point, in ONE `noise` run of a
     deck where every transistor of the instance is in its place (draws kept) but only these are connected, each to
     ideal sources at its gate, source and body voltages of step 1 and at its drain through a 0 V probe. The probes'
     currents are summed by CCVS in series into the output, so that each device's transfer to the output is exactly
     1 ohm and its `.id` and `.1overf` contributions are its channel thermal and flicker current densities. The DC
     solution of this deck is trivial (every terminal is set), and it is checked: the drain current of each device
     equals its current in step 1;
  3. the transfer H from a unit current between drain and source of each of these devices to each output of the
     state, by AC in the isolated cell deck (whose operating point converges);
  4. the output density sum_k S_k |H_k|^2 (plus 4kT/R |H|^2 for the design resistors), the ranking, and for the kept
     devices their A and B (S = A + B / f^ef).
Logic gates (inv, nand2, nand3, srlatch) are not candidates: at every frozen state their outputs are held at the
rails, which is checked (every logic output within 10 mV of 0 or 1.8 V).
"""
import json, math, re, sys
from pathlib import Path
import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import model                                         # noqa: E402
from model import net, raw_ascii, seeded, ALPHA, BAND, COVER   # noqa: E402

KT = 1.380649e-23 * 300.15
LOGIC = re.compile(r"\.(xnad|xiad|xien|xicb|xnsa|xla|xia1|xia2|xnsc|xlc|xid1|xid2|xnsb|xlb|xnsi|xisi|xisd|xicm|xnsp|xnrp|xlp|xip1|xip2)\.|\.xcmp[sm]\.xi[12]\.")
LOGIC_OUT = ("admb", "adm", "en", "cmpb", "sba", "a", "ab", "ad1", "adb", "ad", "sbc0", "c", "cbar", "cd2", "cdel", "sbb",
             "b", "bb", "sib", "si", "sd")
FREQ = "dec 20 1 1e8"


def transistors(text):
    out = {}
    for line in text.splitlines():
        f = line.split()
        if f and f[0].startswith("x") and len(f) > 5 and f[5].startswith("sky130_fd_pr__"):
            out[f[0]] = dict(d=f[1], g=f[2], s=f[3], b=f[4], kind=f[5][len("sky130_fd_pr__"):])
    return out


def resistors(text, cell):
    out = {}
    for line in text.splitlines():
        f = line.split()
        if f and f[0].startswith(f"r.x{cell}.") and "noisy=0" not in line:
            out[f[0][2:]] = (f[1], f[2], f[3])
    return out


def op_run(work, text, seed, state, c, p, ngspice, pdk, cands=(), T=None):
    ctl = [".control", "set numdgt=16", "set filetype=ascii"] + seeded(seed) + model.balance(state, c, p) + ["op"]
    for k, d in enumerate(cands):
        ctl += [f"let idop{k} = @m.{d}.msky130_fd_pr__{T[d]['kind']}[id]", f"echo IDOP {d} $&idop{k}"]
    ctl += ["write op.raw all", "quit", ".endc", ".end"]
    stdout = model.spice(work, text.replace("\n.end\n", "\n") + "\n".join(ctl) + "\n", ngspice, pdk)
    trip = next((float(l.split()[1]) for l in stdout.splitlines() if l.startswith("TRIP ")), None)
    # @m[id] is the drain current of an nfet and minus the drain current of a pfet (ngspice's type sign): made the
    # current into the drain for both
    sign = {d: (1.0 if T[d]["kind"].startswith("nfet") else -1.0) for d in cands}
    ids = {l.split()[1]: sign[l.split()[1]] * float(l.split()[2]) for l in stdout.splitlines() if l.startswith("IDOP ")}
    return raw_ascii(work / "op.raw"), trip, ids


ID_REL, ID_ABS = 1e-3, 1e-12     # the drain-current check: |id(device deck) - id(op)| <= ID_REL |id(op)| + ID_ABS


def id_error(ids, id_op):
    """The largest ||id| - |id_op|| / (ID_REL |id_op| + ID_ABS) over the candidates: the check passes at <= 1. Magnitudes:
    the sign of @m[id] follows ngspice's conventions (type, and the device's own mode: a transistor conducting from
    source to drain, such as xms2 at hold, reads with the opposite sign), while the terminal voltages, which set the
    noise, are forced to those of step 1. ID_ABS: off devices carry fA, at the floor of gmin, and add no noise of note."""
    return max((abs(abs(ids[d]) - abs(id_op[d])) / (ID_REL * abs(id_op[d]) + ID_ABS) for d in id_op if d in ids), default=None)


def id_check(work):
    """The drain-current check recomputed from the logs of an extraction's work directory (WORK/<state>_<cell><port>)."""
    out = {}
    for w in sorted(Path(work).glob("*_*")):
        if not (w / "op" / "log.txt").exists() or not (w / "dev" / "log.txt").exists():
            continue
        T = transistors((w / "op" / "deck.spice").read_text())
        sign = {d: (1.0 if t["kind"].startswith("nfet") else -1.0) for d, t in T.items()}
        op = {l.split()[1]: sign[l.split()[1]] * float(l.split()[2]) for l in open(w / "op" / "log.txt") if l.startswith("IDOP ")}
        dev = {l.split()[1]: float(l.split()[2]) for l in open(w / "dev" / "log.txt") if l.startswith("ID ")}
        out[w.name] = dict(devices=len(op), checked=len(set(op) & set(dev)), max_error=id_error(dev, op))
    return out


SUFFIX = {"f": 1e-15, "p": 1e-12, "n": 1e-9, "u": 1e-6, "m": 1e-3, "k": 1e3, "meg": 1e6, "g": 1e9, "t": 1e12}
PARAMS = {"rleak": 2 * 20e-6 / 5e-12}          # cell.spice: rleak = 2 tu / cq


def value(v):
    v = v.strip("{}").lower()
    if v in PARAMS:
        return PARAMS[v]
    m = re.fullmatch(r"([0-9.eE+-]+)(meg|[fpnumkgt])?", v)
    if not m:
        raise ValueError(f"resistor value {v}")
    return float(m.group(1)) * SUFFIX.get(m.group(2) or "", 1.0)


def vnode(op, n):
    return 0.0 if n == "0" else float(op[f"v({n})"][0])


def device_noise(work, full_text, cands, op, seed, ngspice, pdk):
    """S_k(f) of each candidate at its operating point: one noise run, every terminal set, transfer 1 ohm."""
    keep = []
    for line in full_text.splitlines():
        f = line.split()
        if not f or line.startswith(("*", ".")) or line.startswith("+"):
            if not line.startswith((".nodeset", ".end", ".control")):
                keep.append(line)
            continue
        if f[0].startswith("x") and len(f) > 5 and f[5].startswith("sky130_fd_pr__"):
            if f[0] in cands:
                k = cands.index(f[0])
                keep.append(" ".join([f[0], f"dd{k}", f"dg{k}", f"ds{k}", f"db{k}"] + f[5:]))
            else:
                keep.append(" ".join([f[0], "0", "0", "0", "0"] + f[5:]))
    T = transistors(full_text)
    drv, prev = [], "0"
    for k, d in enumerate(cands):
        t = T[d]
        drv += [f"vpd{k} dd{k}x 0 dc {vnode(op, t['d']):.15g}", f"vprobe{k} dd{k}x dd{k} dc 0",
                f"vpg{k} dg{k} 0 dc {vnode(op, t['g']):.15g}", f"vps{k} ds{k} 0 dc {vnode(op, t['s']):.15g}",
                f"vpb{k} db{k} 0 dc {vnode(op, t['b']):.15g}", f"hsum{k} hs{k} {prev} vprobe{k} 1"]
        prev = f"hs{k}"
    drv += ["vref vref 0 dc 0 ac 1", "rref vref 0 1 noisy=0"]
    ctl = [".control", "set numdgt=16", "set filetype=ascii"] + seeded(seed) + ["op"] + [
        f"echo ID {d} $&i(vprobe{k})" for k, d in enumerate(cands)] + [
        f"noise v({prev}) vref {FREQ} 1", "setplot noise1", "write noise.raw all", "quit", ".endc", ".end"]
    text = "\n".join(keep) + "\n" + "\n".join(drv) + "\n" + "\n".join(ctl) + "\n"
    stdout = model.spice(work, text, ngspice, pdk)
    # ngspice's branch current of vprobe (from dd{k}x through the source to dd{k}) is the current into the drain
    ids = {l.split()[1]: float(l.split()[2]) for l in stdout.splitlines() if l.startswith("ID ")}
    r = raw_ascii(work / "noise.raw")
    f = r["frequency"]
    S = {}
    for d in cands:
        key = f"onoise.m.{d}.msky130_fd_pr__{T[d]['kind']}"
        S[d] = (r[key + ".id"] ** 2, r[key + ".1overf"] ** 2)
    log = (work / "log.txt").read_text()
    return f, S, ids, log.count("stepping failed")


def transfers(work, text, cands, nodes, out, seed, state, c, p, ngspice, pdk):
    inj = [f"iinj{k} {nodes[k][0]} {nodes[k][1]} dc 0 ac 0" for k in range(len(cands))]
    ctl = [".control", "set numdgt=16", "set filetype=ascii"] + seeded(seed) + model.balance(state, c, p)
    for k in range(len(cands)):
        ctl += [f"alter @iinj{k}[acmag]=1", f"ac {FREQ}", f"let h{k} = mag({out})", f"write h{k}.raw h{k}", f"alter @iinj{k}[acmag]=0"]
    ctl += ["op", "write op_after.raw all", "quit", ".endc", ".end"]
    model.spice(work, text.replace("\n.end\n", "\n") + "\n".join(inj + ctl) + "\n", ngspice, pdk)
    log = (work / "log.txt").read_text()
    H = [list(raw_ascii(work / f"h{k}.raw").values())[1] for k in range(len(cands))]
    return H, log.count("stepping failed")


def extract_cell(work, section, seed, cells, c, ngspice, pdk, states):
    res = []
    for state in states:
        focus_list = [o for o in model.outputs(state, cells) if o[0] == c]      # the outputs of model.py, per port but fire
        for focus in focus_list:
            _, p = focus
            text, _ = model.analysis_deck(section, cells, state, focus=focus)
            iso = text if FULL else model.isolate(text, c, cells)
            w = work / f"{state}_{c}{p or ''}"
            T = transistors(iso)
            cands = sorted(d for d in T if d.startswith(f"x{c}.") and not LOGIC.search(d))
            op, trip, id_op = op_run(w / "op", iso, seed, state, c, p, ngspice, pdk, cands, T)
            if trip is not None:                      # the swept source stays where the comparator trips
                src = {"window": "vfrc", "fire": "vfrcq"}[state]
                iso = re.sub(rf"^{src} (\S+) 0 dc \S+$", lambda m: f"{src} {m.group(1)} 0 dc {trip:.15g}", iso, flags=re.M)
            logic = {n: vnode(op, f"x{c}.x{q}.{n}") for q in net.PORTS for n in LOGIC_OUT if f"v(x{c}.x{q}.{n})" in op}
            logic_ok = all(min(abs(v), abs(v - 1.8)) <= 0.01 for v in logic.values())
            f, S, ids, dev_fail = device_noise(w / "dev", iso, cands, op, seed, ngspice, pdk)
            out = model.out_expr(state, c, p)
            R = resistors(iso, c)
            nodes = [(T[d]["d"], T[d]["s"]) for d in cands] + [(a, b) for a, b, _ in R.values()]
            H, ac_fail = transfers(w / "ac", iso, cands + list(R), nodes, out, seed, state, c, p, ngspice, pdk)
            band = (f >= BAND[0]) & (f <= BAND[1])
            contrib = {}
            for k, d in enumerate(cands):
                th, fl = S[d]
                contrib[d] = (th + fl) * H[k] ** 2
            for j, (name, (a, b, val)) in enumerate(R.items()):
                contrib[name] = 4 * KT / value(val) * H[len(cands) + j] ** 2
            total = sum(contrib.values())
            p_total = float(np.trapezoid(total[band], f[band]))
            share = {d: float(np.trapezoid(v[band], f[band])) / p_total for d, v in contrib.items()}
            keep, acc = [], 0.0
            for d in sorted(share, key=share.get, reverse=True):
                if acc >= COVER:
                    break
                keep.append(d); acc += share[d]
            kept = []
            for d in keep:
                if d in S:
                    th, fl = S[d]
                    a = ALPHA[T[d]["kind"]]
                    kept.append(dict(device=d, kind=T[d]["kind"], nodes=[T[d]["d"], T[d]["s"]], share=share[d], alpha=a,
                                     white_A2_Hz=float(np.median(th[band])), flicker_B=float(np.median((fl * f ** a)[band])),
                                     spread_white=float(np.percentile(th[band], 95) / np.percentile(th[band], 5)),
                                     spread_flicker=float(np.percentile((fl * f ** a)[band], 95) / np.percentile((fl * f ** a)[band], 5))))
                else:
                    kept.append(dict(device=d, kind="res", share=share[d]))
            id_err = id_error(ids, id_op)
            parts = {f"{lo:g}-{hi:g}": float(np.sqrt(np.trapezoid(total[(f >= lo) & (f <= hi)], f[(f >= lo) & (f <= hi)])))
                     for lo, hi in ((1, BAND[0]), BAND, (BAND[1], 1e8))}
            r = dict(state=state, cell=c, port=p, output=out, trip=trip, candidates=len(cands), resistors=len(R),
                     logic_at_rails=logic_ok, logic_worst_V=max([min(abs(v), abs(v - 1.8)) for v in logic.values()] or [0]),
                     device_dc_failures=dev_fail, ac_dc_failures=ac_fail, max_rel_id_error=id_err,
                     rms_V=parts, covered=acc, kept=kept, onoise=dict(f=f[::4].tolist(), total=total[::4].tolist()))
            print(state, c, p, "trip", trip, "rails", logic_ok, "fails", dev_fail, ac_fail, "id_err", id_err,
                  {k: round(v * 1e6, 1) for k, v in parts.items()}, [(x["device"], round(x["share"], 3)) for x in kept[:5]], flush=True)
            res.append(r)
    return res


FULL = False          # --full: the reference of V2c, the same method in the full deck (no isolation), where its AC converges


def extract(work, out, section, seed, cells, ngspice, pdk, states):
    res = dict(method="devnoise", full_deck=FULL, stack_conductance=model.COND, section=section, seed=seed, cells=cells, band_Hz=BAND, cover=COVER,
               op_match=model.op_match(work / "opmatch", section, seed, cells, ngspice, pdk), outputs=[])
    print("op match", res["op_match"], flush=True)
    for c in cells:
        res["outputs"] += extract_cell(work, section, seed, cells, c, ngspice, pdk, states)
        Path(out).write_text(json.dumps(res, indent=1) + "\n")


if __name__ == "__main__":
    a = sys.argv[2:]
    if sys.argv[1] == "idcheck":            # devnoise.py idcheck WORK OUT.json
        r = id_check(a[0])
        Path(a[1]).write_text(json.dumps(r, indent=1) + "\n")
        print(max(v["max_error"] for v in r.values()), [k for k, v in r.items() if v["max_error"] > 1 or v["checked"] < v["devices"]])
    elif sys.argv[1] == "extract":          # devnoise.py extract [--full] WORK OUT.json SECTION SEED|none CELLS NGSPICE PDK [STATE ...]
        if a[0] == "--full":
            FULL, a = True, a[1:]
        if a[0] == "--no-cond":                  # V2's conditioning check: the stack nodes without their conductance
            model.COND, a = False, a[1:]
        extract(Path(a[0]), Path(a[1]), a[2], None if a[3] == "none" else int(a[3]), tuple(a[4].split(",")), a[5], a[6],
                a[7:] or ["hold", "window", "fire", "pulse"])
