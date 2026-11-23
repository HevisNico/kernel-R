"""The SPICE deck of one layered network: every R cell, every inverter, their stimulus sources and write gates.

The transistor circuits are not changed:
- the R cell is research/circuit/cell.spice (two ports, main charge, FIRE comparator, protection latch), read from the
  file and turned into a sub-circuit `rcell`. Only its ideal stimulus changes, as in research/network-circuit/net.py
  (method, not code): each port gets its own admission, reset and precharge signals (ks, kr, kp), its pulse date (ts)
  and amplitude (amp) as nodes driven by sources that the driver sets while the run is stopped; the imposed leak is
  off (node gl at 0);
- the inverter is research/circuit/inverter/inverter.py (proof/circuit-inverter-composition 062a2862): the main charge,
  comparator and latch of the R cell (taken from the same cell.spice lines), a gated help sink, an inhibitory PMOS input
  and a reset transmission gate, turned into a sub-circuit `rinv` whose clocks (help window, admission window, input
  current, reset) are nodes driven by sources that the driver sets per slot. Design values from config.json.

The write gate of a port (read-only gate of research/learned-dnf-circuit/gate.py): its dose bias source idis is set to 0.
Mismatch: a section ending in _mm and `setseed` in the session (as research/circuit/run.py). No noise sources are
switched on. No junction areas and no wire capacitances: there is no layout of a network.
"""
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
PORTS = (1, 2)
NEVER = 1.0


def swap(text, old, new):
    assert text.count(old) == 1, (old, text.count(old))
    return text.replace(old, new)


def cell_parts(cfg):
    lines = (HERE / cfg["circuit"]["cell_spice"]).read_text().splitlines()
    head = lines[1:lines.index(".include blocks.spice") + 1]
    first = lines.index(next(l for l in lines if l.startswith(".subckt rport ")))
    last = lines.index(".ends")
    port = "\n".join(lines[first:last + 1])
    port = swap(port, ".subckt rport vq vr0 pb vmem vdd vcm vhi vlo vpre vinit ta=0 tb=1 tj=2",
                ".subckt rport vq vr0 pb vmem vdd vcm vhi vlo vpre vinit ks kr kp ts amp gl")
    old = next(l for l in port.splitlines() if l.startswith("bip "))
    port = swap(port, old, "bip vdd gm i = {ioff} + v(ks) * (v(amp)*{ipk}*exp(-(time - v(ts))*{at}) - {ioff})")
    for name, clock in (("bsen  sen0 ", "ks"), ("brst  rst0 ", "kr"), ("bpreb preb0", "kp")):
        old = next(l for l in port.splitlines() if l.startswith(name))
        port = swap(port, old, f"{name} 0 v = 1.8*v({clock})")
    port = swap(port, "rlk sum 0 {rlk}", "bleak sum 0 i = v(sum)*v(gl)")
    rest = lines[last + 1:-1]
    model = [l for l in rest if l.startswith(".model")]
    supplies = [l for l in rest if re.match(r"v(dd|r0|fire|reopen|cm|hi|lo|pre) ", l)]
    body = [l for l in rest if l and not l.startswith(("*", ".model")) and l not in supplies
            and not l.startswith(("vinit ", "x1 ", "x2 "))]
    assert len(supplies) == 8 and len(model) == 1 and any(l.startswith("xlp ") for l in body)
    # the main charge, comparator and latch: the lines from `ibm` to the last reference switch
    core = [l for l in body if not l.startswith("ibm ")]
    return head, port, body, core, model, supplies


def rcell(port, body):
    out = [".subckt rcell vdd vr0 vfire vreopen vcm vhi vlo vpre gl " +
           " ".join(f"vinit{p} ks{p} kr{p} kp{p} ts{p} amp{p}" for p in PORTS)]
    out += [f"x{p} vq vr0 pb vmem{p} vdd vcm vhi vlo vpre vinit{p} ks{p} kr{p} kp{p} ts{p} amp{p} gl rport" for p in PORTS]
    return "\n".join(out + body + [".ends"])


def rinv(core, cfg):
    d, tu = cfg["inverter"], cfg["stimulus"]["tu_s"]
    unit = 5e-12 * 0.5                                  # cq * vunit: one unit of the charge coordinate
    ih, ij = d["H0"] * unit / tu, d["J0"] * unit / tu
    hm, im, sn, sp, rn, rp = (d[k] for k in ("help_mirror", "inhib_mirror", "switch_n", "switch_p", "reset_n", "reset_p"))
    return "\n".join([
        ".subckt rinv vdd vr0 vfire vreopen khelp kinb kj krst krstb",
        "ibm ibm 0 10u"] + core + [
        f"ihref vdd hg dc {ih:.12g}",
        f"xmh1 hg hg 0 0 sky130_fd_pr__nfet_01v8 w={hm['w']} l={hm['l']}",
        f"xmh2 hd hg 0 0 sky130_fd_pr__nfet_01v8 w={hm['w']} l={hm['l']}",
        f"xsh hs khelp hd 0 sky130_fd_pr__nfet_01v8 w={sn['w']} l={sn['l']}",
        "vah vq hs dc 0",
        f"xmj1 jg jg vdd vdd sky130_fd_pr__pfet_01v8 w={im['w']} l={im['l']}",
        f"xmj2 jd jg vdd vdd sky130_fd_pr__pfet_01v8 w={im['w']} l={im['l']}",
        f"bjref jg 0 i = {ij:.12g}*v(kj)",
        f"xsj jd kinb js vdd sky130_fd_pr__pfet_01v8 w={sp['w']} l={sp['l']}",
        "vaj js vq dc 0",
        f"xsrn vq krst vr0 0 sky130_fd_pr__nfet_01v8 w={rn['w']} l={rn['l']}",
        f"xsrp vq krstb vr0 vdd sky130_fd_pr__pfet_01v8 w={rp['w']} l={rp['l']}",
        ".ends"])


def names(s):
    """Instance names: R cells c<layer>_<index>, inverters n<j>."""
    cells = [f"c{l + 1}_{i}" for l, nodes in enumerate(s["layers"]) for i in range(len(nodes))]
    invs = [f"n{j}" for j in range(s["m"])] if s["front"] else []
    return cells, invs


def build(s, cfg):
    """Netlist text, no analysis command (the session issues them)."""
    c = cfg["circuit"]
    head, port, body, core, model, supplies = cell_parts(cfg)
    tu, cyc, lead = cfg["stimulus"]["tu_s"], cfg["stimulus"]["cycle_tu"] * cfg["stimulus"]["tu_s"], cfg["stimulus"]["lead_s"]
    cells, invs = names(s)
    top = []
    for x in cells:
        nodes = []
        for p in PORTS:
            top += [f"vinit{x}{p} vinit{x}{p} 0 {c['vinit']:.12g}",
                    f"vks{x}{p} ks{x}{p} 0 pulse(0 1 {NEVER} 1n 1n {tu - 1e-9:.12g} 2)",
                    f"vkr{x}{p} kr{x}{p} 0 pulse(1 0 {NEVER} 1n 1n {cyc + lead:.12g} 2)",
                    f"vkp{x}{p} kp{x}{p} 0 pulse(0 1 {NEVER} 1n 1n {cyc:.12g} 2)",
                    f"vts{x}{p} ts{x}{p} 0 dc {NEVER}", f"vamp{x}{p} amp{x}{p} 0 dc 1"]
            nodes.append(f"vinit{x}{p} ks{x}{p} kr{x}{p} kp{x}{p} ts{x}{p} amp{x}{p}")
        top.append(f"x{x} vdd vr0 vfire vreopen vcm vhi vlo vpre gl {' '.join(nodes)} rcell")
    for x in invs:
        top += [f"vkh{x} kh{x} 0 pulse(0 1.8 {NEVER} 1n 1n 1u 2)",
                f"vki{x} ki{x} 0 pulse(1.8 0 {NEVER} 1n 1n 1u 2)",
                f"vkj{x} kj{x} 0 pulse(0 1 {NEVER} 1n 1n 1u 2)",
                f"vkr{x} kr{x} 0 pulse(0 1.8 {NEVER} 1n 1n 1u 2)",
                f"vkb{x} kb{x} 0 pulse(1.8 0 {NEVER} 1n 1n 1u 2)",
                f"x{x} vdd vr0 vfire vreopen kh{x} ki{x} kj{x} kr{x} kb{x} rinv"]
    out = [f"* layered network {s['tag']}: {len(cells)} R cells, {len(invs)} inverters (development, not preregistered)",
           f'.lib "pdk/models/sky130.lib.spice" {c["section"]}']
    out += head + [port, rcell(port, body)] + ([rinv(core, cfg)] if invs else []) + model + supplies + top
    out += [f".option temp={c['temperature']}", "vgl gl 0 dc 0", ".end"]
    return "\n".join(out) + "\n"


def size(text):
    """Transistors of the deck (SKY130 device instances, sub-circuits expanded) and its element lines."""
    blocks = (HERE / "../circuit/blocks.spice").read_text()
    subs, cur = {}, None
    for l in (blocks + "\n" + text).splitlines():
        t = l.split()
        if not t or t[0].startswith("*"):
            continue
        if t[0].lower() == ".subckt":
            cur = t[1]
            subs[cur] = []
        elif t[0].lower() == ".ends":
            cur = None
        elif cur is not None:
            subs[cur].append(t)

    def count(lines):
        n = 0
        for t in lines:
            if t[0][0].lower() != "x":
                continue
            model = next((x for x in t[1:] if x in subs or x.startswith("sky130_fd_pr")), None)
            n += 1 if model and model.startswith("sky130_fd_pr") else count(subs[model]) if model else 0
        return n
    top = [l.split() for l in text.splitlines() if l.split() and not l.startswith(("*", "."))]
    inside = set()
    for name in subs:
        pass
    body = []
    depth = 0
    for l in text.splitlines():
        t = l.split()
        if not t:
            continue
        if t[0].lower() == ".subckt":
            depth += 1
        elif t[0].lower() == ".ends":
            depth -= 1
        elif depth == 0 and not t[0].startswith(("*", ".")):
            body.append(t)
    return dict(transistors=count(body), top_elements=len(body))
