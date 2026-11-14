"""Several R cells in one transistor-level deck, with pulses at any date: the testbench of phase 0.

Exploratory tool. It preregisters nothing and is no registered runner.

The circuit of `../circuit/cell.spice` is not changed. What changes is around it:

- the cell (two ports, main capacitor, FIRE comparator, protection latch) becomes a sub-circuit, so
  that the deck holds several cells, each with its own devices and its own mismatch sample;
- the stimulus no longer repeats on a fixed period. Each port of each cell has its own three timing
  signals (admission, reset of the sequencing latches, end of precharge) and its own pulse current,
  all tied to one date: the start of that port's next pulse. The date is set while the run is stopped.
  The signals keep the shape they have in `cell.spice`: pulse sources with 1 ns edges;
- the imposed leak of each integrator is a conductance set by the node `gl` (zero by default);
- with `junction="areas"` every transistor gets the source and drain areas of stage J
  (`../sky130-supervisor-closure/junction`); with `caps`, the wire capacitances of a layout
  extraction are added inside each cell (nothing between cells: there is no layout of a network).

A session drives the simulator through a pipe: run to a date or to the next FIRE of a watched cell,
schedule a pulse, go on. Who schedules what, and when, is the router's business (`router.py`).
"""
import importlib.util
import json
import math
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
CLOSURE = HERE.parent / "sky130-supervisor-closure"
CIRCUIT = HERE.parent / "circuit"
sys.path.insert(0, str(CLOSURE))
import sim

TU = 20e-6                      # one time unit: the length of a pulse
CYCLE = 6 * TU                  # a port is busy for six units from the start of its pulse; then reset and precharge
LEAD = 1e-6                     # the reset of the sequencing latches is released 1 us before the pulse
NEVER = 1.0                     # a date after the end of every run
NOISE_STEP = 0.4e-6             # the noise sources draw a value every 0.4 us; no edge may fall on such a date
PORTS = (1, 2)


def snap(t):
    """The first date at or after t that is 0.1 us after a noise sample: every edge of a pulse that starts there
    (start, start - 1 us, start + 20 us, start + 120 us) is then 0.1 us away from the samples, as in `cell.spice`."""
    k = math.ceil((t - 0.1e-6) / NOISE_STEP - 1e-9)
    return max(k, 0) * NOISE_STEP + 0.1e-6


def swap(text, old, new, count=1):
    assert text.count(old) == count, (old, text.count(old))
    return text.replace(old, new)


def deck(cells=("a", "b"), section="tt", temperature=27, noise=False, junction="areas", caps=None, areas=None, vinit=0.3895):
    """Netlist text of a deck with one R cell per name in `cells`. No analysis command: the session issues them.

    `vinit` is the preset of every stored voltage, or a dict {(cell, port): volts}. `areas` and `caps` are paths of
    csv files for one cell, in the format of `junction/netlist.py`; `junction="areas"` uses the areas of stage J."""
    text = (CIRCUIT / "cell.spice").read_text()
    lines = text.splitlines()
    head = lines[1:lines.index(".include blocks.spice") + 1]
    first, last = lines.index(next(l for l in lines if l.startswith(".subckt rport "))), lines.index(".ends")
    port = "\n".join(lines[first:last + 1])
    port = swap(port, ".subckt rport vq vr0 pb vmem vdd vcm vhi vlo vpre vinit ta=0 tb=1 tj=2",
                ".subckt rport vq vr0 pb vmem vdd vcm vhi vlo vpre vinit ks kr kp ts amp gl")
    old = next(l for l in port.splitlines() if l.startswith("bip "))
    port = swap(port, old, "bip vdd gm i = {ioff} + v(ks) * (v(amp)*{ipk}*exp(-(time - v(ts))*{at}) - {ioff})")
    for name, clock, rest in (("bsen  sen0 ", "ks", None), ("brst  rst0 ", "kr", None), ("bpreb preb0", "kp", None)):
        old = next(l for l in port.splitlines() if l.startswith(name))
        port = swap(port, old, f"{name} 0 v = 1.8*v({clock})")
    port = swap(port, "rlk sum 0 {rlk}", "bleak sum 0 i = v(sum)*v(gl)")
    rest = lines[last + 1:-1]
    model = [l for l in rest if l.startswith(".model")]
    supplies = [l for l in rest if re.match(r"v(dd|r0|fire|reopen|cm|hi|lo|pre) ", l)]
    body = [l for l in rest if l and not l.startswith(("*", ".model")) and l not in supplies and not l.startswith(("vinit ", "x1 ", "x2 "))]
    assert len(supplies) == 8 and len(model) == 1 and any(l.startswith("xlp ") for l in body) and any(l.startswith("ibm ") for l in body)
    cell = [".subckt rcell vdd vr0 vfire vreopen vcm vhi vlo vpre gl vinit1 ks1 kr1 kp1 ts1 amp1 vinit2 ks2 kr2 kp2 ts2 amp2"]
    cell += [f"x{p} vq vr0 pb vmem{p} vdd vcm vhi vlo vpre vinit{p} ks{p} kr{p} kp{p} ts{p} amp{p} gl rport" for p in PORTS]
    cell += body + [".ends"]
    if noise:
        params = json.loads((CIRCUIT / "noise.json").read_text())["params"]
        body_text = "\n".join(cell)
        for node, white, flicker in (("nzc", params["vncw"], params["vncf"]), ("nzo", params["vnow"], params["vnof"]),
                                    ("nzi", params["inmw"], 0), ("nzm", params["vnmw"], params["vnmf"])):
            old = f"vnz{node[2]} {node} 0 dc 0"
            new = f"{old} trnoise({white:.16g} {params['tnz']:.16g} {1 if flicker else 0} {flicker:.16g})"
            if node == "nzm":
                body_text = swap(body_text, old, new)
            else:
                port = swap(port, old, new)
        cell = body_text.splitlines()
    top = []
    for c in cells:
        nodes = []
        for p in PORTS:
            v0 = vinit[(c, p)] if isinstance(vinit, dict) else vinit
            top += [f"vinit{c}{p} vinit{c}{p} 0 {v0:.12g}",
                    f"vks{c}{p} ks{c}{p} 0 pulse(0 1 {NEVER} 1n 1n {TU - 1e-9:.12g} 2)",
                    f"vkr{c}{p} kr{c}{p} 0 pulse(1 0 {NEVER} 1n 1n {CYCLE + LEAD:.12g} 2)",
                    f"vkp{c}{p} kp{c}{p} 0 pulse(0 1 {NEVER} 1n 1n {CYCLE:.12g} 2)",
                    f"vts{c}{p} ts{c}{p} 0 dc {NEVER}", f"vamp{c}{p} amp{c}{p} 0 dc 1"]
            nodes += [f"vinit{c}{p} ks{c}{p} kr{c}{p} kp{c}{p} ts{c}{p} amp{c}{p}"]
        top.append(f"x{c} vdd vr0 vfire vreopen vcm vhi vlo vpre gl {' '.join(nodes)} rcell")
    out = [f"* {len(cells)} R cells, pulses at any date (phase 0 of the network experiment, exploratory)", f'.lib "pdk/models/sky130.lib.spice" {section}']
    out += head + [port] + cell + model + supplies + top + [f".option temp={temperature}", "vgl gl 0 dc 0", ".end"]
    text = "\n".join(out) + "\n"
    if junction is None and areas is None and caps is None:
        return text
    spec = importlib.util.spec_from_file_location("stage_j_netlist", CLOSURE / "junction" / "netlist.py")
    netlist = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(netlist)
    one = netlist.read_areas(areas or CLOSURE / "junction" / "areas.csv")
    every = None if junction == "zero" else {f"x{c}.{path}": value for c in cells for path, value in one.items()}
    wires = None
    if caps is not None:                                    # the capacitances of one cell, repeated inside each cell
        local = lambda node, c: node if node in ("0", "vdd", "vr0", "vfire", "vreopen", "vcm", "vhi", "vlo", "vpre") else f"x{c}.{node}"
        wires = [(local(a, c), local(b, c), f) for c in cells for a, b, f in netlist.read_caps(caps)]
    flat, devices = netlist.build(text, (CIRCUIT / "blocks.spice").read_text(), areas=every, zero=junction == "zero", caps=wires)
    assert len(devices) == 232 * len(cells), len(devices)
    return flat


def signals(cells, noise=True):
    out = []
    for c in cells:
        out += [f"v(x{c}.p)", f"v(x{c}.vq)"]
        for p in PORTS:
            out += [f"v(x{c}.vmem{p})", f"v(x{c}.x{p}.sum)", f"v(x{c}.x{p}.si)", f"v(ks{c}{p})", f"v(amp{c}{p})"]
        out += [f"v(x{c}.nzm)"] + [f"v(x{c}.x{p}.{n})" for p in PORTS for n in ("nzo", "nzc")]
    return out + ["v(gl)"]


class Session(sim.Session):
    """One simulator process on a network deck."""

    def __init__(self, folder, text, cells, ngspice, pdk, seed=None, stop_s=0.02, max_step="200n", noise_id=None, shim=None):
        self.cells = tuple(cells)
        self.saved = signals(self.cells)
        self.folder = Path(folder)
        self.folder.mkdir(parents=True, exist_ok=False)
        (self.folder / "pdk").symlink_to(Path(pdk).resolve(), target_is_directory=True)
        shutil.copyfile(CIRCUIT / "spiceinit.txt", self.folder / ".spiceinit")
        (self.folder / "input.spice").write_text(text)
        assert sim.digest(ngspice) == sim.NGSPICE_SHA256, "not the pinned ngspice 42 binary"
        assert subprocess.check_output(["git", "-C", str(Path(pdk).resolve()), "rev-parse", "HEAD"], text=True).strip() == sim.PDK_COMMIT
        env = dict(os.environ, SPICE_SCRIPTS=str(sim.SPINIT.parent))
        if noise_id is not None:          # exploratory only: fixes the process number that seeds the noise
            env.update(LD_PRELOAD=str(shim), FAKEPID=str(noise_id))
        self.log = (self.folder / "session.log").open("w")
        self.p = subprocess.Popen([str(ngspice), "-p", "input.spice"], cwd=self.folder, env=env, stdin=subprocess.PIPE,
                                  stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, bufsize=1)
        self.n, self.started, self.max_step, self.stop_s = 0, False, max_step, stop_s
        self.cmd("set numdgt=16")
        if seed is not None:
            self.cmd(f"setseed {seed}")
            self.cmd("reset")
        self.cmd("save " + " ".join(self.saved))
        self.busy = {(c, p): -1.0 for c in self.cells for p in PORTS}          # date until which the port is in a cycle
        self.now = 0.0

    def run(self, until, watch=()):
        """Go on to date `until`, or to the first time point where the protection latch of a watched cell is high.
        Returns the date reached."""
        self.cmd("delete all")
        self.cmd(f"stop when time >= {until:.12g}")
        for c in watch:
            self.cmd(f"stop when v(x{c}.p) > 0.9")
        if not self.started:
            self.started = True
            self.cmd(f"tran 1u {self.stop_s:.12g} 0 {self.max_step}")
        else:
            self.cmd("resume")
        self.now = self.last("time")
        return self.now

    def last(self, vector):
        out = self.cmd(f"print {vector}[length(time)-1]")
        return float(out.strip().split("=")[-1])

    def protected(self, c):
        return self.last(f"v(x{c}.p)") > 0.9

    def fire_date(self, c, after):
        """Date at which the protection latch of cell c last rose through 0.9 V, after `after`."""
        self.n += 1
        out = self.cmd(f"meas tran f{self.n} when v(x{c}.p)=0.9 rise=last from={after:.12g}")
        return float(out.split("=")[1].split()[0])

    def pulse(self, c, p, date, amp=1):
        """Schedule the next pulse of port p of cell c at `date`. The port must be out of its previous cycle, and the
        run must be stopped early enough for the reset to be released 1 us before the pulse."""
        assert date >= self.busy[(c, p)] and date - LEAD >= self.now + 0.2e-6, (c, p, date, self.busy[(c, p)], self.now)
        self.cmd(f"alter @vks{c}{p}[pulse] = [ 0 1 {date:.12g} 1n 1n {TU - 1e-9:.12g} 2 ]")
        self.cmd(f"alter @vkr{c}{p}[pulse] = [ 1 0 {date - LEAD:.12g} 1n 1n {CYCLE + LEAD:.12g} 2 ]")
        self.cmd(f"alter @vkp{c}{p}[pulse] = [ 0 1 {date:.12g} 1n 1n {CYCLE:.12g} 2 ]")
        self.cmd(f"alter vts{c}{p} dc = {date:.12g}")
        self.cmd(f"alter vamp{c}{p} dc = {amp:.12g}")
        self.busy[(c, p)] = date + CYCLE + 4e-6             # the cycle, then 4 us of precharge before the next one

    def close(self, raw="trace.raw"):
        self.cmd("set filetype=binary")
        self.cmd(f"write {raw} " + " ".join(self.saved))
        self.p.stdin.write("quit\n")
        self.p.stdin.flush()
        try:
            self.p.wait(timeout=60)
        finally:
            self.log.close()
        return self.folder / raw
