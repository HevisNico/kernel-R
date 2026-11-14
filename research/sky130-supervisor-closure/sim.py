"""The two-port cell driven slot by slot: deck and interactive simulator session.

Qualification tool of phase 1. It is not a registered runner and launches no registered campaign.

The transistor circuit of `../circuit/cell.spice` is not changed. Only its ideal stimulus is:
each port gets a selection node `sel` (its clocks run in a slot only while `sel` is high) and an
amplitude node `amp` (1: an ordinary read pulse; 0: a clock-only cycle with no admitted input
current); the imposed leak of each integrator becomes a conductance set by the node `gl`, so
that its value can be changed while the run is stopped. The global clocks repeat every 220 us:
one service period of 440 us is a maintenance slot followed by a read slot.

With `ammeter=True` a source of 0 V also measures the write current of each port, as in
`../sky130-supervisor-map/probe.py`. The first qualification runs had it. No bound uses that
current, and with noise it makes the solver abort at the SF corner ("timestep too small" on the
current of that source, 12 sessions out of 12; none out of 3 without it): the deck without it is
the one to use, and the circuit is then the original one up to the stimulus.

With `junction="areas"` the sub-circuits are expanded in place and every transistor receives the
source and drain areas of `junction/areas.csv`, by `junction/netlist.py`: the construction of
stage J of the layout study, copied unchanged (see JUNCTION_AREAS.md). Without them the device
model has no junction capacitance and a junction current that ignores temperature.
`junction="zero"` expands the same way with all areas at zero: the identity test.
"""
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess

HERE = Path(__file__).resolve().parent
CIRCUIT = HERE.parent / "circuit"
SLOT = 220e-6
PERIOD = 2 * SLOT
T0 = 4.1e-6                     # start of the pulse in its slot
TU = 20e-6                      # one time unit: the length of a pulse
NGSPICE_SHA256 = "820658317b0b54035208da41936fd6871ce924036e5ea4113a4168b821b7fc45"
PDK_COMMIT = "1232782c1b9fab3aacda74d67ce7c92bf7da8105"
SPINIT = HERE / "runtime" / "spinit"      # committed start file: one thread
GATE = "((time >= {ta} && time < {tb}) || time >= {tj})"
SIGNALS = ["v(vq)", "v(p)", "v(vmem1)", "v(vmem2)", "v(x1.sum)", "v(x2.sum)", "v(x1.si)", "v(x2.si)",
           "v(x1.a)", "v(x1.b)", "v(x2.a)", "v(x2.b)", "i(v.x1.vdose)", "i(v.x2.vdose)",
           "v(nzm)", "v(x1.nzo)", "v(x2.nzo)", "v(x1.nzi)", "v(x2.nzi)", "v(x1.nzc)", "v(x2.nzc)",
           "v(sel1)", "v(sel2)", "v(amp1)", "v(amp2)", "v(gl)"]


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def swap(text, old, new, count=1):
    assert text.count(old) == count, (old, text.count(old))
    return text.replace(old, new)


def expanded(text, zero):
    """The deck with its sub-circuits expanded and the junction areas of stage J on each transistor (or zeros)."""
    spec = importlib.util.spec_from_file_location("stage_j_netlist", HERE / "junction" / "netlist.py")
    netlist = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(netlist)
    areas = None if zero else netlist.read_areas(HERE / "junction" / "areas.csv")
    out, devices = netlist.build(text, (CIRCUIT / "blocks.spice").read_text(), areas=areas, zero=zero)
    assert len(devices) == 232, len(devices)
    return out


def deck(section="tt", temperature=27, noise=False, vinit1=0.3895, vinit2=0.3895, leak_S=0.0, ammeter=False, junction=None):
    """Netlist text of the cell with the slot-by-slot stimulus. No analysis command: the session issues them."""
    text = (CIRCUIT / "cell.spice").read_text()
    text = swap(text, ".global ksen krst kpreb", ".global ksen krst kpreb")
    text = swap(text, ".subckt rport vq vr0 pb vmem vdd vcm vhi vlo vpre vinit ta=0 tb=1 tj=2",
                ".subckt rport vq vr0 pb vmem vdd vcm vhi vlo vpre vinit sel amp gl")
    text = swap(text, GATE, "(v(sel) > 0.5)", 4)
    text = swap(text, "({ipk}*exp(", "(v(amp)*{ipk}*exp(")
    text = swap(text, "rlk sum 0 {rlk}", "bleak sum 0 i = v(sum)*v(gl)")
    if ammeter:
        text = swap(text, "xmsi x si sum 0", "vdose writefeed sum 0\nxmsi x si writefeed 0")
    for port in (1, 2):
        old = next(l for l in text.splitlines() if l.startswith(f"x{port} "))
        assert old.startswith(f"x{port} vq vr0 pb vmem{port} vdd vcm vhi vlo vpre vinit rport")
        text = swap(text, old, f"x{port} vq vr0 pb vmem{port} vdd vcm vhi vlo vpre vinit{port} sel{port} amp{port} gl rport")
    if noise:
        params = json.loads((CIRCUIT / "noise.json").read_text())["params"]
        for node, white, flicker in (("nzc", params["vncw"], params["vncf"]), ("nzo", params["vnow"], params["vnof"]),
                                    ("nzi", params["inmw"], 0), ("nzm", params["vnmw"], params["vnmf"])):
            old = f"vnz{node[2]} {node} 0 dc 0"
            text = swap(text, old, f"{old} trnoise({white:.16g} {params['tnz']:.16g} {1 if flicker else 0} {flicker:.16g})")
    lines = ["* Supervised two-port cell, slot-by-slot stimulus (phase-1 qualification)", f'.lib "pdk/models/sky130.lib.spice" {section}']
    lines += text.splitlines()[1:-1]
    lines += [f".param tper={SLOT:.12g}", f".option temp={temperature}",
              f"vinit1 vinit1 0 {vinit1:.12g}", f"vinit2 vinit2 0 {vinit2:.12g}",
              "vsel1 sel1 0 dc 0", "vsel2 sel2 0 dc 0", "vamp1 amp1 0 dc 0", "vamp2 amp2 0 dc 0",
              f"vgl gl 0 dc {leak_S:.12g}", ".end"]
    text = "\n".join(lines) + "\n"
    assert junction in (None, "areas", "zero")
    return text if junction is None else expanded(text, junction == "zero")


class Session:
    """One ngspice process driven through a pipe: run to a date, read means, change the controls, go on."""

    def __init__(self, folder, text, ngspice, pdk, seed=None, max_step="200n", stop_s=None, noise_id=None, shim=None):
        self.folder = Path(folder)
        self.folder.mkdir(parents=True, exist_ok=False)
        (self.folder / "pdk").symlink_to(Path(pdk).resolve(), target_is_directory=True)
        shutil.copyfile(CIRCUIT / "blocks.spice", self.folder / "blocks.spice")
        shutil.copyfile(CIRCUIT / "spiceinit.txt", self.folder / ".spiceinit")
        (self.folder / "input.spice").write_text(text)
        assert digest(ngspice) == NGSPICE_SHA256, "not the pinned ngspice 42 binary"
        assert subprocess.check_output(["git", "-C", str(Path(pdk).resolve()), "rev-parse", "HEAD"], text=True).strip() == PDK_COMMIT
        env = dict(os.environ, SPICE_SCRIPTS=str(SPINIT.parent))
        if noise_id is not None:          # exploratory only: fixes the process id that seeds the noise (see ../circuit/repetition, PR 115)
            env.update(LD_PRELOAD=str(shim), FAKEPID=str(noise_id))
        self.log = (self.folder / "session.log").open("w")
        self.p = subprocess.Popen([str(ngspice), "-p", "input.spice"], cwd=self.folder, env=env, stdin=subprocess.PIPE,
                                  stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, bufsize=1)
        self.n = 0
        self.started = False
        self.max_step, self.stop_s = max_step, stop_s
        self.signals = [s for s in SIGNALS if "vdose" not in s or "\nvdose " in text]
        self.cmd("set numdgt=16")
        if seed is not None:
            self.cmd(f"setseed {seed}")
            self.cmd("reset")
        self.cmd("save " + " ".join(self.signals))

    def cmd(self, line):
        self.n += 1
        mark = f"MARK{self.n}DONE"
        self.p.stdin.write(line + "\n" + f"echo {mark}\n")
        self.p.stdin.flush()
        out = []
        while True:
            got = self.p.stdout.readline()
            if not got:
                self.log.write("".join(out))
                self.log.flush()
                raise RuntimeError("the simulator ended during: " + line)
            if mark in got:
                break
            out.append(got)
        text = "".join(out)
        self.log.write(f">>> {line}\n{text}")
        self.log.flush()
        low = text.lower()
        if any(token in low for token in ("aborted", "timestep too small", "transient op failed", "fatal error")):
            raise RuntimeError("fatal simulator message during: " + line)
        return text

    def run_to(self, t):
        """Advance to the first solver point at or after date t."""
        self.cmd("delete all")
        self.cmd(f"stop when time >= {t:.12g}")
        if not self.started:
            self.started = True
            self.cmd(f"tran 1u {self.stop_s:.12g} 0 {self.max_step}")
        else:
            self.cmd("resume")

    def finish(self):
        self.cmd("delete all")
        self.cmd("resume" if self.started else f"tran 1u {self.stop_s:.12g} 0 {self.max_step}")

    def mean(self, signal, lo, hi):
        """Time-weighted mean of a signal between two dates, as the `meas` command of the simulator gives it."""
        self.n += 1
        name = f"m{self.n}"
        self.cmd(f"meas tran {name} avg {signal} from={lo:.12g} to={hi:.12g}")
        out = self.cmd(f"print {name}")
        return float(out.strip().split("=")[-1])

    def set(self, source, value):
        self.cmd(f"alter {source} dc = {value:.12g}")

    def close(self, raw="trace.raw"):
        self.cmd("set filetype=binary")
        self.cmd(f"write {raw} " + " ".join(self.signals))
        self.p.stdin.write("quit\n")
        self.p.stdin.flush()
        try:
            self.p.wait(timeout=60)
        finally:
            self.log.close()
        return self.folder / raw

    def kill(self):
        try:
            self.p.kill()
        finally:
            self.log.close()
