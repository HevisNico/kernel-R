"""One ngspice 42 process driven through a pipe (method of research/sky130-supervisor-closure/sim.py, own code).

Run to a date or to the first FIRE of a watched cell, measure a latch crossing, set a source, go on.
"""
import hashlib
import os
from pathlib import Path
import shutil
import subprocess

HERE = Path(__file__).resolve().parent
FATAL = ("aborted", "timestep too small", "transient op failed", "fatal error", "singular matrix")


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def prepare(folder, text, cfg):
    c = cfg["circuit"]
    folder = Path(folder)
    folder.mkdir(parents=True, exist_ok=True)
    pdk = (HERE / c["pdk"]).resolve()
    if not (folder / "pdk").exists():
        (folder / "pdk").symlink_to(pdk, target_is_directory=True)
    shutil.copyfile(HERE / c["blocks_spice"], folder / "blocks.spice")
    shutil.copyfile(HERE / c["spiceinit"], folder / ".spiceinit")
    (folder / "input.spice").write_text(text)
    ng = shutil.which("ngspice")
    assert ng and sha256(ng) == c["ngspice_sha256"], "not the pinned ngspice 42 binary"
    head = subprocess.check_output(["git", "-C", str(pdk), "rev-parse", "HEAD"], text=True).strip()
    assert head == c["pdk_commit"], "not the pinned SKY130 model commit"
    return folder, ng


def count_nodes(folder, cfg):
    """Distinct circuit nodes of the expanded deck, from an operating point with every vector kept."""
    folder = Path(folder)
    deck = (folder / "input.spice").read_text().replace("\n.end\n", "\n.control\nop\ndisplay\nquit\n.endc\n.end\n")
    (folder / "size.spice").write_text(deck)
    out = subprocess.run(["ngspice", "-b", "size.spice"], cwd=folder, capture_output=True, text=True, timeout=600).stdout
    volts = [l for l in out.splitlines() if ": voltage" in l]
    (folder / "size.spice").unlink()
    return len(volts)


class Session:
    def __init__(self, folder, text, cfg, seed=None, stop_s=1.0):
        self.folder, ng = prepare(folder, text, cfg)
        self.log = (self.folder / "session.log").open("w")
        self.p = subprocess.Popen([ng, "-p", "input.spice"], cwd=self.folder, stdin=subprocess.PIPE,
                                  stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, bufsize=1)
        self.n, self.started, self.stop_s = 0, False, stop_s
        self.max_step = cfg["circuit"]["max_step"]
        self.now = 0.0
        self.cmd("set numdgt=16")
        if seed is not None:
            self.cmd(f"setseed {seed}")
            self.cmd("reset")

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
        if any(t in low for t in FATAL):
            self.log.flush()
            raise RuntimeError("fatal simulator message during: " + line + "\n" + text[-2000:])
        return text

    def run(self, until, watch=()):
        """Go on to `until`, or to the first time point where a watched latch node is above 0.9 V."""
        self.cmd("delete all")
        self.cmd(f"stop when time >= {until:.12g}")
        for node in watch:
            self.cmd(f"stop when v({node}) > 0.9")
        if not self.started:
            self.started = True
            self.cmd("save " + " ".join(f"v({x})" for x in self.saved))
            self.cmd(f"tran 1u {self.stop_s:.12g} 0 {self.max_step}")
        else:
            self.cmd("resume")
        self.now = self.last("time")
        return self.now

    def last(self, vector):
        out = self.cmd(f"print {vector}[length(time)-1]")
        return float(out.strip().split("=")[-1])

    def rise(self, node, after, k=1):
        """Date of the k-th rise of a node through 0.9 V after `after`, or None (printed with 16 digits)."""
        self.n += 1
        name = f"r{self.n}"
        out = self.cmd(f"meas tran {name} when v({node})=0.9 rise={k} from={after:.12g}")
        if "failed" in out.lower() or "out of interval" in out.lower():
            return None
        got = self.cmd(f"print {name}")
        try:
            return float(got.strip().split("=")[-1])
        except ValueError:
            return None

    def alter_pulse(self, source, values):
        self.cmd(f"alter @{source}[pulse] = [ {' '.join(f'{v:.12g}' if isinstance(v, float) else str(v) for v in values)} ]")

    def alter_dc(self, source, value):
        self.cmd(f"alter {source} dc = {value:.12g}")

    def close(self):
        try:
            self.p.stdin.write("quit\n")
            self.p.stdin.flush()
            self.p.wait(timeout=60)
        except Exception:
            self.p.kill()
        finally:
            self.log.close()
