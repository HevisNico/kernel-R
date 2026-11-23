"""One ngspice run of one instance.

Mismatch is the PDK's own (MC_MM_SWITCH = 1 in section `tt_mm`, AGAUSS on each device's parameters), drawn as
research/circuit/run.py's `_mm` sections do: `setseed SEED` then `reset` in the control block, before the analysis.
run.py is a script; its mechanism is reused here, not its code. The ngspice setup (`spiceinit.txt`: hsa behaviour,
skywaterpdk, one thread) and the cell's subcircuits (`blocks.spice`) are read unchanged from research/circuit.
"""
import hashlib, subprocess, time
from pathlib import Path
import numpy as np

CIRCUIT = Path(__file__).resolve().parents[3]          # research/circuit
FINGER = ("v(ibm)", "@m.xcmpm.xm1.msky130_fd_pr__pfet_01v8_lvt[vth]", "@m.xcmpm.xm2.msky130_fd_pr__pfet_01v8_lvt[vth]",
          "@m.xmh1.msky130_fd_pr__nfet_01v8[vth]", "@m.xmj1.msky130_fd_pr__pfet_01v8[vth]")
SAVED = ("v(vq)", "i(vah)", "i(vaj)", "v(p)", "v(cmpm)")


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def run(folder, seed, deck, tstop, maxstep, ngspice="ngspice", timeout=3600):
    """Run `deck` with mismatch sample `seed` (None: no draw) in `folder`. Returns the columns and the run's record."""
    folder = Path(folder)
    folder.mkdir(parents=True, exist_ok=True)
    pdk = folder / "pdk"
    if not pdk.exists():
        pdk.symlink_to(CIRCUIT / "pdk", target_is_directory=True)
    (folder / "blocks.spice").write_text((CIRCUIT / "blocks.spice").read_text())
    (folder / ".spiceinit").write_text((CIRCUIT / "spiceinit.txt").read_text())
    draw = f"setseed {seed}\nreset\n" if seed is not None else ""
    control = (f"\n.control\n{draw}op\necho FINGER {' '.join('$&' + n for n in FINGER)}\n"
               f"set wr_singlescale\nset wr_vecnames\noption numdgt=12\ntran 1n {tstop:.12g} 0 {maxstep}\n"
               f"wrdata trace.txt {' '.join(SAVED)}\nquit\n.endc\n")
    assert deck.endswith("\n.end\n")
    (folder / "input.spice").write_text(deck[: -len(".end\n")] + control.lstrip("\n") + ".end\n")
    t0 = time.time()
    out = subprocess.run([ngspice, "-b", "input.spice"], cwd=folder, capture_output=True, text=True, timeout=timeout)
    wall = time.time() - t0
    log = out.stdout + out.stderr
    (folder / "ngspice.log").write_text(log)
    if out.returncode or not (folder / "trace.txt").exists() or "aborted" in log or "too small" in log:
        raise RuntimeError(f"{folder.name}: ngspice failed\n" + log[-3000:])
    finger = [l.split()[1:] for l in out.stdout.splitlines() if l.startswith("FINGER")]
    data = np.loadtxt(folder / "trace.txt", skiprows=1)
    cols = dict(t=data[:, 0], vq=data[:, 1], ih=data[:, 2], ij=data[:, 3], p=data[:, 4], cmp=data[:, 5])
    rec = dict(files={f: sha(folder / f) for f in ("input.spice", "trace.txt", "ngspice.log")}, wall_s=wall,
               finger=[float(v) for v in finger[0]] if finger else None, points=int(len(data)))
    return cols, rec
