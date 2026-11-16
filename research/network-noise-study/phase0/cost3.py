"""Phase 0, feasibility, no claim: the cost of the device model with PWL sources, on three-cell network runs.

  cost3.py runs  WORK OUT.json NGSPICE PDK READS
  cost3.py parse WORK OUT.json NGSPICE PDK MS [MS ...]
  cost3.py dnf   WORK OUT.json NGSPICE PDK DNF_PATH NEED campaign 4's run (dnf.calendar(NEED x 4)), quiet / injected / the model's
                                                          devices (pwlmodel) / every analog transistor (pwl46)

`runs`: four network runs of the nominal cell (section tt), three cells a, b, c, four at a time as in the
campaigns. The calendar: each port of each cell READS reads 18 units apart, cell b 6 units after cell a and cell c
12 units after, so that no cell sees two pulses closer than 18 units. Modes:
  quiet       no noise source
  injected    the trnoise sources of campaigns 1 to 3
  pwl10       10 device sources per cell and the 2 shot terms per cell, as PWL sources (noisegen.py)
  pwl46       46 device sources per cell (every analog transistor) and the 2 shot terms per cell, as PWL sources
The amplitudes of the device sources are placeholders (those of op-amp xm3 at the hold point of the nominal cell):
this measures cost, not noise. The words of these runs are not looked at.

  fsmodel / fs46 / fszero   the same sources as XSPICE filesource instances (groups of 8 columns, xtrtol=7);
              fszero: the model's sources present with every amplitude at zero, against `quiet` (zerocheck.py)

`parse`: the pwl46 deck of three cells for a run of MS ms, loaded, solved at its operating point and run for 10 us
only: what the samples alone cost in generation, parse time and memory, for runs as long as a campaign's.
Each value is the wall time and the peak resident memory of the simulator process (from wait4).
"""
import json, math, os, subprocess, sys, time
import numpy as np
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent.parent / "network-circuit"))
sys.path.insert(0, str(HERE))
import net, router                     # noqa: E402
import noisegen, cost                  # noqa: E402

CELLS = ("a", "b", "c")
Q, IPK = 1.602176634e-19, 5e-12 * 0.5 * math.log(4) / 20e-6       # the peak of bip, from the parameters of cell.spice


def calendar(reads):
    src = []
    for i, port in enumerate((1, 2)):
        for k in range(reads):
            for j, c in enumerate(CELLS):
                src.append((18 * (i * reads + k) + 6 * j, c, port))
    return dict(name=f"three cells, each port {reads} reads 18 units apart", sources=sorted(src), edges=[],
                horizon=18 * 2 * reads + 12)


def dnf_calendar(dnf_path, need=4):
    """Campaign 4's network run, need 4 everywhere (`dnf.calendar(4, 4, 4, 4)` of research/learned-dnf-circuit, read
    from DNF_PATH, a copy of that file: code, no data), as a calendar of the router: the external inputs as sources,
    the routed lines as edges from a and b to the ports of c, open over the decision window of each routed slot.
    An emulation for the cost only: every input at amplitude 1 (not 0.49 on layer 1) and no read-only gate."""
    import importlib.util
    spec = importlib.util.spec_from_file_location("dnf", dnf_path)
    dnf = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(dnf)
    slots = dnf.calendar(need, need, need, need)
    src, edges = [], []
    for s in slots:
        for n, off in s["inputs"].items():
            c, p = dnf.INPUTS[n]
            src.append((s["date"] + off, c, p))
        if s["routed"]:
            for line, (c, p) in dnf.LINES.items():
                edges.append(dict(name=f"{line}->{c}{p}@{s['date']}", source=line, gate=[s["date"], s["date"] + dnf.WINDOW],
                                  delay=dnf.WIRE, cell=c, port=p))
    return dict(name=f"campaign 4, need {need} (emulated)", sources=sorted(src), edges=edges,
                horizon=slots[-1]["date"] + dnf.SLOT + dnf.SETTLE)


CODEMODEL = "/usr/lib/x86_64-linux-gnu/ngspice/analog.cm"     # XSPICE analog code models of the ngspice 42 package
# With any XSPICE 'A' device in the circuit ngspice lowers trtol, for the whole circuit, from its default 7 to 1
# ("Reducing trtol to 1 for xspice 'A' devices"): a different time-step control, under which the network deck stops
# with "timestep too small" at 1 us even with every source at zero. xtrtol keeps the default of the other runs.
XTRTOL = os.environ.get("XTRTOL", "7")
MODEL_DEVICES = None        # set by --model: the union of the kept devices of EXTRACT_nominal.json, per cell


def chosen_model(c):
    return [d.replace("xa.", f"x{c}.", 1) for d in MODEL_DEVICES]


FS_GROUP = 8      # columns per filesource: one file of 76 columns (lines of ~1 100 characters) stops the deck at 1 us


def filesource(name, columns, path, scale="1"):
    """The samples of the sources as XSPICE `filesource` instances (analog.cm), each reading its own text file
    sequentially: one row per sample time, FS_GROUP sources per file, linear between samples. Their outputs are the
    nodes nzp<k>. One file for every source fails: the deck stops ("timestep too small") at 1 us even with every
    amplitude at zero, while one column works (phase 0); hence the groups."""
    n = len(columns[0])
    t = np.arange(n) * noisegen.NT
    out = []
    for g in range(0, len(columns), FS_GROUP):
        cols = columns[g:g + FS_GROUP]
        f = Path(f"{path}.{g // FS_GROUP}")
        np.savetxt(f, np.column_stack([t] + list(cols)), fmt="%.9g")
        nodes = " ".join(f"%v(nzp{g + k})" for k in range(len(cols)))
        ones, zeros = " ".join([scale] * len(cols)), " ".join(["0"] * len(cols))
        out += [f"a{name}{g // FS_GROUP} [{nodes}] fs{name}{g // FS_GROUP}",
                f'.model fs{name}{g // FS_GROUP} filesource (file="{f}" amploffset=[{zeros}] amplscale=[{ones}] '
                f"timeoffset=0 timescale=1 timerelative=false amplstep=false)"]
    return out


def pwl_sources(text, per_cell, tstop, noise_seed=1, kind="pwl", fs_path=None, fs_scale="1"):
    model = json.loads((HERE / "MODEL_nominal.json").read_text())
    ref = next(m for m in model["model"] if m["device"] == "xa.x1.xop.xm3")
    nodes = {}
    for line in text.splitlines():
        f = line.split()
        if f and "sky130_fd_pr__" in line:
            nodes[f[0]] = (f[1], f[3])
    names = sorted(d for c in CELLS for d in (chosen_model(c) if per_cell == 0 else cost.chosen(c, per_cell)))
    n = int(math.ceil(tstop / noisegen.NT)) + 2
    out, cols, gains = [], [], []
    for k, d in enumerate(names):
        g = math.sqrt(ref["white_A2_Hz"] / (2 * noisegen.NT)) / 1e-3
        cols.append(noisegen.samples(noise_seed, k, n, ref["white_A2_Hz"] / g ** 2, ref["flicker_B"] / g ** 2, ref["alpha"],
                                     slow=(90000, 0)))
        gains.append((nodes[d][0], nodes[d][1], g))
    base = len(names)
    for j, (c, p) in enumerate((c, p) for c in CELLS for p in net.PORTS):       # the declared shot terms, 2qI
        A = 2 * Q * IPK
        g = math.sqrt(A / (2 * noisegen.NT)) / 1e-3
        cols.append(noisegen.samples(noise_seed, base + j, n, A / g ** 2))
        gains.append((f"x{c}.x{p}.dq", f"x{c}.vmem{p}", g))
    for k, (a, b, g) in enumerate(gains):
        if kind == "pwl":
            out.append(noisegen.pwl(f"vnzp{k}", f"nzp{k}", cols[k]))
        out += [f"rnzp{k} nzp{k} 0 1k noisy=0", f"gnzp{k} {a} {b} nzp{k} 0 {g:.10g}"]
    if kind == "fs":
        out += filesource("nz", cols, fs_path, fs_scale)
    return out, len(gains)


def _run(work, mode, ngspice, pdk, reads, dnf_path=None):
    """`reads` is the need of the campaign-4 calendar when dnf_path is given."""
    global MODEL_DEVICES
    original, info = net.deck, {}
    cal = dnf_calendar(dnf_path, reads) if dnf_path else calendar(reads)
    if mode in ("pwlmodel", "fsmodel", "fszero"):      # the union of the kept devices of the devnoise extraction, per cell
        ex = json.loads((HERE / "DEVNOISE_nominal.json").read_text())
        MODEL_DEVICES = sorted({k["device"] for o in ex["outputs"] if o["state"] != "preset" and o["cell"] == "a"
                                for k in o["kept"] if k["kind"] != "res"})
    horizon = router.ORIGIN + cal["horizon"] * net.TU + 50e-6

    def deck(**kw):
        t = original(**kw)
        if mode.startswith(("pwl", "fs")):
            t0 = time.time()
            kind = mode[:3] if mode.startswith("pwl") else "fs"
            per_cell = 0 if mode.endswith(("model", "zero")) else int(mode[len(kind):])
            fs_path = (Path(work) / f"{mode}.samples.txt").resolve()
            fs_path.parent.mkdir(parents=True, exist_ok=True)
            lines, info["sources"] = pwl_sources(t, per_cell, horizon, kind=kind, fs_path=fs_path,
                                                 fs_scale="0" if mode == "fszero" else "1")
            t = t.replace("\n.end\n", "\n" + "\n".join(lines) + "\n.end\n")
            info["generation_s"] = time.time() - t0
            info["deck_MB"] = len(t) / 1e6
            info["samples_file_MB"] = (sum(f.stat().st_size for f in fs_path.parent.glob(fs_path.name + ".*")) / 1e6
                                       if kind == "fs" else None)
        return t
    net.deck = deck
    if mode.startswith("fs"):            # the code model is loaded at start-up, before the deck, as ngspice requires
        import shutil
        copy = shutil.copyfile

        def with_codemodel(src, dst, *a, **k):
            r = copy(src, dst, *a, **k)
            if Path(dst).name == ".spiceinit":
                with open(dst, "a") as f:
                    f.write(f"codemodel {CODEMODEL}\nset xtrtol={XTRTOL}\n")
            return r
        net.shutil.copyfile = with_codemodel
    r = router.run(Path(work) / mode, cal, Path(ngspice), Path(pdk), cells=CELLS, seed=None, section="tt",
                   noise=mode == "injected")
    import resource
    print(json.dumps(dict(mode=mode, sources=info.get("sources", 21 if mode == "injected" else 0), wall_s=r["wall_s"],
                          points=r["points"], simulated_ms=horizon * 1e3, pulses=sum(o["delivered"] for o in r["occurrences"]),
                          generation_s=info.get("generation_s"), deck_MB=info.get("deck_MB"),
                          samples_file_MB=info.get("samples_file_MB"),
                          peak_rss_MB=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss / 1024)))


def runs(work, out, ngspice, pdk, reads, dnf_path=None, modes=("quiet", "injected", "pwl10", "pwl46")):

    def one(m):
        p = subprocess.run([sys.executable, "-B", __file__, "_run", work, m, ngspice, pdk, str(reads)] + ([dnf_path] if dnf_path else []),
                           capture_output=True, text=True)
        if p.returncode != 0:
            print(f"{m} failed:\n{p.stderr[-3000:]}", file=sys.stderr, flush=True)
            return dict(mode=m, error=p.stderr[-3000:])
        r = json.loads(p.stdout.strip().splitlines()[-1])
        print(json.dumps(r), file=sys.stderr, flush=True)
        return r
    with ThreadPoolExecutor(4) as ex:
        res = list(ex.map(one, modes))
    for r in res:
        print(json.dumps(r))
    Path(out).write_text(json.dumps(dict(cells=CELLS, reads=reads, calendar=f"dnf need {reads}" if dnf_path else "reads", runs=res), indent=1) + "\n")


def parse(work, out, ngspice, pdk, lengths):
    import pilot
    res = []
    for ms in lengths:
        t0 = time.time()
        text = net.deck(cells=CELLS, section="tt")
        lines, ns = pwl_sources(text, 46, ms * 1e-3)
        text = text.replace("\n.end\n", "\n" + "\n".join(lines) + "\n.end\n")
        gen = time.time() - t0
        w = Path(work) / f"parse{ms:g}"
        w.mkdir(parents=True)
        (w / "pdk").symlink_to(Path(pdk).resolve(), target_is_directory=True)
        import shutil
        shutil.copyfile(HERE.parent.parent / "circuit" / "spiceinit.txt", w / ".spiceinit")
        (w / "deck.spice").write_text(text.replace("\n.end\n", "\n.control\nop\ntran 0.4u 10u 0 200n\nquit\n.endc\n.end\n"))
        env = dict(os.environ, SPICE_SCRIPTS=str(pilot.sim.SPINIT.parent))
        t1 = time.time()
        p = subprocess.Popen([ngspice, "-b", "deck.spice"], cwd=w, env=env, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        _, status, ru = os.wait4(p.pid, 0)
        r = dict(ms=ms, sources=ns, samples_per_source=int(ms * 1e-3 / noisegen.NT), deck_MB=len(text) / 1e6,
                 generation_s=gen, simulator_wall_s=time.time() - t1, peak_rss_MB=ru.ru_maxrss / 1024, status=status)
        print(json.dumps(r), flush=True)
        res.append(r)
    Path(out).write_text(json.dumps(dict(cells=CELLS, runs=res), indent=1) + "\n")


if __name__ == "__main__":
    a = sys.argv[2:]
    if sys.argv[1] == "_run":
        _run(a[0], a[1], a[2], a[3], int(a[4]), *(a[5:6] or [None]))
    elif sys.argv[1] == "runs":
        runs(a[0], a[1], a[2], a[3], int(a[4]))
    elif sys.argv[1] == "dnf":                 # cost3.py dnf WORK OUT.json NGSPICE PDK DNF_PATH NEED
        runs(a[0], a[1], a[2], a[3], int(a[5]), a[4], tuple(a[6:]) or ("quiet", "injected", "pwlmodel", "pwl46"))
    elif sys.argv[1] == "parse":
        parse(a[0], a[1], a[2], a[3], [float(x) for x in a[4:]])
