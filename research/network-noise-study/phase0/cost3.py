"""Phase 0, feasibility, no claim: the cost of the device model with PWL sources, on three-cell network runs.

  cost3.py runs  WORK OUT.json NGSPICE PDK READS
  cost3.py parse WORK OUT.json NGSPICE PDK MS [MS ...]

`runs`: four network runs of the nominal cell (section tt), three cells a, b, c, four at a time as in the
campaigns. The calendar: each port of each cell READS reads 18 units apart, cell b 6 units after cell a and cell c
12 units after, so that no cell sees two pulses closer than 18 units. Modes:
  quiet       no noise source
  injected    the trnoise sources of campaigns 1 to 3
  pwl10       10 device sources per cell and the 2 shot terms per cell, as PWL sources (noisegen.py)
  pwl46       46 device sources per cell (every analog transistor) and the 2 shot terms per cell, as PWL sources
The amplitudes of the device sources are placeholders (those of op-amp xm3 at the hold point of the nominal cell):
this measures cost, not noise. The words of these runs are not looked at.

`parse`: the pwl46 deck of three cells for a run of MS ms, loaded, solved at its operating point and run for 10 us
only: what the samples alone cost in generation, parse time and memory, for runs as long as a campaign's.
Each value is the wall time and the peak resident memory of the simulator process (from wait4).
"""
import json, math, os, subprocess, sys, time
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


def pwl_sources(text, per_cell, tstop, noise_seed=1):
    model = json.loads((HERE / "MODEL_nominal.json").read_text())
    ref = next(m for m in model["model"] if m["device"] == "xa.x1.xop.xm3")
    nodes = {}
    for line in text.splitlines():
        f = line.split()
        if f and "sky130_fd_pr__" in line:
            nodes[f[0]] = (f[1], f[3])
    names = sorted(d for c in CELLS for d in cost.chosen(c, per_cell))
    n = int(math.ceil(tstop / noisegen.NT)) + 2
    out = []
    for k, d in enumerate(names):
        g = math.sqrt(ref["white_A2_Hz"] / (2 * noisegen.NT)) / 1e-3
        x = noisegen.samples(noise_seed, k, n, ref["white_A2_Hz"] / g ** 2, ref["flicker_B"] / g ** 2, ref["alpha"],
                             slow=(90000, 0))
        out += [noisegen.pwl(f"vnzp{k}", f"nzp{k}", x), f"rnzp{k} nzp{k} 0 1k noisy=0",
                f"gnzp{k} {nodes[d][0]} {nodes[d][1]} nzp{k} 0 {g:.10g}"]
    base = len(names)
    for j, (c, p) in enumerate((c, p) for c in CELLS for p in net.PORTS):       # the declared shot terms, 2qI
        A = 2 * Q * IPK
        g = math.sqrt(A / (2 * noisegen.NT)) / 1e-3
        x = noisegen.samples(noise_seed, base + j, n, A / g ** 2)
        out += [noisegen.pwl(f"vnzs{j}", f"nzs{j}", x), f"rnzs{j} nzs{j} 0 1k noisy=0",
                f"gnzs{j} x{c}.x{p}.dq x{c}.vmem{p} nzs{j} 0 {g:.10g}"]
    return out, len(names) + 6


def _run(work, mode, ngspice, pdk, reads):
    original, info = net.deck, {}
    cal = calendar(reads)
    horizon = router.ORIGIN + cal["horizon"] * net.TU + 50e-6

    def deck(**kw):
        t = original(**kw)
        if mode.startswith("pwl"):
            t0 = time.time()
            lines, info["sources"] = pwl_sources(t, int(mode[3:]), horizon)
            t = t.replace("\n.end\n", "\n" + "\n".join(lines) + "\n.end\n")
            info["generation_s"] = time.time() - t0
            info["deck_MB"] = len(t) / 1e6
        return t
    net.deck = deck
    r = router.run(Path(work) / mode, cal, Path(ngspice), Path(pdk), cells=CELLS, seed=None, section="tt",
                   noise=mode == "injected")
    import resource
    print(json.dumps(dict(mode=mode, sources=info.get("sources", 21 if mode == "injected" else 0), wall_s=r["wall_s"],
                          points=r["points"], simulated_ms=horizon * 1e3, pulses=sum(o["delivered"] for o in r["occurrences"]),
                          generation_s=info.get("generation_s"), deck_MB=info.get("deck_MB"),
                          peak_rss_MB=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss / 1024)))


def runs(work, out, ngspice, pdk, reads):
    modes = ["quiet", "injected", "pwl10", "pwl46"]

    def one(m):
        p = subprocess.run([sys.executable, "-B", __file__, "_run", work, m, ngspice, pdk, str(reads)], capture_output=True, text=True)
        return json.loads(p.stdout.strip().splitlines()[-1]) if p.returncode == 0 else dict(mode=m, error=p.stderr[-3000:])
    with ThreadPoolExecutor(4) as ex:
        res = list(ex.map(one, modes))
    for r in res:
        print(json.dumps(r))
    Path(out).write_text(json.dumps(dict(cells=CELLS, reads=reads, runs=res), indent=1) + "\n")


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
        _run(a[0], a[1], a[2], a[3], int(a[4]))
    elif sys.argv[1] == "runs":
        runs(a[0], a[1], a[2], a[3], int(a[4]))
    elif sys.argv[1] == "parse":
        parse(a[0], a[1], a[2], a[3], [float(x) for x in a[4:]])
