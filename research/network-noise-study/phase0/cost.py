"""Phase 0, feasibility, no claim: what a noise source per device costs in a real network run of the nominal cell.

  cost.py WORK OUT.json MODEL.json NGSPICE PDK [READS]

Four network runs of the nominal cell (section tt, no mismatch seed), two cells, the calendar of
`../../network-circuit/phase1/noisechar.py` with READS reads per port (default 3), run four at a time as in the
campaigns:
  quiet     no noise source;
  injected  the four injected sources per port of every campaign so far (`../../circuit/noise.json`);
  device10  the injected sources removed, 10 device current sources per cell (the 4 of the hold pilot per port,
            and the input pair of the FIRE comparator);
  device46  the injected sources removed, 46 device current sources per cell: every analog transistor (op-amp,
            both comparators, mirror, sensor).
The device sources here are for the cost only: each has the white and flicker amplitude extracted for
xa.x1.xop.xm3 in MODEL.json, not its own. The words and doses of these runs mean nothing and are not looked at.
"""
import json, sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent.parent / "network-circuit"))
sys.path.insert(0, str(HERE.parent.parent / "network-circuit" / "phase1"))
import net, router, noisechar          # noqa: E402
import pilot                           # noqa: E402

OPAMP = [f"xop.{d}" for d in ("xm1", "xm2", "xm3", "xm4", "xm5", "xm6", "xmb", "xmt")]
WINDOW = [f"xcmps.{d}" for d in ("xm1", "xm2", "xm3", "xm4", "xm5", "xm6")]
PORT_OTHER = ["xmin", "xmout", "xmdis", "xmbd", "xmpre"]
FIRE = [f"xcmpm.{d}" for d in ("xm1", "xm2", "xm3", "xm4", "xm5", "xm6", "xmb", "xmt")]


def chosen(c, n):
    if n == 10:
        return [f"x{c}.x{p}.xop.{d}" for p in (1, 2) for d in ("xm1", "xm2", "xm3", "xm4")] + [f"x{c}.xcmpm.xm1", f"x{c}.xcmpm.xm2"]
    return [f"x{c}.x{p}.{d}" for p in (1, 2) for d in OPAMP + WINDOW + PORT_OTHER] + [f"x{c}.{d}" for d in FIRE]


def with_sources(text, cells, n, ref):
    devs = {}
    for line in text.splitlines():
        f = line.split()
        if f and "sky130_fd_pr__" in line:
            devs[f[0]] = (f[1], f[3])
    model = dict(model=[dict(ref, nodes=list(devs[d])) for c in cells for d in chosen(c, n)])
    return text.replace("\n.end\n", "\n" + "\n".join(pilot.device_sources(model)) + "\n.end\n"), len(model["model"])


def run_mode(args):
    work, mode, model_path, ngspice, pdk, reads = args
    import subprocess
    p = subprocess.run([sys.executable, "-B", __file__, "_one", str(work), mode, model_path, ngspice, pdk, str(reads)],
                       capture_output=True, text=True)
    return json.loads(p.stdout.strip().splitlines()[-1]) if p.returncode == 0 else dict(mode=mode, error=p.stderr[-2000:])


def _one(work, mode, model_path, ngspice, pdk, reads):
    model = json.loads(Path(model_path).read_text())
    ref = next(m for m in model["model"] if m["device"] == "xa.x1.xop.xm3")
    original, info = net.deck, {}

    def deck(**kw):
        t = original(**kw)
        if mode.startswith("device"):
            t, info["sources"] = with_sources(t, kw.get("cells", ("a", "b")), int(mode[6:]), ref)
        return t
    net.deck = deck
    cal = noisechar.calendar(reads)
    r = router.run(Path(work) / mode, cal, Path(ngspice), Path(pdk), seed=None, section="tt", noise=mode == "injected")
    sim_ms = (r["origin_s"] + cal["horizon"] * net.TU) * 1e3
    print(json.dumps(dict(mode=mode, sources=info.get("sources", 14 if mode == "injected" else 0),
                          wall_s=r["wall_s"], points=r["points"], simulated_ms=sim_ms,
                          pulses=sum(o["delivered"] for o in r["occurrences"]))))


if __name__ == "__main__":
    if sys.argv[1] == "_one":
        _one(*sys.argv[2:7], int(sys.argv[7]))
    else:
        work, out, model_path, ngspice, pdk = sys.argv[1:6]
        reads = int(sys.argv[6]) if len(sys.argv) > 6 else 3
        modes = ["quiet", "injected", "device10", "device46"]
        with ThreadPoolExecutor(4) as ex:
            res = list(ex.map(run_mode, [(work, m, model_path, ngspice, pdk, reads) for m in modes]))
        for r in res:
            print(json.dumps(r))
        Path(out).write_text(json.dumps(dict(reads=reads, runs=res), indent=1) + "\n")
