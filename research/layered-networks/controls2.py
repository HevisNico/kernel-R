"""Stage-N controls of the campaign plan (CAMPAIGN_PLAN_DRAFT.md §6): the skew slots (S) and the untrained run (U).
Development only. New file: instrument.py, run.py and noise2.py are imported, not changed.

S, skew. After the 2^m test slots of a stage-N run, one slot per both cell (spec order): all gates closed
(read-only), both ports pulsed at the gate's amplitude, port 2 arriving `shift_tu` = 2 tu after port 1 (campaigns 4 to
6: "the second input 2 units late", research/learned-dnf-circuit/dnf.py `control == "skew"`), nothing routed past the
cell. Slot record: kind "skew", info {cell, layer, index, shift_tu, late_port}, one read. S holds iff its emission is
null. The record lists the skew slots in "skews", as it lists the tests in "tests".

U, untrained. A fresh session of the same deck and seed, the 2^m test slots only, from the preset, with no lesson and
every R cell gated: OUT/untrained_record.json, with "control": "U". U holds iff no R-cell read of any test slot has an
emission. The inverters fire on absent inputs, which is expected and reported.

  controls2.py stagen SPEC OUT SEED ROUND [scale=1] [overlay=FILE] [positive=1]   training, tests, skews (ROUND 0:
                                no noise); positive=1 (development only) adds, after the skews, the same slots with
                                shift 0 (kind "skew_check", counted for nothing): a trained both cell must FIRE there
  controls2.py untrained SPEC OUT SEED [overlay=FILE]
  controls2.py verdicts DIR                                         S and U verdicts of the records in DIR

Every run writes OUT/trace.raw at its end (ngspice `write`, the saved vectors over the whole session) and its
digests OUT/trace.digest.json.
"""
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import instrument  # noqa: E402
import noise2  # noqa: E402
import run as runmod  # noqa: E402
import spec as specmod  # noqa: E402

SHIFT_TU = F(2)


def both_cells(s):
    return [(k, i) for k, nodes in enumerate(s["layers"], start=1) for i, n in enumerate(nodes) if n["gate"] == "both"]


def skew_slot(net, s, k, i, shift_tu=SHIFT_TU):
    cal, tim, st = net.cfg["calendar"], net.tim, net.cfg["stimulus"]
    c = f"c{k}_{i}"
    T = net.next_T
    net.next_T = net.snap(T + net.slot_ns)
    net.ses.run((T - net.ns(cal["gate_lead_tu"])) * 1e-9)
    net.set_gates(set())                                    # every port read-only; measures u
    start = T + net.ns(tim["offset"][k])
    a1 = T + net.ns(tim["offset"][k - 1]) + net.delta       # as a routed pulse from layer k - 1 at its read start
    a2 = a1 + net.ns(shift_tu)
    amp = st["amp"][s["layers"][k - 1][i]["gate"]]
    net.pulse(c, 1, a1, amp)
    net.pulse(c, 2, a2, amp)
    end = (T + net.ns(cal["watch_tu"])) * 1e-9
    node = f"x{c}.p"
    latch = emission = None
    t = net.ses.run(end, [node])
    if t < end - 1e-12 and net.ses.last(f"v({node})") > 0.9:
        lt = net.ses.rise(node, (a1 - 1000) * 1e-9)
        latch = round(lt * 1e9)
        emission = net.snap(latch + net.delta) - net.delta
    rec = dict(kind="skew", T=T, info=dict(cell=c, layer=k, index=i, shift_tu=str(shift_tu), late_port=2),
               lines=[None] * s["lines"], inv=[],
               reads=[dict(layer=k, index=i, start=start, arrivals=[a1, a2], latch=latch, emission=emission, second=None)],
               u=net.last_u)
    net.slots.append(rec)
    return rec


def write_trace(net):
    """The simulator's trace of the whole session, the saved vectors over every time point, as ngspice writes it
    (OUT/trace.raw): the duplicate check compares it byte for byte, its `Date:` header line excluded, as campaign (a)
    compared trace.raw."""
    try:
        net.ses.cmd("write trace.raw")
    except Exception as e:                                  # reported by the duplicate check as a missing file
        print(f"trace.raw not written: {e}")
        return
    digest(net.ses.folder / "trace.raw")


def digest(path):
    """trace.digest.json beside trace.raw: sha256 of the text header without its Date: line, sha256 of the data after
    the header, and the Date: line itself. A trace of an XOR3 run is about 1.7 GB: the digests let the duplicate check
    run after the raw files are removed (tests/check_duplicate.py uses the raw files when both are present)."""
    path = Path(path)
    hh, hd, date, size = hashlib.sha256(), hashlib.sha256(), None, 0
    with path.open("rb") as f:
        while True:
            line = f.readline()
            if not line:
                break
            size += len(line)
            if line.startswith(b"Date:"):
                date = line.decode(errors="replace").strip()
            else:
                hh.update(line)
            if line in (b"Binary:\n", b"Values:\n"):
                break
        while True:
            chunk = f.read(1 << 20)
            if not chunk:
                break
            size += len(chunk)
            hd.update(chunk)
    d = dict(file=path.name, size=size, header_sha256_without_date=hh.hexdigest(), data_sha256=hd.hexdigest(),
             date_line=date)
    (path.parent / "trace.digest.json").write_text(json.dumps(d, indent=1) + "\n")
    return d


def _net(s, cfg, out, seed, rnd, scale):
    cells, _ = instrument.deckmod.names(s)
    ns = noise2.noise_seed(seed, rnd) if int(rnd) > 0 else None
    if ns is None:
        return instrument.CalNetwork(s, cfg, out, int(seed)), None
    env = dict(LD_PRELOAD=str(noise2.shim(HERE / "build")), FAKEPID=str(ns))
    with noise2.noisy_deck(cells, float(scale), env):
        return instrument.CalNetwork(s, cfg, out, int(seed)), ns


def _cfg(overlay):
    import lcal2
    return lcal2.config(overlay)[0] if overlay else json.loads((HERE / "config.json").read_text())


def stagen(spec_path, out, seed, rnd, scale=1.0, overlay=None, positive=False, log=print):
    """noise2.run's training and tests, then the skew slots: OUT/noisy_record.json with "skews"."""
    s, cfg, out = specmod.load(spec_path), _cfg(overlay), Path(out)
    t0 = time.time()
    net, ns = _net(s, cfg, out, seed, rnd, scale)
    status, lessons, words, tests, skews = "done", [], {}, [], []
    try:
        lessons, words, tests = noise2.train_and_test(net, s, cfg, log)
        for k, i in both_cells(s):
            r = skew_slot(net, s, k, i)
            skews.append(len(net.slots) - 1)
            log(f"skew c{k}_{i}: {'FIRE' if r['reads'][0]['emission'] is not None else 'silent'}")
        if positive:                                        # development check only: the same slot, coincident
            for k, i in both_cells(s):
                r = skew_slot(net, s, k, i, shift_tu=F(0))
                r["kind"] = "skew_check"
                log(f"skew_check (shift 0) c{k}_{i}: {'FIRE' if r['reads'][0]['emission'] is not None else 'silent'}")
    except Exception as e:
        status = f"failed: {e}"
        log(status)
    finally:
        write_trace(net)
        cpu = runmod.cpu_of(net.ses.p.pid)
        net.ses.close()
    text = (out / "input.spice").read_text()
    rec = dict(tag=s["tag"], seed=int(seed), round=int(rnd), noise_seed=ns, noise_scale=float(scale) if ns else 0.0,
               status=status, input_spice_sha256=hashlib.sha256(text.encode()).hexdigest(),
               cost=dict(wall_s=time.time() - t0, cpu_s=cpu),
               words={f"{k}/{i}/{g}": w for (k, i, g), w in words.items()}, lessons=lessons, tests=tests, skews=skews,
               slots=net.slots)
    (out / "noisy_record.json").write_text(json.dumps(rec, indent=1, default=str) + "\n")
    return rec


def untrained(spec_path, out, seed, overlay=None, log=print):
    s, cfg, out = specmod.load(spec_path), _cfg(overlay), Path(out)
    t0 = time.time()
    net, _ = _net(s, cfg, out, seed, 0, 0)
    status, tests = "done", []
    try:
        for x in specmod.patterns(s["m"]):
            r_ = net.slot("test", specmod.rails(s, x), len(s["layers"]), {}, set(), dict(pattern=[int(b) for b in x]))
            tests.append(len(net.slots) - 1)
            fired = [f"c{r['layer']}_{r['index']}" for r in r_["reads"] if r["emission"] is not None]
            log(f"untrained test {''.join(str(int(b)) for b in x)}: R cells firing {fired or 'none'}")
    except Exception as e:
        status = f"failed: {e}"
        log(status)
    finally:
        write_trace(net)
        cpu = runmod.cpu_of(net.ses.p.pid)
        net.ses.close()
    text = (out / "input.spice").read_text()
    rec = dict(tag=s["tag"], seed=int(seed), round=0, noise_seed=None, noise_scale=0.0, control="U", status=status,
               input_spice_sha256=hashlib.sha256(text.encode()).hexdigest(), cost=dict(wall_s=time.time() - t0, cpu_s=cpu),
               words={}, lessons=[], tests=tests, slots=net.slots)
    (out / "untrained_record.json").write_text(json.dumps(rec, indent=1, default=str) + "\n")
    return rec


def verdicts(d):
    d, out = Path(d), {}
    if (d / "noisy_record.json").exists():
        r = json.loads((d / "noisy_record.json").read_text())
        sk = [r["slots"][j] for j in r.get("skews", [])]
        out["S"] = dict(slots=len(sk), holds=all(x["reads"][0]["emission"] is None for x in sk),
                        cells={x["info"]["cell"]: x["reads"][0]["emission"] is None for x in sk},
                        noise_seed=r["noise_seed"], status=r["status"])
    if (d / "untrained_record.json").exists():
        r = json.loads((d / "untrained_record.json").read_text())
        fires = [(r["slots"][j]["info"]["pattern"], f"c{x['layer']}_{x['index']}") for j in r["tests"]
                 for x in r["slots"][j]["reads"] if x["emission"] is not None]
        inv = sum(1 for j in r["tests"] for v in r["slots"][j]["inv"] if v["emission"] is not None)
        out["U"] = dict(tests=len(r["tests"]), holds=not fires and r["status"] == "done", r_cell_fires=fires,
                        inverter_emissions=inv, status=r["status"])
    return out


if __name__ == "__main__":
    cmd, *a = sys.argv[1:]
    kw = dict(x.split("=", 1) for x in a if "=" in x)
    pos = [x for x in a if "=" not in x]
    if cmd == "stagen":
        r = stagen(*pos[:4], scale=float(kw.get("scale", 1)), overlay=kw.get("overlay"), positive=kw.get("positive") == "1")
        print(json.dumps(dict(status=r["status"], words=r["words"], skews=r["skews"], cost=r["cost"]), indent=1))
    elif cmd == "untrained":
        r = untrained(*pos[:3], overlay=kw.get("overlay"))
        print(json.dumps(dict(status=r["status"], cost=r["cost"]), indent=1))
    elif cmd == "verdicts":
        print(json.dumps(verdicts(pos[0]), indent=1))
    else:
        sys.exit(__doc__)
