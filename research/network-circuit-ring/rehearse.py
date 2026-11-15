"""One run of the ring on the nominal cell, for the rehearsal of phase 0. Not a registered runner.

  rehearse.py OUT N LAPS quiet|noise|control NGSPICE PDK
  rehearse.py OUT N READS scan-<port>|train-quiet|train-noise NGSPICE PDK
  rehearse.py collect DATA REHEARSAL.json

The deck has N nominal cells (model section `tt`, no mismatch, no seed: not an instance), the junction areas of
stage J, and the noise of the simulator only with `noise`. `quiet` and `noise` play `ring.ring(N, LAPS)` with the
router guard at 16 units; `control` plays the ring outside the timing condition (`ring.control`), without the
guard, so that the pulses that the guard would refuse are delivered. Writes `summary.json` in OUT.
"""
import json
from pathlib import Path
import sys
import time

HERE = Path(__file__).resolve().parent
NET = HERE.parent / "network-circuit"
sys.path.insert(0, str(NET))
sys.path.insert(0, str(NET / "phase1"))
sys.path.insert(0, str(HERE))
import measure
import net
import ring
import router

MOVE_MV = 0.01                  # as D2 of campaign 1: the stored voltage of a port moves only by its doses


def summary(result, tr):
    """What the run did, port by port, from the record of the router and from the waveform."""
    calendar = result["calendar"]
    n, P = calendar["n"], calendar["period"]
    chain = ring.ports(n)
    words = router.word(result)
    mine = {p: [o for o in result["occurrences"] if f"{o['cell']}{o['port']}" == p] for p in chain}
    lap = lambda o: int((o["date_s"] - router.ORIGIN) / net.TU // P) + 1
    writes = [lap(o) for p in chain for o in mine[p] if o["delivered"] and not o["fire"] and o[f"writes{p[1]}"] == 1]
    starts = {c: sorted(o["date_s"] for o in result["occurrences"] if o["cell"] == c and o["delivered"]) for c in result["cells"]}
    closest = {c: min((b - a) / net.TU for a, b in zip(s, s[1:])) for c, s in starts.items() if len(s) > 1}
    other, doses = 0.0, []
    for p in chain:                                         # the stored voltage of the port between and across its pulses
        key, previous = f"u{p[1]}", None
        for o in mine[p]:
            if not o["delivered"]:
                continue
            before, after = o[key + "_before_V"] * 1e3, o[key + "_after_V"] * 1e3
            if previous is not None:
                other = max(other, abs(before - previous))
            if o["fire"] or o[f"writes{p[1]}"] != 1:
                other = max(other, abs(after - before))
            else:
                doses.append(before - after)
            previous = after
        if previous is not None:
            other = max(other, abs(result["final_u_V"][p] * 1e3 - previous))
    idle = [abs(result["final_u_V"][c + "2"] - result["initial_u_V"][c + "2"]) * 1e3 for c in result["cells"][1:]]
    return dict(n=n, laps=calendar["laps"], period_units=P, reach_units=calendar["reach"], guard_units=result["guard_units"], noise=result["deck"]["noise"],
                simulated_ms=calendar["horizon"] * net.TU * 1e3, wall_s=result["wall_s"], points=result["points"],
                words={p: words.get(p, "") for p in chain}, pulses_on_other_ports={p: w for p, w in words.items() if p not in chain},
                needs=[words.get(p, "").count("s") for p in chain],
                freeze_lap=max(writes) if writes else 0, after_the_last_write=[len(words.get(p, "")) - 1 - words.get(p, "").rfind("s") for p in chain],
                fires={c: sum(f["cell"] == c for f in result["fires"]) for c in result["cells"]},
                routed=sum(len(f["routed"]) for f in result["fires"]), root_fires_routed_nowhere=sum(f["cell"] == "a" and not f["routed"] for f in result["fires"]),
                refused=sum(bool(o.get("refused")) for o in result["occurrences"]), undelivered=sum(not o["delivered"] for o in result["occurrences"]),
                on_a_protected_cell=sum(bool(o.get("protected_at_start")) for o in result["occurrences"] if o["delivered"]),
                still_queued_at_the_horizon=len(result["still_queued_at_the_horizon"]),
                closest_pulses_units=closest, separation_by_construction=ring.separation(calendar), holds_by_construction=ring.holds_by_construction(calendar),
                latency_units=[min(o["latency"] for o in result["occurrences"] if o.get("fire")), max(o["latency"] for o in result["occurrences"] if o.get("fire"))]
                if any(o.get("fire") for o in result["occurrences"]) else None,
                dose_mV=[min(doses), max(doses)] if doses else None, largest_move_that_is_not_a_dose_mV=other,
                largest_move_of_an_unused_port_mV=max(idle) if idle else None,
                initial_u_mV={p: result["initial_u_V"][p] * 1e3 for p in chain}, final_u_mV={p: result["final_u_V"][p] * 1e3 for p in chain},
                waveform_ends_s=float(tr.t[-1]), reached_its_last_date=bool(tr.t[-1] >= router.ORIGIN + calendar["horizon"] * net.TU - 1e-9),
                raw_sha256=result["raw_sha256"], deck_sha256=result["deck_sha256"])


def measure_run(out, n, reads, mode, ngspice, pdk):
    """The per-port measures of the campaign on the deck of the ring, for their wall time: `scan-<port>` is the scan of
    one port by `phase1/cellscan.py` (its list of cells set to those of the ring), `train-quiet` and `train-noise` are
    `ring.train(n, reads)`."""
    began = time.time()
    if mode.startswith("scan-"):
        import cellscan
        cellscan.CELLS = ring.cells(n)
        port = mode[5:]
        assert port in ring.ports(n)
        r = cellscan.scan(out, "tt", None, port[0], int(port[1]), ngspice, pdk)
        s = dict(word="".join("F" if p["fire"] else "s" if p["kind"] != "dose" else "d" for p in r["pulses"]), pulses=len(r["pulses"]),
                 bracket_stored_mV=[v * 1e3 for v in r["bracket_stored_V"]], simulated_ms=max(p["date_s"] for p in r["pulses"]) * 1e3)
    else:
        calendar = ring.train(n, reads)
        r = router.run(out, calendar, ngspice, pdk, cells=ring.cells(n), seed=None, section="tt", noise=mode == "train-noise")
        s = dict(words={p: w for p, w in router.word(r).items()}, simulated_ms=calendar["horizon"] * net.TU * 1e3)
    (out / "pdk").unlink()
    s.update(n=n, mode=mode, points=r["points"], total_wall_s=time.time() - began, raw_sha256=r["raw_sha256"], deck_sha256=r["deck_sha256"])
    (out / "summary.json").write_text(json.dumps(s, indent=1) + "\n")
    print(json.dumps(s))


def collect(data, out):
    """Gathers the `summary.json` of the run folders of DATA (`n<N>-<what>`) into one file, with what the model gives
    for each run of the ring: the zero-error words for the need that the scan of the nominal cell shows."""
    runs = {}
    for folder in sorted(Path(data).glob("n*-*")):
        if not (folder / "summary.json").exists():
            continue
        n, what = folder.name[1:].split("-", 1)
        s = json.loads((folder / "summary.json").read_text())
        kind = "ring" if what.split("-")[0] in ("quiet", "noise", "control") else what.split("-")[0]
        runs[f"{kind}-{n}-{what if kind == 'ring' else what.split('-', 1)[1]}"] = s
    need = runs["scan-3-a1"]["word"].index("F")
    for name, s in runs.items():
        if name.startswith("ring-"):
            z = ring.zero_error([need] * (s["n"] + 1), s["laps"])
            s["model"] = dict(need=need, words=dict(zip(ring.ports(s["n"]), z["words"])), freeze_lap=z["freeze_lap"], after_the_last_write=z["after_the_last_write"])
            s["as_the_model"] = s["words"] == s["model"]["words"] and s["freeze_lap"] == z["freeze_lap"] and s["after_the_last_write"] == z["after_the_last_write"]
    report = dict(what="rehearsal of phase 0 of campaign 2 on the nominal cell (model section tt, no mismatch, no seed): not an instance, not a registered run; see rehearse.py",
                  simulator=dict(ngspice_sha256=net.sim.NGSPICE_SHA256, pdk_commit=net.sim.PDK_COMMIT), at_a_time="four simulations or fewer on one machine of four processors",
                  need_of_the_nominal_port=need, runs=runs)
    Path(out).write_text(json.dumps(report, indent=1) + "\n")
    print(json.dumps({name: s.get("as_the_model", s.get("word", s.get("words"))) for name, s in runs.items()}))


def main():
    if sys.argv[1] == "collect":
        return collect(sys.argv[2], sys.argv[3])
    out, n, laps, mode, ngspice, pdk = Path(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4], Path(sys.argv[5]), Path(sys.argv[6])
    if mode.startswith(("scan-", "train-")):
        return measure_run(out, n, laps, mode, ngspice, pdk)
    assert mode in ("quiet", "noise", "control")
    calendar = ring.control(n, laps) if mode == "control" else ring.ring(n, laps)
    began = time.time()
    result = router.run(out, calendar, ngspice, pdk, cells=ring.cells(n), seed=None, guard=None if mode == "control" else ring.SEPARATION,
                        section="tt", noise=mode == "noise")
    (out / "pdk").unlink()
    s = summary(result, measure.Trace(out / "trace.raw"))
    s.update(mode=mode, total_wall_s=time.time() - began)
    (out / "summary.json").write_text(json.dumps(s, indent=1) + "\n")
    print(json.dumps({k: s[k] for k in ("n", "mode", "words", "freeze_lap", "refused", "wall_s")}))


if __name__ == "__main__":
    main()
