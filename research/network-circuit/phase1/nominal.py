"""Rehearsal on the nominal cell: the network calendar of 18 units, with noise, no mismatch. Phase 1, exploratory.

  nominal.py run OUT NGSPICE PDK            one network run, guard at 16 units
  nominal.py collect NOMINAL_REHEARSAL.json OUT...

The nominal cell is not one of the instances. What the model says of it on this calendar is in
`CircuitNetwork.lean` (`nominalRun`): four writes on every port, pushed with phase 1 before these runs.
"""
import json
from pathlib import Path
import statistics as st
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent))
import calendars
import model


def collect(folders):
    gap = dict.fromkeys(model.PORTS, 359378)
    log, writes, _ = model.run(gap, model.seed(*calendars.counts(calendars.reciprocal(18))), 224)
    expected = {p: model.word(log, p) for p in model.PORTS}
    runs = []
    for folder in folders:
        r = json.loads((Path(folder) / "result.json").read_text())
        assert r["deck"] == dict(section="tt", noise=True) and r["seed"] is None and r["guard_units"] == 16
        words, ports = {}, {}
        for name in model.PORTS:
            occ = [o for o in r["occurrences"] if f"{o['cell']}{o['port']}" == name]
            words[name] = "".join("r" if o.get("refused") else "x" if not o["delivered"] else "F" if o["fire"] else "s" for o in occ)
            lat = [o["latency"] for o in occ if o["delivered"] and o["fire"]]
            ports[name] = dict(fires=len(lat), mean_latency=st.mean(lat), sd_latency=st.stdev(lat))
        dates = {c: sorted(o["date_s"] for o in r["occurrences"] if o["cell"] == c and o["delivered"]) for c in r["cells"]}
        runs.append(dict(run=Path(folder).name, words=words, as_the_model=words == expected, fires=len(r["fires"]), refused=sum(1 for o in r["occurrences"] if o.get("refused")),
                         still_queued=len(r["still_queued_at_the_horizon"]), least_separation_units=min(b - a for d in dates.values() for a, b in zip(d, d[1:])) / 20e-6,
                         ports=ports, wall_s=r["wall_s"], deck_sha256=r["deck_sha256"], raw_sha256=r["raw_sha256"]))
    between = {name: st.stdev(x["ports"][name]["mean_latency"] for x in runs) for name in model.PORTS}
    within = {name: st.mean(x["ports"][name]["sd_latency"] for x in runs) for name in model.PORTS}
    return dict(what="network runs of the calendar of 18 units on the nominal cell, with noise; see nominal.py", calendar=calendars.reciprocal(18)["name"],
                words_of_the_model=expected, runs=runs, sd_between_runs_of_the_mean_latency=between, mean_sd_of_the_latency_within_a_run=within)


if __name__ == "__main__":
    if sys.argv[1] == "run":
        import router
        r = router.run(Path(sys.argv[2]), calendars.reciprocal(18), Path(sys.argv[3]), Path(sys.argv[4]), guard=16, section="tt", noise=True)
        print(json.dumps(dict(word=router.word(r), fires=len(r["fires"]), wall_s=round(r["wall_s"]))))
    else:
        Path(sys.argv[2]).write_text(json.dumps(collect(sys.argv[3:]), indent=1) + "\n")
