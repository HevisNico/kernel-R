"""The network runs of phase 0 against what EXPECTATION.md said before them. No simulation is run.

  network_summary.py DATA          -> NETWORK.json   (DATA: folder of the runs of router.py, outside the repository)
"""
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import net
import router

EXPECTED = dict(native=dict(words=dict(a1="ssssFFFF", b1="sss", b2="ssssFFF", a2="sss"), writes=dict(a1=4, b1=3, b2=4, a2=3), fires=dict(a=4, b=3),
                            routed=dict(forward=3, **{"return": 3})),
                longer=dict(words=dict(a1="ssssFFFFFFFFF", b1="ssssFFFF", b2="ssssFFFFFF", a2="ssssFF"), writes=dict(a1=4, b1=4, b2=4, a2=4), fires=dict(a=11, b=10),
                            routed=dict(forward=8, **{"return": 6})))


def main():
    data, out = Path(sys.argv[1]), {}
    for name, expected in EXPECTED.items():
        r = json.loads((data / f"net-{name}" / "result.json").read_text())
        units = lambda s: (s - r["origin_s"]) / net.TU
        words = router.word(r)
        writes = {k: sum(o[f"writes{o['port']}"] for o in r["occurrences"] if o["delivered"] and f"{o['cell']}{o['port']}" == k) for k in words}
        other = sum(o[f"writes{3 - o['port']}"] for o in r["occurrences"] if o["delivered"])
        fires = {c: sum(f["cell"] == c for f in r["fires"]) for c in r["cells"]}
        routed = {e["name"]: sum(x["edge"] == e["name"] for f in r["fires"] for x in f["routed"]) for e in r["calendar"]["edges"]}
        gaps = {}
        for c in r["cells"]:
            dates = sorted(units(o["date_s"]) for o in r["occurrences"] if o["cell"] == c)
            gaps[c] = min(b - a for a, b in zip(dates, dates[1:]))
        out[name] = dict(calendar=r["calendar"]["name"], expected=expected, words=words, writes=writes, writes_on_a_port_that_was_not_pulsed=other, fires=fires, routed=routed,
                         as_expected=words == expected["words"] and writes == expected["writes"] and fires == expected["fires"] and routed == expected["routed"],
                         pulses=len(r["occurrences"]), not_delivered=sum(not o["delivered"] for o in r["occurrences"]),
                         arrived_protected=sum(o["delivered"] and o["protected_at_start"] for o in r["occurrences"]),
                         still_queued_at_the_horizon=len(r["still_queued_at_the_horizon"]), smallest_gap_between_pulses_of_a_cell_units=gaps,
                         wire_arrivals_units={e["name"]: [units(o["date_s"]) for o in r["occurrences"] if o["origin"] == e["name"]] for e in r["calendar"]["edges"]},
                         fire_dates_units={c: [f["calendar_date"] for f in r["fires"] if f["cell"] == c] for c in r["cells"]},
                         fire_latencies=[o["latency"] for o in r["occurrences"] if o["delivered"] and o["fire"]],
                         doses_mV=[min(o["step_mV"] for o in r["occurrences"] if o["delivered"] and not o["fire"]), max(o["step_mV"] for o in r["occurrences"] if o["delivered"] and not o["fire"])],
                         stored_change_in_doses={k: (r["initial_u_V"][k] - r["final_u_V"][k]) * 1e3 / 1.3495 for k in r["final_u_V"]},
                         simulated_ms=(r["origin_s"] + r["calendar"]["horizon"] * net.TU) * 1e3, wall_s=r["wall_s"], points=r["points"],
                         raw_sha256=r["raw_sha256"], deck_sha256=r["deck_sha256"])
    (HERE / "NETWORK.json").write_text(json.dumps(out, indent=1) + "\n")
    for name, x in out.items():
        print(name, x["as_expected"], x["words"], x["fires"], x["routed"], round(x["wall_s"]))
    cost = {}
    for name, label in (("cost-j", "junction areas of stage J"), ("cost-layout", "areas and wire capacitances of layout 2.2")):
        r = json.loads((data / name / "result.json").read_text())
        rows = r["pulses"]
        cost[label] = dict(run="one cell alone, six pulses 22 units apart, no other simulation on the machine", word="".join("F" if p["fire"] else "s" for p in rows),
                           dose_mV=rows[0]["step_mV"], first_fire_latency=next(p["latency"] for p in rows if p["fire"]),
                           protected_until_units=next(p["protected_until_units"] for p in rows if p["fire"]), error_phase_units=rows[0]["error_phase_units"],
                           simulated_ms=(rows[-1]["date_s"] + net.CYCLE + 5e-6) * 1e3, wall_s=r["wall_s"], points=r["points"], raw_sha256=r["raw_sha256"], deck_sha256=r["deck_sha256"])
    (HERE / "COST.json").write_text(json.dumps(cost, indent=1) + "\n")
    print({k: (round(v["wall_s"]), v["word"], round(v["simulated_ms"], 2)) for k, v in cost.items()})


if __name__ == "__main__":
    main()
