"""The threshold budget in two parts, by the rule of LEVEL_PROTOCOL.md. No simulation is run.

Writes level_samples.csv, level_summary.json and LEVEL_RESULTS.md.
"""
import csv
import json
import statistics
from pathlib import Path

from local_analyze import COL, OFFSET, PERIOD, TU, at, crossings, load

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
CELL = dict(run="mc_2064", quiet="mm2064_quiet_retry1", noisy=("mm2064_noise_1_retry1", "mm2064_noise_2_retry1"))


def levels(name):
    """Level q at the latch rise of every single-port period with a FIRE: {(port, pulse number): row}."""
    d, _ = load(name)
    if d is None:
        return None
    out = {}
    for k in range(1, 21):
        lo, hi = k * PERIOD, (k + 1) * PERIOD
        fire = [t for t, s in crossings(d, COL["p"], lo, hi) if s > 0]
        if fire:
            port, pulse = (1, k - 1) if k <= 10 else (2, k - 11)
            vq = at(d, COL["vq"], fire[0])
            out[(port, pulse)] = dict(run=name, port=port, pulse=pulse, period=k, fire_time=fire[0],
                                      fire_latency=(fire[0] - k * PERIOD - OFFSET) / TU, vq_at_fire=vq, level=0.1 + (1.25 - vq) / 0.5)
    return out


def main():
    with (ROOT / "need_budget_ports.csv").open(newline="") as fh:
        table = [r for r in csv.DictReader(fh) if r["run"] == CELL["run"]]
    level0 = 0.1 + float(table[0]["trip_proxy"]) / 0.5
    quiet = levels(CELL["quiet"])
    noisy = {n: levels(n) for n in CELL["noisy"]}
    S = dict(rule="LEVEL_PROTOCOL.md", cell=CELL["run"], level0=level0, trip_proxy=float(table[0]["trip_proxy"]))
    if quiet is None or any(v is None for v in noisy.values()):
        S["status"] = "not_evaluable: a raw trace is not present"
        (HERE / "level_summary.json").write_text(json.dumps(S, indent=2) + "\n")
        print(S["status"])
        return
    rows = list(quiet.values())
    for r in rows:
        r["minus_level0"] = r["level"] - level0
    ell_static = max(abs(r["minus_level0"]) for r in rows)
    deltas, alone = [], []
    for name, lv in noisy.items():
        for key, r in sorted(lv.items()):
            r["minus_level0"] = r["level"] - level0
            if key in quiet:
                r["delta_from_quiet"] = r["level"] - quiet[key]["level"]
                deltas.append(r["delta_from_quiet"])
            else:
                alone.append(f"{name} port {key[0]} pulse {key[1]}: FIRE in the noisy replay only")
            rows.append(r)
        alone += [f"{name} port {k[0]} pulse {k[1]}: FIRE in the quiet replay only" for k in sorted(quiet) if k not in lv]
    sd = statistics.stdev(deltas)
    ell_dynamic = max(max(abs(x) for x in deltas), 3 * sd)
    S.update(status="analyzed", quiet_levels=len(quiet), quiet_level_min=min(r["level"] for r in quiet.values()),
             quiet_level_max=max(r["level"] for r in quiet.values()), ell_static=ell_static,
             paired=len(deltas), unpaired=alone, delta_mean=statistics.mean(deltas), delta_sd=sd, delta_max_abs=max(abs(x) for x in deltas),
             ell_dynamic=ell_dynamic, ell=ell_static + ell_dynamic,
             smallest_level=min(r["level"] for r in rows), level_at_least_19_20=min(r["level"] for r in rows) >= 0.95 and level0 >= 0.95)
    ports = []
    for r in table:
        d0, a, m, b = float(r["d0_proxy"]), float(r["a_proxy"]), int(r["ceiling_count"]), float(r["b_sample"])
        room = lambda ell: d0 / 2 - a - m * b - 20 / 17 * ell - 1 / 8000
        ports.append(dict(run=r["run"], port=int(r["port"]), observed_silent=int(r["observed_silent"]), m=m, d0=d0, a=a, b=b,
                          room_historical_ell_0=room(0.0), room_recorded=float(r["room_proxy"]),
                          room_with_ell_static=room(ell_static), room_with_ell=room(ell_static + ell_dynamic)))
    S["ports"] = ports
    (HERE / "level_summary.json").write_text(json.dumps(S, indent=2) + "\n")
    fields = ["run", "port", "pulse", "period", "fire_time", "fire_latency", "vq_at_fire", "level", "minus_level0", "delta_from_quiet"]
    with (HERE / "level_samples.csv").open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=fields, lineterminator="\n")
        w.writeheader(); w.writerows(rows)

    L = ["# The threshold budget in two parts", "",
         "Written by `level_analyze.py` under `LEVEL_PROTOCOL.md`. Levels are in the declared coordinate `q`.", "",
         f"Cell `{CELL['run']}`. Reference level of the historical table: `level0 = 0.1 + {S['trip_proxy']} / 0.5` = {level0:.5f}.", "",
         "| Part | Value | From |", "|---|---|---|",
         f"| `ell_static` | {ell_static:.5f} | {len(quiet)} single-port periods with a FIRE in the replay without noise; their level goes from {S['quiet_level_min']:.5f} to {S['quiet_level_max']:.5f} |",
         f"| `ell_dynamic` | {ell_dynamic:.5f} | {len(deltas)} paired periods of the two noisy replays: largest \\|delta\\| {S['delta_max_abs']:.5f}, standard deviation {sd:.5f}, mean {S['delta_mean']:+.5f}. A statistic, not a certified bound |",
         f"| `ell` | {ell_static + ell_dynamic:.5f} | their sum |", "",
         f"Smallest level seen: {S['smallest_level']:.5f}. `19/20 <= level` and `19/20 <= level0`: {'yes' if S['level_at_least_19_20'] else 'NO'} on these values.", "",
         "Periods with a FIRE in only one of a noisy replay and the quiet one, left out of `delta`: " + ("; ".join(alone) if alone else "none") + ".", "",
         "## room", "",
         "`d0`, `a`, `m` and `b` are those of the historical table. Only `ell` changes.", "",
         "| Port | Observed silent pulses | m | room with `ell = 0` (historical) | room with `ell_static` | room with `ell_static + ell_dynamic` (statistical) |", "|---|---|---|---|---|---|"]
    for p in ports:
        L.append(f"| `{p['run']}`, port {p['port']} | {p['observed_silent']} | {p['m']} | {p['room_historical_ell_0']:+.6f} | {p['room_with_ell_static']:+.6f} | {p['room_with_ell']:+.6f} |")
    L += ["", "The first value reproduces the historical table. The second uses a measure made on the cell. The third adds a statistic of two replays "
          "and is not certified for the original trajectory.", ""]
    (HERE / "LEVEL_RESULTS.md").write_text("\n".join(L))
    print("\n".join(L))


if __name__ == "__main__":
    main()
