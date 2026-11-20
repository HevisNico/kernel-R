"""Development only: G5 of DOSE_PLAN.md, "the network does what the measures say", on one quiet network run of the
nominal cell. No simulation: it reads the run's record and waveform with campaign 5's readers (the path of
analyze.rows_of: plans4.network, measure.Trace, reads4.network_reads, reads4.words).

  g5.py REPO LABEL RUN_DIR OUT.json

G5, as written: the six words and the 16 outputs are those the needs give (dnf.zero_error at the run's needs).
Also reported, as the direct check that a calibration deck cannot make (G2): no read both fires and writes; every
read that may write and fires has no write; the two skew slots leave a and b silent; and, on every training read
that writes, the ERROR entry (the rise of the write signal) and the FIRE latencies of the same cell.
"""
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import dosedev

TU = 20e-6


def judge(repo, label, run):
    dosedev.repo_paths(repo)
    import measure
    import plans4
    import reads4
    from c4 import dnf
    run = Path(run)
    rec = json.loads((run / "record.json").read_text())
    needs, control = rec["needs"], rec["control"]
    plan, slots = plans4.network(tuple(needs), control)
    result = json.loads((run / "evidence" / "result.json").read_text())
    rows = reads4.network_reads(measure.Trace(run / "evidence" / "trace.raw"), result, slots)
    seen, prime = reads4.words(rows), reads4.words(rows, prime=True)
    zero = dnf.zero_error(*needs)        # without the control, as campaign 5's predicted.py: with "skew", the two skew
    #                                      slots carry the patterns AB and CD and would overwrite those two test outputs
    want = dict(a1=zero["words"]["a"], a2=zero["words"]["a"], b1=zero["words"]["b"], b2=zero["words"]["b"], c1=zero["words"]["c1"], c2=zero["words"]["c2"])
    out = dict(label=label, run=rec["id"], needs=needs, control=control, reached_its_last_date=rec["reached_its_last_date"], slots=len(rows),
               words=dict(seen=seen["words"], predicted=want, equal={p: seen["words"][p] == want[p] for p in want}),
               words_prime_equal_words=seen["words"] == prime["words"],
               tests=dict(differ=[dict(pattern=k, seen=seen["tests"].get(k), predicted=v) for k, v in zero["tests"].items() if seen["tests"].get(k) != v],
                          patterns=len(zero["tests"]), outputs=3 * len(zero["tests"])),
               skew=seen["skew"])
    fire_and_write, may_write_and_fire, entries, latencies, gated_writes, gated_move = [], 0, {}, {}, [], 0.0
    for x in rows:
        for c, r in x["reads"].items():
            wrote = {p: r["ports"][p]["writes"] for p in ("1", "2")}
            if r["fire"]:
                latencies.setdefault(c, []).append(r["latency"])
                if any(wrote.values()):
                    fire_and_write.append(dict(slot=x["slot"], stage=x["stage"], cell=c, writes=wrote))
                if not r["gated"]:
                    may_write_and_fire += 1
            if r["gated"]:
                if any(wrote.values()):
                    gated_writes.append(dict(slot=x["slot"], stage=x["stage"], cell=c, writes=wrote))
                gated_move = max([gated_move] + [abs(r["ports"][p]["move_mV"]) for p in ("1", "2")])
            for p in ("1", "2"):
                for rise in r["ports"][p]["rises"]:
                    entries.setdefault(c, []).append((rise["rise_s"] - r["start_s"]) / TU)
    out["write_and_fire"] = dict(
        reads_that_fire_and_write=fire_and_write, reads_that_may_write_and_fire=may_write_and_fire,
        gated_reads_that_write=gated_writes, largest_gated_move_mV=gated_move,
        per_cell={c: dict(error_entry_units=[min(entries[c]), max(entries[c])] if c in entries else None, writes_seen=len(entries.get(c, [])),
                          fire_latency_units=[min(latencies[c]), max(latencies[c])] if c in latencies else None, fires_seen=len(latencies.get(c, [])),
                          entry_minus_latest_fire_units=(min(entries[c]) - max(latencies[c])) if c in entries and c in latencies else None)
                  for c in ("a", "b", "c")})
    skew_silent = all(not v for d in seen["skew"].values() for v in d.values()) if seen["skew"] else None
    out["checks"] = {"the six words are those the needs give": all(out["words"]["equal"].values()),
                     "the 16 outputs are those the needs give": not out["tests"]["differ"] and len(seen["tests"]) == len(zero["tests"])}
    out["beside_G5"] = {"no read both fires and writes": not fire_and_write, "no gated read writes": not gated_writes,
                        "the two skew slots leave a and b silent": skew_silent, "word equals word' on every port": out["words_prime_equal_words"]}
    out["G5"] = "go" if all(out["checks"].values()) else "stop"
    return out


if __name__ == "__main__":
    a = sys.argv[1:]
    res = judge(a[0], a[1], a[2])
    Path(a[3]).write_text(json.dumps(res, indent=1) + "\n")
    print(json.dumps({k: res[k] for k in ("label", "run", "needs", "G5", "checks", "beside_G5", "words", "write_and_fire", "skew")}, indent=1))
