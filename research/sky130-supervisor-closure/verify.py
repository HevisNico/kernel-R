"""Checks of the published qualification that need no waveform. Run by CI; runs no simulation.

  verify.py

The raw waveforms are outside Git; `closure.py DATA --check` recomputes every number from them. This
script checks what can be checked without them: that the bounds follow from the published
measurements, that they satisfy the conditions of the proved kernel, that the files pushed before
the confirmations are the bounds that were confirmed, that the confirmation says what the README
says, and that the kit records are those of the committed files.

Two qualifications are published: QUALIFICATION.json, on netlists with the junction areas of stage J
(the one that counts), and QUALIFICATION_SCHEMATIC.json, on the netlists without areas that came
first (kept as it was when stage J was received; see JUNCTION_AREAS.md).
"""
import hashlib
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE / "launchkit"))
import budget
import closure
import kernel as K
import launch
import tables

STAGE_J = {"junction/netlist.py": "48175a9e44cbee3f22c8b94144ea29811c66088d6ecbf7419ce6bbd49dd642da",
           "junction/areas.csv": "2d89bea15524df3e317c087216a992a443b9a3b147351e99d2d675b3dbb7d17d"}


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def inside(small, big):
    """Every value of `small` is in `big` at the same place (a later analysis may add keys, never change one)."""
    if isinstance(small, dict):
        return isinstance(big, dict) and all(k in big and inside(v, big[k]) for k, v in small.items())
    if isinstance(small, list):
        return isinstance(big, list) and len(small) == len(big) and all(inside(a, b) for a, b in zip(small, big))
    return small == big


def bounds_follow(q, own):
    maps = {c: dict(joint=[tuple(x) for x in m["joint"]], single=m["single"]) for c, m in q["reads_map"].items()}
    assert closure.designs(q["thresholds"], maps, q["read_noise"], q["doses"], own=own) == q["designs"], "the published bounds are not those of the published measurements"
    feasible = {}
    for c, d in q["designs"].items():
        for k, design in d.items():
            ok = True
            for port in design["ports"]:
                b = K.Bounds(**port["bounds"])
                assert port["well_formed"] == (port["room_for_2H_units"] >= 0 and b.well_formed())
                if port["well_formed"]:
                    assert b.H <= b.Dmin <= b.Dmax and b.S + 2 * b.H + 2 * b.epsilon + b.Dmax <= b.capacity
                ok = ok and port["well_formed"]
            assert design["well_formed"] == ok
            if ok:
                feasible.setdefault(k, []).append(c)
    return feasible


def confirmed(q, complete):
    assert closure.summary(q["confirmation"]) == q["confirmation_summary"]
    for name, g in q["confirmation_summary"].items():
        assert g["bounds_not_the_design"] == 0 and g["writes_not_as_commanded"] == 0, name
        if name.endswith("no noise"):               # the deterministic guarantee: nothing may fail
            assert g["correct"] == g["services"] and g["refusals"] == 0 and g["enclosures_broken"] == 0, name
            assert g["reads_outside_floor_and_capacity"] == 0 and g["fires_outside_reads"] == 0, name
    if complete:                                    # every configuration that has bounds was confirmed with and without noise
        for c, d in q["designs"].items():
            for k, design in d.items():
                usable = design["well_formed"] and all(p.get("holds_the_reference_leak", True) for p in design["ports"])
                runs = [s for s in q["confirmation"].values() if s["config"] == c and str(s["design"]) == k]
                assert (len([s for s in runs if not s["noise"]]) >= 2) == usable, (c, k)


def main():
    q = json.loads((HERE / "QUALIFICATION.json").read_text())
    old = json.loads((HERE / "QUALIFICATION_SCHEMATIC.json").read_text())

    # the construction and the areas are those of stage J, unchanged
    for name, digest in STAGE_J.items():
        assert sha(HERE / name) == digest, "not the file of stage J: " + name
    assert q["netlist"].startswith("with the junction areas") and old["netlist"] == "without junction areas"
    assert q["identity_of_the_expanded_deck"] and all(r["identical"] for r in q["identity_of_the_expanded_deck"])

    # the tools are the ones that produced the published numbers
    for name, digest in q["source_sha256"].items():
        assert sha(HERE / name) == digest, "changed since the qualification: " + name
    assert q["contract"] == dict(joint=list(closure.JOINT), single=list(closure.SINGLE)) and q["margins"] == closure.MARGIN

    # thresholds: a bracket of at most 20 uV on each port, latency monotone in the reserve
    assert set(q["thresholds"]) == set(closure.CONFIGS) and len(closure.CONFIGS) == 9
    for rows in q["thresholds"].values():
        for t in rows:
            assert t["latency_monotone"] and 0 < t["bracket_uV"] <= 20 and t["latency_at_threshold"] <= 1.0

    # the bounds follow from the published measurements; the files pushed before the confirmations hold the same bounds
    feasible = bounds_follow(q, own=True)
    bounds_follow(old, own=False)
    for pushed, analysis in (("BOUNDS_JUNCTION.json", q), ("BOUNDS.json", old)):
        b = json.loads((HERE / pushed).read_text())
        assert all(inside(b[key], analysis[key]) for key in ("contract", "margins", "thresholds", "read_noise", "doses", "designs")), pushed
    assert sorted(feasible["0"]) == sorted(closure.CONFIGS), "without noise margin every configuration must have bounds"

    # confirmation
    confirmed(q, complete=True)
    confirmed(old, complete=False)                  # that batch was stopped when stage J was received

    # noise: every noisy sequence drew its own noise; the fingerprint follows the draw
    for x in (q, old):
        assert x["noise_fingerprints"]["noisy_sequences"] == x["noise_fingerprints"]["distinct"] > 0
        assert all(v for k, v in x["fingerprint_check"].items() if k != "cases")

    # budget and tables: those the published numbers give
    assert budget.table(q) == json.loads((HERE / "BUDGET.json").read_text())
    text = (HERE / "README.md").read_text()
    for name, table in tables.blocks(q, json.loads((HERE / "BUDGET.json").read_text()), old).items():
        assert f"<!-- table {name} -->\n{table}\n<!-- end -->" in text, "README.md does not hold the table of the published numbers: " + name

    # kit: pinned interpreter, identical outputs, end-to-end test of this very launcher
    identity = json.loads((HERE / "PYTHON_IDENTITY.json").read_text())
    assert identity["all_identical"] and identity["compared"] == 23 and identity["joint_reads_compared"] == 8
    for key in ("python_version", "python_sha256", "numpy_version", "numpy_record_sha256"):
        assert identity[key] == launch.EXPECTED[key]
    synthetic = json.loads((HERE / "launchkit" / "SYNTHETIC_TEST.json").read_text())
    assert synthetic["all_checks_passed"] and synthetic["launcher_sha256"] == sha(HERE / "launchkit" / "launch.py")
    assert synthetic["environment"] == launch.EXPECTED
    assert b"set num_threads=1" in (HERE / "runtime" / "spinit").read_bytes()

    # nothing registered lives here
    for name in ("PREDICTION.md", "CAMPAIGN.json", "RUN_ATTEMPT.json"):
        assert not list(HERE.rglob(name)), "a registered file in the qualification folder: " + name
    print("PASS:", len(q["evidence_files"]), "+", len(old["evidence_files"]), "evidence files identified;",
          {k: len(v) for k, v in sorted(feasible.items())}, "configurations with bounds per version;",
          {k: f"{g['correct']}/{g['services']}" for k, g in q["confirmation_summary"].items()})


if __name__ == "__main__":
    main()
