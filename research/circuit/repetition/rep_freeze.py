"""Frozen inputs of the repetition campaign. No simulation is run and no result of this campaign is read.

  rep_freeze.py A1_PORTS_CSV   -> frozen.json

Reads the table of rule A1 (asymmetric-ports.csv of the branch codex/physical-readout-enclosures, at the
commit named in PREDICTION.md, given on the command line) and the public files of the two certification
campaigns. Writes, for each port that passes rule A1, the constants that the repetitions use.
"""
import csv
import hashlib
import json
import math
from fractions import Fraction
from pathlib import Path
import statistics
import sys

HERE = Path(__file__).resolve().parent
UNCOND = HERE.parent / "certification-unconditional"
sys.path.insert(0, str(UNCOND))
import uncond_analyze as U
import uncond_amend1 as M

A, CERT = U.A, U.CERT


def main():
    source = Path(sys.argv[1])
    a1 = [r for r in csv.DictReader(source.open(newline="")) if r["eligible"] == "True"]
    cal = json.loads((CERT / "calibration.json").read_text())
    kappa = cal["kappa"]
    pred = {(r["cell"], int(r["port"])): r for r in csv.DictReader((CERT / "predictions.csv").open(newline=""))}
    p109 = {(r["cell"], int(r["port"])): r for r in csv.DictReader((UNCOND / "ports_amendment1.csv").open(newline=""))}
    # eps_kappa of the certification campaign: largest |G - Y - kappa| over the silent single-port reads of its 100 test runs
    dev = []
    for run in A.MANIFEST["stages"]["test"]:
        A.HERE = CERT
        rows, _, why = A.load("test", run["name"])
        assert rows is not None, why
        dev += [abs(A.gain_silent(r) - A.gain_early(r) - kappa) for r in rows if int(r["port"]) in (1, 2) and r["fired"] != 1]
    ports = []
    for r in a1:
        seed, port = int(r["cell"]), int(r["port"])
        cell = f"t{seed}"
        rows, charge, _, why = U.load(UNCOND, "gain", f"u{seed}_train")
        assert rows is not None, why
        early, why = M.load_early(UNCOND, "gain", f"u{seed}_train", rows)
        assert early is not None, why
        g, why = U.compare(rows, charge, port, kappa)
        e, why2 = M.eps3_of(rows, charge, early, port)
        assert g is not None and e is not None, (why, why2)
        o, p = p109[(cell, port)], pred[(cell, port)]
        assert abs(float(o["eps3"]) - float(Fraction(r["epsilon"]))) < 1e-9 and int(p["m"]) == int(r["m"])
        ports.append(dict(cell=cell, seed=seed, port=port, m=int(r["m"]), a_s=float(p["a_s"]), start_gain=float(p["start_gain"]),
                          level0=float(p["level0"]), h3=float(o["h3"]), eps3_109=float(o["eps3"]), D0=g["D"], DE0=e["DE"],
                          count_107=int(r["count"]), status3_109=o["status3"]))
    out = dict(rule="PREDICTION.md, frozen inputs", a1_table_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
               kappa=kappa, d0=cal["d0"], eps_kappa=max(dev), eps_kappa_reads=len(dev), MZ=A.MZ, MQ=A.MQ, MG=U.MG, ports=ports)
    (HERE / "frozen.json").write_text(json.dumps(out, indent=1) + "\n")
    print(len(ports), "ports,", len({p["cell"] for p in ports}), "cells; eps_kappa", max(dev), "over", len(dev), "reads")


if __name__ == "__main__":
    main()
