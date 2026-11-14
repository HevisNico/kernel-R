"""The tables of README.md, written from QUALIFICATION.json, QUALIFICATION_SCHEMATIC.json and BUDGET.json. No simulation is run.

  tables.py          rewrites the blocks of README.md between `<!-- table NAME -->` and `<!-- end -->`
  tables.py --check  fails if a block of README.md is not the one the published numbers give
"""
import json
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent


def md(header, rows):
    lines = ["| " + " | ".join(header) + " |", "|" + "|".join("---" if i == 0 else "---:" for i in range(len(header))) + "|"]
    return "\n".join(lines + ["| " + " | ".join(str(x) for x in r) + " |" for r in rows])


def summary_rows(q):
    return [[name, g["sequences"], g["services"], g["correct"], g["refusals"], g["writes_not_as_commanded"], g["fires_outside_reads"], g["enclosures_broken"],
             f"{g['smallest_joint_latency']:.4f}", f"{g['largest_single_latency']:.4f}", f"{g['largest_observer_error_uV']:.3f}"]
            for name, g in sorted(q["confirmation_summary"].items())]


SUMMARY = ["Version", "sequences", "services", "correct", "refusals", "writes not as commanded", "FIRE outside a read", "enclosures broken",
           "smallest joint latency", "largest single latency", "largest observer error (uV)"]


def blocks(q, b, old):
    out = {}
    out["thresholds"] = md(["Configuration", "silent reads to learn (port 1, port 2)", "own drift (mV per period)", "Port 1: U_S (mV)", "bracket (uV)", "latency at U_S",
                            "Port 2: U_S (mV)", "bracket (uV)", "latency at U_S"],
                           [[c, f"{rows[0]['trained_after']}, {rows[1]['trained_after']}", f"{max(t['own_drift_mV_per_period'] for t in rows):.3f}"]
                            + [x for t in rows for x in (f"{t['u_service_V'] * 1e3:.4f}", f"{t['bracket_uV']:.1f}", f"{t['latency_at_threshold']:.4f}")]
                            for c, rows in q["thresholds"].items()])
    out["losses"] = md(["Configuration", "own loss, port 1 (mV per period)", "port 2", "added per 1e-11 S, port 1 (mV)", "port 2", "dose, port 1 (mV)", "port 2"],
                       [[c, f"{d['loss_line'][0]['own_loss_mV'][1]:.4f}", f"{d['loss_line'][1]['own_loss_mV'][1]:.4f}", f"{d['loss_line'][0]['mV_per_siemens'] * 1e-11:.4f}",
                         f"{d['loss_line'][1]['mV_per_siemens'] * 1e-11:.4f}"] + [f"{g[0]:.4f} to {g[1]:.4f}" for g in d["gross_dose_mV"]] for c, d in q["doses"].items()])
    rows = []
    for c, m in q["reads_map"].items():
        joint, single = m["joint"], m["single"]
        low = min(joint, key=lambda x: abs(x[0]))
        rows.append([c, len(joint), f"{low[1]:.4f} at {low[0]:.2f}", f"{joint[-1][1]:.4f} at {joint[-1][0]:.2f}",
                     f"{max(x[1] for s in single for x in s):.3f}", f"{min(x[1] for s in single for x in s):.3f} at {max(x[0] for s in single for x in s):.2f}"])
    out["reads"] = md(["Configuration", "joint reads", "joint latency near zero reserve (at sum, mV)", "at the largest sum measured (mV)",
                       "largest single latency", "smallest single latency (at reserve, mV)"], rows)
    out["noise"] = md(["Configuration", "noisy sequences", "joint reads", "sd of joint latency", "largest shift", "single reads", "sd as reserve (mV)", "largest (mV)",
                       "doses", "sd of dose (mV)", "largest (mV)"],
                      [[c, n["runs"], n["joint_reads"], f"{n['sd_joint_latency']:.5f}", f"{n['largest_joint_latency_shift']:.5f}", n["single_reads"],
                        f"{n['sd_single_as_reserve_mV']:.3f}", f"{n['largest_single_as_reserve_mV']:.3f}", n["doses"], f"{n['sd_dose_mV']:.4f}",
                        f"{n['largest_dose_shift_mV']:.4f}"] for c, n in q["read_noise"].items()])
    for k in ("0", "2", "3"):
        rows = []
        for c, d in q["designs"].items():
            for i, port in enumerate(d[k]["ports"]):
                x = port["bounds"]
                rows.append([f"{c} port {i + 1}", f"{d[k]['sum_limit_mV']:.3f}" + ("" if d[k]["joint_curve_crossed"] else " (largest measured)"),
                             f"{x['S'] / 1e4:.4f}", f"{x['semantic_capacity'] / 1e4:.4f}", f"{x['Dmin'] / 1e4:.4f}", f"{x['Dmax'] / 1e4:.4f}", f"{x['epsilon'] / 1e4:.4f}",
                             f"{port['room_for_2H_units'] / 1e4:.4f}", f"{x['H'] / 1e4:.4f}" if port["well_formed"] else "none", f"{port['own_loss_mV']:.4f}",
                             f"{port['largest_leak_over_1e11_ohm']:.2f}" if port["well_formed"] else "none"])
        out["design" + k] = md(["Port", "limit of the sum (mV)", "S", "C", "Dmin", "Dmax", "epsilon", "room for 2H", "H", "own loss", "largest imposed leak (x 1e-11 S)"], rows)
    out["confirmation"] = md(SUMMARY, summary_rows(q))
    out["schematic"] = md(SUMMARY, summary_rows(old))
    out["aborted"] = md(["Run", "netlist", "ammeter", "noise", "message of the simulator"],
                        [[a["run"], name, "yes" if a["ammeter"] else "no", "yes" if a["noise"] else "no", a["message"]]
                         for name, x in (("without areas", old), ("with areas", q)) for a in x["aborted_runs"]])
    out["budget"] = md(["Services per run", "estimate (s)", "time limit (s)", "runs per machine", "runs", "services", "bound per machine", "expected per machine"],
                       [[p["services_per_run"], p["estimate_s"], p["timeout_s"], p["runs_per_machine"], p["runs"], p["services"],
                         f"{p['bound_per_machine_s'] / 3600:.2f} h", f"{p['expected_wall_per_machine_s'] / 3600:.2f} h"] for p in b["packings"]])
    return out


def main():
    q = json.loads((HERE / "QUALIFICATION.json").read_text())
    b = json.loads((HERE / "BUDGET.json").read_text())
    old = json.loads((HERE / "QUALIFICATION_SCHEMATIC.json").read_text())
    readme = HERE / "README.md"
    text = readme.read_text()
    new = text
    for name, table in blocks(q, b, old).items():
        pattern = re.compile(r"(<!-- table " + name + r" -->\n)(?:.*?\n)??(<!-- end -->)", re.S)
        assert len(pattern.findall(new)) == 1, "README.md must hold the block exactly once: " + name
        new = pattern.sub(lambda m: m.group(1) + table + "\n" + m.group(2), new)
    if "--check" in sys.argv:
        assert new == text, "a table of README.md is not the one the published numbers give"
        print("PASS: the tables of README.md are those of the published numbers")
    else:
        readme.write_text(new)


if __name__ == "__main__":
    main()
