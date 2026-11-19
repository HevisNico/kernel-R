"""Campaign 6: the disk check before a stage's launch, on each machine (the audit of 2026-11-19; the coordinators'
disk precondition). A small script OUTSIDE stages6.frozen(), like marker_check. A refusal means that machine does not
launch the stage; its report goes with the stage's evidence.

  diskcheck.py MANIFEST.json MACHINE OUT_PARENT [MARGIN_MB]     writes DISK_CHECK_<campaign_id>_<MACHINE>.txt next to the manifest

The stage's footprint on MACHINE: for each of its runs, the largest run folder measured for its kind (the batch's
collected evidence, and campaign 5's smoke run for the network runs, with room for the longest calendars), counted
twice (the run folder and its collected copy). It passes only if the free space where the runs are written (OUT_PARENT)
exceeds that footprint plus MARGIN_MB (default 500). The report records the df line, the uptime and the free memory.
"""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

# the largest run folder per kind, in MB (the batch's evidence: cal-on 79.3, cal-off 68.1, pair 76.6, line 81.3,
# bothfire 3.0, onesided 25.1; the smoke network run's trace 64.3 at need 4, with room for need 7's longer calendar)
MB = {"cal-on": 85, "cal-off": 75, "pair": 85, "line": 90, "bothfire": 5, "onesided": 30, "network": 130}
TWICE = 2                                                # the run folder and its collected copy


def kind(run):
    a = run["argv"]
    if a[1].endswith("meas6.py"):
        if a[2] == "cal":                                    # {python} meas6 cal STAGE {out} INSTANCE GUARD ...
            return "cal-on" if a[6] == "on" else "cal-off"
        k = a[7]                                             # {python} meas6 scan STAGE {out} INSTANCE CELL KIND ...
        return {"bothfire": "bothfire", "onesided": "onesided"}.get(k, "pair" if k == "pair" else "line")
    return "network"


def footprint_mb(m, machine):
    return sum(MB[kind(r)] * TWICE for r in m["runs"] if r["machine"] == machine)


def check(manifest_path, machine, out_parent, margin_mb=500):
    m = json.loads(Path(manifest_path).read_text())
    need = footprint_mb(m, machine) + margin_mb
    free = shutil.disk_usage(out_parent).free / 1e6
    lines = [f"stage {m['campaign_id']}, machine {machine}: {sum(r['machine'] == machine for r in m['runs'])} runs",
             f"footprint {footprint_mb(m, machine)} MB (largest measured run folder per kind, twice) + margin {margin_mb} MB = {need} MB",
             f"free at {out_parent}: {free:.0f} MB",
             "df: " + subprocess.run(["df", "-h", str(out_parent)], capture_output=True, text=True).stdout.strip().splitlines()[-1],
             "uptime -s: " + subprocess.run(["uptime", "-s"], capture_output=True, text=True).stdout.strip(),
             "MemAvailable: " + next((l.split(":", 1)[1].strip() for l in Path("/proc/meminfo").read_text().splitlines() if l.startswith("MemAvailable")), "unknown")]
    ok = free > need
    if not ok:
        lines.append(f"REFUSED: {free:.0f} MB free, {need} MB needed; free space before launching")
    return ok, lines


def main(argv=None):
    a = sys.argv[1:] if argv is None else argv
    manifest, machine, out_parent = Path(a[0]), a[1], Path(a[2])
    margin = int(a[3]) if len(a) > 3 else 500
    assert machine in ("a", "b"), "machine a or b"
    ok, lines = check(manifest, machine, out_parent, margin)
    m = json.loads(manifest.read_text())
    text = "\n".join(lines + [f"VERDICT: {'PASSED' if ok else 'REFUSED'}", ""])
    (manifest.parent / f"DISK_CHECK_{m['campaign_id']}_{machine}.txt").write_text(text)
    print(text, end="")
    raise SystemExit(0 if ok else 1)


if __name__ == "__main__":
    main()
