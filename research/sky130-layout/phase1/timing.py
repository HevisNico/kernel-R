"""The timing run of ../AMENDMENT_2.md: how much slower is the stage-P netlist than the schematic?

  python3 -I timing.py check                  build the two decks, simulate nothing
  python3 -I timing.py run --machine A --go   the timing run; writes SCOPE_P.json

The run is the 2-period ramp of the nominal cell of the certification campaign: the deck that
../../circuit/certification/cert_run.py builds for its mode "ramp", read and not edited. It is
simulated once as it is, then once rewritten by netlist.py with the source and drain areas of
p_areas.csv and the capacitances of p_caps_primary.csv (../AMENDMENT_3.md), one after the other,
with nothing else running. `f` is the second wall time divided by the first.

The outputs of the two simulations are never read: they go to a folder that is deleted before
anything is printed. Only the two wall times and the return status of the simulator are kept.
The scope of stage P follows from `f` by the table of ../PREDICTION.md, and from nothing else.
"""
import hashlib
import json
import os
import platform
import shutil
import subprocess
import sys
import tempfile
import time
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
CIRCUIT = HERE.parent.parent / "circuit"
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(CIRCUIT / "certification"))
NGSPICE = os.environ.get("P1_NGSPICE", "/usr/bin/ngspice")
MODELS = Path(os.environ.get("MODELS", CIRCUIT / "pdk"))
RUN = dict(name="timing", mode="ramp", section="tt", seed=None, noise=False)
INPUTS = [HERE / "p_areas.csv", HERE / "p_caps_primary.csv", HERE / "netlist.py", HERE / "timing.py",
          CIRCUIT / "cell.spice", CIRCUIT / "blocks.spice", CIRCUIT / "certification" / "cert_run.py"]
SCOPES = [(6, "full"), (10, "reduced"), (18, "minimal")]


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def scope_of(f):
    for limit, name in SCOPES:
        if f <= limit:
            return name
    return "none"


def decks(folder):
    """The two decks, written in `folder`: the schematic and the stage-P netlist."""
    import cert_run
    import netlist
    for name in ("blocks.spice",):
        shutil.copy(CIRCUIT / name, folder / name)
    shutil.copy(CIRCUIT / "spiceinit.txt", folder / ".spiceinit")
    os.symlink(MODELS, folder / "pdk")
    schematic = cert_run.deck(RUN, "out_schematic.txt")
    (folder / "schematic.spice").write_text(schematic)
    text, devices = netlist.build(schematic.replace("out_schematic.txt", "out_stage_p.txt"),
                                  (CIRCUIT / "blocks.spice").read_text(),
                                  areas=netlist.read_areas(HERE / "p_areas.csv"),
                                  caps=netlist.read_caps(HERE / "p_caps_primary.csv"))
    (folder / "stage_p.spice").write_text(text)
    return len(devices), sum(l.startswith("cpar") for l in text.splitlines())


def simulate(folder, deck):
    env = dict(os.environ, SPICE_SCRIPTS=str(CIRCUIT / "bridge_check" / "runtime"))
    started = time.perf_counter()
    p = subprocess.run([NGSPICE, "-b", deck], cwd=folder, env=env, stdin=subprocess.DEVNULL,
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    return time.perf_counter() - started, p.returncode


def main(argv):
    cmd = argv[1] if len(argv) > 1 else ""
    if cmd not in ("check", "run"):
        sys.exit(__doc__)
    assert digest(NGSPICE) == json.loads((HERE / "j_manifest.json").read_text())["ngspice_sha256"], "simulator changed"
    commit = subprocess.run(["git", "-C", str(MODELS), "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
    assert commit == json.loads((HERE / "j_manifest.json").read_text())["pdk_commit"], "device models changed"
    folder = Path(tempfile.mkdtemp(prefix="timing_", dir=HERE / "build"))
    try:
        transistors, capacitors = decks(folder)
        if cmd == "check":
            print(f"decks built: {transistors} transistors with areas, {capacitors} capacitors added; nothing simulated")
            return
        if "--go" not in argv or "--machine" not in argv:
            sys.exit("the timing run starts only on the owner's word: run --machine A --go")
        machine = argv[argv.index("--machine") + 1]
        out = HERE / "SCOPE_P.json"
        if out.exists():
            sys.exit("SCOPE_P.json exists: the timing run is made once")
        load = os.getloadavg()[0]
        t1, s1 = simulate(folder, "schematic.spice")
        t2, s2 = simulate(folder, "stage_p.spice")
    finally:
        shutil.rmtree(folder, ignore_errors=True)        # the outputs are deleted before anything is printed
    ok = s1 == 0 and s2 == 0
    f = t2 / t1
    result = dict(what="timing run of AMENDMENT_2: the 2-period ramp of the nominal cell, schematic then stage-P netlist",
                  utc=datetime.now(timezone.utc).isoformat(timespec="seconds"), machine=machine, host=platform.node(),
                  cores=os.cpu_count(), load_average_before=round(load, 2),
                  wall_schematic_s=round(t1, 3), wall_stage_p_s=round(t2, 3),
                  simulator_status=[s1, s2], f=f if ok else None,
                  scope=scope_of(f) if ok else "not measured: a simulation did not end normally",
                  rule="f <= 6: full; 6 < f <= 10: reduced; 10 < f <= 18: minimal; f > 18: no stage P (PREDICTION.md)",
                  transistors_with_areas=transistors, capacitors_added=capacitors,
                  outputs="deleted before this file was written; never read",
                  ngspice_sha256=digest(NGSPICE), pdk_commit=commit,
                  sha256={str(p.relative_to(HERE.parent.parent)): digest(p) for p in INPUTS})
    out.write_text(json.dumps(result, indent=1) + "\n")
    print(f"schematic {t1:.1f} s, stage-P netlist {t2:.1f} s, f = {f:.3f}, scope: {result['scope']}")


if __name__ == "__main__":
    main(sys.argv)
