"""Builds the layout of the cell, block by block, and checks each block.

  python3 -I build.py [block ...]        default: every block, bottom-up

For each block: the Magic cell is written (build/NAME.mag), Magic runs its full DRC and extracts
it, and netgen compares the extraction with the netlist that schematic.py writes for that block
from cell.spice and blocks.spice. A block is used in a larger one only when both are clean.
"""
import json
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))        # also under python3 -I

import devices
import schematic
from floorplan import ARRAY, PLACE, assemble
from tech import BUILD, NETGEN_SETUP

ORDER = ["inv", "nand2", "nand3", "srlatch", "comp_wc4_lc1", "comp_wc16_lc4", "opamp", "rport", "rcell"]


def device_key(e):
    if e.kind == "mos":
        return devices.key_of(e.ref, w=e.par["w"], l=e.par["l"])
    if e.kind == "res":
        return devices.key_of(e.ref, l=e.par["length"])
    return devices.key_of("mim", s=e.par["side"], n=e.par["count"])


def all_devices(blocks):
    """Every device of the cell drawn once: key -> Comp."""
    specs, todo = {}, {}
    for sub in blocks.values():
        for e in sub.elems:
            key = device_key(e) if e.kind != "block" else None
            if key is None or key in todo:
                continue
            todo[key] = e
            if e.kind == "mos":
                nf = schematic.finger_count(e.par["w"])
                specs[key] = (e.ref, dict(w=e.par["w"] / nf, l=e.par["l"], nf=nf, guard=1, topc=1, botc=0, conn_gates=1))
            elif e.kind == "res":
                n = e.par["series"]
                # one strip per resistor in series; a single resistor of 0.35 um is drawn as a snake of
                # two strips, of which Magic reads the length along the bend
                if n > 1:
                    specs[key] = (e.ref, dict(l=e.par["length"] / n, nx=n))
                elif e.ref.endswith("0p35"):
                    specs[key] = (e.ref, dict(l=SNAKE[e.par["length"]], nx=2, snake=1))
                else:
                    specs[key] = (e.ref, dict(l=e.par["length"]))
    gen = devices.generate(specs)
    comps = {}
    for key, e in todo.items():
        if e.kind == "mos":
            nf = schematic.finger_count(e.par["w"])
            comps[key] = devices.mos(key, gen[key], e.ref, e.par["w"] / nf, e.par["l"], nf)
        elif e.kind == "res":
            comps[key] = devices.res(key, gen[key], e.ref, e.par["length"], e.par["series"])
        elif e.par["count"] <= 4:
            comps[key] = devices.mim(key, e.par["side"], e.par["count"], e.par.get("per_row"))
        elif e.name == "cf":
            assert len(ARRAY["dummies"]) == e.par["dummies"] and ARRAY["nx"] * ARRAY["ny"] == e.par["count"] + 1 + e.par["dummies"]
            comps["cfcs"] = devices.cap_array("cfcs", e.par["side"], **ARRAY)
    for c in comps.values():
        c.write()
    return comps


SNAKE = {17.5: 8.0}         # drawn length of each of the two strips -> Magic reads 17.505 um


def check(name, blocks):
    """Magic DRC and extraction, netgen LVS. Returns a dict of results."""
    (BUILD / f"{name}_sch.spice").write_text(schematic.spice(blocks, name))
    tcl = [f"load {name}", "select top cell", "drc style drc(full)", "drc check", "drc catchup",
           f'puts "DRCCOUNT [drc list count total]"',
           'foreach {why boxes} [drc listall why] { puts "DRCWHY [llength $boxes] x $why : [lrange $boxes 0 2]" }',
           "extract all", "ext2spice lvs", f"ext2spice -o {name}_lay.spice", "quit -noprompt"]
    (BUILD / f"{name}_check.tcl").write_text("\n".join(tcl) + "\n")
    log = devices.run_magic(f"{name}_check.tcl", f"{name}_check.log")
    drc = [l for l in log.splitlines() if l.startswith("DRC")]
    count = int(next(l for l in drc if l.startswith("DRCCOUNT")).split()[1])
    p = subprocess.run(["netgen", "-batch", "lvs", f"{name}_lay.spice {name}", f"{name}_sch.spice {name}",
                        str(NETGEN_SETUP), f"{name}_lvs.out"], cwd=BUILD, capture_output=True, text=True, stdin=subprocess.DEVNULL)
    (BUILD / f"{name}_netgen.log").write_text(p.stdout + p.stderr)
    lvs = (BUILD / f"{name}_lvs.out").read_text()
    final = [l for l in lvs.splitlines() if l.startswith("Final result")]
    prop = "property errors" in lvs.lower() or "property errors" in p.stdout.lower()
    match = bool(final) and "match uniquely" in final[-1] and not prop
    return dict(block=name, drc=count, drc_why=[l[7:] for l in drc if l.startswith("DRCWHY")],
                lvs=final[-1] if final else "no result", property_errors=prop, clean=count == 0 and match)


def main(argv):
    BUILD.mkdir(exist_ok=True)
    blocks = schematic.load()
    print(f"{schematic.check_inventory(blocks)} devices, as in the inventory", flush=True)
    comps = all_devices(blocks)
    want = argv[1:] or ORDER
    built, results = {}, []
    for name in ORDER:
        if name not in PLACE:
            continue
        sub = blocks[name]
        built[name] = assemble(sub, comps, built, device_key)
        built[name].write()
        if name in want:
            r = check(name, blocks)
            r.update(devices_below=len(schematic.flat(blocks, name)), **built[name].stats)
            b = built[name].bbox
            r.update(width_um=(b[2] - b[0]) / 200, height_um=(b[3] - b[1]) / 200)
            results.append(r)
            print(f"{name}: DRC {r['drc']}, LVS {r['lvs']}{', property errors' if r['property_errors'] else ''}", flush=True)
            for w in r["drc_why"][:6]:
                print("    ", w[:200])
        if name == want[-1]:
            break
    (BUILD / "results.json").write_text(json.dumps(results, indent=1) + "\n")
    return 0 if all(r["clean"] for r in results) else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
