# Reproduce the exploratory phase-0 diagnostics

These commands regenerate nominal constant-leak action probes only. They do
not execute the old v5 runner, a jump scenario or a registered campaign. Use
an empty output directory: each case is created exclusively. The original
19 attempts (three setup failures before transient analysis, sixteen completed
probes) remain listed in RESULTS.json. The corrected setup below regenerates
the sixteen completed waveforms, not the historical setup failures.

Run from the repository root on Linux x86_64 with Python3.12 and numpy2.3.5.
The installed binary is ngspice44.2; the PDK commit matches the original circuit
campaign. The temporary-file adapter only redirects anonymous temporary files
into the writable output directory; it does not change circuit equations.

```sh
python3 -m pip install numpy==2.3.5
mkdir -p research/sky130-supervisor-map/generated/runtime
PHASE0_RUNTIME="$PWD/research/sky130-supervisor-map/generated/runtime"
curl --fail --location https://deb.debian.org/debian/pool/main/n/ngspice/ngspice_44.2+ds-1_amd64.deb -o "$PHASE0_RUNTIME/ngspice.deb"
python3 - "$PHASE0_RUNTIME/ngspice.deb" <<'PYHASH'
import hashlib,sys
from pathlib import Path
assert hashlib.sha256(Path(sys.argv[1]).read_bytes()).hexdigest() == '4d76721dd91416055b1088cfc58626d4db47b91afda7c73258c0968ba6e4d24e'
PYHASH
dpkg-deb -x "$PHASE0_RUNTIME/ngspice.deb" "$PHASE0_RUNTIME/extracted"
python3 - "$PHASE0_RUNTIME/extracted/usr/bin/ngspice" <<'PYHASH'
import hashlib,sys
from pathlib import Path
assert hashlib.sha256(Path(sys.argv[1]).read_bytes()).hexdigest() == '5854f6506e3e54e0553b687401a5d82aec82229c2c28a93b7eb37b6e079dda84'
PYHASH
git clone https://github.com/efabless/skywater-pdk-libs-sky130_fd_pr "$PHASE0_RUNTIME/pdk"
git -C "$PHASE0_RUNTIME/pdk" checkout 1232782c1b9fab3aacda74d67ce7c92bf7da8105
cat > "$PHASE0_RUNTIME/spinit" <<'SPINIT'
set num_threads=1
SPINIT
gcc -shared -fPIC -O2 research/circuit/bridge_check/runtime/tmpfile_in_workspace.c -o "$PHASE0_RUNTIME/tmpfile.so"
for PHASE0_CASESET in probe map timing threshold leak; do
  python3 -B research/sky130-supervisor-map/probe.py     --ngspice "$PHASE0_RUNTIME/extracted/usr/bin/ngspice"     --pdk "$PHASE0_RUNTIME/pdk"     --runtime "$PHASE0_RUNTIME"     --cases "research/sky130-supervisor-map/$PHASE0_CASESET-cases.json"     --output research/sky130-supervisor-map/generated/replay || break
done
python3 -B research/sky130-supervisor-map/analyze_saved.py   --generated research/sky130-supervisor-map/generated/replay --check-traces
```

The final check requires the exact waveform inventory and every SHA-256 below.
It deliberately ignores new wall-clock measurements. A different solver, PDK,
floating-point environment or extraction changes can fail byte identity; do
not silently update expected hashes. Failed/incomplete simulations are retained
and stop the launcher. The validation tests reject corrupt and incomplete
waveforms, a missing global stimulus node, and a late FIRE masquerading as
successful service. Remote CI checks summaries and these controls without
rerunning ngspice. It does not substitute for the local raw-evidence check.

`probe.py` is the exact executed exploratory prototype (hash recorded per
attempt). Its initial auxiliary `gross_write_*` metadata integration used
arbitrary ringing-current endpoints and is not a delivered-dose measurement.
`analyze_saved.py` removes those fields and reports complete-native-interval
current integrals with omitted durations instead. This numerical correction
reads existing waveforms; it does not rerun or replace a case.

## Waveform fingerprints

Gzip headers use mtime0; these are the original compressed bytes. Raw waveforms
are not committed. Each file below is relative to this directory.

| File | Bytes | SHA-256 |
|---|---:|---|
| `generated/clockonly-380-wired/trace.txt.gz` | 386101 | `e9f8da229b72a3b9acf2b351dc1646fadf55e2872096f75698779453aa8ac5ce` |
| `generated/maint95-382-wired/trace.txt.gz` | 449493 | `f51a7fefe5488c8da273c18d4ce51bb86c57600f4f2f0ab714a39815b9a51981` |
| `generated/maint95-384-wired/trace.txt.gz` | 391259 | `cb1a4d7b6bc238fc35b2a65de57a554ae890ec0393e0bdf7b7390c1c56bb8b7d` |
| `generated/pair-383-wired/trace.txt.gz` | 927087 | `0601f82c49e7e7b212bbd2e5bcb553314cb1822054f5b5508116e2d466d69722` |
| `generated/pair-384-wired/trace.txt.gz` | 865112 | `47c4a79421dec2b819d6d61a4788bf333b875a201a3bc45690dc9328e8f96fb1` |
| `generated/pair-clock-383-leak10/trace.txt.gz` | 871571 | `43a465092751856047c9e9387cf82bd1b6f9c24a5628e5993388cc02d5f8bbb6` |
| `generated/pair-clock-384/trace.txt.gz` | 864490 | `c33f752447925fb9dff1c9412310b955a5501e62afc6b66eae07cf328dadb0ce` |
| `generated/pair-clock-384-100ns/trace.txt.gz` | 1193735 | `48036561eea4baae6abf1185b33258973ab73b4bff6d7899e19c2db8be17873d` |
| `generated/runtime-alternating/trace.txt.gz` | 3044355 | `66ef81225cc73dedfeb43a2f5fbf1b438918dfbe18ed601c7cafaf6e14e94512` |
| `generated/service-384-wired/trace.txt.gz` | 448647 | `cf75e9585fbb27c62c0284d3a592c9184a477be5eed2827fbb1524dbd523c27d` |
| `generated/service-3845/trace.txt.gz` | 452249 | `d49d1bd6ee0a26a2e5257322b710a0d605a29fe93a2eb1889653ecfdb3365aea` |
| `generated/service-3847/trace.txt.gz` | 389551 | `42f37bb440fcf10f473d12b67a61f94d3ba8922a8f8f91422a48b37494a6d446` |
| `generated/service-3848/trace.txt.gz` | 392075 | `ee8eefa11540f5a4df297b193176eca1024bc4a77523d8d68a5f62d673899945` |
| `generated/service-385-wired/trace.txt.gz` | 392975 | `c34b67f22981a655995521aa31f5575d85004a14c9c27ef8ef0925040095169a` |
| `generated/wait-384-leak10/trace.txt.gz` | 220313 | `c679308f74f291bbb98c2c7250ace3f6cd7a138efc1fc583381c6f1614b98640` |
| `generated/wait-384-wired/trace.txt.gz` | 205218 | `b102721106a432d391b95fe41e6ce5e24cb4b376670dc32adc88e4ea155a4b6b` |
