# Qualification evidence: commands and byte identities

These are exploratory phase-1 diagnostics, not future registered scenarios.
Do not use these commands to launch a registered campaign or to replace a
failed registered run. The owner launch kit has a separate durable no-relaunch
protocol. Raw exploratory traces are not committed to Git.

Use the ngspice42 binary, pinned PDK and Python/numpy identities in
[the environment table](launchkit/README.md#exact-environment). Local calibration
used the existing sandbox portability adapter and a one-thread ngspice startup:

```sh
mkdir -p ../qualification-runtime
printf 'set num_threads=1\n' > ../qualification-runtime/spinit
gcc -shared -fPIC -O2 research/circuit/bridge_check/runtime/tmpfile_in_workspace.c -o ../qualification-runtime/tmpfile.so -ldl
```

Set PHASE1_NGSPICE and PHASE1_PDK to their absolute locations. From the repo
root, the exact case sets can be regenerated into a fresh exploratory folder:

```sh
python3 -B research/sky130-supervisor-qualification/calibrate.py --ngspice "$PHASE1_NGSPICE" --pdk "$PHASE1_PDK" --runtime "$PWD/../qualification-runtime" --cases research/sky130-supervisor-qualification/capacity-cases.json --output "$PWD/../qualification-replay"
python3 -B research/sky130-supervisor-qualification/calibrate.py --ngspice "$PHASE1_NGSPICE" --pdk "$PHASE1_PDK" --runtime "$PWD/../qualification-runtime" --cases research/sky130-supervisor-qualification/capacity-followup-cases.json --output "$PWD/../qualification-replay"
python3 -B research/sky130-supervisor-qualification/calibrate.py --ngspice "$PHASE1_NGSPICE" --pdk "$PHASE1_PDK" --runtime "$PWD/../qualification-runtime" --cases research/sky130-supervisor-qualification/domain-cases.json --output "$PWD/../qualification-replay"
python3 -B research/sky130-supervisor-qualification/calibrate.py --ngspice "$PHASE1_NGSPICE" --pdk "$PHASE1_PDK" --runtime "$PWD/../qualification-runtime" --cases research/sky130-supervisor-qualification/numerics-cases.json --output "$PWD/../qualification-replay"
python3 -B research/sky130-supervisor-qualification/calibrate.py --ngspice "$PHASE1_NGSPICE" --pdk "$PHASE1_PDK" --runtime "$PWD/../qualification-runtime" --cases research/sky130-supervisor-qualification/timing-cases.json --output "$PWD/../qualification-replay"
python3 -B research/sky130-supervisor-qualification/report.py --generated "$PWD/../qualification-replay" --check-traces --deterministic-only
```

For a comparable runtime factor run all six timing probes serially with no
other simulator load. Wall times are not replay identities. Noise traces are
also not byte-reproducible from setseed; the timing case file contains three
noisy probes and three quiet controls. The final command checks the **23
noise-off trace hashes**, not the three fresh Gaussian realizations. It never
updates the reference hashes after a mismatch. Cross-platform library and
solver differences must be investigated if hashes differ; exact executable
identity alone is not a proof of identical external libraries.

[RESULTS.json](RESULTS.json) publishes the SHA-256 and byte count of each of
130 files: the deck, compressed raw waveform, metadata and both simulator logs
for each diagnostic. Every waveform is gzip-compressed once with mtime=0;
these exact bytes, including the three unique noise realizations, are retained
in `sky130-phase1-calibration-evidence.zip` separately from Git. Archive SHA-256:

```
1fa489e21bbd459e8897c4940671a62b1d3e25a96f1c853fe9c985b66189eb22
```

The archive contains 130 untouched files and an EVIDENCE_INDEX.json, not the
PDK, symlinks or duplicate plaintext waveforms. To check the original retained
archive after extracting to a fresh directory:

```sh
python3 -B research/sky130-supervisor-qualification/report.py --generated /absolute/path/to/extracted-evidence --check-traces
python3 -B research/sky130-supervisor-qualification/report.py --generated /absolute/path/to/extracted-evidence --check
```

The second command verifies source and deck identities, raw hashes and full
waveform re-extraction against saved metadata and RESULTS.json. It does not
rerun ngspice. The CI summary check explicitly does not claim to read these
excluded raw files. The synthetic launcher test is separate and may be run
in fresh synthetic fixtures as described in launchkit/README.md.
