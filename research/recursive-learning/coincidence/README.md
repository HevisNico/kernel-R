# Run the coincidence comparison

The runner implements the registered [coincidence benchmark](../COINCIDENCE_BENCHMARK.md)
for the kernel and protocol revisions recorded in the manifest. The reduced
equations and constants are transcribed from the pinned Lean source.
The numerical implementation has no machine-checked correspondence to
the Lean semantics. Use
CPython 3.12.14 and NumPy 2.3.5. From the repository root, install the
dependency and run from a committed checkout.

```sh
python -m pip install -r research/recursive-learning/coincidence/requirements.txt
python research/recursive-learning/coincidence/run.py output/coincidence \
  --runner-commit "$(git rev-parse HEAD)"
```

The two cells are independent up to the timestamp comparison. Evaluate
each cell once per training label, setting and read date, then combine
those results for the full set of test trials. Sensor event dates follow
the READY response and subsequent exponential decays. Split the training
pulse at ERROR entry, the end of writing, and contact with the gain cap.
Integrate the varying gain contribution with 32-point Gauss–Legendre
quadrature. Use 42 bisections on the increasing response branch for
each MARK and FIRE. The optional quadrature order 16 is a convergence
check. Coincident pulse expiry, cap contact and timer expiry end their
respective flows independently and leave the continuous state intact.
Timestamp equality is evaluated using the strict aperture from the
protocol.

Conservative work bounds include the rate of memory updates and keep
the reserve gate open. The runner checks silence at training and on
untrained reads, verifies that the trained read fires before ERROR,
and uses the minimum protection duration to exclude a second report.
It stops on any violation of these assumptions. A completed row records
`report_guards_passed`. Missing, extra, training and untrained reports
are excluded by those checks for the scored cases. The runner does not
count those events on an independently simulated trajectory. This reduction
calculates the scored events without advancing state that cannot affect
those events after the last pulse.

The timed comparator includes the nominal and two cap candidates, plus
doses from 0.60 to 1.50 in steps of 0.05 at duration 12. Within each box
and time scale, rank these common settings by sampled decision failures,
then by their smaller positive or negative slack. Break remaining ties
in the recorded setting order. The winning candidate is an empirical
lower bound on what the unrestricted comparator can achieve. The
revised discharge sweep uses durations 0.15, 0.20, 0.25, 0.30, 0.35,
0.40, 0.45, 0.50, 0.55, 0.60, 0.65, 0.70, 0.80, 1, 1.5, 2, 4, 8 and 12.
The revised sample keeps the 621 original points and appends four corners.
For both trained ports and both cell orders, the fast cell has high ERROR
entry, low ERROR exit and low FIRE. The slow cell has the opposite
realization. Evaluate all registered offsets and jitter endpoints at each
corner. Sample results and
floating-point guards do not certify universal claims.

The output contains the shared sampled coordinates, every setting's
counts and margins, the worst witness for each offset, and a manifest
with file hashes. Scale the coordinates through the runner's
`realizations` function to recover each box exactly. The report counts
use separate definitions for the positive and negative timing classes.

The `--fabrication` option runs one fabrication radius. Joining shard
CSVs in the order 0, 0.003, 0.1 with a single header reproduces the
unsharded CSV. All shards use the same sampled coordinates.

For the independent DOP853 spot check, install
`validation-requirements.txt` and run the following from the repository root.

```sh
python research/recursive-learning/coincidence/verify_ivp.py > ivp.csv
```

The script integrates the continuous state and locates the mode and cap
events on 24 trained-read trajectories, including a case with ERROR before
pulse expiry. It compares the resulting gain and first read report with
the reduced calculation. This checks selected trajectories with two
numerical methods.
