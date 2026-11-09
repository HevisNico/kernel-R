# Run the coincidence comparison

The runner implements the registered [coincidence benchmark](../COINCIDENCE_BENCHMARK.md)
for the pinned kernel and protocol revisions recorded in the manifest. Use
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
It stops on any violation of these assumptions. This reduction
calculates the scored events without advancing state that cannot affect
those events after the last pulse.

The timed comparator includes the nominal and two cap candidates, plus
doses from 0.60 to 1.50 in steps of 0.05 at duration 12. Within each box
and time scale, rank these common settings by sampled decision failures,
then by their smaller positive or negative slack. Break remaining ties
in the recorded setting order. The winning candidate is an empirical
lower bound on what the unrestricted comparator can achieve. The
discharge ablation uses durations 0.15 and 12. Sample results and
floating-point guards do not certify universal claims.

The output contains the shared sampled coordinates, every setting's
counts and margins, the worst witness for each offset, and a manifest
with file hashes. Scale the coordinates through the runner's
`realizations` function to recover each box exactly. The report counts
use separate definitions for the positive and negative timing classes.
