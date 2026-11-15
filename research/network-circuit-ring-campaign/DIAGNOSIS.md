# Diagnosis of the N-own failure

Added after the one analysis. It changes no generated file: [`REPORT.md`](REPORT.md) and
[`RESULTS.json`](RESULTS.json) stay as generated, and the verdict of N-own stays **fails**.

The diagnosis of the failing port-run (`a-7301-ring-noisy1`, port `c1`, pulse 5, word `ssss?FFFFFF`) is
`research/network-circuit-ring-campaign-3/DIAGNOSIS_N_OWN.md`, on the branch
`research/network-circuit-ring-campaign-3-commitment`, commit `e69fab5` (SHA-256
`d1ba8c0f60f5395cc507ff92a109a9776b848d476aec9a10ee0eb38756cd656b`), accepted by the owner. In short: the read
was a clean FIRE with no write and no charge; the counted "write" is a spike of about 4 ns on the write signal at
the edge of the testbench at 6 units after the start of the pulse, inside the interval in which the analysis
counts writes. One such spike exists in each of campaigns 1 and 2, both in noisy runs.
