ROBUST ENTRY FROM BIRTH

Read THEOREM.md. The original prepared-section assumption is discharged for a
specified pulses-only warm-up: each READY-born cell receives sixteen port-0
pulses at 0,8,...,120, with intercell routes closed until 160. No state reset or
settings copy occurs; port 2 remains untrained until the chain phase.

Persistent charge noise prevents entry into the old delta-wide resting band.
The new section uses radius rho=1e-5+2*nu and a noise-dependent recovery interval.
At epsilon=.1,nu=.002,alpha=0, b lies in approximately
[.17996777281787,.18003222718213]. Its wider interval is substituted into all
36 local continuation inequalities and they are rechecked.

The eight birth certificates each check 150 enclosures and 48 strict inequalities.
They cover the warm-up, widened section and local continuation, with source and
semantic checks. All 12 unit/regression tests pass. The numerical campaign has
39 configurations through N=32, with 176 cells, 2112 warm-up emissions and 5448
chain emissions. Every cell is simulated continuously from birth. Checkpoints
at 159.9 test the section, and frozen probes test retained port-2 learning.

From the package root:
  python -B birth/tests.py -v
  python -B birth/verify.py birth/certificates/eps0.1_nu0.002_alpha0.json
  python -B birth/validate.py
  python -B birth/validate.py --verify-record

Reports, traces and unit logs are in evidence/. The original entry theorem was
consulted as a reference and is saved under reference/; this preparation protocol
is different from its A-teaches-B calendar. It requires externally accessible
preparation inputs for every cell. Entry from only a single network source and
birth states with residual ERROR phases remain outside the claim. No Lean work
or GitHub write is part of this deliverable.
