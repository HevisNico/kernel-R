# N-cell composition theorem

The proof now covers **every finite directed chain**, with 15*N independent
physical parameters in either the ±0.3% or ±10% relative box. The numerical
proof obligations do not depend on N. Read the
[written theorem and induction](../../proof/reciprocal_composition/THEOREM.md).

The scalable protocol prepares all cells without settings copies, then sends
an exact period-4 train only to the leaf. Its responses teach the next cell,
whose responses teach the next, through to the root. All cells remain alive.

The packet contract closes under one relay:

`P(m,L,J) -> P(m+2,L-4,J)`.

m is slow-prefix length, L is regular-tail length, and J bounds the actual
dates' phase errors around an ideal packet. A cell does not amplify J;
a wire adds its own per-pulse jitter budget. The proof handles the actual
MARK recovery trajectory and the raw current after return, with no reset.

## Guarantees and resource bounds

For K source pulses, `K >= 4*N+12`:

- Cell j from the leaf emits `K-5-2*j`; the root emits `K-2*N-3`.
- Every cell gains exactly 0.2 in b during fast training, from its own
  prepared b to [0.37999,0.38001]. Its active gain ends at its birth gain
  times exp(2.4).
- The root retains at least eight regular-tail outputs. A disconnected
  frozen period-4 probe gives 8/8 afterwards, versus 4/8 for prepared relays
  and 0/8 for the leaf beforehand.
- Cutting any link leaves all its ancestors at their prepared settings.
- Fast-phase total traffic is `N*(K-N-4)`: quadratic at minimum K, despite
  linear source length and time. No chip efficiency benefit is claimed.

## Jitter is an explicit path resource

Each wire delay is a fixed centre plus per-pulse error bounded by sigma_i.
The sum of sigma_i along the chain must be at most **0.15**. All total
delays remain in [0.3,0.4]. This is a sufficient budget, not an impossibility
bound for networks outside it.

| N | Minimum K | Uniform per-link jitter allowance | Root outputs at minimum K |
|---:|---:|---:|---:|
| 1 | 16 | no wire | 11 |
| 3 | 24 | ±0.05 | 15 |
| 4 | 28 | ±0.05 | 17 |
| 16 | 76 | ±0.01 | 41 |
| 100 | 412 | ±1/660 | 209 |

For **fixed wire delays**, sigma_i=0, every finite depth is covered with each
fixed delay independently in [0.3,0.4]. For arbitrary independent per-pulse
jitter, the uniform specialization is min(0.05,0.15/(N-1)). The original
±0.05 per link is covered through N=4 by this contract; it is not silently
kept unchanged at arbitrary depth. Likewise, the old fixed 25-pulse source
is not claimed to supply eight learned-tail outputs for arbitrary N.

## Verify or instantiate

Python and its standard library suffice, with no numerical dependencies:

```sh
python -B certify/reciprocal_composition/tests.py
python -B certify/reciprocal_composition/verify.py \
  results/reciprocal_composition/eps1e-1/certificate.json \
  --entry-certificate results/reciprocal_entry/eps1e-1/certificate.json \
  --entry-code certify/reciprocal_entry \
  --local-certificate results/reciprocal_learning/eps1e-1/certificate.json \
  --local-code certify/reciprocal_learning \
  --cells 100
```

Use `--jitter 0` for the fixed-wire case, or an exact decimal/fraction for
a specific per-link allowance. Unsupported budgets and short source trains
are refused. `--pulses` defaults to 4*N+12. Replace eps1e-1 by eps3e-3 to
replay the narrower box. The same certificate can instantiate enormous N
without allocating one simulation or certificate per cell.

Each box has **81 strict inequalities, 176 enclosures and 12 exact polynomial
identities**, plus authenticated replay of the earlier preparation theorem.
The test suite has 21 positive, budget, algebra and deliberate-refusal checks.
[Example instances](instances.json) illustrate the formulas; they are not the
universal proof. The checker verifies local arithmetic and polynomial algebra;
the universal hybrid-flow induction is the written argument, not full Lean.

## Supplementary numerical checks

The [recorded numerical checks](numerical_checks.json) use the unchanged
single-cell numerical R engine, including actual birth-to-preparation dynamics.
Chains of 1,3,4,16,32 cells match every predicted emission count, two-MARK
recovery change and retained probe. The latter runs include sampled ±10%
parameters and alternating worst-amplitude or random wire errors within budget.
These are cross-checks, not proofs of the boxes or arbitrary N.

```sh
python -m pip install -r requirements.txt
python -B experiments/composition/run.py --out audit_runs/new_composition.json
```

In the English ZIP, open `12_Certified_N_Cell_Composition/RESULTS.html`, or
run `python -B 12_Certified_N_Cell_Composition/code/tests.py` from the extracted
top-level folder. Its dependency code and certificates are in folders 09 and 10.
Optional numerical replay in that ZIP uses
`python -B 02_R_Simulation/composition/run.py --out numerical_replay.json`
after installing `02_R_Simulation/requirements.txt`.

Canonical channel pulses, an exact source cadence, a supplied preparation
schedule and fixed device parameters are assumptions. Arbitrary graphs,
feedback cycles, repeated lessons after saturation, general learned pedagogy
and hardware energy/area gains remain outside the result.
