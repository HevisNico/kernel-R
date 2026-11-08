# Certified cadence cascade: C -> B -> A

The pulses-only prototype is now covered from the declared READY birth family
through time **789.9**, including C's introduction and fast-cadence feedback.
The proof covers 45 independently varying per-port physical parameters, for
both ±0.3% and ±10% boxes, and independent per-pulse wire delays in [0.3,0.4].

| Result | C | B | A |
|---|---:|---:|---:|
| Emissions in the fast block | 20 | 18 | 16 |
| Additional full recovery MARK doses | 2 | 2 | 2 |
| b at 639.9 | birth b + 0.1 | birth b + 0.1 | birth b + 0.1 |
| b at 789.9 | birth b + 0.3 | birth b + 0.3 | birth b + 0.3 |
| Frozen period-4 probe before | 0/8 | 4/8 | 4/8 |
| Frozen period-4 probe after | 8/8 | 8/8 | 8/8 |

The active ports are C port 0 and B/A port 2. The pre-fast C baseline differs
from the settings-copy run because this theorem uses pulses only. A has no
direct fast source. Cutting either reverse link leaves A at its pre-fast
settings and its retained probe at 4/8.

Read the [complete written proof](../../proof/reciprocal_cadence/THEOREM.md).
The machine artifacts are in [eps3e-3](eps3e-3/certificate.json) and
[eps1e-1](eps1e-1/certificate.json), with independent integer replay reports.
Each certificate contains the per-input case trace, root witnesses, sufficient
strict inequalities, outward enclosures and authenticated prefix dependency.
For each box, the new checker validates 95 input cases, 1,030 strict inequalities
and 2,533 enclosures, in addition to replaying both earlier theorems. The test
suite has 18 positive, nominal-conformance and deliberate-refusal checks.

## Reproduce

Python and its standard library suffice. From the repository root:

```sh
python -B certify/reciprocal_cadence/tests.py
python -B certify/reciprocal_cadence/verify.py \
  results/reciprocal_cadence/eps1e-1/certificate.json \
  --entry-certificate results/reciprocal_entry/eps1e-1/certificate.json \
  --entry-code certify/reciprocal_entry \
  --local-certificate results/reciprocal_learning/eps1e-1/certificate.json \
  --local-code certify/reciprocal_learning
```

Replace `eps1e-1` by `eps3e-3` for the narrower box. Regenerate by replacing
`verify.py <certificate>` with `certify.py --epsilon 0.1 --out <new-file>`
and keeping the four dependency options. Use a new output file.

In the English ZIP, run `python -B 11_Certified_Cadence_Cascade/code/tests.py`
from the extracted top-level folder. The tests locate the bundled dependencies.
The standalone checker likewise accepts the code and certificate paths in
folders 09, 10 and 11 as explicit arguments.

The integer checker verifies the root signs rather than trusting the Decimal
root search. Both arithmetic implementations follow the same written induction;
this is not independent mathematical peer review or a full Lean formalization.
The result stops before settings copies at 800 and open reciprocal exchanges.
It proves acquisition of port response and recovery cadence, not learned
pedagogy in general or a hardware advantage.
