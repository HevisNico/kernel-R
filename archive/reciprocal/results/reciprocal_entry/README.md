# Prepared-section entry is now proved for the pulses-only prototype

This is the follow-up to folder 09's conditional local theorem. It proves entry
from the declared near-nominal READY birth family and composes that entry with
"A learns from B", through time 459.9.

| Physical box | New entry obligations | Independent replay | Old local theorem |
|---|---:|---:|---|
| ±0.3% | 59 pass | 170 enclosures | Reverified and composed |
| ±10% | 59 pass | 170 enclosures | Reverified and composed |

The 59 obligations consist of 55 strict inequalities and four closed inclusions.
The linked local theorem adds 31 strict inequalities and 103 enclosures. Sixteen
new arithmetic, positive-case, metadata, dependency and refusal tests pass.

## What the completed chain says

A starts at time 0. B is introduced at 160 with the same specified birth family:
READY modes, near-rest q/m, log-gains within 1e-5 of ln(0.3,1.2,0.3), b within
1e-5 of **0.08**, and E in [50,100]. This includes the original nominal initial
states and adds small state uncertainty. Both cells' 30 original per-port
physical parameters vary independently within the relative box, fixed in time.

Under the original **pulses-only** source/contact schedule, each cell receives
exactly one protected full MARK in its warm-up. This raises b by exactly 0.1,
to [0.17999,0.18001]. At 319.9, both cells meet every hypothesis of the previously
certified prepared section. No cell is reset and no settings value is copied.

The following B->A phase therefore has the previously proved three full ERROR
doses for A's feedback port, now **from the birth family rather than an assumed
entry state**. The feedback gain is multiplied by exp(1.8), in
[1.8148760904722349957656331678657619638566,
1.8149123883570220784068819983289122355248]. The isolated retained probe is
0/8 before that feedback phase and 8/8 afterwards.

The pulse counts through time 459.9 are A=38, B=27. The prefix decomposes as:
A learns its own source (12 emissions), A teaches B (A16/B14), then B teaches back
(A10/B13). The nominal recorded run agrees; no numerical sampling establishes
the proof, which uses real-box interval inequalities and an induction.

## Why one recovery update is enough

The protected pulse arrives while the slow initial b≈0.08 has not reopened the
main cell. Even allowing the full possible b increase, its SLOW integral through
ERROR end is at most 0.827486, below ln(2.5)≈0.916291. Thus the entire MARK and
ERROR are protected. The MARK adds exactly 0.1 to b.

The lower integral by three units after that input exceeds 0.978514, above the
return target: the main cell must reopen before then. Later inputs arrive after
the now-faster stable return, before 6.990787 units. This is a certified bound on
the continuous b(t) dynamics; recovery is not set by a test script.

## Scope

This closes the entry gap for `impulsions`, the native pulse-learning variant.
It does not certify the variant with settings copies at time 160 or the fully
open reciprocal phase after time 800. C's introduction at 480 is outside this
prefix. Initial auxiliaries are READY, not the broader historical A22 family
that also permits residual ERROR. Main thresholds/leaks and other constants stay
at their original values; the boxes concern the original five per-port parameters.

The proof is computer-assisted with outward rounding, a written model argument,
and independent integer arithmetic. It is not a complete Lean formalization or
a hardware validation. Folder 09's conditional theorem remains unchanged; this
folder provides its verified entry bridge for the stated configuration.

## Reproduce from folder 10 in the ZIP

Only Python's standard library is needed. Folder 09 is the pinned dependency.

```sh
python -B code/certify.py --epsilon 0.003 --link-certificate ../09_Certified_A_Learns_From_B/eps3e-3/certificate.json --link-code ../09_Certified_A_Learns_From_B/code --out eps3e-3/certificate.json
python -B code/verify.py eps3e-3/certificate.json --link-certificate ../09_Certified_A_Learns_From_B/eps3e-3/certificate.json --link-code ../09_Certified_A_Learns_From_B/code --out eps3e-3/independent_check.json
python -B code/certify.py --epsilon 0.1 --link-certificate ../09_Certified_A_Learns_From_B/eps1e-1/certificate.json --link-code ../09_Certified_A_Learns_From_B/code --out eps1e-1/certificate.json
python -B code/verify.py eps1e-1/certificate.json --link-certificate ../09_Certified_A_Learns_From_B/eps1e-1/certificate.json --link-code ../09_Certified_A_Learns_From_B/code --out eps1e-1/independent_check.json
python -B code/tests.py --link-code ../09_Certified_A_Learns_From_B/code --link-003 ../09_Certified_A_Learns_From_B/eps3e-3/certificate.json --link-01 ../09_Certified_A_Learns_From_B/eps1e-1/certificate.json --report tests_replay.json
```

In the repository use `certify/reciprocal_entry/` as the code folder and
`results/reciprocal_learning/` plus `certify/reciprocal_learning/` for the pinned
dependency. `THEOREM.md` contains the complete entry and composition argument.
