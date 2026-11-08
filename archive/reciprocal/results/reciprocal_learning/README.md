# Certified local link: A learns from B

The unchanged R laws admit a local, computer-assisted interval proof of the first
feedback-learning effect, from an explicit prepared section.

| Physical parameter box | Decimal certificate | Independent integer replay |
|---|---|---|
| ±0.3% | Pass: 31 strict obligations | Pass: 103 enclosures |
| ±10% | Pass: 31 strict obligations | Pass: 103 enclosures |

The boxes contain all five original per-port parameters, independently in each
of three ports of two cells: 30 real physical parameters. The stronger local
±10% result does not extend A22's global network certificate to ±10%.

## Precisely what is proved

Both cells start READY, with all auxiliaries READY and no active currents;
q and auxiliary charges are within 1e-5 of rest, feedback-port log-gain is within
1e-5 of ln(0.3), b is in [0.17999,0.18001], and reserve E is in [50,100]. Other
gains may be any positive values below their caps.

B receives 16 canonical pulses spaced by 8. Its outputs reach A's port 2 after
a delay independently in [0.3,0.4] for each pulse. There is no other input, no
A->B link and no settings copy in this phase.

For every real choice in these boxes, B emits 13 pulses; A emits 10. A gains
exactly three complete ERROR doses, so

`g_A_after = g_A_before * exp(1.8)`.

The gain enclosure is [1.8148760904722349957656331678657619638566,
1.8149123883570220784068819983289122355248]. An isolated retained-state probe
with plasticity disabled and eight pulses spaced by 20 gives **0/8 before,
8/8 after**. A's b is unchanged. No cell is reset during learning.

Local time 0 corresponds to the prototype's time 320, with terminal observation
at 459.9. The section is preserved by silence from 319.9 to 320. The nominal
recorded states at 319.9 lie in it. **Reachability of this prepared section from
the earlier prototype history over the whole box is not proved here.**

## Proof method

The written proof is in `THEOREM.md` in the ZIP, or
`proof/reciprocal_learning/THEOREM.md` in the repository. It establishes a local
input invariant, exactly three subthreshold full-dose cycles, then a one-response
regime whose ERROR phases are fully protected. At ±10%, a possible ERROR/raw-current
overlap is bounded directly instead of assuming an event priority.

The primary checker uses the byte-identical A22 outward Decimal interval module.
An independent arithmetic implementation uses only Python integers and fractions,
with directed fixed-point operations and explicit series tails for exp/ln. It
replays the sufficient inequalities and verifies that all its enclosures fit
inside the published ones. Fourteen positive/arithmetic/tamper/refusal tests pass.

This is a computer-assisted local theorem with a written model-to-inequality
argument. It is not a complete Lean formalization or a proof of the whole
reciprocal prototype. Physical thresholds/leaks outside the original five-parameter
family, measurement noise, arbitrary faults and silicon behavior are not covered.

## Reproduce from this folder in the ZIP

No third-party dependencies, compiler or network access are required:

```sh
python -B code/certify.py --epsilon 0.003 --out eps3e-3/certificate.json
python -B code/verify.py eps3e-3/certificate.json --out eps3e-3/independent_check.json
python -B code/certify.py --epsilon 0.1 --out eps1e-1/certificate.json
python -B code/verify.py eps1e-1/certificate.json --out eps1e-1/independent_check.json
```

The test runner checks the inherited module's original SHA-256, and additionally
compares its bytes against the frozen-engine original when run in the repository.
From this ZIP folder, run `python -B code/tests.py --report tests_replay.json`.
From repository root:

```sh
python -B certify/reciprocal_learning/tests.py --report results/reciprocal_learning/tests.json
```

Failed sufficient conditions are refusals, not counterexamples to the property.
The next mathematical link is a certified enclosure of the earlier history that
reaches this prepared section. After that, the local theorem can be composed
without treating the observed nominal entry state as a universal assumption.


## Follow-up

The new `reciprocal_entry` result (folder `10_Certified_Section_Entry` in the ZIP)
now proves section entry for the pulses-only READY birth family and composes this
local theorem through time 459.9. The local theorem and its pinned code/certificates
remain unchanged; the new proof does not cover the settings-copy variant.
