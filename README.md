# kernel-R

A hybrid dynamical kernel for pulse-driven learning and adaptation.

This repository contains the R cell definition, our reciprocal-learning and
teaching experiments, and their new local computer-assisted proofs. The older
A22 network engines and historical proof archive stay in the
[upstream repository](https://github.com/HevisNico/a22-going-further).

## Start here

- [R kernel definition](kernel/README.md) and [original model](model/full_model_reference.md).
- [Cadence cascade proof](proof/reciprocal_cadence/THEOREM.md): C's faster cadence reaches A through B, from birth through time 789.9.
- [Birth-to-feedback proof](proof/reciprocal_entry/THEOREM.md): pulses-only initialization through time 459.9.
- [Prepared-section theorem](proof/reciprocal_learning/THEOREM.md): the local A-learns-from-B effect.
- [Reciprocal prototype](experiments/reciprocal/README.md): cells remain alive and learn back from their students.
- [Learned teaching choice](experiments/reciprocal/pedagogy/README.md) and [within-lesson adaptation](experiments/reciprocal/adaptive/README.md).
- [Complete English prototype ZIP](downloads/R_Reciprocal_Prototype.zip): runnable code, recordings, reports and proofs in titled folders.

Extract the ZIP and open `11_Certified_Cadence_Cascade/RESULTS.html` for the latest
proof, or `03_Visualization/OPEN_IN_BROWSER.html` for the recorded three-cell
network. The viewer replays simulations rather than solving the equations.

## Results and scope

| Work | Evidence and boundary |
|---|---|
| Reciprocal R | Numerical three-cell network; parents remain alive and relearn from peer pulses. Schedules and settings copies are supplied. |
| Teaching efficacy | Actual and reversed feedback both improve transmission; that alone does not establish learned pedagogy. |
| Curriculum selection | Native R gains store a teaching choice in an added diagnostic/feedback/readout architecture. |
| Within-lesson adaptation | A learned stopping policy improves on fixed durations; a programmed equivalent rule matches it. |
| Local feedback theorem | ±0.3% and ±10% physical boxes, from a prepared section. |
| Entry and composed theorem | The declared READY birth family reaches that section; pulses-only protocol through time 459.9. |
| Cadence cascade theorem | From birth through 789.9, on 45-parameter boxes: C->B->A; b gains 0.2 in each cell's fast stage; A's frozen period-4 probe improves 4/8 to 8/8. |

The composed proof starts with b near 0.08, establishes one protected full MARK
in each cell, and reaches b near 0.18 at time 319.9. It then proves
`g_A,after = g_A,birth * exp(1.8)` on A's feedback port, with an isolated retained
probe changing from 0/8 to 8/8. The box contains all 30 original per-port physical
parameters of A and B independently.

The cadence extension reaches 789.9, including C's introduction, 20/18/16 fast
emissions in C/B/A and two full recovery MARK doses in each. It covers all 45
per-port physical parameters independently, with per-pulse wire jitter in [0.3,0.4].
The [cadence results](results/reciprocal_cadence/README.md) include retained probes
and causal cuts: without either reverse link, A remains at 4/8.

These ±10% prefix results do not certify the older entire A22 network at ±10%,
the settings-copy variant, open recurrence after 800 or adaptive pedagogy. The new
theorems combine written hybrid-flow arguments with checked interval obligations;
they are not complete Lean formalizations or independently peer-reviewed mathematics.

## Verify the proofs

Python 3.12 and its standard library suffice; no numerical packages or network
access are required.

```sh
python -B -m unittest discover -s tests
python -B certify/reciprocal_learning/tests.py
python -B certify/reciprocal_entry/tests.py --link-code certify/reciprocal_learning --link-003 results/reciprocal_learning/eps3e-3/certificate.json --link-01 results/reciprocal_learning/eps1e-1/certificate.json
python -B certify/reciprocal_entry/verify.py results/reciprocal_entry/eps1e-1/certificate.json --link-certificate results/reciprocal_learning/eps1e-1/certificate.json --link-code certify/reciprocal_learning
python -B certify/reciprocal_cadence/tests.py
```

There are 14 local-theorem, 16 entry/composition and 18 cadence tests. The cadence
checker replays 95 actual input cases, 1,030 strict obligations and 2,533 enclosures
for each physical box, and rechecks the authenticated earlier theorems.
The entry checker
verifies 59 obligations and 170 enclosures, then rechecks the pinned local theorem's
31 obligations and 103 enclosures. The two arithmetic implementations are outward
Decimal intervals and integer fixed point with explicit exp/ln series tails.

## Restore recordings or run a fresh experiment

The recorded data are kept once in the ZIP instead of duplicating dozens of
large JSON files in the source tree. Restore them with their SHA-256 checks:

```sh
python -B tools/prepare_recordings.py
```

This creates ignored `audit_runs/` inputs. Existing different local outputs are
never overwritten. The full records remain directly inspectable inside the ZIP.
To run a fresh network:

```sh
python -m pip install -r requirements.txt
python -u -B experiments/reciprocal/simulate.py --out audit_runs/new_reciprocal
python -u -B experiments/reciprocal/analyse.py --out audit_runs/new_reciprocal
python -u -B experiments/reciprocal/validate.py --out audit_runs/new_reciprocal
```

NumPy 2.3.5 and SciPy 1.17.0 are pinned. Use a new output directory for each run.
The individual experiment guides provide further teaching and adaptation commands.

## Rebuild the ZIP

```sh
python -B tools/prepare_recordings.py
python -B experiments/reciprocal/package.py
```

The output is `dist/R_Reciprocal_Prototype.zip`, constrained below 30,000,000 bytes.
The provided download is a pinned research snapshot; rebuilding an archive need
not preserve ZIP timestamps, while its source/data manifest remains verifiable.

Optional viewer QA uses Node.js: `npm install`, then `npm run check:viewer`.
`npm run check:browser` additionally needs an installed Playwright Chromium binary.
The original reports distinguish DOM/SVG checks from unavailable full-browser tests.

## Reference boundary and limitations

The retained `kernel/` and `model/` documents preserve the original definition and
its hashes. Their historical A22 engine locations refer to the upstream project,
which is not vendored here. See [provenance](docs/PROVENANCE.md).

General pedagogy, semantic memory, new waveform invention and chip energy/area
benefits remain unproved. Observation bins, feedback coding, lesson primitives
and copying rules are supplied components unless explicitly learned in a test.
R's monotone parameters impose saturation and forgetting limits. The
[proposed invention protocol](experiments/reciprocal/adaptive/INVENTION_PROTOCOL.md)
is a future experiment, not a completed result.

## How this was built

This work is done with two AI assistants, **Claude** (Anthropic) and **ChatGPT** (OpenAI), under the direction of Nicolas Breuillaud.

## License

Source code is [MIT](LICENSE). Documents, proofs, data, certificates and other
non-code material are CC BY 4.0 under [LICENSE-docs.md](LICENSE-docs.md).
