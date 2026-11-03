# Model references: current R protocol and historical A22 snapshot

For the current R cell, read the [kernel guide](../kernel/README.md) and
[model-to-Lean correspondence](../docs/MODEL_LEAN_CORRESPONDENCE.md).
The [repository overview](../README.md) states the finite-chain theorem.

[`CURRENT_SPEC.md`](CURRENT_SPEC.md) is a **historical A22 specification**:
216 cells, 28 training pulses, terminal time 230. Its title and references use
the upstream repository's context; it does not specify the current kernel-R
finite-chain protocol. Its original name and bytes are retained because the
[local-learning source manifest](../results/reciprocal_learning/SOURCE_MANIFEST.json)
authenticates it. The [full model reference](full_model_reference.md) is also
retained as source material.

Six relative links in the frozen A22 snapshot refer to files kept upstream,
not files distributed in this focused repository. Read them at the pinned
upstream commit `269483eb2c6227b369cffb2c46f86eaae5272bb8`:

| Snapshot reference | Upstream source |
|---|---|
| General-epsilon coverage | [Coverage extension](https://github.com/HevisNico/a22-going-further/blob/269483eb2c6227b369cffb2c46f86eaae5272bb8/proof/inherited_eps1e-3/extensions/COVERAGE_THEOREM_GENERAL_EPS_EN.txt) |
| C7/C6/P | [Lemma extension](https://github.com/HevisNico/a22-going-further/blob/269483eb2c6227b369cffb2c46f86eaae5272bb8/proof/inherited_eps1e-3/extensions/LEMMAS_C7_C6_EN.txt) |
| Lemma E rounding | [Correction guide](https://github.com/HevisNico/a22-going-further/blob/269483eb2c6227b369cffb2c46f86eaae5272bb8/proof/inherited_eps1e-3/extensions/lemma_e_outward_rounding/README.md) |
| Calendar bridge | [Coverage bridge](https://github.com/HevisNico/a22-going-further/blob/269483eb2c6227b369cffb2c46f86eaae5272bb8/proof/inherited_eps1e-3/extensions/CALENDAR_COVERAGE_BRIDGE.md) |
| Future invariance | [Future extension](https://github.com/HevisNico/a22-going-further/blob/269483eb2c6227b369cffb2c46f86eaae5272bb8/proof/inherited_eps1e-3/extensions/FUTURE_INVARIANCE_GENERAL_EPS_EN.txt) |
| Proof index | [Upstream reading order](https://github.com/HevisNico/a22-going-further/blob/269483eb2c6227b369cffb2c46f86eaae5272bb8/proof/README.md) |
