# Lean verification scripts

From `proof/lean`, run the source checks directly and the other checks as
modules. For example:

```sh
python scripts/check_sources.py
python -m scripts.evidence.generate_evidence --check
python -m scripts.negative.check_hybrid_crossing_negative
```

- [Negative controls](negative/) compile the valid contract and check that
  its deliberately altered counterpart fails.
- [Evidence tools](evidence/) regenerate the exact endpoint checks, replay
  robust certificates, export Lean's trusted declarations and produce the
  CI report. The generated manifests live in [../evidence](../evidence/).
- [Fixtures](fixtures/) contain checked examples used by the controls.

The [Lean reproduction guide](../README.md#reproduce) and the
[CI workflow](../../../.github/workflows/lean.yml) give the full commands.
