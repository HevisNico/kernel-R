# Historical data identifiers

The folder titles, guides, reports and viewer are in English. Original machine
identifiers and raw recordings are retained for compatibility and traceability.
Use this dictionary when reading scripts, JSON keys or result filenames.

| Identifier | Meaning |
|---|---|
| `complet` | Pulses + settings |
| `impulsions` | Pulses only |
| `reglages` | Settings only |
| `sans_transfert` | No exchange |
| `sans_retour` | No feedback to parents / no student feedback |
| `sans_plasticite` | No plasticity |
| `retour_reel` | Actual student feedback |
| `retour_inverse` | Time-reversed feedback |
| `les_deux` | Both transmission channels |
| `monde_A` | A's local source |
| `nouveauté_B` | B's new local source |
| `cadence_C` | C's cadence source |
| `test_ouvert` | External source during open exchange |
| `exercice` | External training exercise |
| `retour_rejoue` | Replayed feedback pulse |
| `analyse.py` | Analysis script |
| `Avant rencontre` | Before meeting a student |
| `Exercices sans retour` | Exercises without feedback |
| `Vrais retours` | Actual feedback |
| `Retours inversés` | Reversed feedback |

## Recording provenance

English localization changes documentation, paths, viewer text and the viewer
exporter. It does not change R's equations, experimental schedules or numerical
results. Raw JSON/JSONL files are copied byte for byte from the recorded runs,
including any original phase names or display labels.

The `source_sha256` fields in recorded plans identify the source at the time of the
original run. They are historical records, not assertions about a later edited
exporter. `05_Verification/SHA256SUMS.json` identifies every other file in this ZIP.

The 55 network checks and 37 teaching checks were performed on the recorded
experiments. Translating the viewer does not constitute another numerical run.
