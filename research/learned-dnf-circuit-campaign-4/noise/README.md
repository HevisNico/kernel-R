# Campaign 4's frozen copy of the noise study's code

PREDICTION.md (commit `1596b36`), Noise-model extraction: "a frozen copy of the noise study's extraction code in
this folder", with its own seed guard. The four files come from the noise study's branch
`research/network-noise-study-phase0` at **commit `74e93b4`**, the code that the GO of the validation's attempt 2
released (`validation/GO`, commit `341aac1`). Their SHA-256 there:

| File | SHA-256 at 74e93b4 | Changed here |
|---|---|---|
| `phase0/devnoise.py` | `016234f5fa43e2b83e09f0438a0482ae4ddd0d4152aab1ccbdb12ade676dd5a2` | yes |
| `phase0/model.py` | `38630ca29a81619b0793d918ea9b026da0ade18858a48fd544f1d08484917cce` | yes |
| `phase0/pilot.py` | `40ea3b678c61ae2a135bc01447dfd0b6a769ecb9cc1b846a9dc14abe4ca5c0c6` | yes |
| `phase0/noisegen.py` | `2415336b5f31de902ae47d573f76081dd855c6f20355df82d73374ddd2085b45` | no |

The changes, and nothing else (`git diff` against the originals shows them):

1. **Seed guard** (`pilot.py`): `ALLOWED_SEEDS` is empty, so every mismatch seed is refused unless the campaign's
   runner (`../run4.py`) allows the one seed of its run, after checking that it is one of 7501 to 7500 + I and that
   the run is inside a launch of the kit. The noise study's own guard on 7101 to 7103, in its own files, is unchanged.
2. **One output per run** (`devnoise.py`): `extract_cell` takes a `port`, and `extract_part` runs one output of one
   cell in one state; `merge` puts the parts back in the order of a single-run `extract`. Orchestration only: the
   method and its deterministic result are unchanged, which the rehearsal checks (the merged parts equal the
   single-run extraction byte for byte).
3. **The isolation check per cell** (`model.py`): `op_match` takes `only`, the cells whose isolated deck is compared
   with the full deck, so that each cell's check runs once, in that cell's first output run.
4. **Reuse of the trip value** (`devnoise.py`): `REUSE_TRIP`, False by default (the code of the noise study
   unchanged). True skips the second DC sweep of the transfer step and keeps the trip value found in the
   operating-point step. It is set from BEFORE_M.json, which adopts it only if the noise study's identity check
   passes.
