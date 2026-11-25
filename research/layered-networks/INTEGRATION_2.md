# The campaign integration branch, prepared for the freeze (2026-11-25, local)

INTEGRATION.md (the construction rule) is kept as it is. This note records the state prepared for the freeze.

**Base**: origin/main 3f27bb36 (Merge pull request #189, which holds proof/inverter-bridge, the Lean gate). The branch
only adds files with respect to it (git diff --name-status 3f27bb36: A only).

| Source (fetched by name) | Tip | Merge base with main | Files (A only) |
|---|---|---|---|
| research/layered-stage-d | b74d9514 | 822e02a5 | 863 |
| research/layered-networks (noise2/3, controls2–5, noise4) | 458bc7a6 | 822e02a5 | 74 |
| research/inverter-instances (the kit) | d599300d | 806b0a36 | 20 |
| proof/inverter-bridge (the Lean gate) | in main (#189) | — | 0 |

- 957 source entries cover 956 paths. The one path in two sources (research/layered-networks/CAMPAIGN_PLAN_DRAFT.md) has
  the same blob in both. No source path exists on main. So there is no conflict.
- On top: INTEGRATION.md (earlier), this note and FREEZE_PINS_DRAFT.json (the files the freeze must pin, by sha256,
  computed on this tree).
- This commit adds the 17 files stage-d gained since 7d7acf1a:
  - campaign_run8/9/10, analyze7, envcheck_layered2, ref_extract, sealpush2, yield_lot2;
  - tests/check_noise_identity2 and the tests of these;
  - the yield-lot aggregate.

## Update notes moved here from INTEGRATION.md

They were appended to INTEGRATION.md in local commits a181f08a and 7d7acf1a after it had been pushed (bb5ae626). INTEGRATION.md is restored to its pushed content, and the notes are kept here, verbatim:

| research/layered-networks (noise3, controls3: the sealed stage N) | 3ce53cdc | e15b494a | 15 |

**Update (2026-11-25):** 3ce53cd's 15 files (noise3, controls3 and their tests and report) and stage-d's campaign_run6.py and analyze6.py added, still additions only against main.

**Update (2026-11-25, later):** research/layered-networks ee58b78 and 458bc7a (controls4, controls5, noise4_budget.json and their reports and records) and stage-d's campaign_run7.py, indeck_noise4.py, noise4_gate/ and their tests and smoke records added; additions only against main.

## Update (2026-11-25): envcheck_layered3

stage-d 26a2d9f8 adds envcheck_layered3.py (Lean's real toolchain binary resolved through elan and pinned to bf8d54e4, the elan proxy recorded outside static), campaign_run11.py (ENV by envcheck_layered3, refused unless every check holds) and tests/test_envcheck3.py. FREEZE_PINS_DRAFT_2.json supersedes FREEZE_PINS_DRAFT.json, which is kept as it is.
