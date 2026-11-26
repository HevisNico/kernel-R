# The campaign integration branch: research/layered-campaign-int (addition D, rebuilt 2026-11-24)

**Development, local.** One branch that holds every piece the campaign runs.
- **Its base is origin/main 3f27bb36**: Merge pull request #189, which already holds the inverter bridge and its two
  CI edits.
- **Added on top**, without a merge commit: each source tip's changed files (against its merge base with main),
  checked out file by file.
- A file whose version on main differs from the source's base would stop the construction. None did.
- The branch **only adds files** with respect to main (git diff --name-status 3f27bb36: A only).

| Source | Tip | Merge base with main | Files added |
|---|---|---|---|
| research/layered-stage-d (local) | 70a0f66b18 | 822e02a5 | 706 |
| research/layered-networks (noise2, controls2, check_duplicate) | e15b494a | 822e02a5 | 29 |
| research/inverter-instances (the kit) | d599300d | 806b0a36 | 20 |
| proof/inverter-bridge | — | already in main (#189) | 0 |
| noise3, controls3 (seal_log) | not landed | — | — |

**Rule for later tips:** rebuild the same way, from main and the new tips. A conflict stops the construction and is
reported.

The earlier construction (based on research/layered-stage-d, e5a2622e/e2165368) is kept locally as
research/layered-campaign-int-old and is superseded.
