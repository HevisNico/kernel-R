# D3 under the owner's decision (2026-11-26): 40 GB at launch, comparisons exempt from the guard. Development only

## The rule
- **TEMPLATE_CAMPAIGN_4.json** (703e8b8a…): disk_launch_gb 40, disk_guard_gb 20, and disk_guard_exempt naming the
  comparisons. campaign_run16 refuses templates 1–3 and plans made from them.
- **campaign_run16.py:** campaign_run15 with the comparison steps C<n> (kind "C"), and only those, exempt from the
  guard. They free disk: the round's raw is deleted after an agreeing comparison, once its digest and extract exist.
  - A start below the guard is logged in OUTROOT/GUARD_EXEMPT.json.
  - Stage D, the N rounds, U, the duplicates and every other step stay guarded.

## The test (tests/test_campaign_run16.py, 2/2)
- **The forced low-disk condition:** the guard threshold is set 1000 GB above the free space.
- **C1** runs and is done, and is logged as exempt. The round's raw (19,433,552 bytes, a NOT1 N0) is then deleted
  after the extract; free space rises by 16,424,960 bytes, net of the 3 MB extract.
- **Held:** a new N step (N2) is held, with no status entry and nothing run. So are a step named C2 of kind N, and
  stage D.

## The peak under the rule (disk_peak2.py → dev/disk_peak/DISK_PEAK_2.json)
The model and sizes are disk_peak.py's; the margin is 40 − 20 = 20 GB.

| machines | worst peak | expected peak | margin left at the worst |
|---|---|---|---|
| m = 12 | 14.72 GB | 13.55 GB | 5.28 GB |
| m = 8 | 16.64 GB | 14.98 GB | 3.36 GB |

Every machine is within the margin at m = 12 and at m = 8. If a machine still meets the guard, its comparisons run and
delete their raws, so it does not stop.

## Also
tests/test_analyze10.py copies the instance folders with symlinks=True (not pushed, fixed in place). It now passes on a
root whose inv/ holds dangling pdk links (final dry run K08).
