# FREEZE_PINS.json against the dff747c4 pins

155 files at dff747c4, 114 now: 5 added, 46 dropped, 1 changed. No pinned file imports, runs or names a dropped one (checked over every pinned .py: import statements and file-name literals). Every other group (configuration and specs, Lean gate, kernel, inverter kit, the two report groups) is unchanged.

| File | Change | Why |
|---|---|---|
| EXCLUDED.json | added | the seed draw's exclusion list (draw_seeds.py reads it) |
| EXCLUDED_PRINT.txt | added | the seed draw's exclusion list (draw_seeds.py reads it) |
| analysis.py | added | MUST_BE_PINNED (campaign.py) |
| campaign.py | added | MUST_BE_PINNED (campaign.py) |
| campaign_template.json | added | MUST_BE_PINNED (campaign.py) |
| sealpush.py | changed | the branch_creation fix (2011058e) |
| TEMPLATE_CAMPAIGN.json | dropped | superseded template (campaign_template.json) |
| TEMPLATE_CAMPAIGN_2.json | dropped | superseded template (campaign_template.json) |
| TEMPLATE_CAMPAIGN_3.json | dropped | superseded template (campaign_template.json) |
| TEMPLATE_CAMPAIGN_4.json | dropped | superseded template (campaign_template.json) |
| TEMPLATE_CAMPAIGN_5.json | dropped | superseded template (campaign_template.json) |
| analyze.py | dropped | superseded analysis (analysis.py) |
| analyze10.py | dropped | superseded analysis (analysis.py) |
| analyze2.py | dropped | superseded analysis (analysis.py) |
| analyze3.py | dropped | superseded analysis (analysis.py) |
| analyze4.py | dropped | superseded analysis (analysis.py) |
| analyze5.py | dropped | superseded analysis (analysis.py) |
| analyze6.py | dropped | superseded analysis (analysis.py) |
| analyze7.py | dropped | superseded analysis (analysis.py) |
| analyze8.py | dropped | superseded analysis (analysis.py) |
| analyze9.py | dropped | superseded analysis (analysis.py) |
| campaign_run.py | dropped | superseded driver (campaign.py) |
| campaign_run10.py | dropped | superseded driver (campaign.py) |
| campaign_run11.py | dropped | superseded driver (campaign.py) |
| campaign_run12.py | dropped | superseded driver (campaign.py) |
| campaign_run13.py | dropped | superseded driver (campaign.py) |
| campaign_run14.py | dropped | superseded driver (campaign.py) |
| campaign_run15.py | dropped | superseded driver (campaign.py) |
| campaign_run16.py | dropped | superseded driver (campaign.py) |
| campaign_run17.py | dropped | superseded driver (campaign.py) |
| campaign_run2.py | dropped | superseded driver (campaign.py) |
| campaign_run3.py | dropped | superseded driver (campaign.py) |
| campaign_run4.py | dropped | superseded driver (campaign.py) |
| campaign_run5.py | dropped | superseded driver (campaign.py) |
| campaign_run6.py | dropped | superseded driver (campaign.py) |
| campaign_run7.py | dropped | superseded driver (campaign.py) |
| campaign_run8.py | dropped | superseded driver (campaign.py) |
| campaign_run9.py | dropped | superseded driver (campaign.py) |
| controls5.py | dropped | superseded by controls4 (run from the noise tree); nothing pinned imports it |
| disk_peak.py | dropped | disk measurement of the superseded chain; nothing pinned imports it |
| disk_peak2.py | dropped | disk measurement of the superseded chain; nothing pinned imports it |
| tests/check_noise_identity2.py | dropped | a control check run in the noise tree at noise_commit, not in this tree; nothing pinned imports or names it |
| tests/check_noise_sources.py | dropped | a control check run in the noise tree at noise_commit, not in this tree; nothing pinned imports or names it |
| tests/check_ref_level.py | dropped | a control check run in the noise tree at noise_commit, not in this tree; nothing pinned imports or names it |
| tests/test_analyze10.py | dropped | test of a superseded driver or analysis |
| tests/test_campaign_run13.py | dropped | test of a superseded driver or analysis |
| tests/test_campaign_run14.py | dropped | test of a superseded driver or analysis |
| tests/test_campaign_run15.py | dropped | test of a superseded driver or analysis |
| tests/test_campaign_run16.py | dropped | test of a superseded driver or analysis |
| tests/test_campaign_run17.py | dropped | test of a superseded driver or analysis |
| yield_lot.py | dropped | pre-campaign yield lot; nothing pinned imports it |
| yield_lot2.py | dropped | pre-campaign yield lot; nothing pinned imports it |
| (tools) kernel_library | changed | the text now names campaign.py build_kernel and analysis.py, in place of the superseded driver and analysis |

Kept and noted: controls2/3/4.py and noise2/3.py stay pinned (campaign.py runs controls4 from the noise tree at noise_commit; this tree's copies are in the import closure as before). noise4_gate/sitecustomize.py stays pinned (indeck_noise4.py puts that folder on the path).
