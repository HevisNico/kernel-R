# Family campaign (a): the independent rerun of the frozen code (amendment 1)

Run on M3, 2026-11-22, at the tips named in `FREEZE.txt` (`df3851b2`), each branch fetched by name and checked out
detached. No simulation: ngspice never ran.

## Tips

| Role | Branch | Commit |
|---|---|---|
| freeze marker | research/function-family-campaign-freeze | df3851b241433d3608d2e895014ed678cba3f0c1 |
| amendment 1 | research/function-family-campaign | f8a8809d0317b13657901f0116d90ec8bebd5053 |
| net | research/function-family-campaign-net | 70d9d79514d8acb70c4ab582d7a02ccb7282a55f |
| impl | research/function-family-campaign-impl | 920413ecfcd95721bd52af88584dbbddbf8ed6c5 |
| FF | research/function-family-dev | 0c003fbf8fa5ded0a53aae64b97baa022bc33db1 |
| REPO | research/learned-dnf-circuit-campaign-6-impl | ecfcd1c1517048b3305fdc5ed2ac9f481242ba67 |
| FUP | research/learned-dnf-circuit-campaign-6-followup | 56f9e83e5eb5e2037bcf89ea8d9d33643543d1fc |
| PREP | research/learned-dnf-circuit-campaign-7-prep | b956efe4d311420fb0410f861face9dfe9ae0f4b |
| GEN | research/learned-dnf-generator | 4fca62563a6d03b4f1e45027cb21e76fbc000df2 |

The generator branch's tip was `b81e1e46`, one commit after `4fca6256`. That commit adds only `layered/`.
`4fca6256` was checked out, as `FREEZE.txt` names it.

## Checks before any run

- **Files.** All 17 files that `FREEZE.txt` lists match their SHA-256. `family_predict.py` is `00b6a516…`. Also checked:
  the 7 hashes of `PREDICT_FREEZE.txt` and the 38 files of `GATE_FILES_SHA256SUMS`. All match.
- **Lean.** `lean-4.35.0-linux.tar.zst` comes from the leanprover/lean4 v4.35.0 release. Its SHA-256 is `7289597a…`,
  equal to the pin, checked before unpacking. `bin/lean` is `bf8d54e4…`, equal to the pin. It reports version 4.35.0,
  commit `eb6cafb7`.
- **REAL_7802.** `7802-quiet`, extracted as data from `evidence/learned-dnf-circuit-campaign-6-c1-Q-a` at `7361a444`.
- **TOPUP_EV.** It holds `M1/8301-cal-on-unary` from `evidence/function-family-topup-M1` (`525bb26a`) and
  `M3/DUP/8301-cal-on-unary-dup` from `evidence/function-family-topup-M3` (`06dce775`). The parts were joined, and
  every file was checked against its machine's `SHA256SUMS`.

## Commands

`PY=/home/user/owner-prep/venv312-dev/bin/python` (Python 3.12.3, numpy 2.3.5, M3's `ENV_M3.json`).
`PYTHONPATH=FUP/dev:PREP/dev:FF/dev:impl:net`, with each name a folder of the matching worktree:
`…/research/learned-dnf-circuit-campaign-6-followup/dev`, `…/research/learned-dnf-circuit-campaign-7-prep/dev`,
`…/research/function-family/dev`, `…/research/function-family-campaign/impl`, `…/research/function-family-campaign/net`.

```
cd FF/dev   && $PY -B test_family_predict.py REPO GEN                    > test_family_predict_output.txt
cd net      && $PY -B test_family_net.py REPO                            > test_family_net_output.txt
cd net      && REAL_7802=…/7802-quiet $PY -B test_family_reads.py REPO   > test_family_reads_output.txt
cd impl     && LEAN=…/lean-4.35.0-linux/bin/lean $PY -B test_campaign.py REPO GEN TOPUP_EV > test_campaign_output.txt
cd impl     && $PY -B test_integration.py REPO GEN net                   > test_integration_output.txt
cd GEN/research/learned-dnf-generator && LEAN=…/bin/lean bash gencheck.sh \
    FF/dev/predict_freeze/gates/synthetic/Family_Syn_{X1,X2,F4,F2,F3}.lean > gencheck_output.txt
```

Each command's stdout and stderr went to its file.

## Results

| Output | Verdict | Frozen |
|---|---|---|
| test_family_predict_output.txt | 14 tests, OK | 14, OK |
| test_family_net_output.txt | 33 tests, OK | 33, OK |
| test_family_reads_output.txt | 23 tests, OK, the real 7802-quiet test included | 23, OK |
| test_campaign_output.txt | 36 tests, OK, with LEAN set (M8 through the kernel) and TOPUP_EV given | 36, OK |
| test_integration_output.txt | 16 tests, OK | 16, OK |
| gencheck_output.txt | passed: X1, X2, F4, F2, F3 each compiled, 10 theorems each on a subset of [propext, Classical.choice, Quot.sound] | pass on all 5 |

No test was skipped. Each test output equals its frozen copy line for line, except for the time in "Ran N tests in X s".

## Not checked

- The outputs are not byte-identical to the frozen ones, because the run times differ (amendment 1, "Not checked").
- This is a rerun on one machine, once. It is not a GitHub workflow.
