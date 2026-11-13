# Regenerating exploratory traces without publishing them

No exploratory raw trace is committed. The 50 SHA-256 fingerprints below come
from the already published #119/#121 result records, not from newly selected
simulations. The generators are pinned by source hash in [SHA256.json](SHA256.json).
The files use UTF-8 `json.dumps(rows, sort_keys=True)` with its default separators
and **no trailing newline**, exactly the representation previously fingerprinted.

From the repository root, regenerate all exploratory files:

```sh
python3 -B research/exploratory-reproduction/reproduce.py --output research/exploratory-reproduction/generated
```

Verify an existing generated directory without regenerating it:

```sh
python3 -B research/exploratory-reproduction/reproduce.py --output research/exploratory-reproduction/generated --verify-only
```

Run the automated regeneration/fingerprint checks, including corrupted and missing
file controls:

```sh
python3 -B -m unittest discover -s research/exploratory-reproduction -v
```

`generated/` is ignored by Git. The tests use a temporary directory. They reject
missing, extra or altered files and verify all 50 fingerprints. Existing
exploratory RESULTS.json, oracle calculations and negative controls remain
published normally. No v5 input, registered seed, trace or runner is used here.

The single registered v5 campaign is different: it must never be regenerated
as a substitute for its original evidence. Its original raw files await
explicit authorization before being committed in #120.

## Exact per-file SHA-256

Paths below are relative to the chosen output directory.

| File | SHA-256 |
|---|---|
| `boundary/H140-hard_fill.json` | `e77a9c7be31d9993c4d88e78287837e8db9f851aa2b77c77602382f74be2ea7e` |
| `boundary/H140-hard_max_wait.json` | `3f9a83f9154acca2bbeb8215fc332be7cb55e0fa846ade02ebb9618ed8ddb8ac` |
| `boundary/H140-optimistic_shield.json` | `3f9a83f9154acca2bbeb8215fc332be7cb55e0fa846ade02ebb9618ed8ddb8ac` |
| `boundary/H140-prudent_hard.json` | `64adaf852554a89bd90ddbeb72ace6537bcfb10bd0d6bc671fa33b44f7d438b7` |
| `boundary/H150-hard_fill.json` | `3aa2eb9c091488aa76ab32e33ca4ec7f80426b05525323f56b2382682f6f0b30` |
| `boundary/H150-hard_max_wait.json` | `31704114ad8b8239fd76c8048ed9631e8ef3336ebdaa3992034e332e89721469` |
| `boundary/H150-optimistic_shield.json` | `31704114ad8b8239fd76c8048ed9631e8ef3336ebdaa3992034e332e89721469` |
| `boundary/H150-prudent_hard.json` | `3072e0bc8fb4e1b2a9b582ee84bb2b3d0ae2a81de36c88fdd1fd8c9e6f7efaaa` |
| `economic/high-C1000-hard_fill.json` | `8657887a38215521ae8053d907eeed9bb97ad5f9a0a58f1745823314841fbcc1` |
| `economic/high-C1000-hard_max_wait.json` | `cc77e0608904bb234890717449c86bd8483dda3e90d6c680f51df507171cfa0e` |
| `economic/high-C1000-optimistic_shield.json` | `dffb24ba48217ffed958ad986026f73a1087c86e4497615c290e7236f105cd9f` |
| `economic/high-C1500-hard_fill.json` | `23067438ded09d58709257cc5a37a1f82e874472a0ee129846e2fd96bb2b8296` |
| `economic/high-C1500-hard_max_wait.json` | `cc77e0608904bb234890717449c86bd8483dda3e90d6c680f51df507171cfa0e` |
| `economic/high-C1500-optimistic_shield.json` | `dffb24ba48217ffed958ad986026f73a1087c86e4497615c290e7236f105cd9f` |
| `economic/high-C300-hard_fill.json` | `0c1cec2d7016985cec37a33818c95dfd3387f69197f8ce2a8b906913ffec9ccf` |
| `economic/high-C300-hard_max_wait.json` | `0c1cec2d7016985cec37a33818c95dfd3387f69197f8ce2a8b906913ffec9ccf` |
| `economic/high-C300-optimistic_shield.json` | `0c1cec2d7016985cec37a33818c95dfd3387f69197f8ce2a8b906913ffec9ccf` |
| `economic/high-C3000-hard_fill.json` | `100e768696c44e527b5f1763504237bf1a9224c9ab3a89ff684c5b3fef3ffa81` |
| `economic/high-C3000-hard_max_wait.json` | `cc77e0608904bb234890717449c86bd8483dda3e90d6c680f51df507171cfa0e` |
| `economic/high-C3000-optimistic_shield.json` | `dffb24ba48217ffed958ad986026f73a1087c86e4497615c290e7236f105cd9f` |
| `economic/high-C440-hard_fill.json` | `f4fae7cb6bf2791e56f1f9c0a959c31ff7f37c42894e45535c63a3ba4ea3aec7` |
| `economic/high-C440-hard_max_wait.json` | `f4fae7cb6bf2791e56f1f9c0a959c31ff7f37c42894e45535c63a3ba4ea3aec7` |
| `economic/high-C440-optimistic_shield.json` | `f4fae7cb6bf2791e56f1f9c0a959c31ff7f37c42894e45535c63a3ba4ea3aec7` |
| `economic/high-C660-hard_fill.json` | `48c4caaa14521fdaa8b97ef5c308d8e1ad339f233fc42db07dee8fc9250b19f6` |
| `economic/high-C660-hard_max_wait.json` | `cc77e0608904bb234890717449c86bd8483dda3e90d6c680f51df507171cfa0e` |
| `economic/high-C660-optimistic_shield.json` | `dffb24ba48217ffed958ad986026f73a1087c86e4497615c290e7236f105cd9f` |
| `economic/high-C6600-hard_fill.json` | `f70a0b5551a403711ea646719820afb03dcb84d9140533eb0a4e939f4fde38d4` |
| `economic/high-C6600-hard_max_wait.json` | `cc77e0608904bb234890717449c86bd8483dda3e90d6c680f51df507171cfa0e` |
| `economic/high-C6600-optimistic_shield.json` | `dffb24ba48217ffed958ad986026f73a1087c86e4497615c290e7236f105cd9f` |
| `economic/jump-C1000-hard_fill.json` | `f9938ad6763903931138ebc721eadc9f71b6d88ee052bf146851029f1ac73b9e` |
| `economic/jump-C1000-hard_max_wait.json` | `5e47fa8b7fb8259ff2556008717ecd904d6e47b3e6daf31707479113b44a0281` |
| `economic/jump-C1000-optimistic_shield.json` | `5e47fa8b7fb8259ff2556008717ecd904d6e47b3e6daf31707479113b44a0281` |
| `economic/jump-C1500-hard_fill.json` | `c4879b16095f727d0b808e022c81c31cadff831164be6993f5cb73029a21a103` |
| `economic/jump-C1500-hard_max_wait.json` | `5e47fa8b7fb8259ff2556008717ecd904d6e47b3e6daf31707479113b44a0281` |
| `economic/jump-C1500-optimistic_shield.json` | `5e47fa8b7fb8259ff2556008717ecd904d6e47b3e6daf31707479113b44a0281` |
| `economic/jump-C300-hard_fill.json` | `10163013d77a830a9109fd372ac1d527fa5326c66bf947cb425832ef3d402633` |
| `economic/jump-C300-hard_max_wait.json` | `10163013d77a830a9109fd372ac1d527fa5326c66bf947cb425832ef3d402633` |
| `economic/jump-C300-optimistic_shield.json` | `10163013d77a830a9109fd372ac1d527fa5326c66bf947cb425832ef3d402633` |
| `economic/jump-C3000-hard_fill.json` | `b0d266dba00456e80a798cce288558e06e2c52c264e78de748eb36730a8948bb` |
| `economic/jump-C3000-hard_max_wait.json` | `5e47fa8b7fb8259ff2556008717ecd904d6e47b3e6daf31707479113b44a0281` |
| `economic/jump-C3000-optimistic_shield.json` | `5e47fa8b7fb8259ff2556008717ecd904d6e47b3e6daf31707479113b44a0281` |
| `economic/jump-C440-hard_fill.json` | `01fd992f681d032ece477401754c88fcec9e3e96f5cdb0c02285870fc01e3b0b` |
| `economic/jump-C440-hard_max_wait.json` | `01fd992f681d032ece477401754c88fcec9e3e96f5cdb0c02285870fc01e3b0b` |
| `economic/jump-C440-optimistic_shield.json` | `01fd992f681d032ece477401754c88fcec9e3e96f5cdb0c02285870fc01e3b0b` |
| `economic/jump-C660-hard_fill.json` | `9ad62f3a61c4f0a97177b4cfe5dd6b4fb24e2c402810c3c957a76eee5127c9e1` |
| `economic/jump-C660-hard_max_wait.json` | `5e47fa8b7fb8259ff2556008717ecd904d6e47b3e6daf31707479113b44a0281` |
| `economic/jump-C660-optimistic_shield.json` | `5e47fa8b7fb8259ff2556008717ecd904d6e47b3e6daf31707479113b44a0281` |
| `economic/jump-C6600-hard_fill.json` | `1090ff27894c19ffccd24dc717438f654b5d7b7c8b17d9fd4c751527441d378f` |
| `economic/jump-C6600-hard_max_wait.json` | `5e47fa8b7fb8259ff2556008717ecd904d6e47b3e6daf31707479113b44a0281` |
| `economic/jump-C6600-optimistic_shield.json` | `5e47fa8b7fb8259ff2556008717ecd904d6e47b3e6daf31707479113b44a0281` |
