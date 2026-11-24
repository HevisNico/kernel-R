# The yield lot, rule 2: stage D only, before the freeze (written before any run)

**Development; the owner's addition A of 2026-11-24 with his corrections (relayed by the coordinator).**
- **Supersedes** YIELD_LOT_RULE.md (d78fcd38, unpushed). Its seeds, its plans (dev/yield_lot/) and its report are
  kept; its §4 fallback is replaced below.
- **Committed alone** and **pushed to GitHub before any yield-lot run**: GitHub's record of the push proves that the
  rule came first.
- **The lot is not run until the owner's go.**

## 1. What the lot is for, and only that

- The lot serves **only to fix the campaign sizes**, by §4.
- **No rule, check, gate, budget, threshold or cell design** is changed after its rates are seen. Any such change
  needs a new rule, written and pushed first, and the lot's rates then no longer apply.
- Its 56 seeds are dev seeds:
  - they **enter the campaign's exclusion list**;
  - they **count for no claim**;
  - its predictions are evidence of nothing.

## 2. Seeds and runs

As YIELD_LOT_RULE.md §1–§3, unchanged:
- **The 56 seeds:** the first 56 integers from 6101 upward that are absent from dev/predraw/EXCLUDED.json and whose
  noise seeds 10 S + n are absent too.
  - The exclusion file has sha256 3b2811f95bb635150f30a678da7d3ae6e0afad924826ad76a9eae2c2111f31a3, over 13841
    integers from all 201 branches.
  - Assignment: 24 ANDOR3 (6102–6156), 24 XOR3 (6157–6204), 8 NOT1 (6212–6225). They are listed in full in
    YIELD_LOT_RULE.md §6.
- **What runs:** stage D only, through campaign_run3.py with `steps_until: "D"`, on 12 machines, with the plans
  dev/yield_lot/PLAN_K01..K12.json.
- **What is reported:** k0/n and k3/n per group, with 90 % Wilson intervals.

## 3. The measuring code, pinned (sha256)

**If any file below changes after the lot, the lot's rates no longer hold**, and the sizes must be fixed again.

**The layered package**, research/layered-networks at research/layered-stage-d 4fd209ebab:

| File | sha256 |
|---|---|
| `stage_d.py` | `05c1dbda691b8ae43cd09670b2d42344f332113ac346e79e1a43326730dfc2d6` |
| `stage_d3.py` | `42192944a9290f9a2c2ec4de4ecce563e8ec291f0c02a7401af1ca304373df50` |
| `stage_d4.py` | `60e284248ccf3664964cc2b55018ea5f5b512b410e459559d91625d4053a442f` |
| `stage_d5.py` | `163ce3e2b391d4286cee6cad3f21278128c095ebd65b166cab50d6b25b036a64` |
| `fit.py` | `410af8ba910f7468b70872cc72a15ffbb1598199b22a72199565551c3b7d3414` |
| `fit3.py` | `e78c84b3c2cd7126337e52bd275ec27686c0ee851b5844cf0cae26d951256431` |
| `instrument.py` | `96ef53a13362d751be49a9685cc33d374078808bf7e11edaef7e22c789c46cbd` |
| `scores.py` | `f1e1fb0e9b4b3dce9f1694fe3f4e92078a55e0254516c6ab57d14440e6a0af7b` |
| `records.py` | `d88d2bfbefd92cc609f3b726da501e13f931a0e986d12e7769a258f0f47f983c` |
| `records2.py` | `f568903913f1cb5e99bd4743e85c1ba60866ac446ec1c2215181f68f2ef54882` |
| `deck.py` | `3ae17285870c4842ba4d64bf47a96d157b711df73e61f0c25e30da973db25412` |
| `run.py` | `8edcc2dbfd37fe65bed143a1b3313419bd8e1da62a0f4fcf4a7c9278f7aec893` |
| `session.py` | `da1dd65099af18e53e70323719b2d0f31493a10d91f81faccbf6316170630079` |
| `spec.py` | `32d132a4399d6211d62eb7865865c36f7bddaf4a0f1bc7eef67d51e00c208e7f` |
| `seal.py` | `5678f909bff8363cc70326aa417e08fd4a7a2005cf30a5118e66156e20a4b250` |
| `lcal2.py` | `e236d7e24d623c1ce6870f571463b9a11c376f3899aa2c2015a874ddcaa5a984` |
| `config.json` | `1ccf88fcc32234cf3bad438c80702856172d8eb5dd8f472a9d26cd044fdbcdb6` |
| `calibration.json` | `cf430226cb5cb972b8eb61b047f725c57e2e34f1433058b15b9a16437bedc0d0` |
| `config_inverter_c5.json` | `5e5f4e6588d213e8eccd3ad9a5a1ed53121a10a8e5af3c692b23bd36415b7d53` |
| `specs/not1.json` | `973defa0c748d5e33bcb7d7077a919d8f6344ed77d1bb836ecd8c9808a470b26` |
| `specs/andor3.json` | `6084bbe95ca1a42ce294829fbe11b98969ea9c89b60f044691b9d9b12e4f3535` |
| `specs/xor3.json` | `d009d901d6f2ffaec457a48d40e66cf67f3a16a117894f56e4bf0f9b78d63b0d` |
| `campaign_run.py` | `9ccb3f7f80ad2905a5aab19df7a06a496ea81e1a11b64dd144b32c1656996056` |
| `campaign_run2.py` | `f24d5cbcde4b31939e9767c0e179d8587183b3d9d7170f551a7f79cee3ee7240` |
| `campaign_run3.py` | `469e057b2dd5c3eb64576209a0ea904ee2e89d8ff9ce01415b1db860614ff3f6` |
| `envcheck_layered.py` | `73ed8bd389b687dccf82d837bcae7e0312cdb30b3bfe0d30f1a072f5f217e28f` |
| `yield_lot.py` | `d04f471a488d3c04dbc73744b7124d2eceb2ab339302928f17ed57a5b3dc29f7` |

**The inverter kit**, research/circuit/inverter/instances at research/inverter-instances d599300d51fcf3a1a4c33d103b89827f8ac4da41:

| File | sha256 |
|---|---|
| `invinst/__init__.py` | `4a9079a83b4b58489ed4b5ce2301ae1d0996d6ccc8060d5447bbace5847b5b11` |
| `invinst/campaign.py` | `89e98751ae97a99264d87a46714145b3f1e04f5769c27e56e15a41cc8c01409c` |
| `invinst/cell.py` | `3af942a166d5a39b5399da71fdbb693c6207013a60fa2d23a4e99cdeb1df725e` |
| `invinst/driver.py` | `c49471690c360db4d2c27bec558e054b045a2ec165eabdbbd968c286fe6a168b` |
| `invinst/driver2.py` | `567d1278713ca2477aa3444fdba67d1803462db38d108702c143e7d45374775d` |
| `invinst/gate.py` | `c490b64668c7688b80d4430c7a521a51e705ba5e1fca5146f37a5e047b0b9efd` |
| `invinst/indeck.py` | `92e0e159a2c7936b6cfb4431ea70ba002217ec17f367b480df3084af3e950e3f` |
| `invinst/measure.py` | `88836a2afc40f2d66b75fb216507f1fb3d26d12e97081472bcbb3457c2cf69a8` |
| `invinst/measure2.py` | `14510c53f6ebf46cb7bd473adf17af416f7d691a8187e5906cc35381909f2e2d` |
| `invinst/netdeck.py` | `1f3d83c51c9f08c2bf460c680994fe2fe89e1ebc30b65e92c5adc1f958d01be8` |
| `invinst/sim.py` | `f9fe47c7a9f3a8787c9b8e498843a4a7d51a1fbd6c042b2430de45aa89851b60` |
| `config.json` | `8fd92a1a09c4b71a3c187fd5ad166583bb931d2b6eccf888be5470c23305a5e7` |
| `config_netopts.json` | `42bc7f8073a6e6dd5a23734219d38d405ed032cdc58725a1fb06264b7071fe3e` |

**The controls tree** (only campaign_run3's tree check reads it; the lot runs no stage N): research/layered-networks
e15b494a6569c1cc0be6499d0bcebd28110005e6.

**The environment**, checked on every machine by envcheck_layered.py, which refuses any difference, and recorded in
each OUTROOT's ENV.json:

| Item | Pin |
|---|---|
| numpy | 2.3.5 (research/circuit/requirements.txt) |
| ngspice | 42, executable sha256 820658317b0b54035208da41936fd6871ce924036e5ea4113a4168b821b7fc45 |
| SKY130 models | research/circuit/pdk at 1232782c1b9fab3aacda74d67ce7c92bf7da8105 |
| Lean | 4.35.0 |

- Each machine's ENV.json `static_sha256` is reported with the lot.
- The machines may differ in OS or kernel. That is recorded, and allowed by no rule beyond the pins above.

## 4. The sizing rule

- **Thresholds kept:** "established" needs ≥ 20 counted instances at K0 and ≥ 5 at K3.
- **Ceiling:** 280 core-h.
- **Rates used:** L0_g and L3_g, the lower ends of the 90 % Wilson intervals (z = 1.6449) of group g's eligible and
  room rates. These are conservative.
- **NOT1 = 60, always.**
- **Size per three-layer group g** (ANDOR3, XOR3):
  - N0_g = ⌈20 / L0_g⌉;
  - N3_g = ⌈5 / L3_g⌉;
  - N_g = max(N0_g, N3_g) when N3_g ≤ 80;
  - when k3_g = 0 or N3_g > 80, N_g = N0_g, and the group's K3 is declared in advance in PREDICTION.md as "K3 not
    expected to be established";
  - N_g ≤ 80.
- **Expected cost per instance** (core-min): gate + D + N0 + r3_g × 3 × noisy round, with r3_g = k3/n. To this are
  added the D4 audits on every 6th instance, the U controls and one duplicate per group.
- **If the total exceeds 280 core-h**, cut one instance at a time, stopping as soon as it fits:
  1. XOR3, from N_XOR3 down to N0_XOR3;
  2. then ANDOR3, from N_ANDOR3 down to N0_ANDOR3;
  3. then both alternately below N0, XOR3 first.
  - A group cut below N3 (or N0) is declared in advance "K3 (or K0) not expected to be established".
  - Every group is still run and reported by the established rule.
- **Fewer machines (the owner's correction):** with m machines, 8 ≤ m ≤ 12, the sizes are **the same**, and the
  window is longer: at most 280 / (4 m) hours on 4 cores per machine.
  - There is no reduced ceiling and no NOT1 cut.
  - **Below 8 machines, the campaign is postponed.**
- **Implementation:** yield_lot.py `size` (pinned above). Its output, dev/yield_lot/SIZES.json, is the input of the
  draw.
