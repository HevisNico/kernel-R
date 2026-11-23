# XOR3 at the family design point with the C5 inverter (dev seed 9803)

**Development only, nothing preregistered.** One mismatch draw, no noise. The owner's go, relayed by the coordinator,
covered local work only. Record in `dev/cal6_xor3`, run with
`lcal2.py run specs/xor3.json dev/cal6_xor3 9803 solo=1`.

## What is new (all new files; no pushed file changed)

| File | What |
|---|---|
| `config_inverter_c5.json` | the C5 inverter (help mirror w 2, **l 16**, J0 4.0), research/inverter-instances c5c06e00 `design_sweep/C5_hm2x16.json`, as an overlay on config.json's `inverter`. Only help_mirror.l differs from config.json (16 against 4). The design timing is unchanged: emit_early 0.44, emit_late 0.64, window 0, inside the instance gate's (2/5, 13/20] |
| `lcal2.py` | lcal.py's `run` with the overlay; the run stores it in `OUT/overlay.json` |
| `tests/test_inverter_c5.py` | **passes.** It exports the instances package at c5c06e00 and checks the layered inverter against `invinst/netdeck.py`'s C5 cell at `config_netopts.json`:<br>– every design field equal;<br>– all 32 element lines of the cell identical;<br>– the help current H0·unit/tu and the inhibitory current J0·unit/tu = 5e-7 A equal;<br>– the deck's `.lib`, 6 `.param` and 4 `.option` lines equal to `config_netopts.json`;<br>– 92 inverter devices at zero junction areas.<br>Stated differences, asserted in exact form: the network drives khelp, kinb, krst/krstb and the inhibitory reference from the router (`bjref jg 0 i = 5e-07*v(kj)` against `ijref jg 0 pulse(0 5e-07 …)`); supplies and `.include` are shared; the max step (5/20 ns there, 200 ns here) is not a deck line |
| `records2.py`, `fit2.py` | **repeat rule v2** (below) applied when loading a record; fit2.py writes `fit_v2.json` |
| `leancal2.py` | the calibrated Lean file with the front end, closed by **`layered_inverters_chained`** |
| `tests/check_leancal2.py` | check_leancal.py's checks, plus: an inverter emission moved 1 tu later is rejected |
| `invcompare.py` | each inverter in the network against its stand-alone measure |

## A rule fix found on this run: repeat rule v2

- **The problem.** c1_0's parallel scan closed on [1.80007, 1.80387]. Its U repeat (after a silence) landed at 1.80385,
  0.00002 stage below U, and read **silent**. Rule v1 (`instrument.ScanCell._close`) judged agreement by the measured
  states only, so it narrowed the bracket to ±0.00001. In substance the cell fired and stayed silent at the same
  state.
- **Rule v2 (`records2.py`).** A repeat that gives the opposite of its end's outcome makes the group disputed, and the
  bracket becomes the envelope of L0, U0 and the repeats. Otherwise v1 stands.
- It is applied when loading, from the reads kept in the record. `instrument.py` is pushed and stays as it is, and the
  record file is unchanged. Every changed group is listed in `fit_v2.json` `repeat_rule_v2`.
- **Effect.**
  - On XOR3 c1_0 (parallel): ±0.00001 becomes ±0.00190, and s* moves from 1.80386 to 1.80196.
  - Re-applied to the pushed 2x records:
    - NOT1 9801: no change.
    - ANDOR3 9802: c3_0's disputed bracket moves its lower end by 0.00004. Its errors and margins are unchanged (K0
      +325, K3 −914).
  - **So DESIGN_POINT_REPORT.md's verdicts stand.**

## Scans, D4 and repeats (2x stages)

| Cell | Gate | s* parallel | s* solo | \|Δ\| | half brackets | repeats (par / solo) |
|---|---|---|---|---|---|---|
| c1_0 | both | 1.80196 (v2) | 1.80482 | 0.00286 | 0.0040 | **disputed** (U silent) / agree |
| c1_1 | both | 1.29604 | 1.29858 | 0.00254 | 0.0041 | agree / **disputed** (L fired) |
| c2_0 line 1 | either | 2.42128 | 2.42124 | 0.00004 | 0.0074 | agree / agree |
| c2_0 line 2 | either | 2.68381 | 2.68375 | 0.00006 | 0.0073 | agree / agree |
| c3_0 | copy | 2.29996 | 2.29991 | 0.00006 | 0.0038 | agree / agree |

- Every |Δ| is within the half brackets, and all are within `d4_stage` = 0.005.
- 8 of 10 repeats agree. Both disputes are on the both cells of layer 1, at the read-to-read level.
- The training words are `ssFF` at layer 1 and `sssFF` at layers 2–3, and the tests are correct on all 4 patterns
  (00 silent, 10 FIRE, 01 FIRE, 11 silent).

## Verdicts (θ = 100 000), kernel against mirror

| Cell | Gate | need | ε | H, H_drift, H_D4 | errors K0 | K0 | errors K3 | K3 |
|---|---|---|---|---|---|---|---|---|
| c1_0 | both | 2 | 0 | 31, 2, 47 | 259 / 259 | **eligible**, stop margin +2936 | 2687 / 2687 | **room**, +508 |
| c1_1 | both | 2 | 0 | 29, 2, 38 | 235 / 235 | **eligible**, +10262 | 2483 / 2483 | **room**, +8014 |
| c2_0 | either | 3, 3 | 3 | 73, 5, 2 | 302 / 519 | **eligible**, anchor (2,) +5672 | 3277 / 6457 | **no room: anchor (2,) −266** |
| c3_0 | copy | 3 | 0 | 17, 1, 1 | 117 / 117 | **eligible**, +6024 | 1444 / 1444 | **room**, +4697 |

- **c2_0 at K3** fails only on its line-2 anchor under the max rule (testError 6457, the two-port both-lines budget),
  by 266 units. Its training margins pass. Under the one-port rule (testError 3277) the slack would be +2914, and
  XOR3 would have room at K3. The max rule is kept (DECISIONS.md); this is reported, not proposed.

| K | checkLayeredValid | training | reads | chain dates, front, scheduled, latencies | realised | recognition theorem | kernel |
|---|---|---|---|---|---|---|---|
| K0 | true | true | true | true | true | **proved via `layered_inverters_chained`**: trained, arrival windows, output = XOR at every pattern | accepted (5.2 s), agrees |
| K3 | **false** (c2_0) | true | true | true | true | not emitted | accepted (2.9 s), agrees |

- `tests/check_leancal2.py` holds on both files:
  - K0's `computes` uses only propext, Classical.choice and Quot.sound;
  - a raised lesson score is rejected;
  - testError 99999 is rejected;
  - an inverter emission moved 1 tu later is rejected.
- `FitXOR3.lean` (per cell, K0 and K3) is accepted. `dev/cal6_xor3/fit.json` is a copy of `fit_v2.json` for
  leanfit.py.
- The same emitter, on the pushed NOT1 2x record (a scratch copy), proves NOT1's theorem through
  `layered_inverters_chained` too. It is not committed here.

## The inverters in the network against their stand-alone measure

| | n0 | n1 | stand-alone C5 (lot 2: 60 instances, reltol 1e-4, max step 5 ns) |
|---|---|---|---|
| fired with the input absent | 11/11 | 16/16 | 60/60 |
| silent with the input present | 16/16 | 11/11 | 60/60 |
| latch delay (tu, min / median / max) | 0.5130 / 0.5130 / 0.5130 | 0.5125 / 0.5128 / 0.5130 | 0.5033 / 0.5146 / 0.5245 |
| routed emission (router grid 0.02 tu) | 0.52 in every slot | 0.52 | — |
| a second emission | none | none | — |
| emission in the network's (0.44, 0.64] and the gate's (2/5, 13/20] | yes | yes | yes |

- **No sign that the 200 ns step changes the inverter's behaviour.**
  - Each inverter fired or stayed silent as required in every one of its 27 slots.
  - Its latch delay is inside the stand-alone lot's range, near the median, with a spread of 0.0005 tu or less over
    the run.
- **What this comparison cannot show.**
  - The network instance is a different mismatch draw from any stand-alone instance, so the comparison is against the
    lot's range, not the same instance.
  - The silence and firing *margins* (charge distances to vfire) are not observable in this record: only the latch is
    saved.
  - The netopts re-measurement (806b0a3, "being pushed") was not on the remote when this was written, so the reference
    is lot 2 at 1e-4. The amendment's nominal smoke check at the network's directives gives a silence margin of 0.171
    at K0 (0.189 at 1e-4).
- So the stand-alone gate can be used in a network prediction as far as dates and fire/silence go. Margins need
  `xn*.vq` saved, or the netopts lot.

## Cost (CPU minutes, one core)

| Setup | Training (23 lesson slots) | Tests (4) | Parallel scans (70 slots) | Solo scans (76) | **Total** | **Without solo** |
|---|---|---|---|---|---|---|
| 0.3 | 37.2 | 4.5 | 38.2 | 29.8 | **109.9** | **80.1** |

ANDOR3 at 2x, for comparison: 104.9 and 59.6. YIELD_CHECK_2X.md guessed about 70 [G] without solo; the measured 80
is above that guess.

## Open

- The netopts lot (806b0a3): redo the comparison against it when it is on the remote.
- The inverter margins in the network: save `xn*.vq`, or accept the lot's.
- Future scans should close groups by rule v2 directly. Until then records2.py applies it on loading, which needs no
  rerun.
