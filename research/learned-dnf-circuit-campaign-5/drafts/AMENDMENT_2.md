# Campaign 5, amendment 2: the closure of campaign 5

Pushed alone on `research/learned-dnf-circuit-campaign-5`, after `PREDICTION.md` (commit `a2d8bad`, SHA-256
`36249501a232fb3a9f7e092ac6dee1927767cde852b9519ced7f9c671c110b10`) and amendment 1 (commit `fb5a79f`, SHA-256
`749639d8b8ea5ee8e625b25aecf9bf3843178de38bde5a6072a6b675201afcbe`). It is the owner's decision of 2026-11-18, and it
ends campaign 5. It is the last file of campaign 5.

## 1. The decision

- **Campaign 5 is closed. No claim was tested.** No campaign stage (M1, M2, Q, N1, N2, N3) was launched, `BEFORE_M.md`
  was never written, and no prediction, kernel gate or network run on a campaign instance exists.
- **Seeds 7601 to 7612 were never simulated and are never to be used**, nor are their noise seeds `10 x S + n` for
  `S` = 7601 to 7612 and `n` = 1 to 3.
- **The rehearsal stopped after its stage RQ, by the owner's decision.** RQ had been launched on both machines at
  10:26 UTC, before the owner's decision to stop reached the campaign director. The owner then chose to let it finish,
  deciding nothing on its results. RN and RMEM were never launched. Their stage files and run lists are on the
  rehearsal branch, but no manifest, marker or claim was ever made for them. `REHEARSAL.json` was never written. The
  rehearsal's record is kept as it is (section 2).

## 2. What ran, and where it is kept

Everything ran through the launch kit, in the registered kind, on two machines, four runs at a time. It used the frozen
implementation, the pinned toolchain and amendment 1's inventory rule. The rehearsal branch
`research/learned-dnf-circuit-campaign-5-rehearsal` ends at RQ's marker `10b144e`.

| Stage | What | Frozen code | Result |
|---|---|---|---|
| RC | the chain test, nominal cell | `373cb3d` | ran on both machines. Its deliberately stopped deck stopped at 120 s, as designed. Its wall times enter no rule (section 11.3). The chain test found two defects in the prediction code, both on the nominal cell only (its noise rounds; its untrained control run). They were fixed and refrozen at `f805c20` (CI green), and every chain step then passed. |
| RM | the 6 calibration decks of 7691 to 7693, per machine | `f805c20` | 12 of 12 complete. Guard-on decks took 705 to 734 s, guard-off decks 579 to 603 s, against a limit of 1 850 s: at most 0.40 of the limit. The same deck gave identical measures on both machines. |
| RQ | the cyclic fill of 7692: three runs without noise, one at the need-7 calendar, the untrained control run, per machine | `f805c20` | 10 of 10 complete. Without noise: 699 to 737 s (at most 0.43 of 1 700 s). At need 7: 945 and 965 s (at most 0.45 of 2 130 s). Untrained: 127 and 137 s (at most 0.19 of 740 s). |
| RG | the guards, by direct calls, on each machine | `f805c20` | every refusal fired on both machines, and the allowed case was accepted. |

Machine `a` ran RM and RQ on a "Xeon @ 2.10GHz" and machine `b` on a "Xeon @ 2.30GHz", as recorded under amendment 1.
No machine restarted during a stage. The cases and the mirror mutations passed. The development instances' kernel gate
agreed in Lean and the Python, per checker.

The record kept, each on an orphan branch:

- the checks file `research/learned-dnf-circuit-campaign-5/evidence/rehearsal/CHECKS.jsonl`: 26 checks, all ok, final
  commit `b1bb9ea` on `evidence/learned-dnf-circuit-campaign-5-rehearsal-RC-a` (SHA-256
  `f41b9118e34c2295d563aa077928e4e94618f8851611d9e41623f79397834408`);
- the evidence of each stage and machine, on `evidence/learned-dnf-circuit-campaign-5-rehearsal-RC-a` (`b1bb9ea`),
  `-RC-b` (`2dd0d59`), `-RM-a` (`e993995`), `-RM-b` (`a6c14e4`), `-RQ-a` (`bf2c45c`), `-RQ-b` (`09624e1`) and `-RG-b`
  (`9f92a92`);
- the development instances' `PREDICTED.json` at `f59f6f8` on the rehearsal branch.

## 3. The reason, from the development data only

Campaign 5's development instances (seeds 7691 to 7693, which enter no claim, section 11.1) showed, at stage RM:

- **1 of 3 development instances was measured.** 7691 and 7693 were not measured, because a guard-on FIRE bit
  disagreed with `Z >= theta` on a read (7691 on b, stage 3, both ports; 7693 on b, stage 4, both ports, and on c,
  stage 5, port 2).
- **The measured instance, 7692, was not eligible.** Its stage-3 pair of `a` and the stage-3 teaching read of line 1
  of `c` lacked room. No output had room at `K = 3`.
- **The cause is physical, not a defect.** On every read that did not fire, the guard-on and guard-off decks agreed
  within 0.15 %, so the reads are mapped correctly. But under mismatch, each cell's latch trips at its own level of
  `q`, from 0.981 to 1.022 of the nominal level across the development cells. Every disagreement is a read whose `Z`
  lies between the nominal `theta` and its cell's own trip level.

Section 4.1's rule compares every read with the nominal `theta`, and the budgets of section 4.2 are about 1 %. Against
a spread of about ±2 %, that rule would leave most mismatched instances unmeasured or not eligible. Section 10.5 had
sized the campaign on 92 % measured, from campaign 3. The campaign as preregistered would most likely have ended "not
established" for its primary claim, after about 8 h of compute and 12 seeds. The owner chose to spend neither, and to
close campaign 5.

## 4. Declared slips, none of which changes a result

- The commit message of `240a2f0`, on the RC-a evidence branch, says "20 checks". The checks file it holds has 19.
- Machine `b` first cut a file above 100 MiB into 64 MiB parts (`027fb5e`). It re-cut them at 90 000 000 bytes, as
  section 10.7 requires, in `2dd0d59`.
- The nominal cell's outputs of RC were read for the chain test, as section 11.3 requires. Development outputs were
  read for this closure. No campaign seed's output exists.

## 5. What was known when this was decided

The decision rests on the development instances' calibration (stage RM) and on the statuses and wall times of RC, RM
and RQ. No campaign seed had been simulated. RQ's results decide nothing: its wall times are kept for the design of
any later campaign. Campaign 5's branches are kept on GitHub as its archive and are not merged into `main`.
