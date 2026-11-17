# Campaign 4, amendment 9: the rehearsal's zero-amplitude check failed; its scope under the injected default

Pushed alone on `research/learned-dnf-circuit-campaign-4`, after `PREDICTION.md` (commit `1596b36`) and amendments
1 to 8 (commits `c14124f`, `d6a75a9`, `41cf88b`, `a167f3c`, `6c5630f`, `424f6f9`, `53d50f3`, `d380da6`), after the
rehearsal's record and before `BEFORE_M.md`. It is the owner's decision. Nothing else in `PREDICTION.md` or
amendments 1 to 8 changes, and neither the code nor the record changes.

**No campaign seed (7501 and up) has been simulated, except as the seed guard's refusals, which simulate nothing.**

## 1. The result

The rehearsal's record is `research/learned-dnf-circuit-campaign-4/rehearsal/run-2-completion/REHEARSAL.json` at
commit `1e74a71` on `research/learned-dnf-circuit-campaign-4-wip` (SHA-256
`b5486033e64d00e30b6279edd3f0c902a5c08cbe6f0e778990a9cfea4fd1032c`), written by the completion of attempt 2
(amendment 8) on the frozen commit `093995b`, from the runs of commit `3156ee4`.

**The zero-amplitude check failed** (`checks.zero_amplitude`). Against the run without noise of the same calendar, the
run under the device model with every source at amplitude 0 and `xtrtol=7` gave the same writes and FIRE events, and
stored voltages within 84.5 nV (tolerance 1 uV); but FIRE dates up to 0.358 us apart (tolerance 0.1 us), and two of
the 110 occurrences, routed to cell c (ports 1 and 2), 0.4 us apart: one step of the 0.4 us grid to which routed
dates are snapped (`net.NOISE_STEP`).

**Every other check passed**, those of the injected model included: reproducibility under both models, the
operating point, memory (17.7 % and 21.5 % of the machine), the split extraction's identity, the gate on the
rehearsal's prediction, the seed guard, the stage files' safeguards, the analysis (`PREDICTED.json` reproduced byte
for byte, every record its waveform), and no seed from 7501 simulated. `all_checks_passed` is `false`, and stays so.

## 2. Its scope

The check is that of `PREDICTION.md` (Rehearsal, "Solver setting of the noisy runs under the device model"): it
tests the setting `xtrtol=7`, which only runs under the device model use, its sources being XSPICE `filesource`
instances. Under the injected default, which amendment 7 (commit `53d50f3`, pushed before this result) makes the
noise model of campaign 4, no run has an XSPICE source or sets `xtrtol` (`PREDICTION.md`, Noise model, the injected
default).

So **the failure does not block a launch wholly under the injected default. It blocks any run under the device
model.** It agrees with V7 of the noise study's validation (`research/network-noise-study/validation/REPORT_A2.md`,
commit `fd25955`, section 5: the zero-amplitude sources change no read or dose beyond the floor, but move the FIRE
latencies); no cause is claimed here.

## 3. The extraction runs' limits

The limits basis gives `extract_reuse` a ratio of 1.335 (the `window` parts, about 347 s against 260 s expected).
Under the device model, those runs' time limits, capped at 1.3 times their expected cost (amendment 5, section 2),
would cut them. Under the injected default there is no extraction and no E stage (`PREDICTION.md`, Noise model, the
injected default), so this does not arise.

## 4. What was known when this was decided (2026-11-17, UTC)

The completion ran from 12:29:24 to 13:17:40 and its record was pushed at 13:23:18 (commit `1e74a71`). This amendment
was decided after that result, from that result and amendment 7 only. No campaign data exists: no seed of 7501 or
above has been simulated.
