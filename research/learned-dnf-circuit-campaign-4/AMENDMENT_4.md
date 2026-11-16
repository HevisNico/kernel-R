# Campaign 4, amendment 4: which verdict of the noise study's validation decides campaign 4

Pushed alone on `research/learned-dnf-circuit-campaign-4`, after `PREDICTION.md` (commit `1596b36`) and amendments
1 to 3 (commits `c14124f`, `d6a75a9`, `41cf88b`), **before `BEFORE_M.md` and before any result of the noise study's
validation is known**. It is the owner's decision.

**No campaign seed (7501 and up) has been simulated, and nothing here depends on campaign-4 data or on any result of
the validation.**

## 1. What changed in the noise study

`PREDICTION.md` (Noise model, first item) cites the validation criteria
(`research/network-noise-study/VALIDATION_CRITERIA.md`, commit `5a24d10`) with their amendments 1 (commit `4169e91`)
and 2 (`research/network-noise-study/VALIDATION_AMENDMENT_2.md`, commit `771e8b7`) only. The validation has since two
more amendments:

- amendment 3, `research/network-noise-study/VALIDATION_AMENDMENT_3.md`, commit `59bf911`: machine 5's restart;
- amendment 4, `research/network-noise-study/VALIDATION_AMENDMENT_4.md`, commit `dcec16d`: it names the rule of
  `validation/SPLIT_A2.md` that amendment 3 overrides.

Amendment 4's point 4 has the final analysis report two verdicts: one under the criteria with their amendments 1 to
4, and one under `SPLIT_A2.md` as first written, where machine 5's 33 runs count as missing.

## 2. Which verdict decides campaign 4

In `PREDICTION.md` (Noise model) and in amendment 2 of the noise study, **"the device model is validated" means the
verdict under the validation criteria and their amendments 1 to 4**. The second verdict, under `SPLIT_A2.md` as first
written, does not decide campaign 4. This is the owner's decision: the noise study's amendment 4 reports both
verdicts, but it does not say which one governs.

If the validation report gives no verdict under the criteria and their amendments 1 to 4, or gives "not validated"
or "not established" under them, the device model is not validated for campaign 4, and the second item of
`PREDICTION.md` (Noise model) applies: the owner chooses the model by a file pushed alone before stage M.

## 3. If the two verdicts differ

If the two verdicts differ, `BEFORE_M.md` says so, and the campaign's report states it beside every noisy claim. It
is also stated beside N-out, N-own and N-word, and beside the noise constants, if the validation's values enter them.

## 4. Unchanged

The rule for the noise constants (each the maximum of its value in decision 5 and the validation's value), and
everything else in `PREDICTION.md` and amendments 1 to 3.

## 5. What was known when this file was written (2026-11-16)

The validation's attempt 2 was still running, under its no-look rule. No summary, verdict or partial result of it had
been seen by the campaign director.

The campaign director checked the two amendments of section 1, read-only, on the noise study's branch
`research/network-noise-study-phase0`: `VALIDATION_AMENDMENT_3.md` at commit
`59bf9111e74a5f4c6264a37449b977ff867729cb` (2026-11-16T16:22:18Z), SHA-256
`40bb6e9df4a889e50fc7514a7506d0a200f5a070ee36a7fae5dec348e7f02f6a`; `VALIDATION_AMENDMENT_4.md` at commit
`dcec16dabd2f2658ec21438749185432633907f6` (2026-11-16T16:31:53Z), SHA-256
`032bc8610af090595ba3ef4efd4b5edfc7c73b3cea4ac47f41a59fe4ddc24c08`. Amendment 4's point 4 says what section 1
says, and names no governing verdict.

While this file was under review, the noise study pushed `research/network-noise-study/validation/NOTE_VERDICT.md`,
alone, at commit `9f36aa18fc93c30bad9c881141d638dda9592496` (2026-11-16T16:56:06Z), SHA-256
`9b88961f7bbb43cb8526ae2812e19f147614524a8ced2c7eb068482ae0451fcc`, "before any summary of attempt 2 is looked at".
It says that the verdict under the criteria with their amendments 1 to 4 governs any use of the model, campaign 4
included, and that the verdict under `SPLIT_A2.md` as first written is reported beside it for transparency only. The
campaign director read it, read-only; it holds no result. It agrees with section 2, which stands as the owner's
decision for campaign 4.
