# Campaign 5: the smoke run of M8's eligible path

One run without noise on the nominal cell (model section `tt`, no seed), need 4 with the skew slots, made on
2026-11-17 from 19:01:56 UTC by `run4.py` at commit `8b6be778e36a3193e76eb3fae4b6c83a9035aa87` of
`research/learned-dnf-circuit-campaign-5-wip`. It ran outside the kit and before the freeze, under the pinned toolchain,
for one purpose: CI's case of M8's eligible path (`m8_case.py`), which needs a waveform. It is not a run of the
rehearsal or of the campaign, and enters no check and no claim.

Its waveform (`evidence/trace.raw`, 64 320 092 bytes, SHA-256
`e78fe008ecef96e780914089a8de483cb6eb077414e2463a2ff9f19441d33887`, as `record.json` gives it) is on the branch
`evidence/learned-dnf-circuit-campaign-5-smoke`, at the same path. Wall time 669 s, alone on the machine.
