# controls4.py: the stage-N trace, and the inverter noise sources read from a trace

**Development only, nothing preregistered.** NOT1, dev seed 9801. New files only: `controls4.py`,
`tests/check_controls4.py`, `tests/check_noise_sources.py`. noise3.py, controls3.py and NOISE3_REPORT.md stay as
pushed.

## The defect, and the fix

- noise3.stagen, and so controls3 stagen, wrote no trace.raw and no trace.digest.json. Every controls3 duplicate
  therefore failed `tests/check_duplicate.py` on the missing trace (reported by the stage-D worker).
- **controls4.py** is the same sealed stage N (noise3's) and untrained run (controls2's, which already wrote its trace).
  It adds two things:
  - the trace, written by `controls2.write_trace` before the session closes;
  - in a noisy run, the inverters' noise nodes (xn<j>.nzm, nzh<x>, nzj<x>) saved into the trace.
- The pipeline should call `controls4.py stagen …` and `controls4.py untrained …`, with the same flags as controls3.

| Check (NOT1 9801) | Result |
|---|---|
| `tests/check_controls4.py`: controls4 noiseless against the controls3 run with the same seal | input.spice byte-identical; noisy_record.json identical with cost removed; trace.raw and trace.digest.json present, the digest matching the data |
| Duplicate pair, noisy round 1 (noise seed 98011), through `tests/check_duplicate.py` **unchanged** | **DUPLICATE IDENTICAL**. input.spice identical; record identical; trace.raw 33.6 MB with identical data, `Date:` the only excluded line; session.log identical with its 354 and 358 progress lines excluded and nothing else differing |

## The inverter's injected sources, read from the trace

`tests/check_noise_sources.py dev/controls4/not1_N1a`, saved as `dev/controls4/not1_N1a/noise_sources.json`. Values
are read at the sources' own sample instants k·tnz.

| Source | Measured | noise.json / gate | Note |
|---|---|---|---|
| comparator `vnzm`, white part | 324.5 µV | vnmw 316.6 µV | +2.5 % |
| comparator `vnzm`, total rms over the run | **418 µV** | total_input_uV 335 µV (σ_δ = 6.70e-4 x) | **+25 %** (see below) |
| mirror sources nzh, nzj | 0.4902, 0.4898 nA rms | inmw 0.4902 nA | equal |
| mirror charge over a window of length D (130 disjoint windows) | sd **0.00087 x** | σ_q 0.00078 x | +10 %, standard error about 6 %. Over the 6 actual slot windows: 0.00098 |

- **The comparator source exceeds its budget.** Its flicker part is about 264 µV rms injected, against 109.5 µV in
  noise.json.
  - trnoise is given noise.json's flicker rms as its flicker amplitude. That is net.py's and cert_run.py's convention,
    kept by noise2 and noise3 for the R cells as well.
  - ngspice's 1/f generator yields more than that rms over a run of a few milliseconds.
  - So the injected comparator noise is about 1.25 σ_δ, and the K3 allowance of 3σ_δ covers about 2.4 injected σ.
- **The mirror charge is 10 % above σ_q**, about 1.6 standard errors.
- Both gaps lie in the pessimistic direction: more noise is injected than the gate budgets.
- This is reported, not adjusted. Whether to rescale the flicker amplitude, or to budget the injected level instead,
  is the owner's decision.

## The zero-noise identity

From NOISE3_REPORT.md: all amplitudes at 0, against the noiseless run.

- **NOT1 9801.** Equal: every u, emission, word, lesson, test and skew. Not byte-identical: 5 latch dates moved by −3
  to +10 ns, because the added sources add solver time points.
- **XOR3 9803.** Equal: words, lessons, tests, skews, emissions. 3 of 232 u values differ by 0.1 µV (the record's last
  digit), and latch dates moved by −4 to +17 ns.
- **So the records are not byte-identical.** They are equal in every outcome and every stored voltage, within the
  record's resolution. The differences are listed, not excluded.

## Cost

- NOT1: noiseless controls4 1.4 CPU-min, noisy 2.0. The trace write adds about 1 s.
- Disk: trace.raw is 19.5 MB noiseless and 33.6 MB noisy with the noise nodes saved. XOR3 traces will be larger than
  the 1.7 GB measured before, so deleting each raw file after its digest stays necessary.
