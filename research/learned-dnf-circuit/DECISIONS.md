# Decisions of the owner after the review of phase 0

Phase 0 (#172) was reviewed and accepted. These are the owner's decisions for the campaign that follows. They are
recorded here before any `PREDICTION.md`; the campaign's `PREDICTION.md` will apply them, and is written only once
the theory track has added the one-sided premise of decision 4.

1. **Read-only by the testbench gate** (`idis` off, `gate.py`), with every test read checked for writes in each run.
2. **Layer-1 pulse amplitude 0.49**, fixed now from the nominal cell. Layer 2 keeps amplitude 1.
3. **Calibration covering every stage up to the maximal write count**, with a geometric gain-path model if it fits
   better than the linear one, and a calibration and validation split fixed in `PREDICTION.md`.
4. **The OR cell's saturated pair** is handled by a one-sided premise, which the theory track is adding as a new
   frozen variant. `PREDICTION.md` waits for it.
5. **Noise.** A per-output claim needs room on its training reads as well as its test reads, under `K = 3`, with the
   fixed noise constants raised to the values campaign 3 measured: **0.111 mV between runs, 0.094 mV within a run,
   0.009 mV per dose**. The noise model is fixed in `PREDICTION.md` by the rule of the phase 0 README (the validated
   independent model of the noise study if it exists at preregistration, otherwise the simulator's model).
6. **Size: 9 instances in 6 h** of expected machine time, **one noisy run per instance**.
7. **Controls**: the untrained network, the skewed coincidence, and the nominal predictor.

Then, as before: `PREDICTION.md` pushed alone, the implementation frozen and rehearsed through the launch kit, an
independent review, one launch per machine.

## The gain-path model, on the nominal cell (decision 3)

[`gainpath.py`](gainpath.py), [`GAINPATH.json`](GAINPATH.json): both models, with a free constant help, fitted on
every stage 0 to 7 of the guard-disabled probe; and a split, fitted on stages 0 to 3, 6 and 7 and checked on 4 and 5.
Largest residual `|Z - G|`, in units of the FIRE level:

| Reads | Linear, all stages | Geometric, all stages | Linear, held-out 4 and 5 | Geometric, held-out 4 and 5 |
|---|---|---|---|---|
| layer 1, amplitude 0.49, singles and pairs | 0.0072 | **0.0045** | 0.0083 | **0.0007** |
| layer 2, amplitude 1, single lines | 0.0056 | **0.0003** | 0.0053 | **0.0003** |

The geometric gain path fits better on both cells, and it extrapolates: so by decision 3 the calibration will use it.
The pair of lines of the OR cell is never below the larger single line by less than 0.67 of the FIRE level at any
stage: the one-sided premise of decision 4 holds there with a wide margin on the nominal cell. These are nominal
measures of phase 0, not a preregistered rule.
