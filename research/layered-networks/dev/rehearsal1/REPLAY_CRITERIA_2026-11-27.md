# Rehearsal 1: the replay of the third symbol. Criteria written BEFORE the replay

Dated 2026-11-27. These criteria are pushed before any replay has run. The replay is a reconstruction made after the fact. It is exploratory and changes no verdict.

## Cells

There are four cells, all in the first layer.

| Instance | Cell | Key | Role | Port order of the network arrivals |
|---|---|---|---|---|
| XOR3_27735 | c1_0 | 1/0/0 | refuted (network `sssFF`) | 11.2 / 12.8 µs |
| XOR3_27735 | c1_1 | 1/1/0 | witness (network `ssFF`) | 12.8 / 11.2 µs |
| XOR3_88529 | c1_1 | 1/1/0 | refuted (network `sssFF`) | 12.8 / 11.2 µs |
| XOR3_88529 | c1_0 | 1/0/0 | witness (network `ssFF`) | 11.2 / 12.8 µs |

## Protocol

- **The deck.** Each instance's published stage-D deck is used, with the pinned ngspice and PDK.
- **Same history.** The preset and the first two lesson pulses are kept exactly. ONLY the arrival times of the two inputs of the third read (lesson round 2) change, measured after the slot's T.
  - Case 1: 2.4 / 2.4 µs, as in stage D.
  - Case 2: 12.0 / 12.0 µs, a common delay with the inputs simultaneous.
  - Case 3: the network times in the cell's own port order (table above). Cases 2 and 3 have the same mean arrival.
- **What is saved.** The latched output p, both port comparators (x1 and x2: vs and vrefsn) and the cell's common comparator (vq and vrefmn), with the pulse times.
- **What is reported** per cell and case:
  - the symbol (`F` or `s`) and the latch time;
  - for each comparator, the signed maximum of (inp − inn) over the decision window, in mV, with its time;
  - u before the read;
  - the sampling step.

## Validity, checked first

Case 1 must reproduce stage D's recorded read for every cell: `F`, a latch time within 0.1 µs, and u within 1 µV. If it does not, the replay does not reproduce stage D. It is reported as such, and nothing below is concluded.

## Interpretation, fixed now

| Refuted cells | Witness cells | Reading |
|---|---|---|
| case 2 `F`, case 3 `s` | `F` in all three cases | In these isolated cells, the separation of the two inputs alone, at a constant mean delay, suffices to reproduce the divergence. |
| case 2 `s` | (reported) | In this replay the common delay already suffices; the separation is not needed to explain the divergence. |
| `F` in all three cases | (reported) | Reproducing the arrival times alone on the isolated deck does not reproduce the refutation. A difference between the isolated cell and the network remains to be identified. |
| any other pattern, including a witness giving `s` in case 3 | | It is reported as observed, with no causal reading. |

## What this replay cannot establish

- It explains two past cases. It does not by itself give a rule that predicts a new network.
- Any such rule would have to bound each cell's arrival times before its run, and to measure whether the cell keeps its word over that whole range. It would then be tested on new development seeds before being frozen.
- Under the preregistration, `ssFF` against `sssFF` stays a full refutation, even when the final XOR table is right.

## Addendum, also before the replay (the owner's reading rules)

- **Read per cell.** The four cells are read one by one, each starting from its case-1 validity check. The two instances are not pooled.
- **A mixed result is kept as is.** If 27735 follows one row of the table and 88529 another, that result stands. Two identical training-word deviations may have different causes.
- **"Over the whole range" needs a bound.** Three arrival times can separate the explanations above for these two cases. They do not establish a symbol over a continuous range of arrival times. A claim of the form "over the whole predicted arrival range the third symbol stays F" needs a justification between the tested times, for example a bound on how much the comparator margin can vary. Without such a bound, the result is stated as "stable at the tested times" and nothing more.
