# Plan: deriving `CellLaw` from the hybrid execution

Status: proposal. Nothing here is proved yet. `CellLaw` (in `KernelR/Robust/Induction.lean`)
is the only physical hypothesis of the robust chain induction. This note splits its
derivation into three local lemmas, so that the hybrid semantics is needed in two places
only and the third step is a finite induction.

## Shape of the hypotheses

Each lemma takes the numerical enclosures it uses as **explicit hypotheses**: latency
brackets, phase durations, dose intervals, return bounds. Their rational endpoints are
already checked in `Robust.Evidence`; the remaining premise, as today, is that the real
quantities lie in those intervals. This keeps the semantic part separate from the
arithmetic part, and lets the same lemma serve every certified (ε, ν, α) point.

All three lemmas start from a **section**: main READY with |q − r| ≤ ν/κ (or the birth
band), auxiliaries READY within their rest band, no active current, gain and b in their
intervals, E in [50,100].

## Lemma 1: a silent input

From the section, one canonical input on the active port, and no other input before the
next one at least G = 7.5 later:

- the main charge stays below threshold (no firing, no output);
- the auxiliary runs exactly one MARK, SILENT, ERROR cycle and returns to READY before G;
- the ERROR phase is wholly READY, so the gain receives one full dose in its interval;
- b is unchanged, since MARK occurs while the main cell is READY;
- at the next input the state is back in the section, with the carried excess bound.

Semantic content: first-crossing semantics of the auxiliary, protected phases ignoring
input, and the READY variation-of-constants envelope with noise and amplitude.

## Lemma 2: an emitting input

From the section with the learned gain, one input and none before G later:

- exactly one main crossing, with latency in its bracket, and within δ of the reference
  latency of the same gain (the `Robust.Latency` radius, now applied to the execution);
- MARK ends before the crossing, ERROR lies inside FAST or SLOW: no dose, b unchanged;
- FAST and SLOW complete and the main cell returns to READY with q = r before G;
- exactly one output, at input date plus that latency.

Semantic content: the FAST and SLOW solutions already checked in Lean, the guard at
q = 1/4 and at q = r, and the protected-phase ordering.

## Lemma 3: the input word (finite induction)

Given a stream with L ≥ 4 inputs and gaps at least 7.5: apply Lemma 1 to the first three
inputs and Lemma 2 to every later one, and show that no output occurs between inputs
(no spontaneous firing from the section). This produces exactly the fields of
`CellWitness`: count L − 3, the output dates, the first-shot bound and the regular radius.
It is a recursion on the input index and should be routine once Lemmas 1 and 2 exist.

## Order of work

1. Lemma 2 first: it carries the latency radius, which is the new robust content, and its
   modes (FAST, SLOW) are already solved in Lean.
2. Lemma 1: same READY envelope, plus the auxiliary cycle and the dose.
3. Lemma 3 and the instance `CellLaw` from Lemmas 1 to 3.
4. Optionally, add the learning conclusions (three doses, b, probes) to `CellWitness`,
   so that the chain induction concludes them too.
