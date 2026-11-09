# Does R learn to teach and transmit?

**The experiment shows improved transmission efficacy. It does not yet demonstrate
learning a teaching strategy adapted to a student's progress.**

## What is measured

Teacher A already responds to its own source. It meets student B and receives the
same 32 exercises, spaced by 4 time units. A's outputs teach B. Three training arms
use R's unchanged q/m/z/b/E laws:

1. no feedback from B to A;
2. B's actual response pulses reach A;
3. the same number of feedback pulses is replayed to A with reversed chronology.

The third arm tests whether additional stimulation can explain the benefit without
requiring informative student feedback. Replay keeps the canonical pulse shape
and reverses temporal gaps without overlap. This control is an imposed experimental
protocol, not a mechanism learned by a cell.

Training uses six student contexts: initial taught-port gains 0.3, 0.8 or 1.2,
combined with initial recovery 0.06 or 0.12. These additional initial conditions
are outside A22's narrow certified initial-state family.

The resulting teachers are evaluated on **24 fresh learners**, with independent
uniform ±10% variations of the original five physical parameters per port. The
same 24 learners are paired across teachers: the 144 trials per arm (6 contexts ×
24 learners) are not 144 independent learners.

Teacher plasticity is disabled during evaluation to measure the acquired state.
Responses to identical period-3 or period-4 prompts form a lesson. Each learner
receives the first 6 or 10 pulses actually emitted, retaining their spacing. The
pulse count is matched; lesson duration may differ.

After the lesson, the learner is isolated and its plasticity is disabled. Eight
new prompts at the target period test retained ability. Success requires exactly
one response per prompt, 8/8, without teacher support or learning during the probe.

Three channels are compared: pulses only, settings only, and both. Settings transfer
externally maps the teacher's practiced port 0 to the student's port 1, and copies
b by a maximum rule bounded by local caps. The mapping and copy time are imposed;
R does not choose them. No physical copying cost or bit rate is estimated.

The plan was recorded before computation: **18 teacher training runs and 5,472
learner evaluations**. The primary outcome uses pulses only, a ten-pulse lesson,
and target period 3. Other conditions are secondary comparisons.

## Primary outcome: target period 3, ten teaching pulses

Each count below is the number of the same 24 learners succeeding with every one
of the six trained teachers in an arm. The initial teacher has one configuration.

| Teacher state | Successful learners | Mean probe responses |
|---|---:|---:|
| Before meeting a student | 0/24 | 3/8 |
| After exercises without feedback | 0/24 | 4/8 |
| After actual student feedback | 24/24 | 8/8 |
| After time-reversed feedback | 24/24 | 8/8 |

The ten-pulse lesson lasts about 80.88 time units for the initial teacher, 53.94
after exercises without feedback, and 27 after actual or replayed feedback.
The acquired emission rate contributes to this outcome.

With only six teaching pulses, no learner passes the complete period-3 probe,
including with feedback-trained teachers. Settings alone or both channels already
allow all 24 learners to pass with feedback-trained teachers. Copying directly
transfers an acquired ability; it does not establish a learned copying or selection method.

For target period 4, teachers trained without feedback also succeed with ten pulses.
Student feedback is therefore unnecessary for some observed improvements.

## What changed in the teacher

The teacher starts with b=0.18. Exercises without feedback raise b to 0.38 and the
practiced-port gain to about 3.30695. With actual or reversed feedback, **b reaches
its cap of 1.1 in every context**, and feedback-port gain reaches 4. Feedback speeds
up recovery, enabling faster examples from which new learners acquire the cadence.

Reversed replay reaches the same ceiling. These regular-task results therefore do
not establish sensitivity to a particular student's progress. Equal scores also
have a ceiling limitation; they do not prove feedback chronology is always irrelevant.

A readout control shows that saturated feedback-port gain is unnecessary for the
later lesson on the practiced port: the settings used by that readout and recovery
suffice to reproduce its pulses. The bench adds no reward variable, pedagogical
optimizer, or learned choice of copy timing or transmission channel.

## Interpretation and next experiment

A teacher becomes more effective at transmitting a temporal ability to fresh
learners. Adaptation of its teaching method to an individual learner has not been
shown. Additional stimulation and recovery saturation remain a sufficient
explanation for the present result.

A stronger test would provide measurable value in choosing lessons, timing or
channels according to learner progress, then require actual feedback to outperform
misleading feedback under matched budgets. Any new decision rule must be identified
as an extension to R, rather than attributed to its already demonstrated kernel.

## Verification and limits

All **37 checks** pass: complete experimental grid, no duplicates, pulse budgets,
bounds, exact feedback counts and time reversal, identical external exercises,
no copies during teacher training, positive reserve E, tighter-tolerance convergence,
independent cell replay, and independent integration of several fresh-learner lessons.

The largest tested convergence difference in event times is below 1e-8; see
`validation.json`. This is not a formal proof or electronics experiment. Regular
exercises, few training contexts, saturation and unmodeled hardware costs limit
the conclusions.

`03_Visualization` still replays the original reciprocal network. This teaching
experiment and its data are in `06_Learning_To_Teach`.

## Run again

From the ZIP's main directory, after installing the simulation dependencies:

```sh
python -u -B 02_R_Simulation/teaching/run.py --out 06_New_Trials
python -u -B 02_R_Simulation/teaching/validate.py --out 06_New_Trials
```

The supplied results are preserved. The script prepares the initial teacher again
if the first network recording is unavailable at its working path. Computation
requires no access to GitHub or ChatGPT services. Historical machine identifiers
are translated in `01_Guide/DATA_DICTIONARY.md`.
