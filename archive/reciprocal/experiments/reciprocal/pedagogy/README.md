# Learned curriculum selection with native R plasticity

**This is a numerical proof of concept of a learned teaching choice in an added
R-based architecture. It is not a demonstration of spontaneous pedagogy in an
isolated R cell.**

The system learns which of two pulse lessons helps a behavioral learner profile.
Its acquired choice improves fresh learners and survives settings transfer to a
new policy bank. R's q/m/z/b/E laws are unchanged. Context sensing, outcome coding,
exploration, decoding and the lesson library are explicitly added components.

## Confirmation result

The same **128 fresh learners** are evaluated under every policy and curriculum.
There are four independently trained policy banks; each obtains the counts below.
This is 128 test learners reused across four banks, not 512 independent learners.

| Policy or control | Successful test learners |
|---|---:|
| Before policy training | 67/128 |
| Learned policy, correct outcome credit | **128/128** |
| Best fixed lesson among 13, selected on development data | 99/128 |
| Best fixed lesson among 13, selected in hindsight on this test set | 99/128 |
| R policy plasticity disabled during training | 67/128 |
| Same pulse count, uninformative outcome timing | 67/128 |
| Same outcome pulse times/counts, credit assigned to the other lesson | 3/128 |
| Diagnostic contexts swapped at evaluation | 3/128 |
| Equal saturated policy gains and maximum recovery | 67/128 |
| Inherited learned policy in a new R bank | **128/128** |
| Learner plasticity disabled during its lesson | 0/128 |

Uniform random choice between the two learned-policy lessons has an expected
65.5/128 successes. The learned policy's gain over the development-selected fixed
lesson is 29/128, or 22.66 percentage points. A descriptive paired learner-bootstrap
interval is about +15.6 to +30.5 points for the first bank. This interval is
conditional on the trained policies and this designed benchmark; it does not
estimate generalization to arbitrary tasks or teacher-training populations.

## Why this task needs a teaching choice

The earlier regular-cadence experiment let recovery saturate and did not require
choosing a lesson. Initial development sweeps again found a universally effective
fast lesson for the simple cadence-only task.

This new benchmark deliberately adds a timing specification: after teaching, a
learner must produce exactly one response to each of eight period-8 prompts, with
latency between **0.22 and 0.50 model time units**. Early and late responses both
fail. Such a requirement models a finite timing acceptance window; these values
are a constructed numerical task, not measured chip tolerances.

Two initial learner families have different gain deficits. Each learner has
independent uniform ±10% variations in the original five physical parameters per
port. Taught-port initial gain is uniform in [0.285,0.315] or [1.33,1.47]; b is
uniform in [0.23,0.27]. These initial states are outside A22's certified initial
family. The teacher does not receive the hidden family, gain, b or physical parameters.

A fixed diagnostic sends simultaneous canonical pulses on ports 0 and 1 with
plasticity disabled. An observed response defines context 1; no response defines
context 0. After 30 time units, physical charges and settings are carried into the
lesson without a reset. Context is therefore an externally supplied, observable
binary feature, not a representation learned by R.

The learned policy chooses between ten pulses spaced by 4 or by 8. The first is
useful for the lower-gain profile; the second avoids overshooting the required
latency in the other profile. Both lessons contain exactly ten canonical pulses.
Every learner is observed to the same lesson end, 180 time units. All 13 fixed
comparison lessons fit the same maximum pulse deadline of 144. Different lessons
can finish their emissions at different times.

After the lesson, actual charges and settings are carried forward into an isolated,
plasticity-disabled 8-prompt probe. The policy never sees test-learner probe outcomes
during training. Curriculum alternatives use separate matched copies of a fresh
learner's initial state; a trained live learner is not reset to try another lesson.

## What is learned, and where

There is one persistent R policy cell per diagnostic context, two cells in total.
Each starts with action-port gains [0.3,0.3], guard-port gain 4, b=0.08 and reserve
E=100. Action port 0 names the period-4 lesson; action port 1 names the period-8
lesson. The guard port is a declared addition to the surrounding protocol.

During fixed exploration, both lessons are tried on training learners. A binary
outcome reports whether that learner passed the timing probe. No optimizer, table
of action values or direct weight update is used. The outcome encoder supplies
exactly two canonical pulses to the relevant R policy cell:

- one pulse on the port naming the lesson that was tried;
- one pulse on the guard port, early after failure and late after success.

An early guard fires the main cell before the feedback pulse's auxiliary ERROR
phase. Main protection suppresses action-gain learning. A late guard leaves that
ERROR phase available for native gain plasticity. Thus the **external timing code**
gives R's existing coincidence/phase mechanism a reinforcement interpretation.
The guard schedule is an added learning protocol; claiming the whole reinforcement
rule emerged spontaneously from the isolated kernel would be incorrect.

Feedback is causally delayed until after the diagnostic (30), lesson (180) and
complete probe (80): the feedback block starts at episode time 320. Episodes are
spaced by 360. Policy cells remain alive and evolve continuously between episodes;
q, m, z, b, E and modes are never reset or copied during training.

The successful action gain rises to about 1.814894; the unused action gain remains
0.3. Before training neither action port responds to a single query. Afterwards,
the learned port fires. A fixed decoder queries each action through R's native
single-pulse response with plasticity disabled and selects the earliest responding
action; absent responses use fixed action 0. These readouts use isolated test
copies of the acquired settings and do not overwrite the live policy bank.

| Observable context | Before: action gains | After: action gains | Decoded lesson |
|---|---|---|---|
| 0 | [0.3,0.3] | [1.814894,0.3] | Period 4 |
| 1 | [0.3,0.3] | [0.3,1.814894] | Period 8 |

No code branches on context to prescribe this final action mapping. The mapping
is acquired from training outcomes. Wrong-credit controls use precisely the same
pulse times, counts and contexts, with the two action ports exchanged. Their
recovery histories match while their acquired choices reverse. Resetting only
action gains removes the learned distinction; swapping those gains reverses it.
General recovery saturation alone does not explain the conditional choice.

## What was supplied versus learned

| Component | Status |
|---|---|
| Local q/m/z/b/E equations and phase-dependent plasticity | Existing R mechanism, unchanged |
| Retained action-port gains associating context with lesson efficacy | Learned through R dynamics |
| Behavioral diagnostic and one cell allocated per context | Supplied architecture |
| Candidate lesson timings | Supplied library; not invented by R |
| Success window and binary outcome encoder | Supplied task and feedback circuit |
| Exploration order and time slots | Supplied schedule |
| First-response decoder and fallback | Supplied readout |
| Applying a selected lesson | Supplied pulse sequencer |
| Copying learned settings into a new policy bank | External bounded-max transfer |

## Teaching the teaching policy to another bank

The two action gains and b can be transmitted by the same declared bounded-max
settings-copy operation used elsewhere in this prototype. A fresh bank inherits
the learned readout and obtains 128/128 with the same new learners. The original
bank is retained; it is not killed or reset. The copying rule and copy moment are
external. This experiment does not show that the policy independently learns
when or how to transfer itself.

## Design, pilot and confirmation

The cadence sweep and precision-task exploration are included as
`development_grid.json`, `development_precision.json` and
`development_curricula.json`. The latency window, profile ranges and two candidate
lessons were designed using these development explorations. Among all 13 fixed
curricula, `fast_slow` was selected on disjoint development learners before testing.

An initial 128-learner pilot used prerecorded outcomes and obtained 128/128 versus
91/128 for the selected fixed lesson. Its plan and summary are included as
`pilot_plan.json` and `pilot_summary.json`. Inspection then prompted a causal-clock
correction: teacher feedback is now placed after the full pupil episode. No lesson,
threshold or learner range was retuned. The final confirmation uses a new untouched
test seed, 717000 instead of the pilot's 617000.

Training uses four independent sets of 12 parameter draws, six per family. Each
draw is tested with both actions using matched fresh learners: 24 lesson outcomes
per policy bank, 96 across all four training sets. Controls reuse those outcomes.
There are 16 persistent policy-bank trajectories, 1,664 held-out curriculum assays
(128 × 13), and 128 frozen-learner controls. Results are paired; they must not be
pooled as independent extra learners.

## Verification

All **125 recorded numerical and structural checks** pass, including causal
feedback timing, disjoint seeds, equal pulse budgets, physically bounded monotone
memory, uninterrupted live cells, exact credit permutation, matching recovery in
the credit control, independent event-driven replay of persistent policy cells,
tighter direct-ODE convergence, independent direct-ODE learner lessons, and
inheritance/readout ablations. Details and exact numerical errors are in
`validation.json`. The observed policy reserve remains above 98.72.

These checks are not a formal certificate or transistor-level validation. Teacher
physical parameters are nominal; the ±10% sweep concerns the learners. Initial
profiles and the timing task are constructed. There is no energy/area measurement,
learned diagnosis, curriculum invention, within-lesson adaptation, forgetting or
proof of reliable relearning after reversed contingencies. R's monotone memory
and eventual saturation remain important limits.

The supported claim is deliberately narrow: **R's native plasticity can store a
useful conditional teaching choice when placed in an explicitly defined feedback
architecture.** General pedagogy, spontaneous emergence and industrial usefulness
need further experiments.

## Reproduce

From the extracted ZIP's main directory:

```sh
python -m pip install -r 02_R_Simulation/requirements.txt
python -u -B 02_R_Simulation/pedagogy/run.py --out 07_New_Pedagogy
python -u -B 02_R_Simulation/pedagogy/validate.py --out 07_New_Pedagogy
python -u -B 02_R_Simulation/pedagogy/report.py --out 07_New_Pedagogy
```

The supplied data remain in `07_Learned_Pedagogy`. Optional pilot/development inputs
are copied by the runner only when available in the working checkout; fresh
simulations need neither GitHub nor ChatGPT. A reproduction without pilot metadata
has one fewer provenance check. The exploratory-development scripts are included
under `02_R_Simulation/pedagogy/development` for inspection; their fixed output
paths target the original research checkout.
