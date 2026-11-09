# Learned adaptation during a lesson

**The R-based system learns when to continue a lesson and when to stop, using
intermediate responses from the current learner.** This is a numerical proof of
concept of adaptive stopping. Pulse shape, teaching blocks, observation categories
and preference training are supplied. Inventing a new lesson rhythm or content
has not been demonstrated.

## Reproduced held-out learner results

The published records were recomputed from scratch with the corrected terminal-event
scheduler and a complete source/runtime manifest. This reproduction uses the original
seeds and protocol; it is not a new independent sample.

Three independently trained R memory banks learn the same choices. Each bank is
evaluated on the same pupils; this does not create additional independent samples.
The two 160-learner lots below are disjoint, also disjoint from development and
training. Each pupil has independent ±10% variation in the original five physical
parameters per port.

| Method | Test lot | Confirmation lot |
|---|---:|---:|
| Learned adaptation during the lesson | **140/160** | **147/160** |
| Development-selected fixed duration: 3 blocks | 89/160 | 101/160 |
| Best fixed duration chosen in hindsight among all 4 | 98/160 | 102/160 |
| Adaptive lesson lengths reassigned to other pupils | 88/160 | 78/160 |
| Use only the first observation for every later decision | 125/160 | 134/160 |
| Wrong action credit during training | 33/160 | 39/160 |
| Teacher plasticity disabled during training | 90/160 | 102/160 |
| Learned settings inherited by a new bank | **140/160** | **147/160** |
| Pupil plasticity disabled during teaching | 0/160 | 0/160 |

Mean **pupil-side** pulse counts are 5.5125 and 5.45625, including every assessment
pulse. Reassigned-lesson controls have exactly the same total pupil pulses, 882
and 873, respectively. Thus the matched comparison tests whether a lesson's stopping
time fits the particular pupil, rather than the benefit of an overall duration mix.

The adaptive-versus-preselected-fixed success differences are +31.875 and +28.75
percentage points. Descriptive paired learner-bootstrap intervals for the first
trained bank are about [24.4,39.4] and [22.5,35.6] points. They are conditional on
these trained banks and this constructed task, not uncertainty over arbitrary
training populations or pedagogical tasks. No test is pooled across teacher replicates.

## Timing task and episode

The retained skill is the same finite timing window used previously: exactly one
response to each of eight period-8 prompts, with latency in [0.22,0.50] model time
units. Early and late responses both fail. This is a constructed numerical timing
specification, not a measured chip tolerance.

A supplied teaching block contains:

1. Two canonical teaching pulses on port 1 at local times 0 and 4.
2. Quiet evolution until time 30.
3. One assessment pulse at time 30, with plasticity disabled through time 50.
4. A 40-time-unit teacher readout allowance, ending at time 90.

At that point the teacher chooses CONTINUE or STOP. CONTINUE starts another block;
a four-block ceiling forces termination. Final grading uses eight fresh prompts
with pupil plasticity disabled. Grading outcomes are unavailable until after STOP.

Every real pupil charge and setting is carried through these stages. No pupil is
reset between blocks. Separate matched numerical copies are used for counterfactual
training branches and fixed-duration baselines; an adapted live pupil is not rewound
to try an alternative action.

The pupil pulse budget is at most 12: two teaching pulses plus one assessment per
block. Final grading pulses are reported separately from the teaching budget and
are identical in purpose across conditions. Native teacher readout adds **two
query pulses per block**. Consequently, lower pupil pulse count is not a claim
about lower total circuit energy or even fewer total circuit pulses than every
fixed controller.

## What the teacher observes

The assessment response is externally categorized:

- `missing`: no assessment response;
- `late`: response latency above 0.50;
- `not_late`: response latency at or below 0.50, including an irrecoverably early response.

These categories are supplied, not learned representations. The teacher does not
receive initial gain, recovery, physical parameters, learner identity, a future
trajectory or final grading labels when selecting an action.

One persistent R memory cell is allocated to each category. Each has a CONTINUE
port, a STOP port and a guard port. Its initial gains are [0.3,0.3,4], b=0.08 and
E=100. Native q/m/z/b/E laws and phase-dependent plasticity are unchanged.

## How the stopping rule is learned

Training uses paired rollout preferences from simulated pupil experiments. For
an observed training prefix, the comparison is STOP now versus CONTINUE under a
fixed exploration rollout that continues to the four-block budget:

- If stopping now already passes the retained timing probe, prefer STOP: it uses fewer pupil pulses.
- Otherwise, prefer CONTINUE only if its complete rollout passes.
- If both branches fail, neither action receives positive credit.

This comparison uses measured probe outcomes and pulse counts. It does not assign
a preferred action by observation-category label. It is an **external preference
training procedure**, using matched numerical counterfactuals; autonomous model-free
teaching or an isolated cell discovering this training procedure is not claimed.

Each action trial supplies exactly two canonical pulses to its category's R cell.
A pulse names the tried action. An early guard after a nonpreferred outcome protects
the main cell through the auxiliary ERROR phase, suppressing gain learning. A late
guard after a preferred outcome leaves ERROR-phase native plasticity available.
No optimizer directly updates a gain or recovery setting.

Feedback begins at trial time 500, after the complete possible pupil episode
(360 teaching/assessment/readout time units plus 80 grading units). Trials are
spaced by 540. Three R cells stay alive and evolve continuously throughout training;
there is no state reset or settings copy during that training.

The acquired mapping is CONTINUE for `missing` and `late`, STOP for `not_late`.
The corresponding action gain grows to about 1.814894 while its counterpart stays
0.3. A supplied decoder queries the two action ports and chooses the earliest
native response. Absent responses use CONTINUE; latencies within 1e-7 are tied.
This tolerance prevents floating-point noise from deciding between equal signals.

## Causal online confirmation with the same living teacher

The main paired comparison computes complete counterfactual pupil trajectories
for the controls, but its selector reads only available prefix observations.
`validate.py` separately executes all 320 primary pupil episodes online: it does
not simulate future blocks or final grading before deciding to stop.

`live_validate.py` goes further. It reruns the recorded first training set and
retains that exact full R memory-bank object. The teacher's plasticity is then
frozen for evaluation, while q, m, E and modes keep evolving. For each pupil:

- The pupil completes its current block and assessment.
- The relevant living R cell receives actual CONTINUE and STOP queries in two 20-unit slots.
- Native firings determine the next action.
- The pupil continues or stops; final grading is computed only after the real stop.

That same teacher bank is retained through both entire test lots, without reset
or settings copy. It reproduces **140/160 and 147/160**, using 588 and 582 native
teacher query pulses respectively. This verifies execution of the acquired policy;
it does not add new independent pupil samples.

## Training and held-out profiles

Each of three training sets contains 64 parameter draws. Training initial taught-
port gain is confined to [0.15,0.45] or [1.2,1.5]. Test gain is uniform in [0.15,1.5],
and b is uniform in [0.18,0.40]. The intermediate gain band (0.45,1.2) is absent
from training: 75/90 and 75/87 such fresh pupils pass in the two lots.

All four-block training trajectories are explored. The first eight encountered
comparisons per observable category are retained, without filtering on the winning
action. Both actions receive an outcome for each comparison: 48 action trials per
bank. Correct, wrong-credit, frozen and uninformative controls use the same trial set.

These initial states and protocols are outside the original A22 certificate.
Teacher physical parameters remain nominal; the ±10% variations concern the pupils.

## What has and has not been established

The result supports **learned stopping adaptation** in this supplied architecture.
The initial-observation-only control is worse, and reassigned lengths lose the
benefit despite identical total pupil stimulation. Actual intermediate feedback
therefore matters within the tested protocol.

A deliberately programmed equivalent stopping rule obtains the same result. This
post-hoc reference is explicit in `POSTHOC_ANALYSIS.json`. There is no demonstrated
performance advantage over conventional feedback control, nor a claim that the
simple stopping rule is a new algorithm.

The same descriptive analysis finds 20 failures in the first lot and 13 in the
second. Nine and eight are early at stopping; eleven and five remain late or
missing at the budget. None has a successful alternative prefix among the four
supplied block counts. This is a finite-protocol observation, not impossibility
under another rhythm, pulse budget or learning mechanism.

No new pulse waveform, inter-pulse timing or teaching content is invented here.
The block pattern and budget are provided. `INVENTION_PROTOCOL.md` defines a
stronger future claim and the evidence it would require; those experiments have
not been run.

## Verification, provenance and reserve

All **127 numerical, causal and structural checks** pass. They include seed
separation, exact state carry, frozen assessment settings, complete fixed-duration
controls, exact replay budgets, credit permutation, independent persistent-teacher
replay, tighter teacher integration and independent direct-ODE pupil trajectories.
The separate continuous native-readout verification passes for every primary pupil.
Exact errors and traces are included.

The fast pupil simulator does not explicitly integrate reserve E. A conservative
instantaneous-work bound over the declared parameter box gives W <=225.044. With
E'=10(100-E)-W and initial E=100, this gives E>=77.495, so the positive-reserve
plasticity gate remains open under these assumptions. Teacher reserve is directly
integrated. This argument is not a machine-checked interval certificate.

The task, fixed three-block baseline, 64-pupil training size and seeds were
selected in the earlier development process. This reproduction does not rerun
or establish that process and is not a preregistered experiment. The legacy
adaptive development sweeps, aborted-run plan/log and old evaluation records
have been removed from the current bundle; previous Git revisions retain them.
`REPRODUCTION.json` records this execution, artifact identities and validation.

## Reproduce

New runs write a version-2 provenance manifest before training. It locks
`model.py`, `run.py`, `provenance.py`, both numerical engines (`engine.py` and
`simulate.py`), and the actual Python, NumPy and SciPy versions. Both validators
refuse incomplete manifests, changed engines or different runtime versions
before replaying dynamics.

The bundled results now come from a complete new execution, followed by both
validators, the descriptive analysis and report generation. The reproduced
scores match the earlier scores; they are supported by the new records and
manifest. Legacy two-file plans remain intentionally refused.

From the extracted ZIP's main directory:

```sh
python -m pip install -r 02_R_Simulation/requirements.txt
python -u -B 02_R_Simulation/adaptive/run.py --out 08_New_Adaptive
python -u -B 02_R_Simulation/adaptive/validate.py --out 08_New_Adaptive
python -u -B 02_R_Simulation/adaptive/live_validate.py --out 08_New_Adaptive
python -u -B 02_R_Simulation/adaptive/analyze.py --out 08_New_Adaptive
python -u -B 02_R_Simulation/adaptive/report.py --out 08_New_Adaptive
```

Historical development records are never imported into a new execution. The
reproduced recordings are in `08_Adaptive_Lessons`; no network access is needed
for the calculations. To rerun from the repository, use the same commands with
`experiments/reciprocal/adaptive/` as the script directory and a new output
directory, then package it with `package.py --adaptive-results PATH`.
