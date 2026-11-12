# Related work

This comparison covers the dose, stop-learning, trained-cell and network
results of [v0.4.0](RELEASE_V0_4_0.md). It is limited to the works examined;
it is not an exhaustive priority search. The contribution is the specific
mechanism and its proved consequences under the declared hypotheses.
Rate-independent increments, stopping plasticity, asynchronous signalling
and machine-checked neuronal networks each have precedents.

## Stop-learning: what controls the write?

[Senn and Fusi (2005)](https://doi.org/10.1162/0899766054615644)
already study learning only when the postsynaptic response differs from
the desired output, and prove a generalized perceptron convergence result
under their conditions. [Brader, Senn and Fusi (2007)](https://doi.org/10.1162/neco.2007.19.11.2881)
develop spike-driven learning with bistable synapses and an instructor
signal. The membrane/calcium-gated rule is also set out in
[Noack et al., Section 2.3.1](https://www.frontiersin.org/journals/neuroscience/articles/10.3389/fnins.2015.00010/full):
presynaptic events sample the postsynaptic membrane and a filtered activity
variable to decide whether to modify the synapse.

The hardware history is not confined to clocked switched capacitors.
[Mitra, Fusi and Indiveri (2006)](https://doi.org/10.1109/ISCAS.2006.1693200)
report an analog subthreshold implementation with asynchronous address-event
communication and test-chip measurements. Its [author-repository abstract](https://eprints.gla.ac.uk/117566/)
establishes that precedent; no detailed circuit-equivalence claim is made
here from the abstract alone.

[TEXEL, Greatorex et al. (2025)](https://pmc.ncbi.nlm.nih.gov/articles/PMC12254410/),
Methods, "Learning circuits", uses a filtered postsynaptic activity trace
with calcium thresholds to delimit plasticity. Its potentiation samples a
presynaptic trace; one depression branch uses a fixed increment, and analog
biases control the update strengths. Thus both local gating and stopping
plasticity have implemented precedents.

In Kernel R, the selected training protocol gives a different stopping
construction. A silent pulse leaves the main cell READY during a complete
sensor ERROR phase and writes `8 × (entry − exit)` to its log-gain. A firing
pulse places that phase inside the protected interval, so it writes nothing.
The gate is driven by the cell's phase, without a target-comparison signal
in the cell. This is a prescribed pulse-training task, not a replacement
for the classification tasks of the cited systems.

[`stop_training_exists`](../research/recursive-learning/native/Training/TrainingLoop.lean)
constructs the training execution and establishes stable firing from rest,
with agreement for every competing complete run when the terminal queue
is empty. It assumes the stated parameter bands, rest state and pulse
spacing. If `r` doses suffice to reach an always-firing gain, its sufficient
budget is `2r + 2` pulses. The first FIRE need not be the final stop:
residual charge can cause a FIRE followed by another silent pulse.

## Dose: what fixes the increment?

The closest switched-capacitor precedent examined here is
[Noack et al. (2015), Section 2.3.2](https://www.frontiersin.org/journals/neuroscience/articles/10.3389/fnins.2015.00010/full).
Their ideal step has the form `(C_hebb / C_syn) × (V_a − V_cm)`;
there is no discharge rate in that expression. The circuit uses clocked
phases and row-shared drivers. Its demonstrated stop-learning experiment
sets the stop flags explicitly; Section 3.3 describes externally computed
calcium control for a future backplane. That limitation belongs to that
implementation, not to every earlier stop-learning circuit.

Kernel R instead integrates the sensor's discharge from the ERROR entry
to its exit. The duration changes with the rate; the full-phase log-gain
increment does not. This identity requires uninterrupted exposure, an open
energy gate and no gain-cap clipping. It retains dependence on the
threshold difference and the actuation factor. See the
[cell laws](../model/CELL.md) and [exact dose counting](EXACT_DOSE_COUNTING.md).
Finite reaction delays and unequal threshold errors require the separate
[implementation assumptions](../model/IMPLEMENTATION_ASSUMPTIONS.md).

The comparison is therefore between ways of realizing and enabling an
update. It does not establish that charge-defined increments are new, or
that Kernel R removes every source of fabrication variation.

## What v0.4.0 adds to the comparison

| Result | What Kernel R establishes | Scope of the claim |
|---|---|---|
| Stop-learning | Silent/firing steps yield a finite training construction and a final gain that fires from rest | Spaced canonical pulses, admissible initial state and fixed parameter bands; not general supervised-learning convergence |
| Trained read and coincidence | Training and read occur in one execution; a uniform read window supports a decision on the stated offsets | The trained result replaces the exact birth gain 1.2 and the ±3% FIRE band with its own hypotheses, including a FIRE band of 0.95 to 1.05 |
| Forward-wired networks | Local execution specifications yield a complete network run and agreement of FIRE dates and final values in every complete run | Causal forward wires and compatible local runs; not arbitrary recurrent-network learning |
| Searches | Explicit cells realize count probes and a successive search with `2k + 1` cells for `2^k` needs | The schedule takes exponential time, dose precision tightens with depth, and scheduled wires represent clocked registers |

The supporting statements are
[`trained_read_exists`](../research/recursive-learning/native/Training/JointRead.lean),
[`trained_coincidence_network`](../research/recursive-learning/native/Training/TrainedCoincidence.lean),
[`acyclic_network_states`](../research/recursive-learning/native/Network/AcyclicNetwork.lean)
and [`successive_search_witness`](../research/recursive-learning/native/Search/SuccessiveSearch.lean).
Their existence witnesses accompany the universal claims, so agreement
between complete runs is not the only conclusion.

The [fixed-current separation](../research/recursive-learning/native/Coincidence/CoincidenceSeparation.lean)
uses a different, fixed-birth-gain task. It has not been reproved for the
trained-cell setting. Neither it nor the numerical benchmark establishes
superiority over Noack, TEXEL, calibrated synapses or all timed writes.

## Formal verification: compare models and statements

[De Maria, Di Giusto and Laversa (2018)](https://arxiv.org/abs/1808.01893)
use timed automata with accumulation periods and fixed refractory periods,
validate temporal properties, and infer weights for a desired behaviour.
This is a precedent for formal reasoning about spiking networks and
parameter learning, with a different time and update model.

[Bahrami, Zucchini, De Maria and Felty, arXiv v2 (2026)](https://arxiv.org/html/2505.05362v2)
formalize discrete-time leaky integrate-and-fire neurons in Rocq. Sections
2.2 and 3.2 use rational parameters and Boolean spike histories; the
`NextNeuron` operation retains the static weights. They prove circuit and
archetype properties, including series, parallel and loop behaviours.
This is a direct precedent for machine-checked neuronal-network theorems.

Kernel R uses real-valued continuous flows, threshold events, evolving
log-gains and recovery state. Its v0.4.0 statements connect those dynamics
to training and then to network observations, including parameter bands,
constructed executions and quantification over complete executions.
These are differences in the model and the theorem statements, not a claim
that Lean is intrinsically stronger than Rocq. The forward-wired learning
result also does not subsume the loop behaviours studied in that work.

General deductive verification of continuous and hybrid systems predates
this repository: [KeYmaera X](https://logic.kastel.kit.edu/research/keymaerax/)
reasons about hybrid programs in differential dynamic logic;
[IsaVODEs (2024)](https://doi.org/10.1007/s10817-024-09709-2)
provides compositional reasoning, certified ODE flows and invariants in
Isabelle/HOL. Kernel R contributes an application-specific development,
not a new general foundation for hybrid verification.

Review must still check that the formal definitions represent the intended
cell. See the [review guide](../REVIEW.md) for the scope of native execution
and geometric-crossing correspondence; the latter is protocol-scoped.
An axiom audit does not certify transistor physics or establish novelty.

## Model, timing and circuit evidence

Three timing claims must be kept separate:

- A full ERROR dose ends at a sensor threshold in the ideal model.
- The search constructions use wires that release pulses at preset dates.
- A physical cell needs a way to detect arrivals and initiate sensor cycles.

The circuit study proposed in [PR #103](https://github.com/HevisNico/kernel-R/pull/103)
supplies admission, latch-reset and sensor-precharge timing from ideal
stimulus signals. Its write termination is sensor-controlled; it is not
an autonomous implementation of the complete input interface. Its stated
joint-read latency, about 0.267 model units, is outside the ideal
`(0.239, 0.256]` window. These are scope distinctions, not campaign verdicts.
The [design snapshot](https://github.com/HevisNico/kernel-R/blob/460405f1bd974875a35640c78854458a47123520/research/circuit/DESIGN.md)
documents omitted effects and differences from the model.

The [read-lag theorem](../research/recursive-learning/native/Training/ReadLag.lean)
assumes an additive shift of each cell's observed read FIRE date. It does
not prove that transistor settling has that form. Device simulations and
eventual measurements need a separate correspondence argument before the
ideal timing guarantees can be applied to them.

## Other learning circuits

- **Measured variation.**
  [Mayr et al.](https://arxiv.org/abs/1412.3233) measure spread in
  presynaptic-adaptation update amplitudes. That observation is distinct
  from a comparison of long-term learning increments.
- **Floating-gate synapses.**
  [Hasler et al.](https://papers.neurips.cc/paper/1994/hash/934815ad542a4a7c5e8a2dfa04fea9f5-Abstract.html)
  store a weight as charge on a floating gate. In
  [Figueroa, Bridges and Diorio](https://papers.nips.cc/paper_files/paper/2004/file/f6185f0ef02dcaec414a3171cd01c697-Paper.pdf),
  update rates vary by more than 3:1 between synapses before calibration.
  The authors adjust tunnelling and injection rates locally to obtain
  uniform, symmetric updates, and let LMS learning compensate some offsets.
- **Charge packets in patents.** Fixed charge packets are old. In
  [US 5,136,176](https://patents.google.com/patent/US5136176) the packet
  carries the product of the input and a programmed weight. In
  [US 5,343,555](https://patents.google.com/patent/US5343555) a fixed charge
  is a reference in the signal sent to the soma.
  [US 5,303,329](https://patents.google.com/patent/US5303329) writes the
  weight continuously by injection and tunnelling.
  [US 2015/0278682](https://patents.google.com/patent/US20150278682A1) has
  an asynchronous write triggered by a threshold, with an increment that
  depends on transconductance, capacitance and pulse shape.
- **Write-verify.** Memristive synapses are commonly programmed by cycles of
  reading and rewriting, which
  [add delay](https://arxiv.org/abs/2403.06712).
- **Robust training and homeostasis.**
  [Büchel et al.](https://arxiv.org/abs/2102.06408) train networks for
  performance after deployment on mismatched chips. A
  [cross-homeostatic rule](https://doi.org/10.1038/s41467-025-60697-2)
  targets stable dynamics. In Kernel R the discharge rate cancels from the
  full-phase update, while the thresholds and the actuation factor remain
  in the formula.

## Related principles

- **Ratiometric measurement.** In a
  [dual-slope ADC](https://en.wikipedia.org/wiki/Integrating_ADC) the factor
  `1/RC` is common to both ramps and cancels. In Kernel R the same
  discharge lowers the sensor charge and raises the memory.
- **Delay-insensitive circuits.**
  [Quasi-delay-insensitive logic](https://avlsi.csl.yale.edu/~rajit/ps/qdi.pdf)
  is correct for arbitrary gate and wire delays apart from isochronic
  forks, and that literature already relates confluence to determinism for
  digital circuits. Kernel R gives two separate guarantees. Uniqueness
  compares complete executions for a fixed router and fixed parameters.
  Bounded delays are a hypothesis of the chain theorem.

## Adaptive and contract-based assurance

These works bear on the adaptive layers, such as the
[bounded adaptive search](../research/reusable-controller/ADAPTIVE.md).
Each covers part of what those layers do; none of those examined combines
them. This is a reading of abstracts and main statements, not a systematic
search.

- **Re-learning on demand.**
  [Event-triggered learning](https://arxiv.org/abs/1904.03042)
  (Solowjow and Trimpe) learns a new model only when a statistical test
  finds that observed behaviour departs from the current model.
  [Schlüter, Solowjow and Trimpe](https://arxiv.org/abs/1910.07732) apply
  this to linear quadratic control. This is the closest precedent for
  reopening a decision when a violation is shown. The abstracts examined
  give no explicit bound on the number of triggers; the full texts remain
  to be checked.
- **Bounded switching under noise.**
  [Hespanha, Liberzon and Morse](https://web.ece.ucsb.edu/~hespanha/published/hy-bound.pdf)
  bound the number of switchings of scale-independent hysteresis logic on
  any interval, in the presence of noise and disturbances. This is the
  precedent for bounding the number of reopenings by the accumulated
  perturbation.
- **Contracts at run time.**
  [Adaptive assume-guarantee contracts](https://eskang.github.io/assets/papers/nfm24-adaptation.pdf)
  detect a violated assumption at run time and weaken the guarantee in
  response, without a bound on how often this happens.
  [Assume-Guarantee-Repair](https://www.ncbi.nlm.nih.gov/pmc/articles/PMC7439735/)
  alternates verification and repair at design time.
  [ENTRUST](https://arxiv.org/abs/1703.06350) issues a new assurance case
  with each reconfiguration of a self-adaptive system.
- **Reusing certificates.**
  [VeRecycle](https://arxiv.org/abs/2505.14001) re-certifies only the
  components of a neural policy that a change in dynamics affects.
  [Certified continual learning](https://arxiv.org/abs/2407.06697) aims to
  keep verified properties through retraining.
- **Staying identifiable.** Adaptive MPC with persistent-excitation
  constraints
  ([Lu and Cannon](https://arxiv.org/abs/2211.09275),
  [Hernandez and Trodden](https://arxiv.org/abs/1804.07506)) and
  [forward-looking excitation](https://arxiv.org/abs/2004.01625)
  (Brüggemann and Bitmead, related to dual control) keep the system
  identifiable while controlling it, at a single level of learning.
- **Monitoring architectures.**
  [Neural Simplex](https://arxiv.org/abs/1908.00528) and
  [Black-Box Simplex](https://arxiv.org/abs/2102.12981) switch from a
  learned controller to a verified fallback. One level monitors another;
  guarantees are not composed across levels of learning.
- **Learning hardware and proofs.**
  [Analog on-chip learning circuits](https://arxiv.org/abs/2307.06084)
  implement stop-learning in hardware without a proof.
  [Set-based verification](https://www.em.cs.uni-frankfurt.de/fileadmin/em_files/Paper/2025/DFGpaper.pdf)
  checks analog neural networks under device mismatch, for inference only.
  The Lean hardware work examined, such as
  [CircuitProver](https://arxiv.org/abs/2607.27259), targets digital
  designs. [Altisen, Corbineau and Devismes](https://arxiv.org/abs/1610.08685)
  certify self-stabilizing distributed algorithms in Coq.

## Key references and reading locations

- Senn, W. and Fusi, S. (2005). *Learning Only When Necessary: Better
  Memories of Correlated Patterns in Networks with Bounded Synapses*.
  Neural Computation 17, 2106–2138.
  [DOI](https://doi.org/10.1162/0899766054615644).
  The [abstract](https://pubmed.ncbi.nlm.nih.gov/16105220/) states the
  learning criterion and convergence conditions cited above.
- Brader, J. M., Senn, W. and Fusi, S. (2007). *Learning Real-World
  Stimuli in a Neural Network with Spike-Driven Synaptic Dynamics*.
  Neural Computation 19, 2881–2912.
  [DOI](https://doi.org/10.1162/neco.2007.19.11.2881).
  See also Noack, Section 2.3.1, for the rule used in that implementation.
- Mitra, S., Fusi, S. and Indiveri, G. (2006). *A VLSI Spike-Driven
  Dynamic Synapse Which Learns Only When Necessary*. ISCAS, 2777–2780.
  [DOI](https://doi.org/10.1109/ISCAS.2006.1693200).
  The comparison above uses the author-repository abstract.
- Noack, M. et al. (2015). *Switched-capacitor realization of presynaptic
  short-term-plasticity and stop-learning synapses in 28 nm CMOS*.
  Frontiers in Neuroscience 9:10.
  [DOI](https://doi.org/10.3389/fnins.2015.00010).
  Sections 2.3.1–2.3.2 and 3.3 distinguish the rule, its circuit and the
  demonstrated stop control.
- Greatorex, H. et al. (2025). *A neuromorphic processor with on-chip
  learning for beyond-CMOS device integration*. Nature Communications
  16:6424. [DOI](https://doi.org/10.1038/s41467-025-61576-6).
  Methods, "Learning circuits", describes the traces and stop region.
- De Maria, E., Di Giusto, C. and Laversa, L. (2018). *Spiking Neural
  Networks modelled as Timed Automata with parameter learning*.
  [arXiv:1808.01893v1](https://arxiv.org/abs/1808.01893v1).
  The abstract states the timing model, validation and inference task.
- Bahrami, A., Zucchini, R., De Maria, E. and Felty, A.
  *Modelling and Verifying Neuronal Archetypes in Rocq*.
  [arXiv:2505.05362v2](https://arxiv.org/html/2505.05362v2), revised 2026.
  Sections 2.2, 3.2 and 5–6 define the dynamics and state the circuit results.

This update checks the closest comparisons against the sources and
locations identified above. It does not turn the wider reading list into
a systematic review, or infer the absence of a result from its absence in
an abstract.
