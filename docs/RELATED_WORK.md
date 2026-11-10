# Related work

The comparison below is limited to the works we examined.

**Closest precedent.**
[Noack et al.](https://www.frontiersin.org/journals/neuroscience/articles/10.3389/fnins.2015.00010/full)
build switched-capacitor stop-learning synapses in 28 nm CMOS. Their ideal
weight step has the form `(C_hebb / C_syn) × (V_a − V_cm)` and contains no
discharge rate. Membrane and calcium thresholds enable or block the step,
and its size comes from control voltages and a capacitor ratio. The circuit
is clocked and shares its drivers along a row, which reduces mismatch
between the synapses of that row.
[Mayr et al.](https://arxiv.org/abs/1412.3233) still measure spread in the
update amplitude of the presynaptic adaptation.

Kernel R differs in two ways. Its update integrates a self-timed sensor
discharge between two state thresholds, so the thresholds set the size of
the step. And Lean checks how these updates compose in the chain protocol.

**Other learning circuits**

- **Threshold-gated increments.** In the
  [TEXEL processor](https://pmc.ncbi.nlm.nih.gov/articles/PMC12254410/),
  one depression branch uses a fixed increment. Potentiation is
  proportional to a presynaptic trace sampled at the spike, and analog
  biases set both amplitudes.
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
  [cross-homeostatic rule](https://ideas.repec.org/a/nat/natcom/v16y2025i1d10.1038_s41467-025-60697-2.html)
  targets stable dynamics. In Kernel R the discharge rate cancels from the
  full-phase update, while the thresholds and the actuation factor remain
  in the formula.

**Related principles**

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
- **Formal verification.** Hybrid systems are verified with
  [KeYmaera X](https://logic.kastel.kit.edu/research/keymaerax) and
  [IsaVODEs](https://link.springer.com/article/10.1007/s10817-024-09709-2).
  [De Maria et al.](https://arxiv.org/abs/1808.01893) model spiking networks
  as timed automata, with parameter inference.
  [Bahrami, De Maria, Felty and co-authors](https://arxiv.org/abs/2505.05362)
  prove properties of spiking neuron archetypes in Coq.
