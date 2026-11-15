# Two-layer design addendum

## Training from emitted pulses

1. Train layer 1 as in Phase 0. Each cell receives its own joint target, makes its own FIRE decision and updates its active ports on silence. Use $Q_1+1$ presentations. Keep layer 2 disabled during this stage.
2. Freeze layer 1 and use it in read-only mode. To teach layer-2 cell $i$, broadcast the external stimulus computed for that cell. Route each actual layer-1 FIRE along its fixed wire, using that output's FIRE date plus the wire delay. An upstream silence produces no pulse. Only the selected downstream cell receives this volley. It reads the actual arrived mask, doses its active ports on silence and stops writing on FIRE. Teach one downstream cell per slot, in round and cell order, for $Q_2+1$ rounds.
3. Run both layers read-only for tests. Choose held-out external patterns distinct from both stages' training stimuli. A test can be replayed from the completed training checkpoint. Separate teaching slots through full settlement. The Lean design names this premise `TrainingSeparation`.

The second layer's training input depends on the first layer's learned outputs. There is no external source for its ports. The write decision is local feedback, and the routing between layers is feedforward.

## Which conjunctions are reachable?

Let $T_a$ be the target of upstream cell $a$ and $U_i$ the set of upstream outputs required by downstream cell $i$. The smallest teaching stimulus is the union $S_i = \bigcup_{a\in U_i} T_a$. Its upstream FIRE mask contains $U_i$. It equals $U_i$ exactly when every outside target $T_b$, for $b\notin U_i$, has a bit outside $S_i$. If this check fails, every stimulus that makes all cells in $U_i$ fire also makes at least one outside cell fire. Parameter membership checks the canonical stimulus, using the entire emitted mask.

After training, downstream cell $i$ fires on external pattern $x$ exactly when $S_i\subseteq x$. This class realizes conjunctions of unions of reachable feature sets, so adding the second layer does not produce XOR, exact-pattern detection against supersets, or an output with two incomparable minimal positive patterns. For a control, consider upstream targets $\{0,1\}$, $\{1,2\}$ and $\{0,2\}$. Asking for just the first two upstream FIREs fails reachability, since their union also fires the third. [TwoLayerTarget.lean](TwoLayerTarget.lean) checks this case and an accepted cascade. In the accepted example the upstream targets are $\{0,1\}$, $\{0,2\}$ and $\{0,3\}$. Downstream targets $\{0,1\}$ and $\{1,2\}$ therefore recognize external conjunctions $\{0,1,2\}$ and $\{0,2,3\}$, respectively.

## Calibration hypothesis

`CalibratedAdditiveRead` applies to a particular cell, reachable guarded gain state, active mask and training or test budget. Let $G=h_i+\sum_{j\in S}g_{ij}$ and let $Z$ be the joint read score reported by a calibration fixed before the validation run. Both scores and the threshold $\theta_i$ use the same integer units. The hypothesis requires both

- $-\varepsilon\le Z-G\le\varepsilon$ uniformly for the relevant masks, gain stages, histories and skew, including nonadditivity, bias errors and quantization.
- The extracted FIRE bit equals the threshold comparison $Z\ge\theta_i$. Count emissions through full settlement. If there is a FIRE it is unique, arrives after the last input, and lies within the declared decision window. Exactly the active ports arrive, each once between the slot start and its skew bound. The skew bound lies within the decision window, which ends before the next prepared slot.

The first condition turns the calibrated residual into the additive model's signed error. The second establishes that the normalized score encodes the actual event. A native log-gain increment changes pulse amplitude multiplicatively. Single-port measurements can inform the calibration, while the residual enclosure must cover whole joint reads and every certified dose stage. In particular an empirically measured residual supports only the sampled settings unless an independent enclosure establishes the full window. The timing window must be selected using the physical trace and the declared settlement protocol.

The frozen `TwoLayerCoincidenceRecognition : Prop` uses `CascadeCalibration` as its named bridge premise. It applies `CalibratedAdditiveRead` at each relevant slot and checks that downstream arrivals are the routed upstream emissions. It specifies exact downstream training masks, predicted stops and headroom for the reconstructed guarded memory, and correct downstream FIRE decisions across the external Boolean cube. It assumes supplied observations. Physical execution existence, physical dose footprints and the calibration enclosure remain obligations for a native or circuit refinement. Only the single-layer guarded theorem is proved in this PR.
