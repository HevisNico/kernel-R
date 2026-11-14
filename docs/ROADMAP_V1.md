# Roadmap to v1.0.0

**v1.0.0 is released when this sentence is true as written:**

> A network that learns in closed loop, proved never to saturate and to
> settle its memory, whose learned state can be predicted from measurable
> margins, together with the conditions under which that prediction holds.

"Measurable" means measured on transistor-level simulations of the cell
(SKY130, ngspice), including extracted layout parasitics where available.
Silicon is out of scope for v1.0.0 and is stated as a limit.

## Definition of done

| Part of the sentence | Required for v1.0.0 | Status |
|---|---|---|
| A network that learns in closed loop | A Lean theorem: every native R network that meets explicit, checkable conditions (timing separation, phases, margins) refines the dated guarded model | Proved for the guarded model; native refinement in progress on the two-cell reciprocal witness |
| proved never to saturate and to settle its memory | The network theorem's write bounds, rail headroom and memory stabilization, carried to native networks by the refinement theorem | Proved in the guarded model |
| whose learned state can be predicted from measurable margins | A documented and scripted map from the quantities the port-by-port certification measures (margins, read errors, doses) to the constants of the theorem | Not written yet |
| ... can be predicted ... | A preregistered experiment: a small cyclic network of cells (2 to 3) simulated at transistor level; margins measured per cell; the learned state predicted by the theorem before the network run; then the run | Not started |
| together with the conditions under which that prediction holds | Every hypothesis listed, each with a checked counterexample | Largely done |

## Also for a clean release

- Every open pull request merged or closed.
- README rewritten around the sentence above.
- Release notes with all corrections (the 125 °C artifact of netlists
  without junction areas; the repetition bound counted on independent runs)
  and all limits.
- Zenodo record complete; full waveforms archived publicly.

## Not blocking v1.0.0

The supervisor campaign on the extracted layout, the safety–utility curve
of the certified fraction, and the three rest-state refusals of layout 2.2
enter v1.0.0 if they are ready; they do not block it.
