# Negation by two rails

A network of these cells has no negation: one more pulse can only help a cell to fire. So its functions are the
monotone ones, and the exclusive OR is not among them ([MONOTONE_DNF.md](MONOTONE_DNF.md)).

**Give each input on two lines, the input and its complement, and every Boolean function becomes one of them.**
No cell is changed and no inhibition is used.

## The statement

[`TwoRailsTarget.lean`](TwoRailsTarget.lean) fixes it and [`TwoRails.lean`](TwoRails.lean) proves it, as
`every_function_on_two_rails`:

> For every number of inputs `M` and every Boolean function `f` of `M` inputs, there is an admissible cascade on
> `2 M` lines and one of its outputs whose predicted answer, on the two rails of each input pattern, is `f`.

- **The two rails** of an input pattern (`rails`): line `j` carries input `j`, and line `M + j` carries its
  complement. Of the `2^(2M)` patterns of lines, the `2^M` that are the rails of an input pattern are the ones
  the statement is about.
- **Admissible cascade** and **predicted answer** are those of `monotone_characterization`: `Cascade.Valid` and
  `output`. The proof is a corollary of that theorem. It builds a monotone function of the `2 M` lines that
  equals `f` on the rails, and applies the characterization to it.

The audit requires the theorem with this exact type, and allows only `propext`, `Classical.choice` and
`Quot.sound`.

## The exclusive OR, and campaign 6

On two rails, the exclusive OR of `p` and `q` is `(p and not q) or (not p and q)`
(`exclusive_or_on_two_rails`). That is the function campaign 6's circuit learned, `(A and B) or (C and D)`, read
with `A = p`, `B = not q`, `C = not p` and `D = q`. Campaign 6's circuit has no rails of its own: something
outside would have to put `p`, `not q`, `not p` and `q` on its four lines.

Campaign 6's primary claim covers all 16 patterns of its four inputs, on 4 of 4 eligible instances
([report](../learned-dnf-circuit-campaign-6/REPORT.md)). The four patterns that are the rails of `p` and `q`
are among those 16: `AB` and `CD`, where the circuit fires, and `BC` and `AD`, where it stays silent.

**This is a reading of campaign 6 made afterwards.** Campaign 6 did not preregister an exclusive OR, and nothing
here adds a claim to it.

## What this does not give

- **A complement made by the network.** Something outside must supply each input on both lines. A cell that
  fires when its input is absent would need an inhibition, which the cell laws used here do not have and which
  the proofs of this folder do not cover.
- **A trained network.** The statement is about the predicted answer of an admissible cascade. That a network
  trained by its own pulses gives that answer is the recognition theorem, under its premises.
- **A small network.** The cascade has one first-layer cell for each input pattern that makes the function true,
  with no bound on their number, and each of those cells reads `M` lines, one rail for each input. With
  two-port cells, a term has at most two lines: the exclusive OR of two inputs fits, the parity of three does
  not, without the layered cascades.
- **A circuit.** Nothing here was simulated.
