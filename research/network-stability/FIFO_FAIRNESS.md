# FIFO implements continuation fairness

[ConcreteFairness.lean](ConcreteFairness.lean) proves that clean FIFO is
continuation-fair under the milestone 8 hypotheses. For each finite
alternative continuation, there is a later FIFO prefix whose write vector
dominates the alternative endpoint in **all** coordinates simultaneously.
No bound on queue lifetime and no scalar decrease certificate is used.

FIFO appends new work after existing occurrences. For the first desired
probe of an alternative path, commute each earlier FIFO head across that
selection. The strong diamond transports the remaining alternative path
without increasing its length budget. FIFO either services the desired
occurrence or services an indistinguishable occurrence of the same probe
type first. Induct on the budget of the remaining path. The proof uses the
specific FIFO rule and its treatment of occurrences; it leaves a theorem
for general occurrence-fair schedulers open.

When the inherited nominal read margins hold for every FIFO prefix,
the existing invariance theorem gives the same projected trajectory for
the noisy FIFO run. Thus its writes have the same continuation-fair
domination property.
