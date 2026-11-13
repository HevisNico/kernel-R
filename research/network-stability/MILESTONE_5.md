# Milestone 5 — autonomous feedback

[AutonomousFeedback.lean](AutonomousFeedback.lean) starts from a finite seed queue. Each probe specifies a receiving cell, a bias relative to its initial memory, a nonnegative routed contribution, and the list of probes it emits on FIRE. The next probe is the head of the FIFO queue. Its score is bias plus routed contribution plus the dose times the stored write count, with read error added at the decision. FIRE protects memory and appends its routed probes. Silence writes one dose and appends nothing. Increasing the routed contribution can suppress a write, as the checked control demonstrates. There is no calendar, budget gate, or clipping in the transition.

## Certificate and theorem

Choose natural constants $Q,d,B,U,W,\eta$ before quantifying over the cell count $N$. Fix the router and the initial queue across error traces. Each probe $p$ has a weight $w(p)$ and a reserve $r_i(p)$ for each cell $i$. Let $D(p)$ be the list of downstream probes, counted with multiplicity. The certificate requires

\[
\eta>0,\qquad \eta+\sum_{q\in D(p)}w(q)\le w(p),\qquad
\sum_{q\in D(p)}r_i(q)\le r_i(p),\qquad 1\le r_{\operatorname{cell}(p)}(p).
\]

The seed queue has total weight at most $WN$ and each seed reserve is at most $Q$. The scalar check counts the worst case in which every processed probe fires. The local reserve covers whichever action occurs. A FIRE transfers reserve to its successors, and silence pays for a write at the receiving cell. The weights themselves may vary with probe and network size. The uniform hypothesis is the total seed bound and the fixed decrease $\eta$, with no uniform upper bound on an individual probe weight.

The scalar queue potential decreases by at least $\eta$ at every active step. Every declared FIRE descendant therefore has strictly smaller probe-type weight than its parent. Termination here relies on that acyclic rank on probe types, even for cyclic wiring on cells. [Milestone 7](MILESTONE_7.md) uses the local reserve alone to prove memory stabilization under continuing traffic. Hence the queue is empty by $WN$ steps and stays empty. Separately, for each cell, the number of writes plus its remaining queue reserve never increases. This gives at most $Q$ writes per cell and $QN$ in total at every prefix. If the initial memories lie in $[0,B]$ and $B+dQ<U$, the stored values stay strictly below $U$.

The one-sided score margins from milestone 4 are checked along the nominal autonomous run. With those margins, the first differing decision argument gives the same queue, write counts, and ordered probe/FIRE log under every admissible error trace through the common stopping horizon. The terminal state is therefore unique for the fixed FIFO policy. The model does not compare different scheduling policies. No future exogenous probes arrive after the seed.

## Counterexample

[FeedbackExamples.lean](FeedbackExamples.lean) supplies a one-cell FIRE that replaces its own probe indefinitely. Unit weights and reserves pass the numerical checks at $\eta=0$ with $Q=W=1$. No weights give a strict positive margin, and no finite execution prefix empties the queue. This demonstrates the failure of the general termination conclusion when strict decrease is dropped. The certificate is sufficient and may reject some terminating guards, since it includes every declared FIRE successor. It concerns the transition model and leaves realization by native hybrid R open.
