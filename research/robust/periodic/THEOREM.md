# Constant-period robust prepared chains without charge noise or waveform variation

This sharpens ../THEOREM_N.md under **nu=0 and alpha=0**. The five physical
per-port parameters may still drift arbitrarily within their certified boxes.
Prepared states, input counts K>=3N+1 and the local guard/order conditions are
unchanged. There is no assumption that auxiliary latencies repeat.

## Constant main latency after recovery

The first three silent inputs give exact doses 0.6, independent of Le(t), so
gain is then g*=g_initial*exp(1.8). Subsequent ERRORs are protected and give no
dose. MARK never changes b. Thus g* and b are fixed even though C,Lm,Ls,Le,M drift.
The active gain stays below the minimum cap, so drift of C cannot affect it.

After any firing and full recovery, the guard returns q exactly to r. With no
charge disturbance, silence preserves q=r. A subsequent canonical input obeys

    q_rest(t) = r + g* h(t).

Its first threshold crossing therefore has the same latency ell in (0.5,0.9]
on every such input. The auxiliary's history cannot affect this equation:
local ordering keeps all gain actuation outside the admitted firing interval.
This reasoning would fail with arbitrary charge noise or pulse amplitude changes.

## The exceptional first output advances; it does not delay

Before any silent input, q-r >= -delta (delta=1e-5). During its raw pulse the
gain is at least g_initial_min=.3 exp(-delta). The silent-input lemma rules out
firing. At raw end, variation of constants gives

    q(1)-r >= -delta + g_initial_min*h(1) > 0.

certify_chain.py checks the last strict inequality with the independent integer
interval arithmetic. Subsequent silence preserves nonnegative excess, and
nonnegative input drive preserves it through the next two silent inputs.
Consequently the first emitting input starts with q-r=x>=0. Before its firing,

    q_first(t) = q_rest(t) + x exp(-kappa*t) >= q_rest(t).

By continuity and first-crossing semantics its latency ell_first is at most ell.
Set a=ell-ell_first>=0; the local latency hull also gives a<=0.4. This is an
advance of the first output. With otherwise periodic inputs, the first output
gap is T+a, not T-a. No extra first-firing penalty is necessary in a lower gap
bound.

## Packet invariant and prefix removal

Use a packet of L outputs with ideal phase c, first-output advance a in [0,0.4],
and phase errors e_k in [-J,J]:

    t_0 = c-a+e_0,
    t_k = c+kT+e_k,     1 <= k < L.

Its first gap is at least T+a-2J >= T-2J; all later gaps are at least T-2J.
A source train is this packet with a=0,J=0. A link with fixed center delay d and
per-pulse errors in [-sigma,sigma] increases J to J+sigma and adds d to c.
Here 0<=sigma<=.05 and d in [.3+sigma,.4-sigma], so all actual delays remain
within the local theorem's [.3,.4] interval.

A receiving cell discards precisely the first three inputs. Its first emitted
pulse corresponds to input 3, and all emitting inputs therefore lie beyond the
incoming exceptional prefix. Its first output acquires its own nonnegative
advance a_new, and every later output adds the same latency ell. Output errors
are the corresponding surviving input errors, with no extra latency error.
Thus the output has the same packet form and J; there is one exceptional output,
not an accumulated list of first-firing penalties. Length decreases by three.
This proves the packet invariant by induction through the chain.

## Sufficient period and consequences

Writing J_i=sum_{h<i} sigma_h for the jitter at cell i's input, the local lemma
applies whenever T-2J_i>=7.5. It is sufficient that

    T >= 7.5 + 2 sum_{h=0}^{N-2} sigma_h.

The factor two is necessary for this envelope: two consecutive pulses may have
opposite phase errors. It is a sufficient bound, not a claim of optimality for
the full hybrid model.

With fixed links (all sigma_h=0), **T>=7.5 suffices for every finite N**. Period 8
therefore works independently of depth. More generally, a global sum sigma<=.15
allows period 8 for every finite N. A fixed per-link sigma=.05 without a global
budget still accumulates, giving T>=7.5+.1(N-1).

Counts, three exact doses per cell, unchanged recovery, 0/8 to 8/8 frozen probes
and the conservative global terminal date are as in ../THEOREM_N.md. For fixed
links, every cell's outputs after its first output have exactly period T.
For variable link delays, phase jitter accumulates but intrinsic latency jitter
does not. K=3N+8 leaves exactly eight root outputs.

This is a written packet induction using the checked local bounds, plus one
checked residual inequality. The numerical tests below are evidence, not a
Lean formalization or an exhaustive proof over measurable drift histories.
