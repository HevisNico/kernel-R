# A dedicated noise study: commitment

Fixed by the owner on 2026-11-15 and pushed alone on the branch `research/network-noise-study-commitment`,
**before the network results of campaign 2 are known**: when this file is pushed, no network run of campaign 2 has
started. It changes nothing in campaigns 1, 2 and 3.

1. **After campaign 3, whatever campaigns 2 and 3 give**, a dedicated noise study runs, as a separate claim. It
   neither strengthens nor weakens the claims of campaigns 1 to 3.
2. **First, an independent noise model**, drawn from the noise models of the PDK devices (thermal and 1/f) rather
   than from injected sources fitted to the cell: for example, from an ngspice `.noise` analysis at the operating
   points of the cell, turned into transient sources.
   - Its **feasibility is checked first**.
   - It is **validated on its own, by criteria fixed in advance**, before any campaign uses it: for example, the
     spectrum of the transient noise against the `.noise` spectrum, within a stated tolerance, over the band that
     matters.
3. **Then a preregistered campaign under that model**, on new instances, with 3 to 5 noisy runs per instance and
   the per-port claims N-own and N-word. Its size and budget are fixed in its own preregistration.
4. **Campaign 3 is unchanged** ([`../network-circuit-ring-campaign-3/COMMITMENT.md`](../network-circuit-ring-campaign-3/COMMITMENT.md),
   commit `d758fdb`, and its amendment 1, commit `e1e4a60`).
