# Stronger no-noise extension

Read THEOREM.md. This layer reuses the unchanged local certificates and simulator
in the parent directory; it does not reinterpret the noisy theorem as periodic.

- Zero charge noise and identical waveforms: T >= 7.5 with fixed links, any finite N.
- Link phase error bounded by +/-sigma_i: T >= 7.5 + 2*sum(sigma_i).
- Parameters C,Lm,Ls,Le,M may still drift inside the physical box.
- K=3N+8 source pulses produce eight outputs at the root.

From the parent directory:

```sh
python -B periodic/certify_chain.py results/eps0.1/nu0_alpha0.json --n 32 --k 104 --period 7.5
python -B periodic/tests.py
python -B periodic/validate.py
python -B periodic/validate.py --verify-record
```

The baseline full campaign and its source manifest remain in ../evidence.
This stronger layer has its own report, source manifest, traces and numerical
refinement in evidence/. It checks the sign of the first firing advance, constant
rest latency despite parameter drift, periodic tails with fixed links, and the
phase envelope under alternating endpoint jitter aligned across the whole path.
