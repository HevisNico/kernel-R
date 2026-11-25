# The yield lot's inverter K3 room under noise4's allowance (read-only recount, 2026-11-25)

**Method.** recount_noise4_lot.py (in research/layered-networks) regated every stored lot gate file with noise4.py's
own functions and the gate's mirror at kit d599300. Under the noise.json allowance it reproduces every stored K3
verdict. The output is RECOUNT_NOISE4.json, per instance and inverter.

**Allowance at K3**: noise.json delta 2011/1e6 and eta 2353/1e6; noise4 delta 2506/1e6 and eta 2597/1e6.

| Group | Inverters with K3: noise.json → noise4 | Instances with K3 room: lot → noise4 | Smallest silence margin | Smallest firing margin |
|---|---|---|---|---|
| NOT1 | 8/8 → 8/8 | 5/8 → 5/8 | 0.1108 → 0.1099 | 0.2484 → 0.2476 |
| XOR3 | 48/48 → 48/48 | 6/24 → 6/24 | 0.0919 → 0.0910 | 0.2171 → 0.2163 |
| ANDOR3 (no inverters) | — | 3/24 → 3/24 | — | — |

No instance gains or loses K3 room. The lot's K3 rates, and so the campaign sizes, are unchanged under noise4.
