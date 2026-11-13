# Preflight of the repetitions, machine A

Written by `rep_analyze.py preflight` on machine A. Nominal cell, step 200n.

| Check | Result |
|---|---|
| A training cut after five pulses, with the process id fixed, gives the first five rows of the complete training | yes, byte for byte |
| Two noisy runs with the same noise number give the same rows, charges, noise and trace | yes, byte for byte |
| A noisy run with another noise number gives another noise and other rows | yes |

| Run | Noise number | Rows (SHA-256) | Noise (SHA-256) |
|---|---|---|---|
| `p_trunc` | 900000 | `3f66f83056450e575f43669588b815aab6a1bc752325c81a1d83af631e9773ba` | `e47afc6a60c3c44b7bb2bf3e3f1573a1b9f14a539e1b2707b519c9b3c20daa0e` |
| `p_noise_a` | 900001 | `e2399fba553d0679de41bd94d5b398b3d931f44ebaaf7590100be77f65406414` | `de2992d1b438efd45dc2e6c59ba643cc45c43f498f955fbd2b519c24b220b1b0` |
| `p_noise_b` | 900001 | `e2399fba553d0679de41bd94d5b398b3d931f44ebaaf7590100be77f65406414` | `de2992d1b438efd45dc2e6c59ba643cc45c43f498f955fbd2b519c24b220b1b0` |
| `p_noise_c` | 900002 | `7e3f55b3e2924013c48ba8d995f6c0fbc0cdfbd687237ab5969af0b0b033d3bb` | `7d1af42f46635e8b068b0213d038a5f0120370f1cbea6ea2142e448ddde28f43` |
