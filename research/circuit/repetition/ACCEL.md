# Solver and output options

Written by `rep_analyze.py accel`. Four runs of the nominal training without noise, at 200 ns, run at the same time on one machine.

| Run | KLU | Binary output | Rows (SHA-256) | Charges (SHA-256) | Same as the base | Simulator, s | Reading, s | Total, s |
|---|---|---|---|---|---|---|---|---|
| `a_base` | no | no | `2028416e1e270eea` | `292bf2a48cc5e5e5` | yes | 130 | 1 | 130 |
| `a_klu` | yes | no | `cbfe5c48b6b84365` | `1ea6889e349747af` | **no** | 131 | 0 | 132 |
| `a_bin` | no | yes | `2028416e1e270eea` | `292bf2a48cc5e5e5` | yes | 128 | 0 | 128 |
| `a_klu_bin` | yes | yes | `cbfe5c48b6b84365` | `1ea6889e349747af` | **no** | 135 | 0 | 135 |

Rows of the base run against the nominal training of the certification campaign (`2028416e1e270eea`): the same, byte for byte.

Rule of `PREDICTION.md`: an option is adopted only if its rows and charges are those of the base run byte for byte and its total time is lower. **Binary output: adopted. KLU: not adopted.**
