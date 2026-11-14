# SKY130 supervisor campaign: report

Written by `analyze.py` under [`PREDICTION.md`](PREDICTION.md). Simulations of the two-port cell with junction areas; no layout, no silicon.

14 predictions hold, 0 fail, 0 are not established, of 14.

| | Verdict | Numbers |
|---|---|---|
| M1 | holds | runs: 93, not_entered: 0, refusals: 0 |
| M2 | holds | runs: 93, services: 2232, failed_services: 0, runs_with_a_failed_service: 0 |
| M3 | holds | writes_not_as_commanded: 0, fires_outside_reads: 0 |
| M4 | holds | broken: 0 |
| Q1 | holds | runs: 10, not_entered: 0, refusals: 0 |
| Q2 | holds | runs: 10, services: 240, failed_services: 0, runs_with_a_failed_service: 0 |
| Q3 | holds | writes_not_as_commanded: 0, fires_outside_reads: 0 |
| Q4 | holds | broken: 0 |
| Q5 | holds | outside: 0 |
| Q6 | holds | broken: 0 |
| O1 | holds | runs: 10, failing: 0 |
| O2 | holds |  |
| R1 | holds | runs: 10 |
| R2 | holds | failed: 44, services: 240, fraction: 0.18333333333333332 |

Deterministic claim, per configuration: `tt27` holds, `ss27` holds, `ff27` holds, `sf27` holds, `fs27` holds, `tt-40` holds, `tt125` holds, `mm2001` holds, `mm2002` holds. On the nine configurations: holds.

M2: {"statement": "no run had a failed service", "one_sided_95_upper_bound_on_the_fraction_of_runs": 0.03169888899111484}

Comparison: Under the same jump, the supervised cell failed no service in 93 runs, and the cell left to itself failed 44 of 240 services.

## Runs

| Run | Status | Counts | Services | Failed | Refused at period | Wall time |
|---|---|---|---|---|---|---|
| `a00-main-tt27` | complete | yes | 24 | 0 | [None, None] | 289 s |
| `a01-main-ss27` | complete | yes | 24 | 0 | [None, None] | 283 s |
| `a02-main-ff27` | complete | yes | 24 | 0 | [None, None] | 287 s |
| `a03-main-sf27` | complete | yes | 24 | 0 | [None, None] | 292 s |
| `a04-main-fs27` | complete | yes | 24 | 0 | [None, None] | 286 s |
| `a05-main-tt125` | complete | yes | 24 | 0 | [None, None] | 307 s |
| `a06-main-mm2001` | complete | yes | 24 | 0 | [None, None] | 285 s |
| `a07-main-mm2002` | complete | yes | 24 | 0 | [None, None] | 287 s |
| `a08-quiet-tt27` | complete | yes | 24 | 0 | [None, None] | 175 s |
| `a09-outside-tt27` | complete | yes | 24 | 0 | [9, 9] | 201 s |
| `a10-self-tt27` | complete | yes | 24 | 3 | [None, None] | 260 s |
| `a11-main-tt27` | complete | yes | 24 | 0 | [None, None] | 270 s |
| `a12-main-ss27` | complete | yes | 24 | 0 | [None, None] | 275 s |
| `a13-main-ff27` | complete | yes | 24 | 0 | [None, None] | 276 s |
| `a14-main-sf27` | complete | yes | 24 | 0 | [None, None] | 273 s |
| `a15-main-fs27` | complete | yes | 24 | 0 | [None, None] | 286 s |
| `a16-main-tt125` | complete | yes | 24 | 0 | [None, None] | 298 s |
| `a17-main-mm2001` | complete | yes | 24 | 0 | [None, None] | 282 s |
| `a18-main-mm2002` | complete | yes | 24 | 0 | [None, None] | 280 s |
| `a19-quiet-ss27` | complete | yes | 24 | 0 | [None, None] | 174 s |
| `a20-outside-ss27` | complete | yes | 24 | 0 | [9, 9] | 201 s |
| `a21-self-ss27` | complete | yes | 24 | 4 | [None, None] | 255 s |
| `a22-main-tt27` | complete | yes | 24 | 0 | [None, None] | 268 s |
| `a23-main-ss27` | complete | yes | 24 | 0 | [None, None] | 269 s |
| `a24-main-ff27` | complete | yes | 24 | 0 | [None, None] | 280 s |
| `a25-main-sf27` | complete | yes | 24 | 0 | [None, None] | 289 s |
| `a26-main-fs27` | complete | yes | 24 | 0 | [None, None] | 292 s |
| `a27-main-tt125` | complete | yes | 24 | 0 | [None, None] | 313 s |
| `a28-main-mm2001` | complete | yes | 24 | 0 | [None, None] | 283 s |
| `a29-main-mm2002` | complete | yes | 24 | 0 | [None, None] | 281 s |
| `a30-quiet-ff27` | complete | yes | 24 | 0 | [None, None] | 168 s |
| `a31-outside-ff27` | complete | yes | 24 | 0 | [9, 9] | 198 s |
| `a32-self-ff27` | complete | yes | 24 | 4 | [None, None] | 257 s |
| `a33-main-tt27` | complete | yes | 24 | 0 | [None, None] | 275 s |
| `a34-main-ss27` | complete | yes | 24 | 0 | [None, None] | 275 s |
| `a35-main-ff27` | complete | yes | 24 | 0 | [None, None] | 280 s |
| `a36-main-sf27` | complete | yes | 24 | 0 | [None, None] | 273 s |
| `a37-main-fs27` | complete | yes | 24 | 0 | [None, None] | 277 s |
| `a38-main-tt125` | complete | yes | 24 | 0 | [None, None] | 295 s |
| `a39-main-mm2001` | complete | yes | 24 | 0 | [None, None] | 278 s |
| `a40-main-mm2002` | complete | yes | 24 | 0 | [None, None] | 281 s |
| `a41-quiet-sf27` | complete | yes | 24 | 0 | [None, None] | 172 s |
| `a42-outside-sf27` | complete | yes | 24 | 0 | [9, 9] | 200 s |
| `a43-self-sf27` | complete | yes | 24 | 4 | [None, None] | 252 s |
| `a44-main-tt27` | complete | yes | 24 | 0 | [None, None] | 272 s |
| `a45-main-ss27` | complete | yes | 24 | 0 | [None, None] | 267 s |
| `a46-main-ff27` | complete | yes | 24 | 0 | [None, None] | 264 s |
| `a47-main-sf27` | complete | yes | 24 | 0 | [None, None] | 275 s |
| `a48-main-fs27` | complete | yes | 24 | 0 | [None, None] | 277 s |
| `a49-main-tt125` | complete | yes | 24 | 0 | [None, None] | 307 s |
| `a50-main-mm2001` | complete | yes | 24 | 0 | [None, None] | 288 s |
| `a51-main-mm2002` | complete | yes | 24 | 0 | [None, None] | 292 s |
| `a52-quiet-fs27` | complete | yes | 24 | 0 | [None, None] | 186 s |
| `a53-outside-fs27` | complete | yes | 24 | 0 | [9, 9] | 221 s |
| `a54-self-fs27` | complete | yes | 24 | 4 | [None, None] | 293 s |
| `a55-main-tt27` | failed-never-rerun | no |  |  |  |  |
| `a56-main-ss27` | complete | yes | 24 | 0 | [None, None] | 312 s |
| `a57-main-ff27` | complete | yes | 24 | 0 | [None, None] | 305 s |
| `a58-main-sf27` | complete | yes | 24 | 0 | [None, None] | 309 s |
| `a59-main-fs27` | complete | yes | 24 | 0 | [None, None] | 301 s |
| `a60-main-tt125` | complete | yes | 24 | 0 | [None, None] | 305 s |
| `a61-main-mm2001` | complete | yes | 24 | 0 | [None, None] | 287 s |
| `b00-main-tt27` | complete | yes | 24 | 0 | [None, None] | 272 s |
| `b01-main-ss27` | complete | yes | 24 | 0 | [None, None] | 268 s |
| `b02-main-ff27` | complete | yes | 24 | 0 | [None, None] | 277 s |
| `b03-main-sf27` | complete | yes | 24 | 0 | [None, None] | 270 s |
| `b04-main-fs27` | complete | yes | 24 | 0 | [None, None] | 260 s |
| `b05-main-tt125` | complete | yes | 24 | 0 | [None, None] | 286 s |
| `b06-main-mm2001` | complete | yes | 24 | 0 | [None, None] | 261 s |
| `b07-main-mm2002` | complete | yes | 24 | 0 | [None, None] | 262 s |
| `b08-quiet-tt-40` | complete | yes | 24 | 0 | [None, None] | 164 s |
| `b09-outside-tt125` | complete | yes | 24 | 0 | [9, 9] | 203 s |
| `b10-self-tt125` | complete | yes | 24 | 10 | [None, None] | 261 s |
| `b11-main-tt27` | complete | yes | 24 | 0 | [None, None] | 256 s |
| `b12-main-ss27` | complete | yes | 24 | 0 | [None, None] | 265 s |
| `b13-main-ff27` | complete | yes | 24 | 0 | [None, None] | 271 s |
| `b14-main-sf27` | complete | yes | 24 | 0 | [None, None] | 265 s |
| `b15-main-fs27` | complete | yes | 24 | 0 | [None, None] | 274 s |
| `b16-main-tt125` | complete | yes | 24 | 0 | [None, None] | 285 s |
| `b17-main-mm2001` | complete | yes | 24 | 0 | [None, None] | 262 s |
| `b18-main-mm2002` | complete | yes | 24 | 0 | [None, None] | 263 s |
| `b19-quiet-tt125` | complete | yes | 24 | 0 | [None, None] | 181 s |
| `b20-outside-mm2001` | complete | yes | 24 | 0 | [9, 9] | 221 s |
| `b21-self-mm2001` | complete | yes | 24 | 4 | [None, None] | 238 s |
| `b22-main-tt27` | complete | yes | 24 | 0 | [None, None] | 247 s |
| `b23-main-ss27` | complete | yes | 24 | 0 | [None, None] | 250 s |
| `b24-main-ff27` | complete | yes | 24 | 0 | [None, None] | 247 s |
| `b25-main-sf27` | complete | yes | 24 | 0 | [None, None] | 257 s |
| `b26-main-fs27` | complete | yes | 24 | 0 | [None, None] | 261 s |
| `b27-main-tt125` | complete | yes | 24 | 0 | [None, None] | 287 s |
| `b28-main-mm2001` | complete | yes | 24 | 0 | [None, None] | 258 s |
| `b29-main-mm2002` | complete | yes | 24 | 0 | [None, None] | 264 s |
| `b30-quiet-mm2001` | complete | yes | 24 | 0 | [None, None] | 185 s |
| `b31-outside-mm2002` | complete | yes | 24 | 0 | [9, 9] | 226 s |
| `b32-self-mm2002` | complete | yes | 24 | 4 | [None, None] | 244 s |
| `b33-main-tt27` | complete | yes | 24 | 0 | [None, None] | 258 s |
| `b34-main-ss27` | complete | yes | 24 | 0 | [None, None] | 258 s |
| `b35-main-ff27` | complete | yes | 24 | 0 | [None, None] | 263 s |
| `b36-main-sf27` | complete | yes | 24 | 0 | [None, None] | 263 s |
| `b37-main-fs27` | complete | yes | 24 | 0 | [None, None] | 260 s |
| `b38-main-tt125` | complete | yes | 24 | 0 | [None, None] | 287 s |
| `b39-main-mm2001` | complete | yes | 24 | 0 | [None, None] | 261 s |
| `b40-main-mm2002` | complete | yes | 24 | 0 | [None, None] | 259 s |
| `b41-quiet-mm2002` | complete | yes | 24 | 0 | [None, None] | 190 s |
| `b42-outside-tt27` | complete | yes | 24 | 0 | [9, 9] | 177 s |
| `b43-self-tt27` | complete | yes | 24 | 3 | [None, None] | 233 s |
| `b44-main-tt27` | complete | yes | 24 | 0 | [None, None] | 239 s |
| `b45-main-ss27` | complete | yes | 24 | 0 | [None, None] | 250 s |
| `b46-main-ff27` | complete | yes | 24 | 0 | [None, None] | 245 s |
| `b47-main-sf27` | complete | yes | 24 | 0 | [None, None] | 254 s |
| `b48-main-fs27` | complete | yes | 24 | 0 | [None, None] | 265 s |
| `b49-main-tt125` | complete | yes | 24 | 0 | [None, None] | 284 s |
| `b50-main-mm2001` | complete | yes | 24 | 0 | [None, None] | 267 s |
| `b51-main-mm2002` | complete | yes | 24 | 0 | [None, None] | 265 s |
| `b52-quiet-tt27` | complete | yes | 24 | 0 | [None, None] | 162 s |
| `b53-outside-ss27` | complete | yes | 24 | 0 | [9, 9] | 190 s |
| `b54-self-ss27` | complete | yes | 24 | 4 | [None, None] | 249 s |
| `b55-main-tt27` | complete | yes | 24 | 0 | [None, None] | 261 s |
| `b56-main-ss27` | complete | yes | 24 | 0 | [None, None] | 274 s |
| `b57-main-ff27` | complete | yes | 24 | 0 | [None, None] | 273 s |
| `b58-main-sf27` | complete | yes | 24 | 0 | [None, None] | 277 s |
| `b59-main-fs27` | complete | yes | 24 | 0 | [None, None] | 274 s |
| `b60-main-tt125` | complete | yes | 24 | 0 | [None, None] | 287 s |
| `b61-main-mm2001` | complete | yes | 24 | 0 | [None, None] | 274 s |

Runs that do not count: 1 of 124. `a55-main-tt27` (failed-never-rerun)

## Failed services

| Run | Period | Read | FIRE | Latency | Writes |
|---|---|---|---|---|---|
| `a10-self-tt27` | 15 | port1 | 0 | None | [1, 0] |
| `a10-self-tt27` | 16 | port2 | 0 | None | [0, 1] |
| `a10-self-tt27` | 22 | port2 | 0 | None | [0, 1] |
| `a21-self-ss27` | 15 | port1 | 0 | None | [1, 0] |
| `a21-self-ss27` | 16 | port2 | 0 | None | [0, 1] |
| `a21-self-ss27` | 21 | port1 | 0 | None | [1, 0] |
| `a21-self-ss27` | 22 | port2 | 0 | None | [0, 1] |
| `a32-self-ff27` | 9 | port1 | 0 | None | [1, 0] |
| `a32-self-ff27` | 10 | port2 | 0 | None | [0, 1] |
| `a32-self-ff27` | 18 | port1 | 0 | None | [1, 0] |
| `a32-self-ff27` | 19 | port2 | 0 | None | [0, 1] |
| `a43-self-sf27` | 10 | port2 | 0 | None | [0, 1] |
| `a43-self-sf27` | 12 | port1 | 0 | None | [1, 0] |
| `a43-self-sf27` | 18 | port1 | 0 | None | [1, 0] |
| `a43-self-sf27` | 19 | port2 | 0 | None | [0, 1] |
| `a54-self-fs27` | 15 | port1 | 0 | None | [1, 0] |
| `a54-self-fs27` | 16 | port2 | 0 | None | [0, 1] |
| `a54-self-fs27` | 21 | port1 | 0 | None | [1, 0] |
| `a54-self-fs27` | 22 | port2 | 0 | None | [0, 1] |
| `b10-self-tt125` | 9 | port1 | 0 | None | [1, 0] |
| `b10-self-tt125` | 10 | port2 | 0 | None | [0, 1] |
| `b10-self-tt125` | 12 | port1 | 0 | None | [1, 0] |
| `b10-self-tt125` | 13 | port2 | 0 | None | [0, 1] |
| `b10-self-tt125` | 15 | port1 | 0 | None | [1, 0] |
| `b10-self-tt125` | 16 | port2 | 0 | None | [0, 1] |
| `b10-self-tt125` | 20 | joint | 1 | 0.2820480689086326 | [0, 0] |
| `b10-self-tt125` | 21 | port1 | 0 | None | [1, 0] |
| `b10-self-tt125` | 22 | port2 | 0 | None | [0, 1] |
| `b10-self-tt125` | 23 | joint | 1 | 0.28003437448605206 | [0, 0] |
| `b21-self-mm2001` | 12 | port1 | 0 | None | [1, 0] |
| `b21-self-mm2001` | 13 | port2 | 0 | None | [0, 1] |
| `b21-self-mm2001` | 21 | port1 | 0 | None | [1, 0] |
| `b21-self-mm2001` | 22 | port2 | 0 | None | [0, 1] |
| `b32-self-mm2002` | 9 | port1 | 0 | None | [1, 0] |
| `b32-self-mm2002` | 10 | port2 | 0 | None | [0, 1] |
| `b32-self-mm2002` | 16 | port2 | 0 | None | [0, 1] |
| `b32-self-mm2002` | 18 | port1 | 0 | None | [1, 0] |
| `b43-self-tt27` | 15 | port1 | 0 | None | [1, 0] |
| `b43-self-tt27` | 16 | port2 | 0 | None | [0, 1] |
| `b43-self-tt27` | 22 | port2 | 0 | None | [0, 1] |
| `b54-self-ss27` | 15 | port1 | 0 | None | [1, 0] |
| `b54-self-ss27` | 16 | port2 | 0 | None | [0, 1] |
| `b54-self-ss27` | 21 | port1 | 0 | None | [1, 0] |
| `b54-self-ss27` | 22 | port2 | 0 | None | [0, 1] |
