# V5 — unedited registered evidence report

**Scope:** service under fixed H=150 and the registered sensor/dose laws.
No runtime external authority or optimistic learned law is used. This is a
discrete-model result, not transistor validation or a full proof of arbitrary
Python execution. The Lean kernel/composition and Python evidence checks have
distinct roles. Source and protocol identity are checked by mandatory preflight.

## Already explored replication

The known v3 scenario was explored before preregistration. Its reproduction
is not a blind prediction. The <2.82% claim is restricted to that scenario
and the declared oracle action family; it is not a random-case guarantee.

Early-refill cost: 5671; safe-prudent cost: 5821.
Oracle cost: 5516; relative excess: 2.810007% (exact fraction 155/5516).

## New seeded cases

| Seed | Early cost | Prudent cost | Oracle | Gap % | Probes | Writes | Min pre | Final post | Saturation | Unsafe pre/post |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|
| 2026111301 | 4658 | 4921 | 4561 | 2.126727 | 1058 | 360 | 320 | 440 | 0 | 0/0 |
| 2026111302 | 7706 | 7761 | 7439 | 3.589192 | 1266 | 644 | 210 | 450 | 0 | 0/0 |
| 2026111303 | 8521 | 8521 | 8221 | 3.649191 | 1321 | 720 | 200 | 440 | 0 | 0/0 |
| 2026111304 | 2800 | 3231 | 2745 | 2.003643 | 890 | 191 | 340 | 560 | 0 | 0/0 |
| 2026111305 | 3435 | 3701 | 3305 | 3.933434 | 1055 | 238 | 290 | 590 | 0 | 0/0 |
| 2026111306 | 7948 | 7981 | 7663 | 3.71917 | 1278 | 667 | 140 | 510 | 0 | 0/0 |
| 2026111307 | 8331 | 8351 | 8052 | 3.464978 | 1291 | 704 | 140 | 490 | 0 | 0/0 |
| 2026111308 | 5683 | 5831 | 5455 | 4.179652 | 1163 | 452 | 140 | 550 | 0 | 0/0 |
| 2026111309 | 5827 | 5981 | 5605 | 3.960749 | 1167 | 466 | 140 | 470 | 0 | 0/0 |
| 2026111310 | 5690 | 5861 | 5483 | 3.775305 | 1150 | 454 | 160 | 360 | 0 | 0/0 |
| 2026111311 | 5622 | 5781 | 5396 | 4.188288 | 1162 | 446 | 160 | 430 | 0 | 0/0 |
| 2026111312 | 5732 | 5891 | 5507 | 4.085709 | 1162 | 457 | 150 | 450 | 0 | 0/0 |

Seeded distributions (min / median / max):

```json
{
  "cost": {
    "max": 8521,
    "median": 5711.0,
    "min": 2800
  },
  "final_post": {
    "max": 590,
    "median": 460.0,
    "min": 360
  },
  "gap_percent": {
    "max": 4.188288,
    "median": 3.7472374999999998,
    "min": 2.003643
  },
  "min_pre": {
    "max": 340,
    "median": 160.0,
    "min": 140
  },
  "probes": {
    "max": 1321,
    "median": 1162.5,
    "min": 890
  },
  "saturation_loss": {
    "max": 0,
    "median": 0.0,
    "min": 0
  },
  "writes": {
    "max": 720,
    "median": 455.5,
    "min": 191
  }
}
```

Seeded gaps below 2.82%: 2/12.
Seeded early-refill cases without cost improvement over prudent: 1/12.
These counts have no pass threshold and imply no population confidence or significance.

## Oracle scope and accounting

The offline oracle knows all future loss and noise. It minimizes probes+10*writes
within the registered Ready-at-next-probe, one-command action family. It is not
an autonomous controller or a global physical optimum. There is no terminal
inventory value; saturation and final reserves are retained separately below.

| Case | Oracle probes | Writes | Saturation | Final post | Forward/backward agree |
|---|---:|---:|---:|---:|---|
| known | 1016 | 450 | 110 | 330 | True |
| seed2026111301 | 961 | 360 | 0 | 440 | True |
| seed2026111302 | 999 | 644 | 130 | 320 | True |
| seed2026111303 | 1021 | 720 | 0 | 440 | True |
| seed2026111304 | 825 | 192 | 220 | 560 | True |
| seed2026111305 | 925 | 238 | 170 | 420 | True |
| seed2026111306 | 1003 | 666 | 20 | 270 | True |
| seed2026111307 | 1022 | 703 | 0 | 270 | True |
| seed2026111308 | 935 | 452 | 210 | 340 | True |
| seed2026111309 | 935 | 467 | 320 | 370 | True |
| seed2026111310 | 933 | 455 | 250 | 330 | True |
| seed2026111311 | 926 | 447 | 290 | 360 | True |
| seed2026111312 | 937 | 457 | 150 | 300 | True |

## Outside-boundary control

Refusal timestamps: [661].
Unsafe pre/post periods: 658/658.
Unsafe pre range: [663] to [1320].
Conditional pre/post claim violations: []/[].
False fresh sampled claims: [].
All exposure remains in the saved trace. No service guarantee is asserted once
the fixed physical premise fails. Refusal at an observed lower-bound violation
does not establish detection of every small or between-probe excursion.

## Registered outcomes

| Outcome | Verdict |
|---|---|
| S1 | PASS |
| S2 | PASS |
| S3 | PASS |
| S4 | PASS |
| S5 | PASS |
| S6 | PASS |

Audit issues: 0.

The report audits existing records. It does not execute another controller
trajectory. Every failed prediction and partial/missing record is retained.
