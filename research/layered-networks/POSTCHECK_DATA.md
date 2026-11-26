# Data for a post-campaign check (item 3, 2026-11-26): a proposal, not a decision

The question: after the campaign, we want to run the kernel's recognition theorem and check its three open premises on
the stage-N records:
- the recognition theorem: `layered_recognition_at` and `layered_inverters_chained`;
- the premises: the leak along the trajectory, the latch delay and the routed walk.

What does each need? Are the kept records enough, or are raw traces needed? The answers below are read from the code at
54689b62 / a2ea377f. The sizes for NOT1 are measured. The sizes for XOR3 and ANDOR3 are estimates, and each says what
it rests on.

## What a stage-N round keeps today

- **The record** (`N<n>/noisy_record.json`, kept). It holds:
  - per R-cell read: start, arrivals, latch (the rise of x<c>.p through 0.9 V, to 1 ns), emission (snap(latch+δ)−δ)
    and second (a later rise);
  - per inverter read: start, arrival, latch and emission;
  - per slot, u_p for every port: mean(vmem_p) − mean(sum_p) over the 35 µs window before T − 3 tu
    (instrument.py:9, :290);
  - inverter_x: x_tau, and x_D at T + D − 2 ns.
- **The trace** (`trace.raw`). It is deleted once the round's comparison agrees, except on keep_raw instances. Besides
  the top-level nodes, it saves (instrument.py:267):
  - per R cell: x<c>.p, x<c>.vmem<p> and x<c>.x<p>.sum for every port;
  - per inverter: x<inv>.p and x<inv>.vq;
  - in noisy rounds, the noise nodes.

  The header of a NOT1 N0 trace (52 vectors, 46,959 points) confirms this list. An earlier note of mine, that the
  R-cell stored voltage is not saved, was wrong.

## Per item

1. **The recognition theorem** (`layered_recognition_at`, and `layered_inverters_chained` with the inverter front
   end). Its hypotheses are TrainingCalibration and ReadCalibration, plus the front end's InverterRead and the
   latency schedule:
   - Routed;
   - FiringSlot / AdditiveSlot: the scores and the slot dates;
   - InverterRead: the dates.

   All of these are dates and scores taken from the record and from the sealed fit. leancal.py / leancal2.py already
   emit Cal<TAG>K0/K3.lean from the records through measure.Measure. Each file compiles in about 3–5 s (cal6:
   5.2 s and 2.9 s).

   **The records are enough. No raw is needed.**
2. **The routed walk.** It is checked per read from the dates, in two parts:
   - arrival = the emission below + δ (measure.read_checks);
   - launch = snap(latch + δ) − δ on the 0.4 µs grid (run.py:182).

   **The records are enough.**
3. **The leak along the trajectory.**
   - **(a) Between slots: the records are enough.** This is the stage-D measure D5 (fit.py:249), applied to the stage-N
     records. H_drift = ⌈Σ_p d · max|Δu_p| / D_p⌉, taken over the read-only slots, with u from the per-slot window
     means. It is then compared with the sealed H_drift.
   - **(b) Along the trajectory proper: this needs raw vectors.** That means:
     - for R cells, from the u window to the read instant and through the read: u_p(t) = vmem_p(t) − sum_p(t), from
       x<c>.vmem<p> and x<c>.x<p>.sum;
     - for inverters, x<inv>.vq over the slot. The record has only the point value x_D.
4. **The latch delay.**
   - **(a) Arrival to latch: the records are enough.** The record has both dates (to 1 ns) and the "second" rise.
   - **(b) Contact to latch: this needs raw vectors.** The contact is the comparator crossing, so it needs
     x<c>.x<p>.sum and x<c>.p (R cells) and x<inv>.vq and x<inv>.p (inverters).

So the theorem, the routed walk, the between-slot leak and the arrival-to-latch delay need only the records. The leak
along the trajectory proper and the contact-to-latch delay need raw vectors.

## If raws are wanted: an extract, not the trace

An extract like ref_extract.py would do. It keeps a subset of the original columns, byte for byte (no resampling), with
ref.json and SHA256SUMS. Its vectors:
- time;
- per R cell: p, vmem<p> and x<p>.sum for both ports (5 vectors);
- per inverter: p and vq (2 vectors).

That is 8 vectors for NOT1 (1 cell and 1 inverter), 25 for XOR3 (4 cells and 2 inverters) and 21 for ANDOR3 (4 cells).

| per round | points | premise extract | inverter-only extract (time, p, vq) | whole trace |
|---|---|---|---|---|
| NOT1 N0 (measured) | 46,959 | 3.0 MB | 1.1 MB | 19.5 MB |
| NOT1 noisy (measured) | 76,607 | 4.9 MB | 1.8 MB | 34.9 MB |
| XOR3 N0 (est.) | ~235k | ~47 MB | ~9.4 MB | 1.23 GB |
| XOR3 noisy (est.) | ~507k | ~100 MB | ~20 MB | ~2.7 GB |
| ANDOR3 N0 (est.) | ~195k | ~33 MB | none | 1.01 GB |
| ANDOR3 noisy (est.) | ~400k | ~65 MB | none | ~2 GB |

The estimates rest on these figures:
- XOR3 noisy points: from ref_extract's XOR3 figure of 45 MB for 11 vectors;
- the N0 point counts: from the N0 trace sizes of the dry run, with the vector count assumed close to the noisy one;
- the ANDOR3 noisy figure: assumed to scale with N0 as XOR3's does.

Per instance: N0, plus 3 noisy rounds with probability p_room (NOT1 0.79, XOR3 0.25, ANDOR3 0.27). The sizes are 60
NOT1, 37 XOR3 and 32 ANDOR3. The subset is every 6th instance, as for D4: 10, 6 and 5 instances.

| campaign total | premise extract, expected (all rooms) | inverter-only extract, expected | whole traces |
|---|---|---|---|
| every instance | ~8.2 GB (~21 GB) | ~1.2 GB | ~210 GB |
| every 6th (21 instances) | ~1.3 GB (~3.4 GB) | ~0.20 GB | ~34 GB |

Per machine (12): every instance is about 0.7 GB expected, and about 1.8 GB at worst. Both are far below disk_guard_gb 20.
The sizes that end up in evidence/ matter more than the machines' disks.

## Proposal (for the owner to decide)

- **The theorem, the routed walk, the between-slot leak and the arrival-to-latch delay** use the kept records. Nothing
  changes for these.
- **The trajectory leak and the contact-to-latch delay.** Two options:
  - **P1 (recommended):** a premise extract (the vectors above) on every 6th instance of each group, the D4 positions,
    in every round. That is about 1.3 GB expected. It gives a measured sample per group, which matches the assumption
    the D4 rule already states.
  - **P2:** the same extract on every instance, about 8.2 GB expected and 21 GB at most. It turns "sampled" into
    "checked on every instance", at about 6× the size.
  - Either way the R-cell vectors dominate. An inverter-only extract (0.20 / 1.2 GB) would cover the inverters alone.
- **Cost of either option.** Both need new code: an extract script like ref_extract.py, and a campaign_run14 that
  writes it before the raw is deleted, with tests on a NOT1 and an XOR3 round. They also need a new freeze pin. The
  template then gains one field (for example `premise_extract: "d4_audit"` or `"all"`).
- **Not proposed:** keeping whole traces. That would be about 210 GB, about 26× an extract on every instance,
  for no vector the checks need.
- **Undecided:** the template pinned now has neither option. keep_raw stays the originals of the remote duplicates
  (plan_split2), and disk_guard_gb stays 20.
