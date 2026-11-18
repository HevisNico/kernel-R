# Campaign 5, amendment 1: a change of CPU model at a container restart

Pushed alone on `research/learned-dnf-circuit-campaign-5`, after `PREDICTION.md` (commit `a2d8bad`, SHA-256
`36249501a232fb3a9f7e092ac6dee1927767cde852b9519ced7f9c671c110b10`), during the rehearsal and before its stage RM. It
is the owner's decision of 2026-11-18. Nothing else in `PREDICTION.md` changes.

## 1. What happened

Section 10.1 of `PREDICTION.md` stops a launch on a machine if anything but the boot time differs from the inventory
of the previous stage, the CPU model included. M1's reference inventory is the one written for that machine's last
rehearsal stage.

- The rehearsal's inventories are `INVENTORY_a.json` (SHA-256 `d092ee1c6d9a2df22d50bfc9d402c4bd8a2f3503072782c3efa87fc7037e6a6e`, commit `6e18612`) and `INVENTORY_b.json`
  (SHA-256 `0cdafda6244b106aa479601778716d102f32d7e4f1abd619d47a9f80655bd104`, commit `806464c`), on
  `research/learned-dnf-circuit-campaign-5-rehearsal`. Both record "Intel(R) Xeon(R) Processor @ 2.30GHz", 4
  processors, 16 473 760 kB of memory, kernel 6.18.44-fc-v595, Ubuntu 24.04.5 LTS and the pinned environment.
- Stage RC ran on both machines on these inventories (2026-11-18, 04:54 to 05:15 UTC). Each machine's boot time was
  unchanged from start to end.
- Machine a's container then restarted while idle, during a CI wait (boot 2026-11-18 06:59:15 UTC). No run was in
  progress. Its fresh inventory differs from `INVENTORY_a.json` only in the boot time, the recorded time and the CPU
  model, now "Intel(R) Xeon(R) Processor @ 2.10GHz". Processors, memory, kernel, system, the pinned environment (the
  kit's identity check passes), the presence of `avx512f` and the OpenBLAS core (SkylakeX) are unchanged. Machine a had
  already been on the 2.10GHz part on 2026-11-17, before a restart.

The cloud host's CPU part can therefore change at any restart of a container, which no session controls. Under section
10.1 as written, and since the frozen code fixes one inventory path per machine, machine a could never launch again.

## 2. The rule from now on

1. **The CPU model is recorded, not compared.** It is recorded before every launch (the session's fresh inventory and
   the kit's `INVENTORY_AT_LAUNCH.json`) and reported with every stage's wall times. A change of CPU model no longer
   stops a launch.
2. **Everything else in section 10.1 is unchanged.** A launch is stopped, until a further amendment, if anything but
   the boot time, the recorded time and the CPU model differs from the machine's reference inventory: processors,
   memory, kernel, system, the pinned environment. So is a launch on a CPU without `avx512f`, or whose OpenBLAS core is
   not SkylakeX.
3. **Only rehearsed CPU models run the campaign.** A campaign stage is launched on a machine only if that machine's
   current CPU model is one on which the rehearsal stage of the same kind passed the 0.75 rule (section 11.4) on at
   least one machine: RM for M1 and M2, RQ for Q and its parts, RN and RMEM for N1, N2, N3 and their parts. Otherwise
   nothing is launched on that machine until a further amendment. Each rehearsal run's CPU model is the one in its
   shard's `INVENTORY_AT_LAUNCH.json`. Before each campaign launch, the check of this rule is written in that stage's
   report, and `REPORT.md` lists, per CPU model, the rehearsal stages that passed the 0.75 rule on it. `REHEARSAL.json`,
   written by the frozen code, is not changed by this rule.
4. Section 11.2's rehearsal limits, section 10.4's campaign limits and the 0.75 rule are unchanged.

## 3. What was known when this was decided

This was decided from the inventories and the kit's run statuses only. No output of any run of the rehearsal or of
the campaign was read for it. RC's wall times (cal-on 485 to 514 s, n1 923 to 926 s, nominal cell) enter no rule
(section 11.3). No development or campaign seed had been simulated.
