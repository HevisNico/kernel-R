# Machine brief: running one campaign machine

The driver is **campaign.py**, and only campaign.py. The older drivers (campaign_run*.py) stay in the tree for the
record. analysis.py refuses any root that campaign.py did not write in campaign mode on the frozen template.

1. **Code.** A clone of the frozen commit of this repository, plus two clean worktrees at the template's kit_commit
   and noise_commit, and the SKY130 PDK at research/circuit/pdk:
   ```
   git worktree add --detach ../kit   d599300d51fcf3a1a4c33d103b89827f8ac4da41
   git worktree add --detach ../noise 458bc7a6d763127ff2fe0214e2cb79a1a6549f9b
   ```
   Change nothing in the three trees: no edit and no untracked .py or .json file (campaign mode refuses them).
2. **Environment.** `python -B envcheck_layered4.py check` must pass: Python 3.13.18, numpy 2.3.5, ngspice 42, the
   PDK, Lean 4.35.0 by its real binary. campaign.py checks it again at launch and at every run.
3. **Disk.** At least 40 GB free at launch (campaign_template.json disk_launch_gb).
4. **The plan.** Your PLAN_K<nn>.json, written by plan_split3.py from the draw and campaign_template.json. Do not edit
   it: campaign.py refuses a plan that differs from the template.
5. **Launch:**
   ```
   python -B campaign.py launch campaign campaign_template.json PLAN_K<nn>.json OUTROOT
   ```
   It refuses if:
   - the template is not the frozen one, or a key is missing or extra;
   - a file of FREEZE_PINS.json does not match its sha256 (campaign.py, analysis.py and the template are pinned);
   - a tree is not clean at its commit (a changed tracked file, or an untracked .py or .json);
   - ngspice is already running;
   - OUTROOT is not empty;
   - less than 40 GB is free.
   The pins' check is recorded in OUTROOT/TEMPLATE_CHECK.json.
6. **Wait** in the foreground in chunks of at most 590 s:
   ```
   python -B campaign.py wait OUTROOT 580
   ```
   Exit 0 means the run has ended (DONE written, or the driver is gone); exit 3 means it is still running. `wait`
   follows the pid in OUTROOT/DRIVER_PID. It prints INSTANCES_DONE once the machine's own instances, their rounds and
   U have ended. RESULT_INSTANCES.json and SHA256SUMS.instances are then written: they never depend on another
   machine's seal. Only the remote duplicates (item 8) may still be running.
7. **Never relaunch anything.** A run that stops (the machine, the driver) is resumed, detached, with
   ```
   python -B campaign.py resume campaign campaign_template.json PLAN_K<nn>.json OUTROOT
   ```
   then waited for as in item 6: `resume` writes the new driver's pid to DRIVER_PID, and appends it to
   DRIVER_PIDS.log.
   - Only steps that never started are started then.
   - A step found running is recorded "interrupted" and stays so: its instance is not completed.
   - `resume` and `run` refuse while ngspice runs, while the OUTROOT's driver is alive, or while any other process
     names OUTROOT. Never kill a child to get past this refusal: report it.
   - A driver stopped by SIGTERM or SIGINT kills its own children first (SIGNALS.json).
8. **A machine holding remote duplicates** starts at any time. Each duplicate waits (up to 6 h) for its home
   machine's seal on the home's branch, and needs no manual step.
9. **The window is an expectation, not a limit.** Nothing is killed when it ends: only each step's own time limit
   (time_limits_s) stops a step. Every instance's chain is submitted at the start, in the plan's order, and each
   step takes its cores as the four-core budget frees them. No start order is promised, and it is not the draw
   order.
10. **U takes no core of the budget** (as in the chain). The core budget (4) covers every other step: the
    inverters take m cores, and a remote duplicate's N0 takes one.
11. **Record** `uptime -s` at the start and end (INVENTORY_START, INVENTORY_END). Report DONE, RESULT.json's
    job_errors and stopped_for_disk, and the free disk.

## The rehearsal

- **Size:** 6/6/6, that is 18 instances over the 12 machines (plan_split3.py; analysis.DRAW_SIZES_REHEARSAL), with a
  D4 audit on the 6th instance of each group in draw order (one per group).
- **Its draw:** the drand quicknet round fixed by ITS OWN GitHub announce, on evidence/combined-rehearsal-draw
  (pushed after the freeze, by one creating push; FREEZE.txt, DRAW_ANNOUNCE). The published round 1000000 serves the
  offline tests only, never a run.
- **Its run:** campaign.py in campaign mode on the frozen template, as for the campaign; analysis.py rehearsal reads
  it. Nothing of it counts for the campaign; its seeds enter the second exclusion scan.
