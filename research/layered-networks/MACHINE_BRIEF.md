# Machine brief: running one campaign machine

The driver is **campaign.py**, and only campaign.py. The older drivers (campaign_run*.py) stay in the tree for the
record. analysis.py refuses any root that campaign.py did not write in campaign mode on the frozen template.

1. **Code.** A clone of the frozen commit of this repository, plus two clean worktrees at the template's kit_commit
   and noise_commit, and the SKY130 PDK at research/circuit/pdk:
   ```
   git worktree add --detach ../kit   d599300d51fcf3a1a4c33d103b89827f8ac4da41
   git worktree add --detach ../noise 458bc7a6d763127ff2fe0214e2cb79a1a6549f9b
   ```
2. **Environment.** `python -B envcheck_layered4.py check` must pass: Python 3.13.18, numpy 2.3.5, ngspice 42, the
   PDK, Lean 4.35.0 by its real binary. campaign.py checks it again at launch and at every run.
3. **Disk.** At least 40 GB free at launch (campaign_template.json disk_launch_gb).
4. **The plan.** Your PLAN_K<nn>.json, written by plan_split3.py from the draw and campaign_template.json. Do not edit
   it: campaign.py refuses a plan that differs from the template.
5. **Launch:**
   ```
   python -B campaign.py launch campaign campaign_template.json PLAN_K<nn>.json OUTROOT
   ```
   It refuses if the template is not the frozen one, a key is missing or extra, a tree is not at its commit, ngspice
   is already running, OUTROOT is not empty, or less than 40 GB is free.
6. **Wait** in the foreground in chunks of at most 590 s:
   ```
   python -B campaign.py wait OUTROOT 580
   ```
   Exit 0 means the run has ended (DONE written); exit 3 means it is still running.
7. **Never relaunch anything.** A run that stops (the machine, the driver) is resumed with
   `python -B campaign.py run campaign campaign_template.json PLAN_K<nn>.json OUTROOT`. Only steps that never started
   are started then. A step found running is recorded "interrupted" and stays so: its instance is not completed.
8. **A machine holding remote duplicates** starts at any time: each duplicate waits (up to 6 h) for its home
   machine's seal on the home's branch, and needs no manual step.
9. **Record** `uptime -s` at the start and end (INVENTORY_START, INVENTORY_END). Report DONE, RESULT.json's
   job_errors and stopped_for_disk, and the free disk.
