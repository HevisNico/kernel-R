# Runbook: equivalence test (c) split over K07–K12 (test phase only)

Test (c), tests/test_campaign.py, runs its 23 cases once each, split over six machines that the owner approved for
it. Every machine runs the same commit, with the same environment check. **Nothing here counts for the campaign.**
No case pushes to GitHub: every seal log of (c) is a local bare repository in the work folder.

`<COMMIT>` is the commit named in the message that sent you this runbook. `<nn>` is your machine number (07–12).

| Machine | Cases (one call; test_campaign.py runs them in its own order) | Expected time (last full run) |
|---|---|---|
| K07 | home_run differing_duplicate analysis_refuses analysis_tampered analysis_forged_pins analysis_d8_not_run analysis_d9_copies analysis_d10_manifest analysis_hardening | about 17 min |
| K08 | refusals pins github_times second_seal | about 15 min |
| K09 | timeout guard partial_guard_and_resume | about 10 min |
| K10 | kernel_mirror_disagreement no_pushed_seal | about 12 min |
| K11 | crash interrupt_and_resume k3_budget_stop | about 8 min |
| K12 | sigterm_driver_only sigkill_driver_only | about 6 min |

The analysis cases need the home run of the same call, so they all stay on K07.

**Pushes allowed, and only this one:** your record folder to the new branch evidence/devtest-K<nn> at the end (step 5),
plainly, never forced, with the owner identity and a subject-only message with no trailer.

Acknowledge in one line before acting. Report to the stage-D worker (session_01TzF7ZYVsvGaQ6EzEjxCJLM), with the
coordinator (session_01TzF7ZYZVxJcErqniRxMQ4F) in copy, at each step marked REPORT.

## 1. A fresh clone, fetched by name, at the exact commit

```
export PATH=$HOME/.elan/bin:$PATH
V=<your pinned Python 3.13.18 with numpy 2.3.5, as used for envcheck, with py_ecc 8.0.0 (requirements_beacon.txt)>
W=$HOME/devtest_c                      # must not exist yet: stop and report if it does
mkdir $W && cd $W && git init -q kernel-R && cd kernel-R
git remote add origin https://github.com/HevisNico/kernel-R
for b in research/layered-campaign-dev research/inverter-instances research/layered-networks main; do
  git fetch -q origin refs/heads/$b:refs/remotes/origin/$b
done
git merge-base --is-ancestor <COMMIT> origin/research/layered-campaign-dev && git checkout -q --detach <COMMIT>
git rev-parse HEAD                                  # must print <COMMIT>
git checkout -q -B research/layered-campaign-dev    # test (c) clones this branch name from the local repository
git rev-parse HEAD                                  # must still print <COMMIT>
[ -e research/circuit/pdk ] || ln -s <your SKY130 PDK at 1232782c> research/circuit/pdk
```

The owner identity (for the final push only), taken from main, never printed or written to a file:

```
export GIT_AUTHOR_NAME="$(git log -1 --format=%an origin/main)" GIT_AUTHOR_EMAIL="$(git log -1 --format=%ae origin/main)"
export GIT_COMMITTER_NAME="$GIT_AUTHOR_NAME" GIT_COMMITTER_EMAIL="$GIT_AUTHOR_EMAIL"
```

Change nothing in the tree. (c) makes its own clones and worktrees under $W/c.

## 2. Environment

```
cd $W/kernel-R/research/layered-networks
$V -B envcheck_layered4.py check | tee $W/envcheck.out
$V -c "import py_ecc, numpy, sys; print(sys.version.split()[0], numpy.__version__)"
which lean ngspice
```

The check must print `"ok": true`. REPORT: its output, the Python line, `uptime -s`, nproc and the free disk (at least
40 GB).

## 3. Run your cases, once

```
cd $W/kernel-R/research/layered-networks
$V -B tests/test_campaign.py $W/c <your cases from the table, in its order> 2>&1 | tee $W/c.log
echo rc=$?
```

Run it once, in the foreground (or detached with nohup and the same tee, if your session limits a call's length).
**Never rerun a case.** If the machine or the call stops, REPORT and wait. A failing case is a result: report it, do
not retry.

## 4. REPORT

- the lines of $W/c.log (each case: PASS or FAIL, seconds);
- `$V -c "import json; d=json.load(open('$W/c/TEST_C.json')); print({k: v['ok'] for k, v in d.items() if isinstance(v, dict)}, d.get('all_pass'))"`.

## 5. Push the record to evidence/devtest-K<nn> (additions only, new branch)

```
cd $W
git ls-remote https://github.com/HevisNico/kernel-R refs/heads/evidence/devtest-K<nn>   # must print nothing
git init -q push_K<nn> && cd push_K<nn>
git checkout -q --orphan evidence/devtest-K<nn>
mkdir c_K<nn> && cp $W/c/TEST_C.json $W/c.log $W/envcheck.out c_K<nn>/
(cd $W/kernel-R && git rev-parse HEAD) > c_K<nn>/COMMIT
git add -A && git commit -q -m "devtest (c): K<nn> cases of test (c), TEST mode"
git push -q https://github.com/HevisNico/kernel-R HEAD:refs/heads/evidence/devtest-K<nn>
git ls-remote https://github.com/HevisNico/kernel-R refs/heads/evidence/devtest-K<nn>   # REPORT this line
```

If the push is refused, REPORT it and stop: do not force, do not rename the branch. Then STOP.

## The merge (the stage-D worker)

dev/equiv/merge_test_c.py fetches the six branches by name and writes one TEST_C.json. Each case carries its machine,
and the merge refuses a case missing, run twice, or a machine whose COMMIT or envcheck differs.
