# Runbook: equivalence test (b) on the test machines (test phase only)

Equivalence test (b) runs instances end to end with campaign.py, in **test mode**, and compares the roots byte for
byte with the old chain's roots of the same instances. Each machine runs its share once. **Nothing here counts for
the campaign.** Every output is marked TEST.

| Machine | Plan | What it runs |
|---|---|---|
| K02 | PLAN_K02.json | XOR3 9803 (with room: N0, then N1–N3), U on XOR3 |
| K03 | PLAN_K03.json | ANDOR3 6104 (with room), U on ANDOR3 |
| K05 | PLAN_K05.json | NOT1 6212 and NOT1 6220 (6220 D4-audited), U on NOT1; the home of the NOT1 6212 duplicate (its N0 raw kept) |
| K06 | PLAN_K06.json | the remote duplicate of NOT1 6212, home K05: it waits (up to 6 h) for K05's seal on evidence/devtest-seals-K05 |

All four start at once. K06 needs no manual step: its duplicate starts when K05's seal appears.

**Pushes allowed, and only these:**
- the seal pushes campaign.py makes itself, to evidence/devtest-seals-K<nn>;
- one push of your root to evidence/devtest-K<nn> at the end (step 6).

Use the owner identity, as below, and subject-only messages with no trailer. Push plainly, never force: each branch
is new, and you only add to it.

Acknowledge in one line before acting. Report to the stage-D worker (session_01TzF7ZYVsvGaQ6EzEjxCJLM), with the
coordinator (session_01TzF7ZYZVxJcErqniRxMQ4F) in copy, at each step marked REPORT.

`a8303e8ed8baaf72854d63b099ca30fdbe2bfa8e` is the commit named in the message that sent you this runbook. `<nn>` is your machine number (02, 03, 05
or 06).

## 1. A fresh clone, fetched by name, at the exact commit

```
export PATH=$HOME/.elan/bin:$PATH
V=<your pinned Python 3.13.18 with numpy 2.3.5, as used for envcheck>
W=$HOME/devtest_b                      # must not exist yet: stop and report if it does
mkdir $W && cd $W && git init -q kernel-R && cd kernel-R
git remote add origin https://github.com/HevisNico/kernel-R
for b in research/layered-campaign-dev research/inverter-instances research/layered-networks main; do
  git fetch -q origin refs/heads/$b:refs/remotes/origin/$b
done
git merge-base --is-ancestor a8303e8ed8baaf72854d63b099ca30fdbe2bfa8e origin/research/layered-campaign-dev && git checkout -q --detach a8303e8ed8baaf72854d63b099ca30fdbe2bfa8e
git rev-parse HEAD                                  # must print a8303e8ed8baaf72854d63b099ca30fdbe2bfa8e
git merge-base --is-ancestor d599300d51fcf3a1a4c33d103b89827f8ac4da41 origin/research/inverter-instances
git merge-base --is-ancestor 458bc7a6d763127ff2fe0214e2cb79a1a6549f9b origin/research/layered-networks
git worktree add -q --detach ../kit   d599300d51fcf3a1a4c33d103b89827f8ac4da41
git worktree add -q --detach ../noise 458bc7a6d763127ff2fe0214e2cb79a1a6549f9b
for t in . ../kit ../noise; do [ -e $t/research/circuit/pdk ] || ln -s <your SKY130 PDK at 1232782c> $t/research/circuit/pdk; done
```

**The owner identity** is used for the seal commits and the final push. It is taken from main, and never printed or
written to a file:

```
export GIT_AUTHOR_NAME="$(git log -1 --format=%an origin/main)" GIT_AUTHOR_EMAIL="$(git log -1 --format=%ae origin/main)"
export GIT_COMMITTER_NAME="$GIT_AUTHOR_NAME" GIT_COMMITTER_EMAIL="$GIT_AUTHOR_EMAIL"
```

Change nothing in the three trees. campaign.py refuses an untracked .py or .json in the kit or noise tree.

## 2. Environment

```
cd $W/kernel-R/research/layered-networks
$V -B envcheck_layered4.py check
$V -B campaign.py check test dev/equiv/b/TEST_TEMPLATE_B.json dev/equiv/b/PLAN_K<nn>.json
```

Both must pass: the check prints `"ok": true`, and `"mode": "TEST"`. REPORT: both outputs (the check's `pins` part
may show not_pinned entries: that is expected in test mode), `uptime -s`, nproc, and the free disk (at least 40 GB).

## 3. Launch, detached

```
$V -B campaign.py launch test dev/equiv/b/TEST_TEMPLATE_B.json dev/equiv/b/PLAN_K<nn>.json $W/out_K<nn>
```

REPORT the launch line, or the refusal word for word. Do not try to work around a refusal.

## 4. Wait in the foreground, in chunks of at most 590 s

```
until $V -B campaign.py wait $W/out_K<nn> 580; do :; done
```

Each call prints the steps and ENDED or RUNNING, then DONE and INSTANCES_DONE when present.
- REPORT once at INSTANCES_DONE (or at DONE).
- K06: REPORT when its duplicate has found the seal (out_K06/DUPX_NOT1_6212/seal_wait.json, `found`).

**Never relaunch anything.** If the machine or the driver stops:
- REPORT first;
- resume only when told to, with `$V -B campaign.py resume test dev/equiv/b/TEST_TEMPLATE_B.json
  dev/equiv/b/PLAN_K<nn>.json $W/out_K<nn>`, then wait as above;
- a step found running becomes "interrupted" and is never rerun.

## 5. At the end

REPORT:
- `$V -B campaign.py status $W/out_K<nn>`;
- the first line of `$W/out_K<nn>/DONE`;
- RESULT.json's job_errors and stopped_for_disk;
- `uptime -s`, and the free disk.

## 6. Push the root to evidence/devtest-K<nn> (additions only, new branch)

```
cd $W
git ls-remote https://github.com/HevisNico/kernel-R refs/heads/evidence/devtest-K<nn>   # must print nothing
git init -q push_K<nn> && cd push_K<nn>
git checkout -q --orphan evidence/devtest-K<nn>
mkdir out_K<nn> && cp -a $W/out_K<nn>/. out_K<nn>/
rm -rf out_K<nn>/.seal_log_work/.git                # the seal log is already on its own branch
find out_K<nn> -type f -size +50M | while read f; do
  sha256sum "$f" > "$f.sha256" && split -b 45M -d "$f" "$f.part-" && rm "$f"
done                                                # each big file: <file>.sha256 and <file>.part-00, -01, ...
git add -A && git commit -q -m "devtest (b): K<nn> root of equivalence test (b), TEST mode"
git push -q https://github.com/HevisNico/kernel-R HEAD:refs/heads/evidence/devtest-K<nn>
git ls-remote https://github.com/HevisNico/kernel-R refs/heads/evidence/devtest-K<nn>   # REPORT this line
```

Use the owner identity from step 1, with no trailer. If the push is refused, REPORT it and stop: do not force, do
not rename the branch. Then STOP.
