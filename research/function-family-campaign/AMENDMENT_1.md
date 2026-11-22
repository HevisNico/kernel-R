# Family campaign (a): amendment 1, the check of the frozen code

This amendment changes one line of `PREDICTION.md` (`385c33bf`, SHA-256 `5f9cdfe6…`): the CI line of section 8.
**Nothing else in `PREDICTION.md` changes.** It is pushed alone on `research/function-family-campaign`, before the
code's freeze marker and before any campaign run. Decided by the owner, 2026-11-22.

## What section 8 promised, and why it cannot run

Section 8 says: "**CI** on the frozen commit: the frozen tests, the new code's tests, and `gencheck.sh` on the
synthetic gates of every member."

No workflow of the repository covers this campaign's folders. Every workflow under `.github/workflows` on `main`
runs only on a push to `main` or on a pull request, and no path filter names `research/function-family*` [K, read on
`main`]. A push of a research branch runs none. The frozen code lives on research branches. So that CI never
runs [new].

## What replaces it: an independent rerun

**Where** [new]. On a clean machine that wrote none of the code, M3. It runs at the frozen tips named in the
code's freeze marker (`research/function-family-campaign/FREEZE.txt`), each branch fetched by name.

**First**, every file listed in `FREEZE.txt` is checked against its SHA-256. If one does not match, nothing is run.

**Then**, with no simulation:
- `family_predict.py`'s tests (`research/function-family/dev/test_family_predict.py`, frozen at `f2b3904c`);
- `test_family_net.py` and `test_family_reads.py` (network code). That includes the test on the real 7802-quiet run.
  Its evidence is fetched by name from `evidence/learned-dnf-circuit-campaign-6-c1-Q-a`;
- `test_campaign.py`, with `LEAN` set so that M8 goes through the kernel, and `test_integration.py` (the
  implementation);
- `gencheck.sh` of the generator (`4fca6256`) on the synthetic gate of every member
  (`research/function-family/dev/predict_freeze/gates/synthetic/Family_Syn_{X1,X2,F4,F2,F3}.lean`). Lean is 4.35.0,
  checked first against its pinned archive (`lean-4.35.0-linux.tar.zst`, SHA-256
  `7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`).

**The record.** Every output, with its SHA-256, is pushed in a commit of its own on
`evidence/function-family-campaign-ci`, a new branch, under the owner's identity, before the rehearsal.

**Failure.** Any failed check, failed test or refused gate means that nothing is launched until it is explained in
writing. A rule changed to fix it needs a further amendment, pushed alone.

## Not checked

- Whether a clean machine reproduces the test outputs byte for byte: unittest prints run times, so the outputs are
  compared by their verdicts and test counts, not by their SHA-256.
- This rerun shows the code does what its tests say. It is not a GitHub workflow, and it runs once, at the freeze.
