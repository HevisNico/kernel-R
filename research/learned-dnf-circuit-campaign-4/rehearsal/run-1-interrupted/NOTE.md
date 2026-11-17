# Campaign 4, rehearsal attempt 1: interrupted, no check evaluated

The rehearsal of the frozen implementation (commit `3156ee4`, tree `c19e4ef`) on the nominal cell only, started
2026-11-16 at 18:11:16 UTC in the work folder `/home/user/rehearsal1`. **It was interrupted at about 20:12 UTC, and no
check of the rehearsal was evaluated or looked at.** `REHEARSAL.json` was never written. The owner decided to redo the
whole rehearsal, unchanged, on the same commit, in a new work folder; this attempt enters no limit and no check.

## What happened

The campaign director had started `rehearsal.py` and the uptime recorder as background tasks of the director's
session. Those tasks have a hard limit of 2 h, which the director had not checked; the rehearsal needs about 4 h. At
about 20:12 UTC the limit stopped both tasks with every process under them (`rehearsal.py`, the kit's `run-machine`,
`run4.py`, ngspice). Nothing in the frozen code failed. It is an operator error.

The machine did not restart during the attempt: `uptime -s` read `2026-11-16 17:52:34` at the start, at each stage,
every 10 minutes, and at 20:12:31 UTC after the stop (`meta/uptime.log`; its last line was added by hand after the
stop). The machine was restarted later, while nothing ran: on 2026-11-17 at 05:34:54 UTC, `uptime -s` read
`2026-11-17 05:34:37`. This folder was copied from `/home/user/rehearsal1` after that restart; that folder was not
changed.

## The state at the stop

| Stage (machine) | Status | Runs, wall time |
|---|---|---|
| M (a) | complete, collected 18:22:16 | cal-on 569 s, cal-off 426 s, quiet-nocontrol 631 s, untrained-check 144 s |
| M (b) | complete, collected 18:40:47 | injected-r1 1 103 s, injected-r1-again 1 098 s, injected-r2 1 099 s |
| X (a) | complete, collected 18:43:17 | xcheck-a-hold-1 140 s |
| X (b) | complete, collected 20:02:18 | extract-single 4 763 s |
| E (a) | **interrupted**: launched 20:02:21, `STATE.json` still reads `running`, never collected | 8 parts complete; 3 parts stopped mid-run: `a-None-x-c-window-1`, `a-None-x-c-fire-cell`, `a-None-x-c-pulse-2` (their status `started`) |
| E (b), the predictions and the gate, N, MEMD, MEMI, GUARD, the analysis | not started | |

No seed of 7501 or above was simulated.

## What this folder holds

- `M-a`, `M-b`, `X-a`, `X-b`, `E-a`: the kit's evidence folders as left; `collected-*`: the kit's collected copies
  with their `SURVIVORS.json`.
- `meta/`: `rehearsal.log` (the rehearsal's output), `uptime.log` and `uptime.sh` (the uptime recorder).
- `clone/`: the rehearsal's local clone at the stop. `rehearsal-branch.bundle` holds its commits after `3156ee4`
  (`rehearsal-branch.log`), `files/` the files they wrote, and `remote.bundle` the claims of its local remote
  (`remote-refs.txt`). Its working tree had no uncommitted change (`uncommitted.txt`, empty).
- Three symbolic links were left in the work folders of the three parts stopped mid-run, each
  `work/<part>/op/pdk -> /home/user/campaign/pdk`. They are not copied here.

**Files of 10 MB and more** are on the branch `evidence/learned-dnf-circuit-campaign-4-rehearsal-run-1-interrupted`
(commits `fba07d4` and `de66b7a`), at the same paths. They are all waveform files (`trace.raw`, `noise.raw`); together
they would have added 1.1 GB to the work branch, which CI checks out. Files above 100 MiB are stored there in parts of
90 000 000 bytes, listed in `PARTS.json` on that branch. Their SHA-256 (of the whole file), paths relative to this folder:

```
ccdca7ec63f1209d036c834fb79fc4d14204a8b71d0857473f172a3e6ad08aea  E-a/a-None-x-a-fire-cell/work/fire_a/dev/noise.raw
ad3ccc1321ab2bccd02afb7753a8ca748ffce24d82db3c246dc67c6d16a7b3a7  E-a/a-None-x-a-hold-1/work/hold_a1/dev/noise.raw
75c20c4f3747b4395eb5ac5dd5c6f7ab766b5caca3dea4a8072115472c4623ea  E-a/a-None-x-a-pulse-2/work/pulse_a2/dev/noise.raw
8fd1b5f70fde573c2702a06668faa69d7c279798ff425b499a29bdc8d2bb9d22  E-a/a-None-x-a-window-1/work/window_a1/dev/noise.raw
b0835e1b2852fdcac3e80a4831117450476b2ac09f90150cd71c8bcfb8264cf9  E-a/a-None-x-b-hold-2/work/hold_b2/dev/noise.raw
e245dda6a82814ea2750c9ea44b612ef8c533aa2d5da74b7d3fc42a2c8f81b2c  E-a/a-None-x-b-pulse-1/work/pulse_b1/dev/noise.raw
d17696f034f64f8929a8a6b6df6c54562fbc0b4eea93db0eaac6b1e6a7b77969  E-a/a-None-x-b-window-2/work/window_b2/dev/noise.raw
a81e6eb7323e648cf458c12639d1a3d602d98c05c02c6244c0e8cfee0395ceda  E-a/a-None-x-c-hold-1/work/hold_c1/dev/noise.raw
3b9d07ed26f0b3fd251a0d0bce7b075dd1985651b9f99b83302bf50bbef9f28e  M-a/a-None-cal-off/evidence/trace.raw
faa9b7c8ebbe5a450d9538f230c560f3e810143fc90ad478863b8e6c9887e9ac  M-a/a-None-cal-on/evidence/trace.raw
b2fa678f2b75aa716a382b93b0e2494f3f932a586219ea539c382154f6355602  M-a/a-None-quiet-nocontrol/evidence/trace.raw
f091cb99cfe55407e8504e6a31686867446ade5dcb443bb88c04ac208e4e98ed  M-a/a-None-untrained-check/evidence/trace.raw
5f8b9fdc8c1ed7c290038e0efa5522c2b1acf2cd2f69706c730dc288d45063a0  M-b/b-None-injected-r1-again/evidence/trace.raw
5f8b9fdc8c1ed7c290038e0efa5522c2b1acf2cd2f69706c730dc288d45063a0  M-b/b-None-injected-r1/evidence/trace.raw
418354ff0e3ab601cf2b724c8cfeb2358f073e5c2c55f0cbe40a4b4c8de3c393  M-b/b-None-injected-r2/evidence/trace.raw
3d8e6942997cecc7f9f3781bd0bb06fce85275fd2515a6a299dd270c12a76b86  X-a/a-None-xcheck-a-hold-1/work/hold_a1/dev/noise.raw
4b3432c0350226a7598261940e58004ba355228a067c5ceefaadfa7d21b2114d  X-b/b-None-extract-single/work/fire_a/dev/noise.raw
f92fa8c1e2b784e8a255906bad2a17d9575807e5a60a6b7f880c20e2384e19af  X-b/b-None-extract-single/work/fire_b/dev/noise.raw
e33e06acd5dfc4e7ff0ef2f50a1ce2ec599999a78c287f01443e7f3d710989a2  X-b/b-None-extract-single/work/fire_c/dev/noise.raw
ccc45ee5f9d17a2559dd9d38130eae9fe222d4ec2d2b40f041632be7b244148f  X-b/b-None-extract-single/work/hold_a1/dev/noise.raw
75191237341ba1198ba532f59394e897a6aa44e100eed74a419c61b307459cbf  X-b/b-None-extract-single/work/hold_a2/dev/noise.raw
cb75a6b2bde63f1c4cb2e730e1cf954832127c124d4b929d8c521d1acc28c50b  X-b/b-None-extract-single/work/hold_b1/dev/noise.raw
6711e52db908ef550f63e5d81ec89e2d3850be8a0da84525dba8d217f08d299e  X-b/b-None-extract-single/work/hold_b2/dev/noise.raw
da0f1ea572bd1ee1e8fa003a4a56ab6a8f52295fa09bdaad6833b44a2419ca43  X-b/b-None-extract-single/work/hold_c1/dev/noise.raw
5ef414fdcae9a18a01c7e97f5547d6255c85b79e59508311b13eb9c560d388f9  X-b/b-None-extract-single/work/hold_c2/dev/noise.raw
2782cca61ea5043b9856117972c2c3a8239cb5938ae9cee815d89bbd9be7b34f  X-b/b-None-extract-single/work/pulse_a1/dev/noise.raw
fa25bd14823ea125eea82ccec44559b8fab10b0688ee7ad5a770d83373106070  X-b/b-None-extract-single/work/pulse_a2/dev/noise.raw
26aed18b565142293cf67de7d399c91dbe536f60526f7af8350aaa35ee8a09e4  X-b/b-None-extract-single/work/pulse_b1/dev/noise.raw
276a0a1bc1b9ac590f8dd4c08b26a062983418e730b759424ca1ca2021a2e9ec  X-b/b-None-extract-single/work/pulse_b2/dev/noise.raw
134e25672662d0b226a9faf8e249ee2c887fe1c9792e6ea633f744e1920cf91a  X-b/b-None-extract-single/work/pulse_c1/dev/noise.raw
b9ca2b8b562cc09f8eb02ea7e28d25872cac651d74ef8a38da7ec83f9baef2de  X-b/b-None-extract-single/work/pulse_c2/dev/noise.raw
90cf97375daf604fcc5ddea4f9aa0a533bb49d29aa4009730aeebec71e7184c9  X-b/b-None-extract-single/work/window_a1/dev/noise.raw
e8d1152b0e78091d62be8caba451074265e1ae7977fe27c726eb3360967c28fe  X-b/b-None-extract-single/work/window_a2/dev/noise.raw
efda90ec8ee7b29d04f062e363f37b16441badc6abd3a29dd1d8194df6e509fe  X-b/b-None-extract-single/work/window_b1/dev/noise.raw
26323481f8933da8ee50ca3cafce4f785c44e329678de6b7a3c0542e634a38cf  X-b/b-None-extract-single/work/window_b2/dev/noise.raw
632ce3fbf1c04fb1ad6c59490101e006b9ee3d4317c35b6858005b77638e1506  X-b/b-None-extract-single/work/window_c1/dev/noise.raw
74d0c83277891173f39c263fe34cd758507c4abe861e6fa0a8bf6a6c346361c3  X-b/b-None-extract-single/work/window_c2/dev/noise.raw
3b9d07ed26f0b3fd251a0d0bce7b075dd1985651b9f99b83302bf50bbef9f28e  collected-M-a/a-None-cal-off/evidence/trace.raw
faa9b7c8ebbe5a450d9538f230c560f3e810143fc90ad478863b8e6c9887e9ac  collected-M-a/a-None-cal-on/evidence/trace.raw
b2fa678f2b75aa716a382b93b0e2494f3f932a586219ea539c382154f6355602  collected-M-a/a-None-quiet-nocontrol/evidence/trace.raw
f091cb99cfe55407e8504e6a31686867446ade5dcb443bb88c04ac208e4e98ed  collected-M-a/a-None-untrained-check/evidence/trace.raw
5f8b9fdc8c1ed7c290038e0efa5522c2b1acf2cd2f69706c730dc288d45063a0  collected-M-b/b-None-injected-r1-again/evidence/trace.raw
5f8b9fdc8c1ed7c290038e0efa5522c2b1acf2cd2f69706c730dc288d45063a0  collected-M-b/b-None-injected-r1/evidence/trace.raw
418354ff0e3ab601cf2b724c8cfeb2358f073e5c2c55f0cbe40a4b4c8de3c393  collected-M-b/b-None-injected-r2/evidence/trace.raw
3d8e6942997cecc7f9f3781bd0bb06fce85275fd2515a6a299dd270c12a76b86  collected-X-a/a-None-xcheck-a-hold-1/work/hold_a1/dev/noise.raw
4b3432c0350226a7598261940e58004ba355228a067c5ceefaadfa7d21b2114d  collected-X-b/b-None-extract-single/work/fire_a/dev/noise.raw
f92fa8c1e2b784e8a255906bad2a17d9575807e5a60a6b7f880c20e2384e19af  collected-X-b/b-None-extract-single/work/fire_b/dev/noise.raw
e33e06acd5dfc4e7ff0ef2f50a1ce2ec599999a78c287f01443e7f3d710989a2  collected-X-b/b-None-extract-single/work/fire_c/dev/noise.raw
ccc45ee5f9d17a2559dd9d38130eae9fe222d4ec2d2b40f041632be7b244148f  collected-X-b/b-None-extract-single/work/hold_a1/dev/noise.raw
75191237341ba1198ba532f59394e897a6aa44e100eed74a419c61b307459cbf  collected-X-b/b-None-extract-single/work/hold_a2/dev/noise.raw
cb75a6b2bde63f1c4cb2e730e1cf954832127c124d4b929d8c521d1acc28c50b  collected-X-b/b-None-extract-single/work/hold_b1/dev/noise.raw
6711e52db908ef550f63e5d81ec89e2d3850be8a0da84525dba8d217f08d299e  collected-X-b/b-None-extract-single/work/hold_b2/dev/noise.raw
da0f1ea572bd1ee1e8fa003a4a56ab6a8f52295fa09bdaad6833b44a2419ca43  collected-X-b/b-None-extract-single/work/hold_c1/dev/noise.raw
5ef414fdcae9a18a01c7e97f5547d6255c85b79e59508311b13eb9c560d388f9  collected-X-b/b-None-extract-single/work/hold_c2/dev/noise.raw
2782cca61ea5043b9856117972c2c3a8239cb5938ae9cee815d89bbd9be7b34f  collected-X-b/b-None-extract-single/work/pulse_a1/dev/noise.raw
fa25bd14823ea125eea82ccec44559b8fab10b0688ee7ad5a770d83373106070  collected-X-b/b-None-extract-single/work/pulse_a2/dev/noise.raw
26aed18b565142293cf67de7d399c91dbe536f60526f7af8350aaa35ee8a09e4  collected-X-b/b-None-extract-single/work/pulse_b1/dev/noise.raw
276a0a1bc1b9ac590f8dd4c08b26a062983418e730b759424ca1ca2021a2e9ec  collected-X-b/b-None-extract-single/work/pulse_b2/dev/noise.raw
134e25672662d0b226a9faf8e249ee2c887fe1c9792e6ea633f744e1920cf91a  collected-X-b/b-None-extract-single/work/pulse_c1/dev/noise.raw
b9ca2b8b562cc09f8eb02ea7e28d25872cac651d74ef8a38da7ec83f9baef2de  collected-X-b/b-None-extract-single/work/pulse_c2/dev/noise.raw
90cf97375daf604fcc5ddea4f9aa0a533bb49d29aa4009730aeebec71e7184c9  collected-X-b/b-None-extract-single/work/window_a1/dev/noise.raw
e8d1152b0e78091d62be8caba451074265e1ae7977fe27c726eb3360967c28fe  collected-X-b/b-None-extract-single/work/window_a2/dev/noise.raw
efda90ec8ee7b29d04f062e363f37b16441badc6abd3a29dd1d8194df6e509fe  collected-X-b/b-None-extract-single/work/window_b1/dev/noise.raw
26323481f8933da8ee50ca3cafce4f785c44e329678de6b7a3c0542e634a38cf  collected-X-b/b-None-extract-single/work/window_b2/dev/noise.raw
632ce3fbf1c04fb1ad6c59490101e006b9ee3d4317c35b6858005b77638e1506  collected-X-b/b-None-extract-single/work/window_c1/dev/noise.raw
74d0c83277891173f39c263fe34cd758507c4abe861e6fa0a8bf6a6c346361c3  collected-X-b/b-None-extract-single/work/window_c2/dev/noise.raw
```
