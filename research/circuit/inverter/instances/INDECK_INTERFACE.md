# The inverter gate inside the layered deck (invinst.indeck)

**Development work.** Nothing here is frozen or preregistered. This was asked for by the stage-D session of
research/layered-networks. It closes the open point of CAMPAIGN_INTERFACE.md: a standalone instance at seed S does not
use the network's devices.
- The standalone 9803 fingerprint is v(ibm) 0.506489 V and xm1 vth 0.456762 V.
- In the XOR3 deck at 9803 the values are 0.507924 / 0.455909 for n0, and 0.508336 / 0.452391 for n1.

## The entry

```
python -m invinst.indeck OUTDIR --deck DECK.spice --seed S [--inverters n0,n1] [--config config.json]
```
From Python: `indeck.run(deck_path, outdir, seed, invs=None)`, which returns `OUTDIR/inverter_gate.json`.

- `DECK.spice` is the network's deck text as the network runs it. For example, from research/layered-networks:
  `cfg,_ = lcal2.config("config_inverter_c5.json"); text = instrument.deck_text(spec.load("specs/xor3.json"), cfg)`.
  It is flattened, uses `tt_mm` and has no control block.
- `--inverters` defaults to every `n<j>` of the deck.
- The jobs run one per inverter, 4 at a time, each with a timeout of 1800 s.

## What it runs, per inverter n<j>

1. **An op of the unchanged deck at `setseed S`, then `reset`.** It gives the network's fingerprint of each inverter
   (`NETWORK_FINGERPRINT.json`). The fingerprint is `sim.FINGER` inside `xn<j>`: v(ibm) and the vth of xcmpm.xm1,
   xcmpm.xm2, xmh1 and xmj1.
2. **`check_design`.** The deck's ihref, bjref, help mirror w/l and vfire level must equal config.json's C5 cell.
   Otherwise the run is refused.
3. **The five runs of config.json**, each in a copy of the deck where only these lines change (tests/test_indeck.py
   checks this for every run of every inverter):
   - the five drives `vkh/vki/vkj/vkr/vkb n<j>`, using the standalone timing (the slot at settle_s = 10 µs, and the
     same edges);
   - `i.xn<j>.ihref` set to 0 for the runs without help;
   - for R5 only, `vforce/rforce` onto `xn<j>.vq`, added before `.end`.
   Every other cell and inverter stays at its 'never' drives. The maximum step is the standalone one (5n/20n), not the
   network's 200n.
4. **`same_sample`.** Every run's fingerprint must equal the network's, within `fingerprint_tol_V` 1e-4 V. If one
   differs, the gate's observation `same_sample` fails, and with it K0.
5. **The measured quantities.** They are measure2's, restated in `indeck.quantities`. On the kept standalone traces of
   9711 and 9712, `quantities` gives exactly measure2's MEASURE.json values (checked by hand, not a test).
6. **The gate.** It is `gate.gate`, unchanged: K0, K3, StateBound, Lean `decide +kernel`.

## inverter_gate.json (schema "inverter-indeck/1")

| Field | Meaning |
|---|---|
| `kit_commit`, `package_tree_clean` | git HEAD of this package, and whether its tree was clean |
| `seed`, `deck`, `deck_sha256`, `config_sha256` | the inputs |
| `K0`, `K3` | the instance verdicts: every inverter's K0 must hold for `K0`, and every K3 for `K3` |
| `inverters.n<j>.K0`, `.K3` | campaign.first_failing's rules: the kernel verdict, all observations (including `same_sample`), and StateBound measured and holding. K3 implies K0 |
| `inverters.n<j>.why` | `[]`, or the first failing clause of K0 and of K3 (the names are in CAMPAIGN_INTERFACE.md) |
| `inverters.n<j>.measure_sha256`, `gate_sha256`, `lean_sha256`, `files` | the records and their hashes |
| `inverters.n<j>.same_sample`, `fingerprint` | `fingerprint` holds `names`, `network` (from the unchanged deck) and `runs` (one per run) |
| `inverters.n<j>.margins`, `measures`, `state_bound`, `kernel`, `machine_s` | for the report |
| `open_premises`, `verdict_status` | as in every gate: conditional on the open premises |

`SHA256SUMS` covers every file of OUTDIR except `lean_build/`.

## Cost

- XOR3 at 9803: about 6.1 min CPU per inverter (5 runs of the full deck), plus about 25 s for the network op.
- The two inverters ran in parallel, in 6.9 min wall (the Lean build was cached).
- Disk: about 6 MB per inverter.
