# Identity test I2, with the capacitors of stage P at 0 F

Run on 2026-11-13, after [`../AMENDMENT_3.md`](../AMENDMENT_3.md) was
pushed and before any run of stage P. **These are simulations of the
schematic: every area is written at zero and every capacitor is 0 F.
No run shows a post-layout result.**

```sh
cd research/sky130-layout/phase1 && sh identity_i2.sh        # three runs, about two minutes
```

The rule is that of [`../AMENDMENT_1.md`](../AMENDMENT_1.md): I2 passes
on a run if every FIRE flag, steering flag and count is identical,
every time is identical, every stored voltage is within 2 µV and the
lowest voltage of the main capacitor within 20 µV.

## Result: I2 passes, to the byte

| Run | Cell | Deck | Against | Result |
|---|---|---|---|---|
| `nom_i2` | nominal | expanded, `ad=0 as=0 pd=0 ps=0` on the 232 transistors, **1 436 capacitors of 0 F** | committed `../../circuit/results/nom.csv` | **identical byte for byte**: 0 rows of 21 differ |
| `mm_ref` | seed 6002, no noise | the deck of `run.py` as it is | | the reference |
| `mm_i2` | seed 6002, no noise | expanded, areas at zero, the 1 436 capacitors of 0 F | `mm_ref` | **identical byte for byte**: 0 rows of 21 differ |

- The 1 436 capacitors are the pairs of nodes of
  `p_caps_primary.csv`. `p_caps.csv` holds the same pairs: with every
  value at 0 F the two lists give the same deck, which the script
  checks.
- sha256 of `nom_i2.csv`:
  `a3dbb2cd0c72080c3a93c9dc4d614cfc7fd27635adf146fb733bd112c87e3e4c`,
  that of the committed `nom.csv`.
- sha256 of `mm_i2.csv` and of `mm_ref.csv`:
  `0b2ce7756cf917ddd7a8cb823969517676ad899c83823b45378605e31d5e0126`,
  as in [`IDENTITY.md`](IDENTITY.md).

**This is better than the bounds asked for.** With the eight capacitors
of [`IDENTITY.md`](IDENTITY.md) the last printed digit moved by 1 µV;
with these 1 436 it does not move. No reason was looked for. The bounds
of I2 are not changed.

The three runs were made twice. The first time the script stopped in
its comparison step, on a file path, after the three runs had ended;
the script was corrected and run again. Both times gave the same three
result files.

## Not done

The timing run and the scope. [`timing.py`](timing.py) is written and
builds its two decks (`timing.py check`: 232 transistors with areas,
1 436 capacitors, nothing simulated). It starts only on the owner's
word.
