# Noise study, validation: the identity hash of a raw file

The owner's decision, pushed before attempt 2's `GO`. It is a deviation from "nothing else changes" in
[`../VALIDATION_AMENDMENT_2.md`](../VALIDATION_AMENDMENT_2.md), and is recorded here as one.

**What.** The identity checks of amendment 2's proof, of V7 (the two quiet trains identical byte for byte) and of
V8 (a rerun gives the same stored-voltage waveforms byte for byte) compare `raw_nodate_sha256`: the SHA-256 of the
whole raw file except its `Date:` line. That covers the header fields, the variable list, the point count and the
data block (`vrun.raw_nodate_sha256`). The full-file `raw_sha256` is still recorded for every run, as before. This
adds one recorded hash and changes what V7 and V8 compare. It changes no draw.

**Why.** ngspice writes the date of the run in the header of every raw file. Two runs of the same draw therefore
never have the same full-file hash: phase 0 checked this on two identical V8 runs, whose data were equal. Under the
full-file hash, V7 and V8 would have failed on a date, while the criteria's intent is identical data. Campaign 4's
draft already states "the date line of the raw file aside".
