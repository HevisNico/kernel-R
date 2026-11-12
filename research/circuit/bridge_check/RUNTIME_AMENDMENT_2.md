# Runtime amendment 2, before any replay or sweep

The rules of `REST_PROTOCOL.md`, `GAIN_PROTOCOL.md` and `LOCAL_PROTOCOL.md`
are not changed, and their files are not edited. This amendment changes
the machine on which they are run. It is pushed before the first run.

## What happened

The runs named `*_retry1` in `manifest.json` and the 27 sweeps of
`gain_manifest.json` were made in an earlier session. Nothing of them was
pushed, and that session and its machine are lost. `LOCAL_PROTOCOL.md` was
written after their results had been seen. Those results are not available
here. They are run again from the frozen rules.

## What differs on this machine

| | Frozen manifests | This machine |
|---|---|---|
| Simulator | Debian ngspice 44.2, SHA-256 `5854f650...` | ngspice 42 (Ubuntu 42+ds-3build1), SHA-256 in `runtime2.json` |
| Temporary-file adapter | A compiled adapter, SHA-256 `c91823f3...` | None. `tmpfile()` works here, and the binary of the adapter cannot be rebuilt byte for byte |

ngspice 44.2 could not be installed: the network of this machine refuses
the Debian archive. ngspice 42 is the version of the original campaign,
and this binary is the one that ran its 141 runs. The limitation written
in `REST_PROTOCOL.md` on the change of version therefore falls away for
these runs. Another one replaces it: these runs are not a repetition of
the lost ngspice 44.2 runs, and no number of that session is used.

## What does not change

- The decks come from the frozen `deck()` functions of `rest_probe.py` and
  `gain_probe.py`, imported unchanged.
- The run lists, their order and their names are those of the frozen
  manifests. The rest replays keep the names `*_retry1`, so that the frozen
  `rest_analyze.py` reads them unchanged.
- The frozen source hashes, the PDK revision, the `.spiceinit` check, the
  start file `runtime/spinit`, the time limits (600 s, 120 s) and the rule
  that every run is made once and kept, whatever it gives.
- `rest_analyze.py` and `gain_analyze.py` are run unchanged.

`run_frozen.py` does only this. It checks the frozen files against their
publication commits, and this amendment against the commit that publishes
it, before the first run. The runtime was tested on a deck of one resistor
and one capacitor, not on the circuit.

## Raw traces

A transient trace of 22 periods with 16 digits is tens of megabytes. The
compressed traces are kept in the private working repository, and their
SHA-256 is in each `metadata.json` here. The DC curves are small and are
kept here. A noisy trace cannot be computed again: the seed of a run does
not set its noise.
