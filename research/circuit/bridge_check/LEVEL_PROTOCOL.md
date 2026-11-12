# The threshold budget in two parts

Pushed before any value of the FIRE level is computed from the traces.
This rule is retrospective: it is written after the rest, DC and local
results, the firing patterns of the five replays and the historical
200-port table have been seen. In particular it is known that the three
replays of mismatch seed 2064 give four silent pulses on port 1, where the
original run `mc_2064` gave three. No level at a FIRE has been looked at.

## Quantities

The declared coordinate is `q = 0.1 + (1.25 - Vq) / 0.5`. For a period
with a FIRE, the level of that read is `q` at the rising crossing of the
protection latch at 0.9 V, linearly interpolated between solver points.
The scalar model with that level fires at that date. A silent read has no
such value: it only says that the level is above the largest `q` of the
read.

The historical table normalizes each port to the firing swing of its
cell. Its reference level is therefore

```text
level0 = 0.1 + trip_proxy / 0.5
```

with `trip_proxy` taken unchanged from `need_budget_ports.csv`. The
theorem asks for `|level - level0| <= ell` at every read.

## Static part: measured on the cell

The mismatch sample of a cell is reproduced by its seed. On the replay of
the cell without noise, take the level of every single-port period with a
FIRE.

```text
ell_static = max over these periods of |level(quiet) - level0|
```

It is a measure on the cell and it applies to the original port. It is
still a finite list of reads on one trajectory, not a bound on all reads.
It is available only for a cell that has a replay without noise: here,
seed 2064. For every other cell it is not measured, and nothing is put in
its place.

## Dynamic part: a statistic on the replays

Noise moves the level from one read to the next, and a noisy run is not
reproduced by its seed. For every single-port period that has a FIRE both
in a noisy replay and in the replay without noise of the same cell, same
port and same pulse number, take

```text
delta = level(noisy) - level(quiet)
ell_dynamic = max( largest |delta| , 3 * standard deviation of delta )
```

over the two noisy replays together, the standard deviation with n - 1.
Periods with a FIRE in only one of the two are counted and listed, and
left out of `delta`.

`ell_dynamic` is a statistic of two replays. It has no stated coverage and
it is **not a certified bound for the original trajectory**, whose noise
is another draw. A result that uses it is reported as statistical.

## Use

```text
ell = ell_static + ell_dynamic
room = d0/2 - a - m*b - (20/17)*ell - 1/8000
```

`d0`, `a`, `m` and `b` are the proxies of the historical table, unchanged.
`room` is computed with `ell_static` alone and with `ell`. Both are
reported next to the historical value, which keeps `ell = 0` as an
assumption. A port whose cell has no `ell_static` has no new `room`.

The hypotheses `19/20 <= level` and `19/20 <= level0` are checked on the
same values.

`mc_2064`, port 1, is reported as it comes out. Its original count, three
silent pulses against four, is not changed, and the original port is not
given a new status from the replays: their noise is not its noise.
