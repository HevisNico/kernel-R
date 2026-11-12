# A new rule: decomposition of the budget, and a cumulative budget

This is a new rule, written after the result of `BRIDGE_APPLICATION.md`:
no port of the 100 cells is in the certified domain. That result stays as
it is and stays visible next to anything computed here. Everything pushed
so far has been seen: the replays, the calibration, the threshold budget
of cell 2064, the historical 200-port table and its ten disagreements.
Nothing of what follows has been computed when this rule is pushed.

## Part 1. Which term makes the per-write budget fail

The theorem `needAlong_of_circuit_tolerances` asks for

```text
a + m*b + (20/17)*ell + 1/8000 < d0/2,      b = k*eta + sigma + e.
```

For each of the 200 ports, with `d0`, `a` and `m` of the historical
table, unchanged:

- `b` is the sum measured on the nominal replays: the largest transfer
  residual, the largest sensor tolerance, the largest part of a
  read-to-read increment not explained by the window, and the largest
  local calibration error of one step (`local_summary.json`, run
  `nominal_200ns_retry1`). It is one number for all ports. It is measured
  on nominal devices and applied to every port as an estimate.
- `ell` is `ell_static` for the two ports of cell 2064 and 0 for the
  others, where it is not measured. A room computed with `ell = 0` is
  marked as such.

Report for each port the four terms, `d0/2`, the room, the largest term,
and `b_max = (d0/2 - a - (20/17)*ell - 1/8000) / m`: the largest `b` that
would leave a positive room. Report the port with the largest room, and
the factor `b / b_max` by which `b` would have to shrink for it and for
the median port. A port with `m = 0` or a missing value is not evaluable.

## Part 2. A cumulative budget

The proof of the need theorem only uses bounds on cumulated doses. A
variant, to be proved in Lean before any use here:

```text
if   |z(n) - z(0) - n*d0| <= B   for every n <= m,
and  z(m) <= z(n)                for every n >= m,
and  a + B + (20/17)*ell + 1/8000 < d0/2,
then the need is m.
```

### Measure of the cumulated gain

For a port of an original run, `V(n)` is its stored voltage after its
n-th write, read in the campaign CSV at the end of the period of its n-th
silent pulse. `V(0)` is the stored voltage read at the end of the period
before its first pulse: the period at rest for port 1, the tenth period
for port 2. These are the reads of the original trajectory itself.

With the local calibration at 27 °C of `local_summary.json`, slope `beta`
and secant distance `epsilon`:

```text
z(n) - z(0) = beta * (V(0) - V(n))   within   epsilon * |V(0) - V(n)|
B = max over 1 <= n <= m of  |beta*(V(0) - V(n)) - n*d0| + epsilon*|V(0) - V(n)|
```

The calibration error is that of the lemma `local_slope_step` applied to
the cumulated step. It is proportional to the cumulated step: it is
counted once on the whole, but it does not become smaller than `m` times
the error of one step. The transfer residual, the sensor tolerance and
the window-to-read linkage are not counted any more: the read of the
stored voltage contains their effect.

`d0`, `a` and `m` are those of the historical table, unchanged. `ell` is
as in part 1.

### Status of a port

| Status | Rule |
|---|---|
| Not evaluable | A value is missing, `m = 0`, or the port made fewer than `m` writes, so `V(m)` does not exist |
| Outside the sufficient region | `room = d0/2 - a - B - (20/17)*ell - 1/8000 <= 0` |
| Inside under estimates, count agrees | `room > 0` and the observed count is `m` |
| Inside under estimates, count disagrees | `room > 0` and the observed count is not `m`. Reported as a failure of this application, to be investigated |

"Under estimates" means: not certified. `a` and `d0` remain peak-based
proxies; `ell` is not measured for 99 cells; the calibration is that of
nominal devices on a finite grid; a stored voltage of the campaign is an
average over 40 µs of a noisy signal, printed to 1 µV; the scalar read
equation is not established. A port inside under estimates is not in the
certified domain, and the count of certified ports stays what it is.

The rule makes a port that fired before `m` writes not evaluable. This
depends on the outcome and is said here: such a port cannot support or
contradict the cumulative budget.

No budget, cutoff or estimate is changed after the numbers are seen.
