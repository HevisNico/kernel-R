# Supplemental local-increment and latch diagnostics

This is a retrospective follow-up to the already inspected rest and DC
results. It is not a new preregistered confirmation. The original global
DC grid, raw results and historical 200-port `room` table remain unchanged.
No new simulation is required: this rule uses the retained DC curves and
transient traces. Publish the rule before computing the local summaries.

## Temperature-specific local increment rule

Keep a separate slope at each of -40, 27 and 125 C. Determine the observed
stored-voltage range from the original campaign's `vmem1` and `vmem2`
columns: `pvt_tt_m40.csv` at -40 C, `pvt_tt_125.csv` at 125 C, and every
other result CSV at 27 C (including refresh, mismatch and process corners).
Include the design initial voltage 0.3895 V. At 27 C also include all
pre-read/window endpoint memory voltages in the five new raw-trace extracts.
These are observed ranges; summary averages do not bound unsaved excursions.

Round the minimum down and maximum up to the existing 0.5 mV DC grid.
Do not extend, truncate or shrink the range according to the resulting
budget. If it leaves the available grid or has fewer than two grid points,
report not evaluable. Use the same fixed reference curve (ipk, Vq=1.25 V)
as before, fit its log-gain by OLS on this range, and call its negative
slope beta_T. No pulse count, threshold or room value selects the range/fit.

On all nine DC curves at this temperature, compute every adjacent-grid
secant slope and epsilon_T = max(abs(secant + beta_T)). Report the minimum
and maximum secant and whether they are all strictly negative. For the
piecewise-linear interpolation of each fixed-operating-point curve this
bounds step error by epsilon_T*abs(delta V). It is NOT a bound on the
continuous transistor derivative between grid points or a dynamic or
mismatch calibration. Report the endpoint error 2*global_error separately.

For nominal 27 C windows only, evaluate epsilon_T*abs(delta Vmem) and the
local-beta versions of sensor/residual/summing-node/off-window proxies.
Do not replace the old room table or call any port theorem-qualified.
A gain law that also varies with pulse current/drain voltage needs a
separate operating-point/dynamic error term; equal-operating-point secants
do not remove that obligation. Refresh voltage coverage is not a calibrated
refresh-transient measurement.

## FIRE and comparator event rule

Declare circuit FIRE to be the rising crossing of the protection latch p
at 0.9 V. Record all comparator and latch rising/falling 0.9-V crossings in
every saved period, with linearly interpolated dates, pulse-relative dates,
and high/low dwell lengths. Preserve censored segments at period boundaries.
Record comparator transition dates relative to the first FIRE and most
recent latch transition, and whether protection is active at that instant.

Report overlaps of every comparator high/low segment with active-port
ERROR entry/exit windows. A comparator's sustained high state throughout a
protected ERROR window is not an extra write; check the steering signal
and effective capacitor endpoint change on those firing windows separately.
Report intervals shorter than 200 ns, but do not infer rejection from width
alone: DESIGN.md describes a minimum READY/protected dwell before accepting
a transition, not a universal 200 ns comparator pulse-width filter.
The delayed enable nodes are not saved in these traces, so the nominal
200 ns lockout comparison is descriptive, not a proof of its device-level
minimum at every corner. A silent period has no latch FIRE by the declared
mapping; that mapping alone does not prove agreement with a model-predicted
silent count. Keep those two claims separate.

The earlier ammeter result (up to about 0.56% of one dose in its noisy firing
runs) is partial independent evidence of protected transfer suppression.
It is not an all-window residual bound and not a bound for these new draws.
