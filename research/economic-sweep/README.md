# Exploratory capacity and price sweep

This is a separate exploratory study, not v5 or a v6 experiment. The grid and
scenario definitions were written in [PLAN.md](PLAN.md) before the calculation.
The finite-grid result is in [REPORT.md](REPORT.md); all 56 weighted cells and
14 scenario/capacity cases are retained in [RESULTS.json](RESULTS.json) and
[cells.csv](cells.csv).

The reference controller source is authenticated by SHA256 against #119. It is
imported without invoking its main function; only its existing Controller class
is used with the stated capacity parameter. No historical runner is called or
evidence altered. The only simulator here is the expressly exploratory sweep.

From this directory:

```sh
python3 -B -m unittest -v test_sweep
python3 -B sweep.py
```

When installed in `research/<study-folder>`, the sibling
`research/boundary-cost-study/study.py` is found automatically. Alternatively
pass `--source /absolute/path/to/boundary-cost-study/study.py` to `sweep.py`.
Five tests pass, including independent backward-DP checks of the forward
oracle and the capacity6600 expensive-probe headline. JSON and CSV results
reproduce byte for byte. The algorithm and grid were not tuned after observing
results; changes after calculation added report interpretation and extra
independent checking only.

There are no action-changing cost benefits for the optimistic policy in this
grid. This does not imply all learning is useless: the expensive-probe,
large-capacity region contains a substantial oracle gap not exploited by the
present optimistic mechanism. In the constant-high-rate scenario, some actions
do change while probe/write counts and costs remain identical. Those changes
come from an existing fixed planning margin, not learning a new law.
