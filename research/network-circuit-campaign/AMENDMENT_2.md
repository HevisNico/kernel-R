# Amendment 2 to PREDICTION.md

Pushed alone, before the attempt marker of the measures and before any run
of the campaign. It changes no frozen file and no rule of
[`PREDICTION.md`](PREDICTION.md) or of [`AMENDMENT_1.md`](AMENDMENT_1.md).
It adds two declared comparisons, asked for by the owner: counts and values
only, with no "holds" or "fails". Its script is inside this file, so that
no code file enters the folder.

## 1. Predicted final values (N5)

The model does not only say which pulses fire: it says where each stored
voltage ends. For each eligible instance and each port, from
`PREDICTED.json` alone, before any network run:

    predicted final stored voltage = preset - (writes of the zero-error word) x (measured dose)

in mV, where the preset is the stored voltage of the port before its first
pulse in its scan, and the stored voltage is the stored node minus the
summing node, as everywhere in `PREDICTION.md`.

After the one analysis, the observed final value of each port is read on
the waveform of the `quiet` run, through the frozen `measure.Trace`, as the
mean over the 28 us that end 2 us before the horizon, and printed next to
the predicted one, with the stored voltage of the run before its first
pulse (the mean over the 35 us that end 5 us before date 0).

**What D1 and D2 imply.** If D1 holds on a run, each port made exactly its
predicted writes. If D2 holds as the analysis checks it (amendment 1,
section 3), each write moved the stored voltage by the measured dose within
0.01 mV, and the stored voltage moved by at most 0.01 mV across each other
pulse of the port and between two of its pulses. The final stored voltage
of a port that received `n` pulses is then within `(2 n + 1) x 0.01` mV of
its value at the start of that run minus writes x dose.

The owner asked for the allowance `(n + 1) x 0.01` mV. That is tighter than
what D2 guarantees, and the predicted value starts from the preset of the
scan, not from the start of the run, which D2 does not bind. The script
therefore prints the difference with both allowances and both starting
values, and decides nothing.

## 2. Pulses after learning (N6)

For each port, the number of pulses it receives after its last write:
predicted as the number of letters after the last `s` of its zero-error
word (the whole word if it has no `s`), observed the same way on the word
of the `quiet` run. It says that the memory settles at the predicted value
while pulses keep arriving, at transistor level.

## The script

Run once, after the one analysis, from the root of the repository, with the
pinned interpreter and the evidence folders of the network runs of the two
machines as arguments. It reads `PREDICTED.json`, `RESULTS.json` and the
waveforms of the `quiet` runs that count. Its output is committed as
printed. The instances that are not eligible are printed too, marked as
such; nothing is claimed about any line.

```sh
"$PY" -B - "$RUNS_A" "$RUNS_B" <<'EOF'
import json, sys
from pathlib import Path
B = Path("research/network-circuit-campaign")
sys.path.insert(0, "research/network-circuit")
import measure, net, router
P, R = json.loads((B / "PREDICTED.json").read_text()), json.loads((B / "RESULTS.json").read_text())
after = lambda w: len(w) - 1 - w.rfind("s")
for x in R["runs"].values():
    if x["scenario"] != "quiet":
        continue
    s = str(x["seed"])
    I = P["instances"][s]
    kind = "eligible" if s in P["eligible_instances"] else "not eligible"
    evidence = next(f for f in map(Path, sys.argv[1:]) if (f / x["id"]).is_dir()) / x["id"] / "evidence"
    tr = measure.Trace(evidence / "trace.raw")
    end = router.ORIGIN + json.loads((evidence / "result.json").read_text())["calendar"]["horizon"] * net.TU
    for p in ("a1", "a2", "b1", "b2"):
        c, z, o = I["constants"]["ports"][p], I["zero_error_words"][p], x["words"][p]
        predicted = c["preset_mV"] - z.count("s") * c["dose_mV"]
        first = tr.u(p[0], int(p[1]), router.ORIGIN - 40e-6, router.ORIGIN - 5e-6) * 1e3
        last = tr.u(p[0], int(p[1]), end - 30e-6, end - 2e-6) * 1e3
        print("N5", s, kind, p, "predicted %.4f observed %.4f difference %+.4f | pulses %d: (n+1) x 0.01 = %.2f, (2n+1) x 0.01 = %.2f | initial: run %.4f, scan %.4f"
              % (predicted, last, last - predicted, len(o), (len(o) + 1) * 0.01, (2 * len(o) + 1) * 0.01, first, c["preset_mV"]))
        print("N6", s, kind, p, "pulses after the last write: predicted", after(z), "observed", after(o))
EOF
```

The predicted values of N5 and N6 are fixed by `PREDICTED.json`, which is
committed and pushed before any network run; this script only prints them
next to what was observed.
