# Amendment 1 to PREDICTION.md

Pushed alone, before the attempt marker of the measures and before any run
of the campaign. It changes no frozen file and no rule of
[`PREDICTION.md`](PREDICTION.md). It adds one declared comparison, one
reading rule and two expectations, asked for by the independent review of
the implementation at commit `54a9989`.

## 1. A declared comparison against the nominal predictor (N4)

Not a claim: counts only, with no "holds" or "fails".

The **nominal predictor** ignores the measures. It gives every instance the
words of the nominal cell on the 18-unit calendar (`nominalRun` of
`../network-circuit/phase1/CircuitNetwork.lean`, seen in `REHEARSAL.json`):

| Port | Nominal word |
|---|---|
| `a1` | `ssssFFFFFFFFFFFFFF` |
| `a2` | `ssssFFFFFF` |
| `b1` | `ssssFFFFFF` |
| `b2` | `ssssFFFFFFFFFFFFFF` |

- **N4a.** For each eligible instance, the number of ports, from 0 to 4,
  whose zero-error word in `PREDICTED.json` differs from the nominal word.
- **N4b.** For each `quiet` run that counts, the number of ports whose
  observed word in `RESULTS.json` differs from the nominal word: the ports
  where the nominal predictor would have been wrong. The eligible instances
  and the others are listed apart.

Both are computed from `PREDICTED.json` and `RESULTS.json` alone, after the
one analysis, by this command, with no change to any code. Its output is
committed as printed.

```sh
python3 - <<'EOF'
import json
B = "research/network-circuit-campaign/"
P, R = json.load(open(B + "PREDICTED.json")), json.load(open(B + "RESULTS.json"))
N = dict(a1="ssss" + "F" * 14, a2="ssss" + "F" * 6, b1="ssss" + "F" * 6, b2="ssss" + "F" * 14)
for s in P["eligible_instances"]:
    w = P["instances"][s]["zero_error_words"]
    print("N4a", s, sum(w[p] != N[p] for p in N))
for x in R["runs"].values():
    if x["scenario"] == "quiet":
        s = str(x["seed"])
        print("N4b", s, "eligible" if s in P["eligible_instances"] else "not eligible", sum(x["words"][p] != N[p] for p in N))
EOF
```

What it is for: D1 says that the words computed from the measures are the
observed ones. N4 says how far those words are from what one would have
written without measuring anything. If N4a is 0 for every eligible
instance, D1 cannot tell the measured predictor from the nominal one, and
the report says so.

## 2. Reading rule

The analysis first checks that `PREDICTED.json` is what `predicted.py`
gives from the evidence of the measures, and writes the answer in
`RESULTS.json` (`predictions_are_those_of_the_measures`) and at the top of
`REPORT.md`.

**If that answer is NO, D1, D2 and C1 are reported "not established",
whatever verdicts and counts the analysis printed.** The generated files
are committed as generated; every statement of the results follows this
rule.

## 3. Expectations, not rules

- **C1 can fail.** If every eligible instance has all its margins of a last
  silence above the help that a pulse 8 units earlier gives, the predictor
  that ignores the help is right at 8 units, as it is on the nominal cell
  (rehearsal: the control gave the four zero-error words; the last silences
  of the nominal cell hold by 0.80 mV). `PREDICTION.md` already says that a
  failed C1 shows nothing on that instance and does not touch D1.
- **D2 is checked more strictly than it is written.** `PREDICTION.md` asks
  that no stored voltage move by more than 0.01 mV during a pulse of
  another port or of a FIRE. The analysis checks each port over the whole
  run: between two of its pulses, and across each of its own FIRE pulses,
  its stored voltage moves by at most 0.01 mV. This also counts any slow
  drift between pulses. A failed D2 never refutes D1: D1 is evaluated on
  the run all the same, and the failure of D2 is reported.
