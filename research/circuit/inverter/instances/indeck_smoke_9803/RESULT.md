# invinst.indeck smoke test: XOR3, dev seed 9803

`python -m invinst.indeck OUTDIR --deck xor3.spice --seed 9803` was run at commit 8442393, with a clean package tree.

## The deck

The deck is `instrument.deck_text(spec.load("specs/xor3.json"), lcal2.config("config_inverter_c5.json")[0])`, from
research/layered-networks 8af2cba. Its sha256 is 28b8df45…7301c9e.

## Results

| Inverter | same_sample | K0 | K3 | K3 silence / firing margin | xPresent / xAbsent (limit 1.35) | δ | ηH | CPU |
|---|---|---|---|---|---|---|---|---|
| n0 | true | true | true | 0.1554 / 0.2928 | 0.8457 / 1.2226 | 0.0083 | 0.0318 | 363 s |
| n1 | true | true | true | 0.1584 / 0.2725 | 0.8734 / 1.2185 | 0.0121 | 0.0389 | 364 s |

- **Instance verdict:** K0 true, K3 true.
- **Fingerprints:** every run's fingerprint equals the unchanged deck's, at the 6 digits printed. They match the values
  stage D reported for xn0 and xn1.
- **Wall time:** 6 min 51 s, with the two inverters in parallel.

The kept files are `inverter_gate.json`, `NETWORK_FINGERPRINT.json`, both gate files and `OUTDIR_SHA256SUMS` (the run
folder's SHA256SUMS). The traces are not kept.
