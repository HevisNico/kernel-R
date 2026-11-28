# Raw trace archive: K07, rehearsal 1

## Provenance

- Machine: K07
- Session: session_01TzF7ZX8H83BpXXaEaC2x7C
- Instance: XOR3_70285
- Original path on K07: ~/reh/out_K07/XOR3_70285/N0/trace.raw (the rehearsal root, OUTROOT)
- Root path in the published root: out_K07/XOR3_70285/N0/trace.raw
- Freeze commit: 5d02acce299de86f885a5b3d22ee86d08bcfafad (research/layered-campaign-freeze)
- Published root: evidence/combined-rehearsal-K07 at 4a462ffbab5dc88fdeeee094e9166ee4c035e13a, where this file is listed in NOT_PUBLISHED.txt

## State

Raw data of a completed rehearsal 1 run; its comparison is published in the root (out_K07/XOR3_70285/N0/comparison.json, verdict "observed only (no prediction)").

## Original file

- sha256: e00303ac8daa20dc6ab8c60f667b96bc990016be4089a83c93efee12103ecaf6
- size: 1696023842 bytes
- parts: 34, in this order (33 of 50000000 bytes, the last of 46023842 bytes):

- `out_K07/XOR3_70285/N0/trace.raw.transport-part-000`
- `out_K07/XOR3_70285/N0/trace.raw.transport-part-001`
- `out_K07/XOR3_70285/N0/trace.raw.transport-part-002`
- `out_K07/XOR3_70285/N0/trace.raw.transport-part-003`
- `out_K07/XOR3_70285/N0/trace.raw.transport-part-004`
- `out_K07/XOR3_70285/N0/trace.raw.transport-part-005`
- `out_K07/XOR3_70285/N0/trace.raw.transport-part-006`
- `out_K07/XOR3_70285/N0/trace.raw.transport-part-007`
- `out_K07/XOR3_70285/N0/trace.raw.transport-part-008`
- `out_K07/XOR3_70285/N0/trace.raw.transport-part-009`
- `out_K07/XOR3_70285/N0/trace.raw.transport-part-010`
- `out_K07/XOR3_70285/N0/trace.raw.transport-part-011`
- `out_K07/XOR3_70285/N0/trace.raw.transport-part-012`
- `out_K07/XOR3_70285/N0/trace.raw.transport-part-013`
- `out_K07/XOR3_70285/N0/trace.raw.transport-part-014`
- `out_K07/XOR3_70285/N0/trace.raw.transport-part-015`
- `out_K07/XOR3_70285/N0/trace.raw.transport-part-016`
- `out_K07/XOR3_70285/N0/trace.raw.transport-part-017`
- `out_K07/XOR3_70285/N0/trace.raw.transport-part-018`
- `out_K07/XOR3_70285/N0/trace.raw.transport-part-019`
- `out_K07/XOR3_70285/N0/trace.raw.transport-part-020`
- `out_K07/XOR3_70285/N0/trace.raw.transport-part-021`
- `out_K07/XOR3_70285/N0/trace.raw.transport-part-022`
- `out_K07/XOR3_70285/N0/trace.raw.transport-part-023`
- `out_K07/XOR3_70285/N0/trace.raw.transport-part-024`
- `out_K07/XOR3_70285/N0/trace.raw.transport-part-025`
- `out_K07/XOR3_70285/N0/trace.raw.transport-part-026`
- `out_K07/XOR3_70285/N0/trace.raw.transport-part-027`
- `out_K07/XOR3_70285/N0/trace.raw.transport-part-028`
- `out_K07/XOR3_70285/N0/trace.raw.transport-part-029`
- `out_K07/XOR3_70285/N0/trace.raw.transport-part-030`
- `out_K07/XOR3_70285/N0/trace.raw.transport-part-031`
- `out_K07/XOR3_70285/N0/trace.raw.transport-part-032`
- `out_K07/XOR3_70285/N0/trace.raw.transport-part-033`

## Reconstruction

```
cat out_K07/XOR3_70285/N0/trace.raw.transport-part-* > trace.raw
sha256sum trace.raw     # must print e00303ac8daa20dc6ab8c60f667b96bc990016be4089a83c93efee12103ecaf6
stat -c %s trace.raw    # must print 1696023842
```

The shell glob sorts the parts in their numeric order (000 to 033).

## Digest recorded in the root

The root does not list trace.raw in any SHA256SUMS*. It records a digest of it in out_K07/XOR3_70285/N0/trace.digest.json, which is itself listed in out_K07/XOR3_70285/SHA256SUMS (sha256 29e4c4a0bc8141adf2d8b0603a622a85dfa5687637b99ee89efd295ac71e580a):

- size: 1696023842
- data_sha256: 0d7f754d0ccee5c13838c636cc7f631f07e785158e0b0304e5d09f102cfee227 (the data section)
- header_sha256_without_date: 2841a5b4b49e9030acde36033d2ab0c85daafef9853c85691c09bd51de37a377
- date_line: "Date: Fri Nov 27 16:32:22  2026"

These are digests of the trace's parts as defined by the driver, not of the whole file. The whole-file sha256 above was computed on K07 from the original before splitting. The same source_digest appears in out_K07/XOR3_70285/N0/extract/extract.json.
