# Raw archive: K01, rehearsal 1, XOR3_88529 N0 trace.raw

## Provenance
- Machine: K01 (Claude Code cloud session session_01TzF7ZWh8mrS7YeHvNvVjjd)
- Instance: XOR3_88529 (rehearsal 1 of the combined campaign, campaign mode)
- Original path on the machine: ~/reh/out_K01/XOR3_88529/N0/trace.raw (OUTROOT ~/reh/out_K01)
- Path relative to the published root: out_K01/XOR3_88529/N0/trace.raw
- Freeze commit: 5d02acce299de86f885a5b3d22ee86d08bcfafad (research/layered-campaign-freeze)
- Published root: evidence/combined-rehearsal-K01 at d93e8584edbbb2d76e52a53891a25729d859cd43, where NOT_PUBLISHED.txt lists this file

## State
raw data of a completed rehearsal 1 run; its comparison is published in the root

## Original file
- sha256: 6aa8a9bd1b6bcefa08e2da8abc7b5082d4ec5a7fadf4ecee59ff48231abbe9c5
- size: 1584729184 bytes
- sha256 and size computed on K01 from the original, before splitting; the concatenation of the parts gives back the same sha256 and size (checked on K01)
- Ordered parts (in out_K01/XOR3_88529/N0/, 50,000,000 bytes each except the last, 34,729,184 bytes):
  - trace.raw.transport-part-000
  - trace.raw.transport-part-001
  - trace.raw.transport-part-002
  - trace.raw.transport-part-003
  - trace.raw.transport-part-004
  - trace.raw.transport-part-005
  - trace.raw.transport-part-006
  - trace.raw.transport-part-007
  - trace.raw.transport-part-008
  - trace.raw.transport-part-009
  - trace.raw.transport-part-010
  - trace.raw.transport-part-011
  - trace.raw.transport-part-012
  - trace.raw.transport-part-013
  - trace.raw.transport-part-014
  - trace.raw.transport-part-015
  - trace.raw.transport-part-016
  - trace.raw.transport-part-017
  - trace.raw.transport-part-018
  - trace.raw.transport-part-019
  - trace.raw.transport-part-020
  - trace.raw.transport-part-021
  - trace.raw.transport-part-022
  - trace.raw.transport-part-023
  - trace.raw.transport-part-024
  - trace.raw.transport-part-025
  - trace.raw.transport-part-026
  - trace.raw.transport-part-027
  - trace.raw.transport-part-028
  - trace.raw.transport-part-029
  - trace.raw.transport-part-030
  - trace.raw.transport-part-031

## Reconstruction
```
cd out_K01/XOR3_88529/N0
cat trace.raw.transport-part-* > trace.raw   # the glob sorts 000..031 in order
sha256sum trace.raw                           # 6aa8a9bd1b6bcefa08e2da8abc7b5082d4ec5a7fadf4ecee59ff48231abbe9c5
stat -c %s trace.raw                          # 1584729184
```
Check the parts first with `sha256sum -c SHA256SUMS` from this folder.

## Digest recorded in the root
The root records a digest of the raw, but no whole-file sha256:
- out_K01/XOR3_88529/N0/trace.digest.json, listed in out_K01/XOR3_88529/SHA256SUMS (2b283bea9d6267b6adc7e81927626617e017cfe1a708e59efaf58ae778390ab2), holds:
  - file: trace.raw
  - size: 1584729184
  - header_sha256_without_date: d3dccea47c0b1d1d246b864d6b8255ab8eef85aadd2df7c2adb813f8e4c34d00
  - data_sha256: 3a711e0fe966e55b504f350b05e0ead8a293ef23cfb3c148383245504f5e08a1
  - date_line: "Date: Fri Nov 27 17:16:30  2026"
- out_K01/XOR3_88529/N0/extract/extract.json repeats this digest as source_digest.
