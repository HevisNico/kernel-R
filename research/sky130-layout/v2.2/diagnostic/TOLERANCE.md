# Layout 2.2: the 16 ports with a tolerance on the rest band

**Exploratory, and declared as such. No verdict changes**: C1 fails as
[`../C_REPORT.md`](../C_REPORT.md) says, with the rule as it is. No
simulation is run; the committed results of stage C are read again.

```sh
cd research/sky130-layout/v2.2/diagnostic
python3 -I tolerance.py
```

The rest band of the rule is 0.1 to 0.1001 in level units: `vq`
between 50 µV below its rest reference and the reference itself, with
nothing allowed above it. Here it is widened by a tolerance δ on `vq`
on both sides, and nothing else of the rule is changed. The script
checks first that without tolerance it gives the counts of the report.

| Tolerance on `vq` | Rest band, level units | Certified, of 16 | At status 3 | By rule A1 | Contradicted | Refused for the rest state |
|---|---|---|---|---|---|---|
| none: the rule | 0.1000000 to 0.1001000 | 7 | 4 | 7 | 0 | 3 |
| 0.1 µV | 0.0999998 to 0.1001002 | **8** | 5 | 8 | 0 | 0 |
| 1 µV | 0.0999980 to 0.1001020 | **8** | 5 | 8 | 0 | 0 |
| 10 µV | 0.0999800 to 0.1001200 | **8** | 5 | 8 | 0 | 0 |

**With any of the three tolerances, 8 of the 16 ports would be
certified, and none contradicted.** No port is refused for its rest
state any more, and one port changes:

| Port | Without tolerance | With 0.1, 1 or 10 µV | Rooms of rule A1, silence and FIRE | Room at status 3 |
|---|---|---|---|---|
| `t6051` port 1 | not certified: rest state and rooms | not certified: rooms | −0.01456 and −0.01556 | −0.01672 |
| `t6082` port 1 | not certified: rest state and rooms | not certified: rooms | −0.00571 and −0.00354 | −0.00761 |
| `t6031` port 1 | not certified: rest state only | certified, at status 3 and by rule A1; count 4, need 4 | +0.00680 and +0.00135 | +0.00123 |

- Two of the three refused ports have no room anyway. The rest band
  was the only thing between `t6031` port 1 and its certificate.
- 0.1 µV is just enough: the largest excursion is 90.5 nV (`t6051`).
- **What this does not do.** The rooms are those of the rule as it is:
  they were not recomputed for a wider band. A tolerance of 10 µV
  widens the band by 0.00002 level unit on each side; the smallest room
  among the eight ports is 0.00119. Whether the proof behind the rule
  accepts a rest state above the reference, and at what cost in room,
  is a question for the rule, not for this count.
