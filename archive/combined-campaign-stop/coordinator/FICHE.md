# Archive lot d: the combined campaign's coordinator (stop of 2026-11-28)

- **Provenance:** coordinator session session_01TzF7ZUoTUj44AGYGuEFzHA (cloud container, scratchpad files, never committed before).
- **Base revision:** none (plain files). The state they describe: research/layered-campaign-dev at
  7fa3693ea85a85dde8490e0efdb9eafa80ff7189, research/layered-campaign-freeze at 5d02acce, PR #190 head 0e15bb14.
- **State:** DRAFT / working notes. Nothing here is tested or adopted.

| File | What | State |
|---|---|---|
| AMENDMENT_1_DRAFT_NOT_ADOPTED.md | amendment 1 draft (§1 to §7), extracted verbatim from COORDINATOR_BRIEF_2026-11-28.txt from the line after "AMENDMENT 1 DRAFT" to the end, with a "not adopted" header | draft, not adopted |
| COORDINATOR_BRIEF_2026-11-28.txt | the brief handed to this coordinator (state, plan, lessons, the draft in context) | record, verbatim |
| ETAT.md | the coordinator's running state (French), up to the stop | working notes |
| SUIVI.md | the owner's decisions to carry into the amendment (French): deferred L1, wording, closing criterion | working notes |

## Facts measured at the stop (by the coordinator, not re-verified elsewhere)
- dev 7fa3693e: pushed, 114/114 pins rehashed, FREEZE_PINS.json sha256 6b9704cf…, analysis.py sha256 0c10b8b9…;
  defect suite 52/52 and (a) 24/24 reported by the implementer; review #4 (checker) found no defect above LOW;
  the independent test writer's 90 cases passed 90/90 at 7fa3693e. NOT frozen; proof2 and the full (c) were NOT run on it.
- With draw_seeds.py's own rule (LINE/INT/RANGE, numbers()), the tip of dev 7fa3693e names 61 integers absent from the pinned
  EXCLUDED.json (0 at 9219986b, the scanned tree), 55 of them in [10000, 100000). FREEZE.txt's "rescanned LAST" no longer
  held for dev.

## How to recover
`git fetch origin archive/combined-campaign-stop/coordinator` and check `sha256sum -c SHA256SUMS` in this folder.
