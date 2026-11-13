# Incidents of the repetition campaign

Reported under amendment 2. No script, rule or result was changed.

| Time (UTC, 2026-11-13) | Machine | What | Runs that had ended | What was done |
|---|---|---|---|---|
| between 10:21 and 10:37 | A | The container was restarted by its host during repetition 6 | 21 of 52 | Amendment 2 pushed at 10:38:23; the slice was launched again at 10:38 and ran the 31 other runs with their own noise numbers |
| between 10:14 and 10:39 | B | The container was restarted by its host during repetition 7 | 14 of 52 | After amendment 2 was pulled, the slice was launched again at 10:39 and ran the 38 other runs with their own noise numbers |

On both machines the SHA-256 of the simulator, the commit of the models and the checkouts were intact after the restart; `rep_run.py` checks them at every run. No run failed. A killed run left no file.
