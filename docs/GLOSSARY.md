# Glossary

| Term | Meaning here |
|---|---|
| READY, FAST, SLOW | Main-cell modes. READY admits current. FAST emits a pulse. SLOW recovers before reopening. |
| MARK, SILENT, ERROR | The three phases of a port sensor after threshold crossing. MARK can increase recovery, and ERROR can increase the port's log-gain. |
| Raw current | The active width-one pulse at a port, determined by its arrival time. An input can reach a sensor while the main unit is protected. |
| Log-gain and recovery | The two learned quantities. A port stores `z`, with input gain `exp(z)`. The cell stores `b`, which governs SLOW decay. |
| First contact | The native Lean event convention, in which reaching a READY threshold enables its event. |
| Upward crossing | The written model's FIRE/MARK rule. The actual history approaches from below and a right continuation in the incoming mode moves above threshold. |
| Complete through `T` | The execution reaches `T` and resolves all enabled events and all deliveries due by `T`. |
| Observational equality | Agreement of time, physical coordinates, modes and active raw origins, with pending deliveries compared up to permutation. The theorem compares ordered FIRE dates separately. |
| Terminal saturation | The condition that no jump is enabled at the terminal time. |
| Memory saturation | A port's log-gain reaches its cap and stays there. |
| Reset-window saturation | Permanent blocking in the separate [scalar reset-window model](../research/reset-window/README.md). |
| Non-Zeno | Physical events cannot accumulate in finite time under the specified hypotheses. |
