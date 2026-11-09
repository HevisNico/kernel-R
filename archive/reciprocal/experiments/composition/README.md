# Numerical checks of the compositional chain theorem

`run.py` uses the unchanged three-port single-cell engine, sequentially composing
its actual emissions and delayed deliveries. It numerically integrates each
cell's preparation from birth before starting the fast cascade; no learned
setting is imposed by copy or live reset. Disconnected frozen probes are
separate assays.

Cases cover 1,3,4,16,32 cells, with the latter cases sampling independent
±10% physical parameters and using alternating extreme or random per-pulse
wire errors within the theorem's path budget. Source pulse count, per-node
emissions, recovery and active gain, the last eight source-pulse origins and
before/after frozen probes are checked. The report records parameters and seeds.

```sh
python -m pip install -r requirements.txt
python -B experiments/composition/run.py --out audit_runs/new_composition.json
```

This floating-point engine computes the q/m/z/b flows and accumulated work;
it relies on the theorem's reserve invariant for the open energy gate.
These numerical checks do not certify the parameter boxes or arbitrary N.
The [written compositional proof](../../proof/reciprocal_composition/THEOREM.md)
and [exact arithmetic checks](../../results/reciprocal_composition/README.md)
are separate.
