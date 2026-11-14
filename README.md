# SKY130 supervisor campaign: waveforms of whole runs

Public copy of the 123 waveforms of whole runs (`trace.raw`) of the registered
campaign of `research/sky130-supervisor-campaign`, unchanged. This branch holds
nothing else and shares no history with the rest of the repository.

Each file is at `machine-a/<run>/evidence/trace.raw` or
`machine-b/<run>/evidence/trace.raw`, the path it has in the evidence of its
machine. Its SHA-256 is in the `SURVIVORS.json` of its machine, copied here
and committed with the rest of the evidence under
`research/sky130-supervisor-campaign/evidence/` on the campaign branch.

The run `a55-main-tt27` has no waveform: the simulator stopped it before it
wrote one.

Format: binary raw file of ngspice 42, real values, vectors `v(p)`,
`v(vmem1)`, `v(vmem2)`, `v(x1.sum)`, `v(x2.sum)`, `v(x1.si)`, `v(x2.si)`.
