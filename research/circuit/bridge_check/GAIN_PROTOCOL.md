# Independent nominal-device gain calibration diagnostic

Publish this file, `gain_manifest.json` `gain_probe.py` and `gain_analyze.py` before any DC run.
The first rest replay is already known: all 21 nominal states lie literally
in the band, with the first near its lower boundary. No DC gain result has
been inspected. Original 200-port estimates and classifications stay frozen.

This bench isolates the nominal gain mirror and its READY admission devices
with the exact sizes and connections of `cell.spice`: xmin/xmout (40/2.5),
xms1/xms2 (1/0.15), source reference 0.4 V, supply 1.8 V, dump reference
1.25 V, READY gate levels 1.8 V and 0 V. These are nominal `tt` devices;
this does not identify the mismatch parameters of either physical port in
an existing tt_mm run. There is no transient noise or learning in this bench.

Fixed 27 sweeps: temperatures -40, 27, 125 C; input currents ipk/4, ipk/2,
ipk with ipk = (5 pF)*(0.5 V)*log(4)/(20 us); drain/read-node voltages 0.75,
1.0, 1.25 V. Each sweep covers stored source voltage 0.35 to 0.42 V in
0.0005 V steps (141 points). Use ngspice 44.2 and the pinned SKY130 revision
and runtime adapter recorded in the rest manifest. Timeout: 120 seconds per
sweep. Retain every failure and all raw outputs; no outcome-based reruns.

For each temperature, fit log(Iout/Iin) = intercept - beta*Vmem by ordinary
least squares to the fixed reference sweep (Iin=ipk, Vq=1.25 V). Report beta,
1/beta, and the maximum absolute residual over all nine sweeps at that
temperature, separately from the reference-fit residual. Reject the fit if
any sample is nonfinite or Iout/Iin <= 0; do not silently discard points.
Use no observed silent count, FIRE threshold, final trained gain or room
classification to choose the fit, reference sweep or voltage range.

These maxima are finite-grid diagnostics, not uniform bounds between grid
points or bounds on dynamic read pulses. A good DC fit alone cannot establish
frozen gain, the admitted-current waveform or the scalar read equation.

For subsequent diagnostic calculations, define the nominal dose from this
independent calibration as beta*(Cs/Cf)*0.1, with Cs=400 fF and Cf=30 pF.
If saved window endpoints are available, report separately:

- sensor dose proxy beta*(Cs/Cf)*(Vs(entry)-Vs(exit));
- sensor tolerance sample maximum relative to that nominal dose;
- effective capacitor residual Cf*[(Vmem-Vsum)(entry)-(Vmem-Vsum)(exit)]
  minus Cs*[Vs(entry)-Vs(exit)], in coulombs;
- beta*abs(Vsum(exit)-Vsum(entry)) and inter-window stored-voltage drift;
- voltage-derived log-gain step and whether its sign is robust to the reported
  calibration residual (two endpoints).

The effective residual uses the ideal capacitor constitutive equations of
the netlist; it is not a switch-current measurement. It includes all effects
on the feedback capacitor. Uniform physical error bounds, independent
current cross-checks and dynamic calibration remain separate obligations.
The old room estimates are not replaced or reclassified using these values.
