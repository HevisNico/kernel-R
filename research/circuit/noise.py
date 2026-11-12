"""Noise levels for the transient runs, from small-signal noise analyses of the blocks.

ngspice adds no device noise to a transient. Each block is analysed alone, and its noise is
then injected in the transient as a source at its input:
  white part : band-limited white noise with the total integrated rms of the block, input-referred
  flicker    : a 1/f source with the rms of the flicker part between FLO and the white bandwidth
Writes noise.json.
"""
import subprocess, json, math
import numpy as np
TNZ = 400e-9            # sample time of the transient noise sources: bandwidth 1/(2 TNZ) = 1.25 MHz
FLO = 100.0             # lowest flicker frequency kept: the inverse of a 10 ms run
Q, KT = 1.602e-19, 1.380649e-23 * 300.15

def run(name, body, out_node, src):
    net = [f"* {name}", '.lib "pdk/models/sky130.lib.spice" tt', ".option scale=1e-6", ".include blocks.spice"] + body + [
        ".control", f"noise v({out_node}) {src} dec 20 1 1e10", "setplot noise1",
        f"wrdata work/{name}.txt onoise_spectrum inoise_spectrum", "quit", ".endc", ".end"]
    open(f"work/{name}.spice", "w").write("\n".join(net) + "\n")
    p = subprocess.run(["ngspice", "-b", f"work/{name}.spice"], capture_output=True, text=True)
    d = np.loadtxt(f"work/{name}.txt")
    return d[:, 0], d[:, 1], d[:, 3]          # frequency, output density, input density (V/sqrt(Hz))

def reduce(f, on, inn):
    gain = on / inn                                        # |transfer| from the source to the output
    a0 = float(np.median(gain[(f > 1e3) & (f < 1e4)]))
    out_ms = np.trapezoid(on ** 2, f)                      # total output noise power
    white_density = float(inn[np.argmin(abs(f - 1e6))])    # flat region, V/sqrt(Hz)
    k = float(inn[np.argmin(abs(f - 10))] ** 2 * 10)       # flicker: S = k / f near 10 Hz
    m = f >= FLO
    out_flicker_ms = np.trapezoid(np.minimum(on[m] ** 2, (k / f[m]) * gain[m] ** 2), f[m])
    total_in = math.sqrt(out_ms) / a0
    flicker_in = math.sqrt(out_flicker_ms) / a0
    white_in = math.sqrt(max(total_in ** 2 - flicker_in ** 2, 0.0))
    return dict(dc_gain=a0, white_density_nV=white_density * 1e9, total_input_uV=total_in * 1e6,
                white_input_uV=white_in * 1e6, flicker_input_uV=flicker_in * 1e6)

def comparator(wc, lc, vcmi):
    body = ["vdd vdd 0 1.8", "ib ib 0 10u", f"vp inp 0 dc {vcmi} ac 1", f"vn inn 0 {vcmi}",
            f"xc inp inn out ib vdd 0 comp wc={wc} lc={lc}"]
    return reduce(*run(f"nz_cmp_{wc}_{lc}", body, "xc.o1", "vp"))

def opamp():
    body = ["vdd vdd 0 1.8", "ib ib 0 10u", "vp inp 0 dc 0.4 ac 1", "xo inp sum out ib vdd 0 opamp",
            "cf sum out 30p", "rf sum out 1e9", "cin sum 0 400f"]
    return reduce(*run("nz_opamp", body, "out", "vp"))

win = comparator(4, 1, 0.55)        # window comparator of each port
main = comparator(16, 4, 0.8)       # FIRE comparator
op = opamp()
i_peak = 300e-9                     # mirror output current near the peak of a pulse
mirror = math.sqrt(4 * Q * i_peak / (2 * TNZ))     # both devices of the mirror, band 1/(2 TNZ)
out = dict(sample_time_s=TNZ, flicker_low_frequency_Hz=FLO, window_comparator=win, fire_comparator=main,
           integrator_opamp=op, mirror_shot_rms_nA=mirror * 1e9,
           params=dict(tnz=TNZ, vncw=win["white_input_uV"] * 1e-6, vncf=win["flicker_input_uV"] * 1e-6,
                       vnmw=main["white_input_uV"] * 1e-6, vnmf=main["flicker_input_uV"] * 1e-6,
                       vnow=op["white_input_uV"] * 1e-6, vnof=op["flicker_input_uV"] * 1e-6, inmw=mirror))
json.dump(out, open("noise.json", "w"), indent=1)
for k in ("window_comparator", "fire_comparator", "integrator_opamp"):
    print(k, {a: round(b, 3) for a, b in out[k].items()})
print("mirror shot rms nA", round(mirror * 1e9, 3))
