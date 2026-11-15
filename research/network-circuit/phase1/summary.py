"""Prints the tables of the README from CONSTANTS.json and PREDICTED.json. No number is computed here."""
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
C = json.loads((HERE / "CONSTANTS.json").read_text())["instances"]
P = json.loads((HERE / "PREDICTED.json").read_text())

print("| Instance | Port | Gap, mV | Dose, mV | Gap, doses | Need | Margin of the last silence, mV | Margin of the first FIRE, mV | Help at 16, mV | Help at 18 after a silence / a FIRE, mV | Noise within a run, mV | Run offsets, mV | Protected until, units |")
print("|---|---|---|---|---|---|---|---|---|---|---|---|---|")
for seed, I in C.items():
    for name, p in I["ports"].items():
        h = "%+.3f / %+.3f" % (p["help_18_after_silent_mV"], p["help_18_after_fire_mV"])
        offsets = ", ".join("%+.2f" % x for x in p["noise_run_offsets_mV"])
        print(f"| {seed} | `{name}` | {p['gap_mV']:.3f} | {p['dose_mV']:.4f} | {p['gap_doses']:.3f} | {p['need']} | {p['room_last_silence_mV']:.3f} | {p['room_first_fire_mV']:.3f} | "
              f"{p['help_16_mV']:+.3f} | {h} | {p['noise_within_run_mV']:.3f} | {offsets} | {p['protected_until_units']:.2f} |")
print()
print("| Instance | Noise between runs, mV | Run offsets counted | Dose noise, mV |")
print("|---|---|---|---|")
for seed, I in C.items():
    print(f"| {seed} | {I['noise_between_runs_mV']:.3f} | {I['run_offsets']} of {4 * I['noisy_trains']} | {I['dose_noise_sd_mV']:.4f} |")
print()
print("| Instance | Port | Word without noise, 18 units | Noisy trains with another word |")
print("|---|---|---|---|")
for seed, I in C.items():
    for name, p in I["ports"].items():
        other = ", ".join(f"`{x['word']}`" for x in p["noisy_trains"] if not x["same_word_as_without_noise"]) or "none"
        print(f"| {seed} | `{name}` | `{p['train_18_quiet']['word']}` | {other} of {len(p['noisy_trains'])} |")
print()
for title, key in ((f"With noise, K = {P['k']:g}", "instances"), ("Without noise", "instances_without_noise")):
    print(title)
    print("| Instance | Port | Budget, mV | Zero-error word | Least room, mV | Verdict | Writes | FIRE |")
    print("|---|---|---|---|---|---|---|---|")
    for seed, r in P[key].items():
        for name, p in r.get("ports", {}).items():
            word = p["zero_error_word"]
            short = f"{word.count('s')} s, {word.count('F')} F"
            print(f"| {seed} | `{name}` | {p['budget_mV'][0]:+.3f} to {p['budget_mV'][1]:+.3f} | {short} | {p['least_room_mV']:+.3f} | {p['verdict']} | "
                  f"{' or '.join(map(str, p['writes']))} | {' to '.join(map(str, sorted({p['fires'][0], p['fires'][-1]})))} |")
    print()
print("| Instance | Ports with a known word, without noise and at K = 2, 3, 4 | Every read has room |")
print("|---|---|---|")
for seed in P["instances"]:
    ks = ("0.0", "2.0", "3.0", "4.0")
    by_k = [sum(v == "predicted" for v in P["verdicts_by_k"][seed][k].values()) for k in ks]
    full = ["yes" if n == 4 else "no" for n in by_k]
    print(f"| {seed} | {by_k} | {full} |")
