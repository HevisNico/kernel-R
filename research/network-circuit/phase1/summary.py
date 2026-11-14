"""Prints the tables of the README from CONSTANTS.json and PREDICTED.json. No number is computed here."""
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
C = json.loads((HERE / "CONSTANTS.json").read_text())["instances"]
P = json.loads((HERE / "PREDICTED.json").read_text())

print("| Instance | Port | Gap, mV | Dose, mV | Gap, doses | Need | Margin of the last silence, mV | Margin of the first FIRE, mV | Help at 16, mV | Help at 18 after a silence / a FIRE, mV | Noise of a read, mV | Protected until, units |")
print("|---|---|---|---|---|---|---|---|---|---|---|---|")
for seed, I in C.items():
    for name, p in I["ports"].items():
        h = "%+.3f / %+.3f" % (p["help_18_after_silent_mV"], p["help_18_after_fire_mV"]) if "help_18_after_fire_mV" in p else "-"
        print(f"| {seed} | `{name}` | {p['gap_mV']:.3f} | {p['dose_mV']:.4f} | {p['gap_doses']:.3f} | {p['need']} | {p['room_last_silence_mV']:.3f} | {p['room_first_fire_mV']:.3f} | "
              f"{p['help_16_mV']:+.3f} | {h} | {p.get('noise_sd_mV', float('nan')):.3f} | {p['protected_until_units']:.2f} |")
print()
print("| Instance | Port | Trains alone, 18 units: no noise | with noise |")
print("|---|---|---|---|")
for seed, I in C.items():
    for name, p in I["ports"].items():
        print(f"| {seed} | `{name}` | `{p.get('train_18_quiet', {}).get('word', '-')}` | `{p.get('train_18_noise', {}).get('word', '-')}` |")
print()
print(f"K = {P['k']}")
print("| Instance | Port | Budget, mV | Zero-error word | Least room, mV | Verdict | Writes | FIRE |")
print("|---|---|---|---|---|---|---|---|")
for seed, r in P["instances"].items():
    for name, p in r.get("ports", {}).items():
        word = p["zero_error_word"]
        short = f"{word.count('s')} s, {word.count('F')} F"
        print(f"| {seed} | `{name}` | {p['budget_mV'][0]:+.3f} to {p['budget_mV'][1]:+.3f} | {short} | {p['least_room_mV']:+.3f} | {p['verdict']} | "
              f"{' or '.join(map(str, p['writes']))} | {' to '.join(map(str, sorted({p['fires'][0], p['fires'][-1]})))} |")
print()
print("| Instance | All reads have room | Terminal states | FIRE of A | FIRE of B | Predicted ports at K = 2, 3, 4 |")
print("|---|---|---|---|---|---|")
for seed, r in P["instances"].items():
    by_k = [sum(v == "predicted" for v in P["verdicts_by_k"][seed][k].values()) for k in ("2.0", "3.0", "4.0")]
    learned = [sum(v != "no prediction" for v in P["verdicts_by_k"][seed][k].values()) for k in ("2.0", "3.0", "4.0")]
    print(f"| {seed} | {r['all_reads_have_room']} | {r['terminal_states']} | {r['fires_of_a']} | {r['fires_of_b']} | word: {by_k}; writes: {learned} |")
