#!/usr/bin/env python3
"""Reject altered actual source chronology, warmup and first-phase conclusions."""
from pathlib import Path
import subprocess
import tempfile

from scripts.lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[2]
PREFIX = '''import KernelR.HybridBirthSourceTrain
open KernelR.Hybrid
'''


def cases():
    length = """example {{n}} (i : Fin n) (p : Port) : (sourceTrain i p 0 8 16).length = {value} := by
  norm_num [sourceTrain]
"""
    date = """example {{n θ route s u d ds}} {{e : @Execution n θ route s u}}
    (cut : DeliveryStep e d ds) : cut.afterArrival.time = d.due + {value} := by
  have h := cut.date.2
  linarith
"""
    raw = """example {{n θ route s u d ds}} {{e : @Execution n θ route s u}}
    (cut : DeliveryStep e d ds) : cut.afterArrival.raw d.cell d.port = {value} := by
  exact cut.raw_after
"""
    prefix = """example {{n θ route s u d ds}} {{e : @Execution n θ route s u}}
    (cut : DeliveryStep e d ds) (i : Fin n) (p : Port) : NoArrivalAt cut.{value} i p := by
  exact cut.no_arrivals_before i p
"""
    count = """example {{n θ route s u i count}} {{e : @Execution n θ route s u}}
    (train : PreparedTrain e i count) : (e.emissionTimes i).length = count + {value} := by
  have h := train.emissions
  omega
"""
    train_mark = """example {{n θ route s u i count}} {{e : @Execution n θ route s u}}
    (train : PreparedTrain e i count) (p : Port) : e.ledger.mark i p = {value} := by
  have h := train.mark_zero p
  linarith
"""
    warm_error = """example {{n θ route s u i p weak future}} {{e : @Execution n θ route s u}}
    (warm : Warmup e i p weak future) : warm.head.ledger.error i p = (3/5) * weak + {value} := by
  have h := warm.error_target
  linarith
"""
    warm_emit = """example {{n θ route s u i p weak future}} {{e : @Execution n θ route s u}}
    (warm : Warmup e i p weak future) : warm.head.emissionTimes i = {value} := by
  exact warm.emissions
"""
    birth_b = """example {{n θ route born u i p count}} {{e : @Execution n θ route born u}}
    (birth : BirthInput e i p count) : {value} ≤ birth.cut.afterArrival.x i .b := by
  have h := birth.recovery.1
  linarith
"""
    birth_date = """example {{n θ route born u i p count}} {{e : @Execution n θ route born u}}
    (birth : BirthInput e i p count) : birth.cut.afterArrival.time = {value} := by
  have h := birth.date
  linarith
"""
    first_count = """example {{n θ route born u i p}} {{e : @Execution n θ route born u}}
    (train : BirthSourceTrain e i p) : (e.emissionTimes i).length = {value} := by
  have h := train.emissions
  omega
"""
    first_error = """example {{n θ route born u i p}} {{e : @Execution n θ route born u}}
    (train : BirthSourceTrain e i p) : e.ledger.error i p = {value} := by
  have h := train.error_target
  linarith
"""
    first_mark = """example {{n θ route born u i p}} {{e : @Execution n θ route born u}}
    (train : BirthSourceTrain e i p) : e.ledger.mark i p = {value} := by
  have h := train.mark_target
  linarith
"""
    first_mode = """example {{n θ route born u i p}} {{e : @Execution n θ route born u}}
    (train : BirthSourceTrain e i p) : u.main i = .{value} := by
  exact train.prepared.ready
"""
    first_gain = """example {{n θ route born u i p}} {{e : @Execution n θ route born u}}
    (train : BirthSourceTrain e i p) (q : Port) (hq : q ≠ p) : u.x i (.z q) = born.x i (.z q) + {value} := by
  have h := train.gain_other q hq
  linarith
"""
    return [
        ('all sixteen source tokens are retained', length.format(value='16'), length.format(value='15')),
        ('delivery occurs at its due date', date.format(value='0'), date.format(value='1')),
        ('delivery starts a fresh raw pulse', raw.format(value='some cut.afterArrival.time'), raw.format(value='none')),
        ('the prefix before delivery is isolated', prefix.format(value='span'), prefix.format(value='rest')),
        ('prepared source inputs emit once each', count.format(value='0'), count.format(value='1')),
        ('prepared source inputs have no MARK dose', train_mark.format(value='0'), train_mark.format(value='1/10')),
        ('warmup ERROR counts are derived', warm_error.format(value='0'), warm_error.format(value='3/5')),
        ('warmup emits nothing', warm_emit.format(value='[]'), warm_emit.format(value='[s.time]')),
        ('first delivery retains birth recovery', birth_b.format(value='7999/100000'), birth_b.format(value='17999/100000')),
        ('first source is delivered at zero', birth_date.format(value='0'), birth_date.format(value='1')),
        ('first source phase emits twelve times', first_count.format(value='12'), first_count.format(value='13')),
        ('first source phase has three ERROR doses', first_error.format(value='9/5'), first_error.format(value='12/5')),
        ('first source phase has one MARK dose', first_mark.format(value='1/10'), first_mark.format(value='1/5')),
        ('first source phase restores READY', first_mode.format(value='ready'), first_mode.format(value='slow')),
        ('first source phase preserves other gains', first_gain.format(value='0'), first_gain.format(value='3/5')),
    ]


def main():
    controls = cases()
    with tempfile.TemporaryDirectory(prefix='hybrid-source-negative-', dir=ROOT) as tmp:
        path = Path(tmp) / 'Check.lean'
        command = lean_check_command(tmp)

        def check(source, expected, name):
            path.write_text(PREFIX + source)
            result = subprocess.run([*command, str(path)], cwd=ROOT, text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=180)
            if (result.returncode == 0) != expected:
                raise SystemExit(f'{name}: unexpected result:\n{result.stdout}')
            if not expected and 'error:' not in result.stdout:
                raise SystemExit(f'{name}: failed without a Lean diagnostic:\n{result.stdout}')

        check('\n'.join(good for _, good, _ in controls), True, 'valid source controls')
        for name, _, bad in controls:
            check(bad, False, name)
            print(f'{name}: physical conclusion accepted; altered claim rejected.', flush=True)


if __name__ == '__main__':
    main()
