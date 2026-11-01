#!/usr/bin/env python3
"""Guard actual protected return, reopening and the sixth source delivery."""
from pathlib import Path
import subprocess
import tempfile

from lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[1]
PREFIX = '''import KernelR.HybridBirthPrepared40
open KernelR.Hybrid
'''


def cases():
    contract = """example {{θ ε born}} (hs : @BirthState 1 born) (hb : PhysicalBox θ ε)
    (ha : ∀ p, born.aux 0 p = .ready)
    (hq : born.pending = sourceTrain 0 0 0 8 {count} ++ sourceTrain 0 0 160 8 16) :
    ∃ c : BirthPrepared40 θ born, CompleteThrough c.execution 40 := by
  obtain ⟨c⟩ := birth_protocol_prepared40_exists hs hb ha hq
  exact ⟨c,c.complete⟩
"""
    ctx = """example {{θ born}} (c : BirthPrepared40 θ born) """
    date = ctx + """: c.final.time = {value} := by exact c.date
"""
    complete = ctx + """: CompleteThrough c.execution {value} := by exact c.complete
"""
    main = ctx + """: c.final.main 0 = .{value} := by exact (c.ready 0).ready
"""
    aux = ctx + """(p : Port) : c.final.aux 0 p = .{value} := by exact ((c.ready 0).auxiliary p).1
"""
    q = ctx + """: c.final.x 0 .q = {value} := by exact c.charge
"""
    raw = ctx + """: c.final.raw 0 0 = some {value} := by exact c.raw_active
"""
    queue = ctx + """: c.final.pending = sourceTrain 0 0 48 8 {count} ++ sourceTrain 0 0 160 8 16 := by
  exact c.pending
"""
    deliveries = ctx + """: c.execution.deliveries = sourceTrain 0 0 0 8 {count} := by exact c.deliveries
"""
    outputs = ctx + """: c.execution.ledger.emissions = {value} := by exact c.emissions
"""
    error = ctx + """: c.execution.ledger.error 0 0 = {value} := by exact c.error_dose
"""
    mark = ctx + """: c.execution.ledger.mark 0 0 = {value} := by exact c.mark_dose
"""
    gain = ctx + """: c.final.x 0 (.z 0) = born.x 0 (.z 0)+{value} := by exact c.gain_target
"""
    recovery = ctx + """: c.final.x 0 .b = {value} := by exact c.recovery
"""
    suffix = ctx + """: c.suffix.deliveries = {value} := by exact c.deliveries_suffix
"""
    aux_return = """example {{θ route s p}} (c : ProtectedAuxReturn θ route s p) :
    c.final.main 0 = .{value} := by exact c.main_slow
"""
    aux_date = """example {{θ route s p}} (c : ProtectedAuxReturn θ route s p) :
    {value} < c.final.time := by linarith [c.time_bounds.1]
"""
    aux_gains = """example {{θ route s p}} (c : ProtectedAuxReturn θ route s p) :
    c.final.x 0 (.z 0) = s.x 0 (.z 0) {extra} := by exact c.gains 0 0
"""
    reopen = """example {{θ route s}} (c : SlowReopen θ route s) :
    c.final.x 0 .q = {value} := by exact c.charge
"""
    root = """example {{n}} (s : Snapshot n) (i : Fin n) :
    slowReopenDuration s i = {value} := by rfl
"""
    return [
        ('the factory starts from the full original birth queue', contract.format(count='16'), contract.format(count='15')),
        ('the actual sixth source arrives at forty', date.format(value='40'), date.format(value='32')),
        ('saturation is at the consumed source clock', complete.format(value='40'), complete.format(value='48')),
        ('the main has genuinely reopened by the next source', main.format(value='ready'), main.format(value='slow')),
        ('all auxiliary modes have genuinely returned READY', aux.format(value='ready'), aux.format(value='silent')),
        ('quiet waiting keeps the physical reopen charge', q.format(value='1/10'), q.format(value='1/4')),
        ('the fresh raw has source forty as origin', raw.format(value='40'), raw.format(value='32')),
        ('exactly twenty-six future sources remain', queue.format(count='10'), queue.format(count='11')),
        ('exactly six original sources were delivered', deliveries.format(count='6'), deliveries.format(count='5')),
        ('the protected return does not invent another output', outputs.format(value='[(0,c.mark.first.final.time)]'), outputs.format(value='[(0,40)]')),
        ('protected ERROR adds no extra learning', error.format(value='9/5'), error.format(value='12/5')),
        ('the full protected return retains the actual MARK dose', mark.format(value='1/10'), mark.format(value='0')),
        ('own gain is retained through the protected suffix', gain.format(value='9/5'), gain.format(value='12/5')),
        ('own perturbed recovery is retained', recovery.format(value='born.x 0 .b+1/10'), recovery.format(value='9/50')),
        ('the new suffix consumes only its actual source head', suffix.format(value='[⟨0,0,40⟩]'), suffix.format(value='[]')),
        ('the auxiliary return is still protected by SLOW', aux_return.format(value='slow'), aux_return.format(value='ready')),
        ('raw expiry precedes the actual auxiliary return', aux_date.format(value='33'), aux_date.format(value='34')),
        ('protected auxiliary ERROR does not change gain', aux_gains.format(extra=''), aux_gains.format(extra='+3/5')),
        ('the true reopen threshold is one tenth', reopen.format(value='1/10'), reopen.format(value='1/4')),
        ('the reopen clock uses the own current recovery', root.format(value='Real.log (s.x i .q/(1/10))/s.x i .b'), root.format(value='Real.log (s.x i .q/(1/10))/(9/50)')),
    ]


def main():
    controls = cases()
    with tempfile.TemporaryDirectory(prefix='hybrid-prepared40-negative-', dir=ROOT) as tmp:
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

        check('\n'.join(good for _, good, _ in controls), True, 'valid birth-to40 controls')
        for name, _, bad in controls:
            check(bad, False, name)
            print(f'{name}: physical conclusion accepted; altered claim rejected.', flush=True)


if __name__ == '__main__':
    main()
