"""Compile direct semantic mutations of the conditional deterministic contract."""
from pathlib import Path
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
SOURCE = (HERE/'Model.lean').read_text()
MUTATIONS = [
    ('remove_dose_headroom_during_preparation',
     '(room : report+b.epsilon+b.Dmax ≤ capacity b)',
     '(room : report+b.epsilon ≤ capacity b)'),
    ('discard_observed_loss_refusal',
     'if b.H < lossReport-lossError then .refuse else choose b lo hi',
     'if b.H < lossReport-lossError then .wait else choose b lo hi'),
    ('omit_max_dose_from_maintenance_guard',
     'if hi+b.Dmax ≤ capacity b then .maintenance',
     'if hi ≤ capacity b then .maintenance'),
    ('use_minimum_dose_for_overflow_guard',
     'if hi+b.Dmax ≤ capacity b then .maintenance',
     'if hi+b.Dmin ≤ capacity b then .maintenance'),
    ('optimistic_carry_uses_maximum_dose',
     '| .maintenance => lo-b.H+b.Dmin',
     '| .maintenance => lo-b.H+b.Dmax'),
    ('ignore_the_smaller_semantic_capacity',
     'min b.linearCapacity b.semanticCapacity',
     'max b.linearCapacity b.semanticCapacity'),
    ('double_loss_without_changing_service_guard',
     'def preService (reserve loss : Int) : Int := reserve-loss',
     'def preService (reserve loss : Int) : Int := reserve-2*loss'),
    ('omit_charged_preparation_from_actual_run',
     '  preparationCost cm co entry.preparation + maintenanceCount b w entry.state n*cm + (n+1)*co+n*cs',
     '  maintenanceCount b w entry.state n*cm + (n+1)*co+n*cs'),
    ('count_training_silence_inside_service',
     'r.phase == .guaranteedService && !r.fired', '!r.fired'),
]


def compile_source(path):
    return subprocess.run(['lean',str(path)],cwd=HERE,capture_output=True,text=True,timeout=90)


def main():
    baseline = compile_source(HERE/'Model.lean')
    if baseline.returncode:
        raise RuntimeError('Positive contract does not compile:\n'+baseline.stdout+baseline.stderr)
    for name, old, new in MUTATIONS:
        if SOURCE.count(old) != 1:
            raise RuntimeError('Mutation anchor must occur exactly once: '+name)
        with tempfile.TemporaryDirectory(prefix='contract-mutation-',dir=HERE) as tmp:
            path=Path(tmp)/'Mutated.lean'
            path.write_text(SOURCE.replace(old,new))
            result=compile_source(path)
            output=result.stdout+result.stderr
            if result.returncode==0 or 'error:' not in output or not any(word in output for word in ('omega','Tactic','unsolved goals','Type mismatch','type mismatch')):
                raise RuntimeError('Mutation did not fail a proof as required: '+name+'\n'+output)
        print('PASS: rejected '+name)
    print(f'PASS: positive contract and {len(MUTATIONS)} direct semantic mutations')


if __name__=='__main__':
    main()
