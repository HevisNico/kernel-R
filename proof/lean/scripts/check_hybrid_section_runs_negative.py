#!/usr/bin/env python3
"""Check structural section-run contracts and reject altered interfaces.

Every mutation is paired with a valid Lean statement using the same script.
These controls exercise actual cover extraction, open-phase boundaries,
exposure, count composition, and structural transport. Rejection alone is
not a mathematical proof of the negation of the changed statement.
"""
from pathlib import Path
import subprocess
import tempfile

from lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[1]
PREFIX = '''import KernelR.HybridSectionRuns
import KernelR.HybridDoseCountingTransport
open KernelR.Hybrid
'''


def main():
    extract = '''example {{n θ route s u count}} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port)
    (run : SectionRun .{kind} i p e {start} {end} count) :
    ∃ cover : {cover}SectionCover i p e, cover.count = {count} := by
  exact {kind}_section_run_iff.mp run
'''
    reverse = '''example {{n θ route s u}} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (cover : ErrorSectionCover i p e) :
    SectionRun .error i p e false false ({count}) := by
  exact cover.sectionRun
'''
    append = '''example {{n θ route s v u k l}}
    (first : @Execution n θ route s v) (rest : Execution θ route v u)
    (kind : LearningSection) (i : Fin n) (p : Port)
    (left : SectionRun kind i p first false true k)
    (right : SectionRun kind i p rest true false l) :
    SectionRun kind i p (first.append rest) false false ({count}) := by
  exact left.append right
'''
    exposure = '''example {{n θ route s u}} (flow : @Flow n θ s u)
    (i : Fin n) (p : Port) (exposed : {exposure}) :
    SectionStep (route:=route) .{kind} i p (.flow flow) true true 0 := by
  exact .flow flow exposed
'''
    foreign = '''example {{n θ route s u active}} (jump : @Jump n route s u)
    (kind : LearningSection) (i : Fin n) (p : Port)
    (valid : kind.Valid i p active s) (same : u.aux i p = s.aux i p) :
    SectionStep (θ:=θ) kind i p (.jump jump) active active {count} := by
  exact SectionStep.same_aux_jump jump valid same
'''
    router = '''example {{n θ route route' s u}}
    (e : @Execution n θ route s u) (e' : Execution θ route' s u)
    (i : Fin n) (p : Port) (cover : ErrorSectionCover i p e)
    (copy : Execution.RouterCopy e e') :
    ∃ mapped : ErrorSectionCover i p e', mapped.count = {count} := by
  obtain ⟨mapped⟩ := cover.routerCopy_exists copy
  exact ⟨mapped, cover.routerCopy_count copy mapped⟩
'''
    ports = '''example {{n θ s u}}
    (e : @Execution n θ (fun _ _ => []) s u)
    (i : Fin n) (p : Port) (cover : MarkSectionCover i p e)
    (σ : Equiv.Perm Port) :
    ∃ mapped : MarkSectionCover i (σ.symm p) (e.permutePorts σ),
      mapped.count = {count} := by
  obtain ⟨mapped⟩ := cover.permutePorts_exists σ
  exact ⟨mapped, cover.permutePorts_count σ mapped⟩
'''
    base = dict(kind='error', cover='Error', start='false', end='false', count='count')
    cases = [
        ('closed ERROR run extracts its actual count',
         extract.format(**base), extract.format(**(base | {'count': 'count + 1'}))),
        ('closed MARK run extracts its actual count',
         extract.format(**(base | {'kind': 'mark', 'cover': 'Mark'})),
         extract.format(**(base | {'kind': 'mark', 'cover': 'Mark', 'count': 'count + 1'}))),
        ('initially open section cannot be silently counted as complete',
         extract.format(**base), extract.format(**(base | {'start': 'true'}))),
        ('unfinished terminal section cannot be silently closed',
         extract.format(**base), extract.format(**(base | {'end': 'true'}))),
        ('actual cover enters the automaton without inventing a count',
         reverse.format(count='cover.count'), reverse.format(count='cover.count + 1')),
        ('open-boundary composition retains the sum of counts',
         append.format(count='k + l'), append.format(count='k + l + 1')),
        ('open ERROR flow requires all exposure gates',
         exposure.format(kind='error', exposure='ErrorOpen flow i p'),
         exposure.format(kind='error', exposure='s.aux i p = .error')),
        ('open MARK flow requires protection and headroom',
         exposure.format(kind='mark', exposure='MarkOpen flow i p'),
         exposure.format(kind='mark', exposure='s.aux i p = .mark')),
        ('foreign jump preserves an open phase with zero new sections',
         foreign.format(count='0'), foreign.format(count='1')),
        ('exact router copy constructs a cover and retains its count',
         router.format(count='cover.count'), router.format(count='cover.count + 1')),
        ('actual port relabeling retains complete MARK counts',
         ports.format(count='cover.count'), ports.format(count='cover.count + 1')),
    ]
    with tempfile.TemporaryDirectory(prefix='hybrid-section-runs-negative-', dir=ROOT) as tmp:
        path = Path(tmp) / 'Check.lean'
        section_artifact = ROOT / '.lake/build/lib/lean/KernelR/HybridSectionRuns.olean'
        command = lean_check_command(tmp, root_module='KernelR.HybridDoseCountingTransport',
                                     extra_artifacts={
                                         'KernelR.HybridSectionRuns': [[str(section_artifact)]]})
        for name, good, bad in cases:
            for expected, source in [(True, good), (False, bad)]:
                path.write_text(PREFIX + source)
                result = subprocess.run([*command, str(path)], cwd=ROOT, text=True,
                                        stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                        timeout=120)
                if (result.returncode == 0) != expected:
                    raise SystemExit(f'{name}: unexpected result:\n{result.stdout}')
                if not expected and 'error:' not in result.stdout:
                    raise SystemExit(f'{name}: failed without a Lean diagnostic:\n{result.stdout}')
            print(f'{name}: physical conclusion accepted; altered claim rejected.', flush=True)
    print(f'All {len(cases)} paired section-run controls passed.', flush=True)


if __name__ == '__main__':
    main()
