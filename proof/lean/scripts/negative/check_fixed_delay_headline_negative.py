#!/usr/bin/env python3
"""Check the fixed-delay headline and the canonical finite-chain protocol.

Every altered contract has a valid control with identical premises. The full
headline controls preserve the supplied delay in both semantic witnesses and
both universal conclusions. Router controls check destinations, guards, delay
indices and root behavior. Rejection checks proof interfaces; it is not by
itself a mathematical proof that every altered proposition is false.
"""
from pathlib import Path
import subprocess
import tempfile

from scripts.lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[2]
MODULE = 'KernelR.FixedDelayChainHeadline'
PREFIX = f'import {MODULE}\nopen KernelR.Hybrid\n'


def main():
    headline = '''example {{n θ bornCells K ε}}
    (hborn : ∀ i : Fin (n + 1), BirthState (bornCells i))
    (hb : @PhysicalBox (n + 1) θ ε) (ha : ∀ i q, (bornCells i).aux 0 q = .ready)
    (hqueue : ∀ i, (bornCells i).pending = sourceTrain 0 (finiteChainPreparationPort n i) 0 8 16)
    (sigma centre : ℕ → ℝ) (delay otherDelay : ℕ → ℝ → ℝ)
    (hK : 4 * (n + 1) + 12 ≤ K) (hsigma : ∀ j, 0 ≤ sigma j)
    (hbudget : KernelR.Chain.pathJitter sigma n ≤ 3 / 20)
    (hcentre : ∀ j, j < n → (3 / 10 : ℝ) + sigma j ≤ centre j ∧ centre j ≤ 2 / 5 - sigma j)
    (herror : ∀ j, j < n → ∀ time,
      -sigma j ≤ delay j time - centre j ∧ delay j time - centre j ≤ sigma j) :
    ∃ terminal : Snapshot (n + 1),
      ∃ native : Execution θ (canonicalFiniteChainRouter n {witness_delay} (cadenceChainTerminal n K))
          (familyPreparationBornSource bornCells K) terminal,
      ∃ geometric : CrossingExecution θ (canonicalFiniteChainRouter n {witness_delay} (cadenceChainTerminal n K))
          (familyPreparationBornSource bornCells K) terminal,
        CompleteThrough native (cadenceChainTerminal n K) ∧
        CrossingCompleteThrough geometric (cadenceChainTerminal n K) ∧
        native.toWeak = geometric.execution ∧
        (∀ u (candidate : Execution θ
            (canonicalFiniteChainRouter n {universal_delay} (cadenceChainTerminal n K))
            (familyPreparationBornSource bornCells K) u),
          CompleteThrough candidate (cadenceChainTerminal n K) →
          terminal.ObservationalEq u ∧
            (∀ i, candidate.emissionTimes i = native.emissionTimes i) ∧
            UniversalCadenceOutcome θ bornCells K (cadenceChainTerminal n K) u
              candidate.emissionTimes candidate.ledger.emissions.length) ∧
        (∀ u (candidate : CrossingExecution θ
            (canonicalFiniteChainRouter n {universal_delay} (cadenceChainTerminal n K))
            (familyPreparationBornSource bornCells K) u),
          CrossingCompleteThrough candidate (cadenceChainTerminal n K) →
          terminal.ObservationalEq u ∧
            (∀ i, candidate.execution.emissionTimes i = native.emissionTimes i) ∧
            UniversalCadenceOutcome θ bornCells K (cadenceChainTerminal n K) u
              candidate.execution.emissionTimes candidate.execution.ledger.emissions.length) := by
  exact FixedDelayChainHeadline.every_finite_chain_fixed_delay
    hborn hb ha hqueue sigma centre delay hK hsigma hbudget hcentre herror
'''
    parent = '''example (n : ℕ) (delay : ℕ → ℝ → ℝ)
    (T time : ℝ) (i : Fin (n + 1)) :
    canonicalFiniteChainRouter (n + 1) delay T i.succ time =
      if {window} then
        [⟨i.castSucc, {port}, time + delay ({index}) time⟩] else [] := by
  exact canonicalFiniteChainRouter_parent n delay T time i
'''
    root = '''example (n : ℕ) (delay : ℕ → ℝ → ℝ) (T time : ℝ) :
    canonicalFiniteChainRouter n delay T 0 time = {tokens} := by
  exact canonicalFiniteChainRouter_root n delay T time
'''
    correct_headline = dict(witness_delay='delay', universal_delay='delay')
    correct_parent = dict(window='160 ≤ time ∧ time < T + 1', port='2', index='n - i.val')
    cases = [
        ('native and geometric witnesses retain the supplied delay',
         headline.format(**correct_headline),
         headline.format(**(correct_headline | {'witness_delay': 'otherDelay'}))),
        ('native and geometric universality retain the same canonical router',
         headline.format(**correct_headline),
         headline.format(**(correct_headline | {'universal_delay': 'otherDelay'}))),
        ('each non-root FIRE targets parent port two',
         parent.format(**correct_parent),
         parent.format(**(correct_parent | {'port': '1'}))),
        ('contact window includes 160 and excludes T plus one',
         parent.format(**correct_parent),
         parent.format(**(correct_parent | {'window': '160 < time ∧ time ≤ T + 1'}))),
        ('delivery date uses the correct leaf-indexed link delay',
         parent.format(**correct_parent),
         parent.format(**(correct_parent | {'index': 'n + 1 - i.val'}))),
        ('the root issues no routed token',
         root.format(tokens='[]'), root.format(tokens='[⟨0, 2, time⟩]')),
    ]
    with tempfile.TemporaryDirectory(prefix='fixed-delay-headline-negative-', dir=ROOT) as tmp:
        path = Path(tmp) / 'Check.lean'
        command = lean_check_command(tmp, root_module=MODULE)
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
            print(f'{name}: fixed protocol accepted; altered contract rejected.', flush=True)
    print(f'All {len(cases)} paired fixed-delay headline controls passed.', flush=True)


if __name__ == '__main__':
    main()
