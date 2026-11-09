#!/usr/bin/env python3
"""Paired checks of exact counts on the constructed finite-chain execution.

No check supplies a section cover as a premise. The positive statements use
physical protocol witnesses to construct covers; mutations change the counts
or erase each cell's own birth memory. A rejected proof mutation is an interface
regression check, not by itself a proof of the negated mathematical statement.
"""
from pathlib import Path
import subprocess
import tempfile

from scripts.lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[2]
MODULE = 'KernelR.HybridFiniteChainDoseCounting'
PREFIX = f'import {MODULE}\nopen KernelR.Hybrid\n'
HEADER = '''example {{n θ bornCells K sigma centre delay T ε}}
    (c : @ConstructedBirthCadenceChain n θ bornCells K sigma centre delay T)
    (hb : PhysicalBox θ ε) (i : Fin (n + 1)) :
'''


def main():
    counts = HEADER + '''    ∃ (errors : ∀ j p, ErrorSectionCover j p c.execution)
      (marks : ∀ j p, MarkSectionCover j p c.execution),
      (∀ j, (errors j (cadenceActivePort n j)).count = {errors}) ∧
        ∀ j, (∑ p : Port, (marks j p).count) = {marks} := by
  exact c.exact_section_counts hb
'''
    chosen_error = HEADER + '''    (Classical.choice ((c.sectionCovered hb).1 i
      (cadenceActivePort n i))).count = {count} := by
  obtain ⟨errors, marks, errors_count, marks_count⟩ := c.exact_section_counts hb
  exact ((Classical.choice ((c.sectionCovered hb).1 i
    (cadenceActivePort n i))).count_unique (errors i (cadenceActivePort n i))).trans
      (errors_count i)
'''
    chosen_marks = HEADER + '''    (∑ p : Port,
      (Classical.choice ((c.sectionCovered hb).2 i p)).count) = {count} := by
  classical
  obtain ⟨errors, marks, errors_count, marks_count⟩ := c.exact_section_counts hb
  have same : (∑ p : Port,
      (Classical.choice ((c.sectionCovered hb).2 i p)).count) =
      ∑ p : Port, (marks i p).count := by
    apply Finset.sum_congr rfl
    intro p _
    exact (Classical.choice ((c.sectionCovered hb).2 i p)).count_unique (marks i p)
  exact same.trans (marks_count i)
'''
    gain_offset = HEADER + '''    c.final.x i (.z (cadenceActivePort n i)) =
      {birth}(12 / 5 : ℝ) := by
  obtain ⟨errors, marks, errors_count, marks_count⟩ := c.exact_section_counts hb
  have memory := (c.execution.memory_of_section_covers errors marks).1 i
    (cadenceActivePort n i)
  rw [c.source_values, errors_count i] at memory
  norm_num at memory
  exact memory
'''
    recovery_offset = HEADER + '''    c.final.x i .b = {birth}(3 / 10 : ℝ) := by
  obtain ⟨errors, marks, errors_count, marks_count⟩ := c.exact_section_counts hb
  have memory := (c.execution.memory_of_section_covers errors marks).2 i
  rw [c.source_values, marks_count i] at memory
  norm_num at memory
  exact memory
'''
    cases = [
        ('the physical chain constructs four active ERROR sections',
         counts.format(errors='4', marks='3'), counts.format(errors='3', marks='3')),
        ('the physical chain constructs three MARK sections over all ports',
         counts.format(errors='4', marks='3'), counts.format(errors='4', marks='2')),
        ('any constructed actual ERROR cover has count four',
         chosen_error.format(count='4'), chosen_error.format(count='5')),
        ('alternative actual MARK covers retain total three',
         chosen_marks.format(count='3'), chosen_marks.format(count='4')),
        ('counted gain retains the active port birth value',
         gain_offset.format(birth='(bornCells i).x 0 (.z (cadenceActivePort n i)) + '),
         gain_offset.format(birth='')),
        ('counted recovery retains the cell birth value',
         recovery_offset.format(birth='(bornCells i).x 0 .b + '),
         recovery_offset.format(birth='')),
    ]
    with tempfile.TemporaryDirectory(prefix='hybrid-chain-section-counts-negative-', dir=ROOT) as tmp:
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
            print(f'{name}: physical conclusion accepted; altered claim rejected.', flush=True)
    print(f'All {len(cases)} paired finite-chain section-count controls passed.', flush=True)


if __name__ == '__main__':
    main()
