#!/usr/bin/env python3
"""Paired semantic controls for the zero-recovery execution contracts.

Each public theorem has a positive control accepted before a deliberately
altered conclusion is rejected. This is a proof-regression check, not a claim
that every rejected statement has been proved false. Actual locked executions
are independently constructed by zeroRecoveryIdle_complete.
"""
import argparse
import json
from pathlib import Path
import re
import subprocess
import tempfile
from lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[1]
MODULE = 'KernelR.HybridZeroRecoveryCrossing'
PREFIX = f'import {MODULE}\nopen KernelR.Hybrid Set MeasureTheory\nset_option maxErrors 0\n'

def controls():
    sources = [(ROOT/f'KernelR/{name}.lean').read_text() for name in
               ['HybridZeroRecovery','HybridZeroRecoveryCrossing']]
    mutations = [
        ('Flow.slow_charge_constant_of_zero_recovery',
         'f.path t i .q = s.x i .q', 'f.path t i .q = s.x i .q + 1 / 10'),
        ('Execution.slow_forever_of_zero_recovery',
         'e.AllStates (fun v => v.main i = .slow)', 'e.AllStates (fun v => v.main i = .ready)'),
        ('Execution.zero_recovery_locked_states',
         'v.x i .q = 1 / 4 ∧ v.x i .b = 0', 'v.x i .q = 1 / 10 ∧ v.x i .b = 0'),
        ('Execution.zero_recovery_locked_paths',
         'f.path t i .q = 1 / 4 ∧ f.path t i .b = 0',
         'f.path t i .q = 1 / 10 ∧ f.path t i .b = 0'),
        ('Execution.no_firing_of_zero_recovery',
         'e.emissionTimes i = []', 'e.emissionTimes i = [s.time]'),
        ('Execution.no_mark_of_quiet_sensors',
         'e.NoMarkFlows i', 'e.MainFlows i .ready'),
        ('Execution.zero_recovery_quiet_lock',
         'v.main i = .slow ∧ v.x i .q = 1 / 4', 'v.main i = .ready ∧ v.x i .q = 1 / 4'),
        ('Execution.zero_recovery_repaired_by_mark',
         'u.x i .b = 1 / 10', 'u.x i .b = 1 / 5'),
        ('zeroRecoveryIdle_field',
         ' t i c = 0', ' t i c = 1'),
        ('zeroRecoveryIdle_no_jump',
         'IsEmpty (Jump', 'Nonempty (Jump'),
        ('zeroRecoveryIdle_complete',
         'e.emissionTimes i = []', 'e.emissionTimes i = [start]'),
        ('zeroRecoveryIdle_physical',
         ': PhysicalInvariant θ (zeroRecoveryIdle n time)',
         ': ¬ PhysicalInvariant θ (zeroRecoveryIdle n time)'),
        ('zeroRecoveryIdle_physical_of_box',
         '    PhysicalInvariant θ (zeroRecoveryIdle n time)',
         '    ¬ PhysicalInvariant θ (zeroRecoveryIdle n time)'),
        ('WeakFlow.recovery_without_mark',
         'f.path t i .b = s.x i .b', 'f.path t i .b = s.x i .b + 1 / 10'),
        ('WeakFlow.zero_recovery_locked_paths',
         'f.path t i .q = 1 / 4 ∧ f.path t i .b = 0',
         'f.path t i .q = 1 / 10 ∧ f.path t i .b = 0'),
        ('Jump.slow_stays_at_quarter',
         '    u.main i = .slow', '    u.main i = .ready'),
        ('WeakExecution.zero_recovery_lock',
         'e.emissionTimes i = []', 'e.emissionTimes i = [s.time]'),
        ('CrossingExecution.zero_recovery_lock',
         'e.execution.emissionTimes i = []', 'e.execution.emissionTimes i = [s.time]'),
        ('zeroRecoveryIdle_crossing_complete',
         'e.execution.emissionTimes i = []', 'e.execution.emissionTimes i = [start]'),
    ]
    cases = []
    for name, before, after in mutations:
        source = next(text for text in sources if re.search(r'^theorem '+re.escape(name)+r'\b',text,re.M))
        start = source.index('theorem '+name) + len('theorem '+name)
        end = source.index(':=', start)
        signature = source[start:end]
        good = 'example'+signature+' := by\n  apply KernelR.Hybrid.'+name+' <;> assumption\n'
        assert before in good, (name,before)
        bad = good.replace(before,after,1)
        assert good != bad
        cases.append(dict(name=name,good=good,bad=bad))
    expected = set(re.findall(r'^theorem\s+([\w.]+)','\n'.join(sources),re.M))
    assert {c['name'] for c in cases} == expected
    base = next(c['good'] for c in cases if c['name']=='Execution.no_firing_of_zero_recovery')
    removed = base.replace('    (hmark : e.NoMarkFlows i)', '')
    assert removed != base
    cases.append(dict(name='no-firing requires absent protected MARK',good=base,bad=removed))
    return cases

def run(cases,timeout):
    with tempfile.TemporaryDirectory(prefix='zero-recovery-control-',dir=ROOT) as temp:
        target = Path(temp)/'Check.lean'
        cmd = lean_check_command(temp,root_module=MODULE)
        for variant in ['good','bad']:
            source = PREFIX
            blocks = []
            for case in cases:
                first = source.count('\n')+1
                source += case[variant].rstrip()+'\n\n'
                blocks.append((first,source.count('\n'),case['name']))
            target.write_text(source)
            result = subprocess.run([*cmd,str(target)],cwd=ROOT,text=True,
                                    stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=timeout)
            if variant=='good':
                if result.returncode:
                    raise SystemExit('Original contracts failed:\n'+result.stdout)
                print(f'Accepted all {len(cases)} positive controls.',flush=True)
                continue
            if result.returncode==0:
                raise SystemExit('Altered contracts unexpectedly accepted.')
            if re.search(r'unknown (constant|identifier|tactic)|unexpected token|invalid syntax|'
                         r'invalid (field|dotted identifier)|failed to infer|'
                         r"don't know how to synthesize implicit|failed to synthesize|"
                         r'object file .* does not exist|unknown module prefix',result.stdout,re.I):
                raise SystemExit('Nonsemantic rejection:\n'+result.stdout)
            rejected = set()
            for error in re.finditer(r'^.*?:(\d+):(\d+): error(?:\([^\n]*\))?:',result.stdout,re.M):
                line = int(error.group(1))
                owners = [name for first,last,name in blocks if first<=line<=last]
                if len(owners)!=1:
                    raise SystemExit('Error outside altered contract:\n'+result.stdout)
                rejected.add(owners[0])
            missing = {c['name'] for c in cases}-rejected
            if missing:
                raise SystemExit('Missing individual rejection: '+', '.join(sorted(missing))+'\n'+result.stdout)
            for c in cases:
                print(c['name']+': original accepted; own mutation rejected.',flush=True)
    return [dict(contract=c['name'],positive='accepted',mutation='rejected') for c in cases]

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--timeout',type=int,default=240)
    parser.add_argument('--report',type=Path)
    parser.add_argument('--inventory',action='store_true')
    args = parser.parse_args()
    cases = controls()
    if args.inventory:
        print(json.dumps([c['name'] for c in cases],indent=2));return
    report = run(cases,args.timeout)
    if args.report:args.report.write_text(json.dumps(report,indent=2)+'\n')
    print(f'All {len(cases)} paired zero-recovery controls passed.',flush=True)

if __name__=='__main__':
    main()
