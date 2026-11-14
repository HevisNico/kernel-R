"""Exercise the whole launch kit on an RC circuit, with a failed run and a simulated restart.

Uses the pinned ngspice 42 and the real environment check, but only a new local bare Git repository.
It never contacts GitHub and never runs the R cell or a registered scenario.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import launch

RUNNER = '''import argparse, hashlib, os, subprocess, time
from pathlib import Path
p = argparse.ArgumentParser()
p.add_argument('--out', type=Path); p.add_argument('--deck', type=Path); p.add_argument('--ngspice')
p.add_argument('--sleep', type=float, default=0); p.add_argument('--missing-output', action='store_true')
a = p.parse_args()
a.out.mkdir(exist_ok=False)
(a.out / 'environment.txt').write_text(os.environ.get('SPICE_SCRIPTS', '') + '\\n')
if a.sleep or a.missing_output:
    (a.out / 'partial.bin').write_bytes(b'partial-evidence\\x00unchanged\\n')
    time.sleep(a.sleep)
else:
    (a.out / 'input.spice').write_bytes(a.deck.read_bytes())
    r = subprocess.run([a.ngspice, '-b', 'input.spice'], cwd=a.out, capture_output=True)
    (a.out / 'simulator.stdout').write_bytes(r.stdout); (a.out / 'simulator.stderr').write_bytes(r.stderr)
    assert r.returncode == 0 and (a.out / 'trace.txt').exists()
    # this circuit has no noise: the file only exercises the path of the fingerprint
    (a.out / 'noise.sha256').write_text(hashlib.sha256(os.urandom(32)).hexdigest() + '\\n')
'''
DECK = '''* Synthetic RC circuit, unrelated to the R cell
v1 in 0 pulse(0 1 1u 1n 1n 4u 10u)
r1 in out 1k
c1 out 0 1n
.control
tran 100n 20u
set wr_singlescale
set numdgt=16
wrdata trace.txt v(out)
quit
.endc
.end
'''


def command(argv, cwd, expect=0, timeout=120):
    p = subprocess.run(argv, cwd=cwd, capture_output=True, text=True, timeout=timeout)
    if (p.returncode == 0) != (expect == 0):
        raise AssertionError(str(argv) + '\n' + p.stdout + '\n' + p.stderr)
    return p


def run(root, ngspice, pdk):
    root.mkdir(exist_ok=False)
    repo, remote = root / 'repo', root / 'remote.git'
    repo.mkdir()
    git = lambda *args: command(['git', *args], repo).stdout.strip()
    command(['git', 'init', '--bare', str(remote)], root)
    git('init', '-b', 'kit-test')
    git('config', 'user.name', 'Synthetic launch test')
    git('config', 'user.email', 'synthetic@example.invalid')
    git('remote', 'add', 'origin', str(remote))
    (repo / 'SYNTHETIC_PROTOCOL.txt').write_text('Synthetic RC launch test only. Not the R cell, not a registered scenario.\n')
    git('add', '.')
    git('commit', '-m', 'Synthetic protocol stub')
    protocol = git('rev-parse', 'HEAD')
    (repo / 'tools').mkdir()
    (repo / 'runtime').mkdir()
    shutil.copyfile(HERE / 'launch.py', repo / 'tools' / 'launch.py')
    (repo / 'runtime' / 'spinit').write_text('* synthetic start file\nset num_threads=1\n')
    (repo / 'rc.spice').write_text(DECK)
    (repo / 'runner.py').write_text(RUNNER)
    git('add', '.')
    git('commit', '-m', 'Synthetic implementation')
    source = git('rev-parse', 'HEAD')
    sources = {p: hashlib.sha256((repo / p).read_bytes()).hexdigest() for p in ('tools/launch.py', 'runner.py', 'rc.spice', 'runtime/spinit')}
    argv = ['{python}', '{repo}/runner.py', '--out', '{out}/evidence', '--deck', '{deck}', '--ngspice', '{ngspice}']

    def job(name, machine, scenario, extra=(), outputs=('evidence/trace.txt',), logs=('evidence/simulator.stdout', 'evidence/simulator.stderr'), timeout=20):
        record = dict(id=name, machine=machine, scenario=scenario, deck='rc.spice', runner='runner.py', argv=argv + list(extra), estimate_s=1, timeout_s=timeout,
                      required_outputs=list(outputs), diagnostic_logs=list(logs))
        if not extra:
            record.update(required_outputs=list(outputs) + ['evidence/noise.sha256'], noise_fingerprint='evidence/noise.sha256')
        return record
    runs = [job('a1', 'a', 'alpha'), job('a2', 'a', 'beta', ['--missing-output'], logs=()), job('a3', 'a', 'alpha'), job('a4', 'a', 'beta'),
            job('b1', 'b', 'alpha', ['--sleep', '25'], outputs=('evidence/partial.bin',), logs=(), timeout=40),
            job('b2', 'b', 'beta', ['--sleep', '25'], outputs=('evidence/partial.bin',), logs=(), timeout=40),
            job('b3', 'b', 'alpha'), job('b4', 'b', 'beta')]
    manifest = dict(kind='synthetic', campaign_id='synthetic-rc-kit-test', attempt=1, executor=launch.EXECUTOR, protocol_commit=protocol, source_commit=source,
                    protocol_path='SYNTHETIC_PROTOCOL.txt', protocol_sha256=hashlib.sha256((repo / 'SYNTHETIC_PROTOCOL.txt').read_bytes()).hexdigest(),
                    marker_path='RUN_ATTEMPT.json', launcher_path='tools/launch.py', spinit_path='runtime/spinit',
                    inventory_a_path='INVENTORY_a.json', inventory_b_path='INVENTORY_b.json', source_sha256=sources,
                    budget_s=400, jobs=2, scenario_order=['alpha', 'beta'], runs=runs)
    (repo / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    base = [sys.executable, '-B', str(repo / 'tools/launch.py')]
    env_args = ['--ngspice', str(ngspice), '--pdk', str(pdk)]
    common = ['--repo', str(repo), '--manifest', str(repo / 'manifest.json')] + env_args
    for machine in ('a', 'b'):
        command(base + ['inventory', '--machine', machine, '--out', str(repo / f'INVENTORY_{machine}.json')] + env_args, repo)
    git('add', '.')
    git('commit', '-m', 'Synthetic manifest and inventories')
    git('push', 'origin', 'kit-test')
    preflight = command(base + ['preflight'] + common, repo)
    command(base + ['prepare'] + common, repo)
    # a marker that exists only locally is not enough
    command(base + ['run-machine'] + common + ['--branch', 'kit-test', '--machine', 'a', '--out', str(root / 'unpublished')], repo, expect=1)
    assert not (root / 'unpublished').exists()
    git('add', 'RUN_ATTEMPT.json')
    git('commit', '-m', 'Publish synthetic attempt before launch')
    git('push', 'origin', 'kit-test')
    began = time.monotonic()
    # machine a: one run exits 0 without its output; it stays failed and the runs after it still run
    a = command(base + ['run-machine'] + common + ['--branch', 'kit-test', '--machine', 'a', '--out', str(root / 'machine-a')], repo)
    state_a = json.loads((root / 'machine-a' / 'STATE.json').read_text())
    status_a = {r['id']: r['status'] for r in state_a['records']}
    assert status_a == dict(a1='complete', a2='failed-never-rerun', a3='complete', a4='complete'), status_a
    assert state_a['status'] == 'ended-with-failed-or-lost-runs'
    spice_scripts = (root / 'machine-a/a1/evidence/environment.txt').read_text().strip()
    assert spice_scripts == str(repo / 'runtime'), spice_scripts
    # machine b: the launcher is killed while its two first runs are running, as a restart of the machine would do
    b = subprocess.Popen(base + ['run-machine'] + common + ['--branch', 'kit-test', '--machine', 'b', '--out', str(root / 'machine-b')],
                         cwd=repo, stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=True)
    deadline = time.monotonic() + 30
    while time.monotonic() < deadline:
        f = root / 'machine-b' / 'STATE.json'
        try:
            if f.exists() and len(json.loads(f.read_text())['records']) == 2:
                break
        except ValueError:
            pass
        time.sleep(0.2)
    else:
        raise AssertionError('machine b did not start its first two runs')
    for line in subprocess.run(['ps', '-eo', 'pid,args'], capture_output=True, text=True).stdout.splitlines():
        if str(root / 'machine-b') in line and 'runner.py' in line:
            os.kill(int(line.split()[0]), signal.SIGKILL)
    os.killpg(b.pid, signal.SIGKILL)
    b.wait()
    killed = json.loads((root / 'machine-b' / 'STATE.json').read_text())
    assert [r['status'] for r in killed['records']] == ['started', 'started']
    # a second launch is refused, in this output folder and in another one
    rejected = []
    for machine, where in (('a', 'relaunch-a'), ('b', 'relaunch-b'), ('b', 'machine-b')):
        q = command(base + ['run-machine'] + common + ['--branch', 'kit-test', '--machine', machine, '--out', str(root / where)], repo, expect=1)
        assert 'already claimed' in q.stderr or 'Output exists' in q.stderr
        rejected.append(where)
    # resume is refused while the machine has not restarted
    q = command(base + ['resume-machine'] + common + ['--branch', 'kit-test', '--machine', 'b', '--out', str(root / 'machine-b')], repo, expect=1)
    assert 'did not restart' in q.stderr
    before = {p.relative_to(root).as_posix(): p.read_bytes() for p in sorted((root / 'machine-b').rglob('*')) if p.is_file() and p.parent.name == 'evidence'}
    command(base + ['resume-machine', '--assume-restarted'] + common + ['--branch', 'kit-test', '--machine', 'b', '--out', str(root / 'machine-b')], repo)
    state_b = json.loads((root / 'machine-b' / 'STATE.json').read_text())
    status_b = {r['id']: r['status'] for r in state_b['records']}
    assert status_b == dict(b1='lost-started-before-restart-never-rerun', b2='lost-started-before-restart-never-rerun', b3='complete', b4='complete'), status_b
    assert [e['event'] for e in state_b['events']] == ['launch', 'resume-after-restart'] and sorted(state_b['events'][1]['lost']) == ['b1', 'b2']
    for name, data in before.items():                       # the evidence of the lost runs is untouched
        assert (root / name).read_bytes() == data
    published = []
    for machine in ('a', 'b'):
        target = root / ('published-' + machine)
        command(base + ['collect', '--out', str(root / ('machine-' + machine)), '--destination', str(target)], repo)
        inventory = json.loads((target / 'SURVIVORS.json').read_text())
        for f in inventory['files']:
            original = (root / ('machine-' + machine) / f['path']).read_bytes()
            assert (target / f['path']).read_bytes() == original and hashlib.sha256(original).hexdigest() == f['sha256']
        published.append(dict(machine=machine, files=len(inventory['files']), status=inventory['status']))
    noise = json.loads(command(base + ['check-noise', '--evidence', str(root / 'machine-a'), str(root / 'machine-b')], repo).stdout)
    assert noise['runs_with_fingerprint'] == noise['distinct_fingerprints'] == 5 and noise['all_distinct'], noise
    assert [x['run'] for x in noise['runs_without_fingerprint']] == ['a:a2', 'b:b1', 'b:b2'], noise
    trace = root / 'machine-a/a1/evidence/trace.txt'
    return dict(scope='synthetic RC only; local bare Git remote; no R cell and no registered run',
                launcher_sha256=hashlib.sha256((HERE / 'launch.py').read_bytes()).hexdigest(),
                environment=json.loads(preflight.stdout)['environment'], wall_s=time.monotonic() - began,
                ngspice42_trace_sha256=hashlib.sha256(trace.read_bytes()).hexdigest(),
                unpublished_marker_refused=True, machine_a=status_a, failed_run_stays_failed_and_later_runs_proceed=True,
                start_file_given_by_launcher=True, second_launches_refused=rejected, resume_without_restart_refused=True,
                machine_b_after_resume=status_b, lost_runs_never_rerun_and_evidence_untouched=True, collected=published,
                noise_fingerprints=dict(recorded=noise['runs_with_fingerprint'], distinct=noise['distinct_fingerprints'],
                                        runs_without=[x['run'] for x in noise['runs_without_fingerprint']]),
                remote_claims=git('ls-remote', '--heads', 'origin', 'refs/heads/owner-launch/*').split()[1::2], all_checks_passed=True)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--ngspice', type=Path, required=True)
    p.add_argument('--pdk', type=Path, required=True)
    p.add_argument('--work', type=Path, required=True)
    p.add_argument('--report', type=Path, required=True)
    a = p.parse_args()
    report = run(a.work.resolve(), a.ngspice.resolve(), a.pdk.resolve())
    a.report.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
