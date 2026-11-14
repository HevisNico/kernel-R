"""One-attempt launcher for two cloud machines, second version. No registered campaign is supplied here.

It keeps the protocol of ../../sky130-supervisor-qualification/launchkit/launch.py (preflight,
attempt marker published before launch, permanent claim per machine, raw evidence collected byte for
byte) and changes what the owner asked on 2026-11-13:

- the pinned interpreter is Python 3.12.3 of Ubuntu 24.04 with numpy 2.3.5, both checked by hash;
- the launcher itself gives the simulator its start file, a committed `spinit` frozen by hash;
- the runs of a machine are independent and listed round-robin over the scenarios, so that any
  prefix of the list is balanced; up to `jobs` of them run at the same time;
- a run that fails or reaches its time limit stays failed; the runs not yet started go on;
- after a restart of the machine, `resume-machine` records every run that had started and not
  ended as lost, never runs it again, and goes on with the runs that had never started;
- the inventory of each machine is recorded and bound to the attempt marker;
- every run hands over a fingerprint of the noise it drew; `check-noise` lists the runs that share one.
  The noise of the pinned simulator cannot be replayed: the fingerprint is the only record of it.

The executor is a Claude Code cloud session acting on behalf of the owner, on two cloud containers.
"""
from __future__ import annotations
import argparse
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
import hashlib
import importlib.metadata
import json
import math
import os
from pathlib import Path, PurePosixPath
import platform
import re
import secrets
import signal
import subprocess
import sys
import tempfile
import threading
import time
import urllib.request

EXPECTED = {
    'ngspice_version': '42',
    'ngspice_sha256': '820658317b0b54035208da41936fd6871ce924036e5ea4113a4168b821b7fc45',
    'pdk_commit': '1232782c1b9fab3aacda74d67ce7c92bf7da8105',
    'python_version': '3.12.3',
    'python_sha256': 'e50d468e8b0adfb05733f5b87b3cff34829c4a8c1aea50c865aa8bdfe4bb150f',
    'numpy_version': '2.3.5',
    'numpy_record_sha256': '064003bdb6f9f7bb06e46e07cc3398cbfdc3c114dfe55b89d239e564917be2fb',
    'machine': 'x86_64',
}
EXECUTOR = 'a Claude Code cloud session on behalf of the owner, on two cloud containers whose inventories are recorded'
FORBIDDEN_ENVIRONMENT = ('LD_PRELOAD', 'SPICE_SCRIPTS', 'PYTHONPATH', 'PYTHONHOME')
FATAL = (b'aborted', b'timestep too small', b'transient op failed', b'fatal error')
CLEANUP_ALLOWANCE_S = 10
MAX_BUDGET_S = 14400


class Refusal(RuntimeError):
    pass


def require(test, message):
    if not test:
        raise Refusal(message)


def utc():
    return datetime.now(timezone.utc).isoformat()


def encoded(value):
    return (json.dumps(value, sort_keys=True, indent=2) + '\n').encode()


def sha(data):
    return hashlib.sha256(data).hexdigest()


def write_new(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('xb') as f:
        f.write(data)
        f.flush()
        os.fsync(f.fileno())


def git(repo, *args, data=None, env=None):
    p = subprocess.run(['git', *args], cwd=repo, input=data, capture_output=True, env=env)
    if p.returncode:
        raise Refusal('Git command refused: ' + ' '.join(args[:2]) + '\n' + p.stderr.decode(errors='replace'))
    return p.stdout


def relative(value):
    require(isinstance(value, str) and value and '\\' not in value, 'Invalid path')
    p = PurePosixPath(value)
    require(not p.is_absolute() and p.as_posix() == value and all(x not in ('', '.', '..') for x in value.split('/')), 'Unsafe path: ' + value)
    return value


def frozen_file(repo, name):
    relative(name)
    p = repo
    for part in PurePosixPath(name).parts:
        p /= part
        require(not p.is_symlink(), 'Symlink in frozen input: ' + name)
    require(p.is_file(), 'Missing frozen input: ' + name)
    return p.read_bytes()


def boot_unix():
    """Date at which this machine started, from its uptime."""
    return time.time() - float(Path('/proc/uptime').read_text().split()[0])


def machine_cap(runs, jobs):
    """A bound on the wall time of one machine: independent runs, at most `jobs` at a time, started in list order."""
    caps = [r['timeout_s'] + CLEANUP_ALLOWANCE_S for r in runs]
    return sum(caps) / jobs + max(caps)


def check_budget(runs, budget_s, jobs=1):
    require(type(jobs) is int and 1 <= jobs <= 16, 'jobs must be an integer from 1 to 16')
    require(type(budget_s) in (int, float) and math.isfinite(budget_s) and 0 < budget_s <= MAX_BUDGET_S,
            'Budget must be finite, positive and at most four hours')
    for run in runs:
        estimate, timeout = run.get('estimate_s'), run.get('timeout_s')
        require(type(estimate) in (int, float) and math.isfinite(estimate) and estimate > 0, 'Runtime estimate must be finite and positive')
        require(type(timeout) in (int, float) and math.isfinite(timeout) and timeout >= estimate, 'Timeout must be finite, positive and at least the estimate')
    machines = {m: [r for r in runs if r.get('machine') == m] for m in ('a', 'b')}
    caps = {m: machine_cap(rs, jobs) if rs else 0.0 for m, rs in machines.items()}
    estimates = {m: sum(r['estimate_s'] for r in rs) / jobs for m, rs in machines.items()}
    require(sum(caps.values()) <= budget_s, 'Wall-time caps of the two machines exceed the campaign budget')
    return dict(jobs=jobs, estimated_wall_s=estimates, wall_cap_s=caps, aggregate_cap_s=sum(caps.values()),
                cleanup_allowance_per_run_s=CLEANUP_ALLOWANCE_S, budget_s=budget_s)


def round_robin(runs, order):
    """Every machine lists its runs cycling through the scenarios, so that every prefix is balanced."""
    require(isinstance(order, list) and order and len(set(order)) == len(order) and all(isinstance(x, str) and x for x in order),
            'scenario_order must be a nonempty list of distinct names')
    for machine in ('a', 'b'):
        mine = [r for r in runs if r['machine'] == machine]
        for i, run in enumerate(mine):
            require(run.get('scenario') == order[i % len(order)], f'Machine {machine}: run {run["id"]} breaks the round-robin order')


def read_manifest(repo, path):
    path = path.resolve()
    name = path.relative_to(repo).as_posix()
    data = frozen_file(repo, name)
    m = json.loads(data)
    require(m.get('kind') in ('registered', 'synthetic'), 'Unknown campaign kind')
    require(m.get('attempt') == 1, 'Only attempt 1 is supported')
    require(re.fullmatch(r'[a-z0-9][a-z0-9-]{2,63}', m.get('campaign_id', '')) is not None, 'Invalid campaign ID')
    require(m['kind'] != 'synthetic' or m['campaign_id'].startswith('synthetic-'), 'Synthetic campaign namespace required')
    require(m['kind'] != 'registered' or not m['campaign_id'].startswith('synthetic-'), 'Registered namespace cannot be synthetic')
    require(m.get('executor') == EXECUTOR, 'The manifest must name the executor exactly')
    if m['kind'] == 'registered':
        require(isinstance(m.get('expected_workflows'), list) and m['expected_workflows'] and all(isinstance(x, str) and x for x in m['expected_workflows']),
                'Nonempty expected workflow list required')
    for key in ('protocol_commit', 'source_commit'):
        require(re.fullmatch('[0-9a-f]{40}', m.get(key, '')) is not None, 'Exact commit required: ' + key)
    for key in ('protocol_path', 'marker_path', 'spinit_path', 'inventory_a_path', 'inventory_b_path'):
        relative(m[key])
    require(m['protocol_commit'] != m['source_commit'], 'Protocol must precede implementation')
    git(repo, 'merge-base', '--is-ancestor', m['protocol_commit'], m['source_commit'])
    protocol = git(repo, 'show', m['protocol_commit'] + ':' + m['protocol_path'])
    require(sha(protocol) == m['protocol_sha256'], 'Protocol digest differs')
    unchanged_protocol(repo, m, protocol)
    sources = m['source_sha256']
    require(isinstance(sources, dict) and sources, 'Frozen source inventory required')
    for name_, digest in sources.items():
        local = frozen_file(repo, name_)
        require(sha(local) == digest, 'Local source differs: ' + name_)
        require(git(repo, 'show', m['source_commit'] + ':' + name_) == local, 'Source commit differs: ' + name_)
    require(m['launcher_path'] in sources, 'Launcher itself must be frozen')
    require((repo / m['launcher_path']).resolve() == Path(__file__).resolve(), 'Use the frozen launcher from this repository')
    require(m['spinit_path'] in sources and PurePosixPath(m['spinit_path']).name == 'spinit', 'The simulator start file must be a frozen file named spinit')
    require(b'set num_threads=1' in frozen_file(repo, m['spinit_path']), 'The start file must set one thread')
    ids = set()
    machines = set()
    for run in m['runs']:
        require(re.fullmatch('[a-zA-Z0-9_-]+', run['id']) is not None and run['id'] not in ids, 'Invalid/duplicate run ID')
        ids.add(run['id'])
        machines.add(run['machine'])
        require(run['machine'] in ('a', 'b'), 'Machine must be a or b')
        require(isinstance(run['argv'], list) and run['argv'] and run['argv'][0] in ('{python}', '{ngspice}'), 'Use a frozen Python runner or ngspice, not a shell')
        require(all(isinstance(x, str) for x in run['argv']), 'argv must be strings')
        if m['kind'] == 'registered':
            require(run['argv'][0] == '{python}', 'Registered runs require a frozen Python runner; direct ngspice is forbidden')
        outputs = run.get('required_outputs')
        require(isinstance(outputs, list) and outputs and len(set(outputs)) == len(outputs), 'Nonempty unique required_outputs inventory required')
        for name_ in outputs:
            relative(name_)
        logs = run.get('diagnostic_logs', [])
        require(isinstance(logs, list), 'diagnostic_logs must be a list')
        for name_ in logs:
            relative(name_)
        if m['kind'] == 'registered':
            require(logs, 'Registered runs must expose simulator logs for fatal-error checking')
            require(run.get('noise_fingerprint') is not None, 'Registered runs must name the file that records the fingerprint of their noise')
        if run.get('noise_fingerprint') is not None:
            require(relative(run['noise_fingerprint']) in outputs, 'The noise fingerprint must be one of the required outputs')
        require(run['deck'] in sources and run['runner'] in sources, 'Each deck and runner must be frozen')
        if run['argv'][0] == '{python}':
            require(len(run['argv']) > 1 and run['argv'][1] == '{repo}/' + run['runner'], 'Python argv must execute the frozen runner')
        else:
            require('{deck}' in run['argv'], 'ngspice argv must use the frozen deck')
    require(machines == {'a', 'b'}, 'Both machine shards must be nonempty')
    round_robin(m['runs'], m.get('scenario_order'))
    check_budget(m['runs'], m['budget_s'], m.get('jobs'))
    return m, data, name


def unchanged_protocol(repo, m, protocol):
    require(frozen_file(repo, m['protocol_path']) == protocol, 'Local protocol differs from preregistration')
    require(git(repo, 'show', m['source_commit'] + ':' + m['protocol_path']) == protocol, 'Implementation altered the preregistered protocol')


def allowed_after_freeze(m, manifest_path):
    return {manifest_path, m['marker_path'], m['inventory_a_path'], m['inventory_b_path']}


def runtime_unchanged(repo, m, manifest_path, revision):
    changed = set(git(repo, 'diff', '--name-only', m['source_commit'], revision).decode().splitlines())
    allowed = allowed_after_freeze(m, manifest_path)
    require(changed <= allowed, 'Runtime source tree changed after implementation freeze: ' + repr(sorted(changed - allowed)))


def github_json(path):
    request = urllib.request.Request('https://api.github.com/repos/HevisNico/kernel-R/' + path,
                                     headers={'Accept': 'application/vnd.github+json', 'User-Agent': 'kernel-R-launchkit'})
    with urllib.request.urlopen(request, timeout=30) as response:
        return json.load(response)


def api_pages(path, key, get=github_json):
    result = []
    for page in range(1, 101):
        separator = '&' if '?' in path else '?'
        document = get(path + separator + 'per_page=100&page=' + str(page))
        items = document[key]
        result.extend(items)
        if len(items) < 100:
            return result
    raise Refusal('API pagination did not terminate')


def live_ci_gate(m, get=github_json):
    require(m['kind'] == 'registered', 'Synthetic fixtures must not use the GitHub CI gate')
    runs = api_pages('actions/runs?head_sha=' + m['source_commit'], 'workflow_runs', get)
    latest = {}
    for run in runs:
        require(run['head_sha'] == m['source_commit'], 'CI response includes a different commit')
        previous = latest.get(run['workflow_id'])
        if previous is None or (run['id'], run['run_attempt']) > (previous['id'], previous['run_attempt']):
            latest[run['workflow_id']] = run
    require(set(m['expected_workflows']) <= {x['name'] for x in latest.values()}, 'An expected exact-head workflow is missing')
    checked = []
    for run in latest.values():
        require(run['status'] == 'completed' and run['conclusion'] == 'success', 'Latest exact-head workflow is not successful: ' + run['name'])
        jobs = api_pages('actions/runs/' + str(run['id']) + '/attempts/' + str(run['run_attempt']) + '/jobs', 'jobs', get)
        require(jobs and all(j['status'] == 'completed' and j['conclusion'] == 'success' for j in jobs), 'Latest-attempt jobs are missing or not successful: ' + run['name'])
        checked.append(dict(name=run['name'], id=run['id'], run_attempt=run['run_attempt'], html_url=run['html_url'],
                            jobs=[dict(id=j['id'], name=j['name'], conclusion=j['conclusion']) for j in jobs]))
    require(checked, 'No exact-head workflows found')
    return dict(head_sha=m['source_commit'], observed_utc=utc(), workflows=checked)


def identity(ngspice, pdk):
    """What must be the same on the two machines."""
    import numpy
    actual = dict(ngspice_sha256=sha(ngspice.read_bytes()), pdk_commit=git(pdk, 'rev-parse', 'HEAD').decode().strip(),
                  python_version=platform.python_version(), python_sha256=sha(Path(os.path.realpath(sys.executable)).read_bytes()),
                  numpy_version=numpy.__version__,
                  numpy_record_sha256=sha(importlib.metadata.distribution('numpy').read_text('RECORD').encode()),
                  machine=platform.machine())
    r = subprocess.run([str(ngspice), '--version'], capture_output=True, text=True, timeout=30)
    match = re.search(r'ngspice-(\d+(?:\.\d+)?)\s*:', r.stdout + r.stderr)
    require(r.returncode == 0 and match is not None, 'Cannot identify ngspice version')
    actual['ngspice_version'] = match.group(1)
    return actual


def preflight(repo, manifest, ngspice, pdk):
    m, data, name = read_manifest(repo, manifest)
    if m['kind'] == 'registered':
        require(not any(os.environ.get(x) for x in FORBIDDEN_ENVIRONMENT), 'Simulator/Python runtime overrides are forbidden: the launcher sets the start file itself')
        untracked = set(git(repo, 'ls-files', '--others', '--exclude-standard').decode().splitlines())
        require(untracked <= allowed_after_freeze(m, name), 'Untracked files could shadow frozen runtime inputs; use an otherwise clean checkout')
    actual = identity(ngspice, pdk)
    require(actual == EXPECTED, 'Environment does not match the pinned ngspice 42 / PDK / Python 3.12.3 / numpy 2.3.5: ' + json.dumps(actual))
    require(not git(pdk, 'status', '--porcelain', '--untracked-files=all').strip(), 'PDK working tree is not clean')
    require(not git(repo, 'diff', '--name-only').strip() and not git(repo, 'diff', '--cached', '--name-only').strip(), 'Tracked repository changes exist')
    runtime_unchanged(repo, m, name, 'HEAD')
    return m, data, name, actual


def inventory(machine, environment):
    """The machine itself: recorded, not required to be equal on the two machines."""
    cpu = next((l.split(':', 1)[1].strip() for l in Path('/proc/cpuinfo').read_text().splitlines() if l.startswith('model name')), 'unknown')
    memory = next((l.split(':', 1)[1].strip() for l in Path('/proc/meminfo').read_text().splitlines() if l.startswith('MemTotal')), 'unknown')
    release = next((l.split('=', 1)[1].strip().strip('"') for l in Path('/etc/os-release').read_text().splitlines() if l.startswith('PRETTY_NAME=')), 'unknown')
    return dict(machine=machine, executor=EXECUTOR, recorded_utc=utc(), hostname=platform.node(), kernel=platform.release(), os=release,
                cpu_model=cpu, processors=os.cpu_count(), memory=memory, boot_utc=datetime.fromtimestamp(boot_unix(), timezone.utc).isoformat(),
                environment=environment)


def marker_value(repo, m, manifest_data, manifest_path, environment):
    inventories = {}
    for machine in ('a', 'b'):
        data = frozen_file(repo, m[f'inventory_{machine}_path'])
        record = json.loads(data)
        require(record.get('machine') == machine and record.get('environment') == environment and record.get('executor') == EXECUTOR,
                f'Inventory of machine {machine} does not show the pinned environment')
        inventories[machine] = sha(data)
    return dict(kind=m['kind'], campaign_id=m['campaign_id'], attempt=1, executor=EXECUTOR, manifest_path=manifest_path,
                manifest_sha256=sha(manifest_data), protocol_commit=m['protocol_commit'], source_commit=m['source_commit'],
                environment=environment, inventory_sha256=inventories,
                shards={machine: [r['id'] for r in m['runs'] if r['machine'] == machine] for machine in ('a', 'b')},
                scenario_order=m['scenario_order'], budget=check_budget(m['runs'], m['budget_s'], m['jobs']))


def published_marker(repo, remote, branch, m, data, name, environment):
    if m['kind'] == 'registered':
        url = git(repo, 'remote', 'get-url', remote).decode().strip().removesuffix('.git')
        require(url in ('https://github.com/HevisNico/kernel-R', 'git@github.com:HevisNico/kernel-R'), 'Registered claims require the designated GitHub repository')
    git(repo, 'fetch', '--no-tags', remote, branch)
    commit = git(repo, 'rev-parse', 'FETCH_HEAD').decode().strip()
    git(repo, 'merge-base', '--is-ancestor', m['source_commit'], commit)
    runtime_unchanged(repo, m, name, commit)
    require(git(repo, 'show', commit + ':' + name) == data, 'Remote manifest differs or is unpublished')
    for machine in ('a', 'b'):
        path = m[f'inventory_{machine}_path']
        require(git(repo, 'show', commit + ':' + path) == frozen_file(repo, path), 'Remote inventory differs or is unpublished')
    marker = json.loads(git(repo, 'show', commit + ':' + m['marker_path']))
    expected = marker_value(repo, m, data, name, environment)
    require({k: marker.get(k) for k in expected} == expected, 'Published RUN_ATTEMPT does not bind this campaign')
    require(isinstance(marker.get('created_utc'), str), 'Marker timestamp is missing')
    return commit, marker


def claim_ref(m, machine):
    return 'refs/heads/owner-launch/protocol-' + m['protocol_sha256'] + '/' + machine


def claim(repo, remote, published, m, machine):
    ref = claim_ref(m, machine)
    require(not git(repo, 'ls-remote', '--heads', remote, ref).strip(), 'Machine already claimed: never relaunch, even in another clone/output directory')
    record = dict(campaign_id=m['campaign_id'], protocol_sha256=m['protocol_sha256'], attempt=1, machine=machine, published_marker_commit=published,
                  nonce=secrets.token_hex(32), claimed_utc=utc(), status='claimed-before-execution')
    blob = git(repo, 'hash-object', '-w', '--stdin', data=encoded(record)).decode().strip()
    with tempfile.TemporaryDirectory() as tmp:
        env = dict(os.environ, GIT_INDEX_FILE=str(Path(tmp) / 'index'))
        git(repo, 'read-tree', published, env=env)
        entry = 'OWNER_LAUNCH_CLAIMS/' + m['campaign_id'] + '/' + machine + '.json'
        git(repo, 'update-index', '--add', '--cacheinfo', '100644,' + blob + ',' + entry, env=env)
        tree = git(repo, 'write-tree', env=env).decode().strip()
        commit = git(repo, 'commit-tree', tree, '-p', published, '-m', 'Claim launch ' + m['campaign_id'] + ' machine ' + machine, data=b'').decode().strip()
    # Normal push only. Concurrent claims are distinct sibling commits, so only one can create the ref.
    git(repo, 'push', remote, commit + ':' + ref)
    got = git(repo, 'ls-remote', '--heads', remote, ref).decode().split()
    require(got and got[0] == commit, 'Durable claim could not be confirmed; do not execute')
    return ref, commit, record


def postflight(folder, run):
    """Exit 0 does not imply a complete run: named outputs must exist, and no log may carry a fatal message."""
    outputs = []
    for name in run['required_outputs']:
        data = frozen_file(folder, name)
        require(data, 'Required output is empty: ' + name)
        outputs.append(dict(path=name, bytes=len(data), sha256=sha(data)))
    for name in ['stdout.log', 'stderr.log'] + run.get('diagnostic_logs', []):
        log = frozen_file(folder, name).lower()
        require(not any(token in log for token in FATAL), 'Fatal simulator marker in ' + name + '; preserve evidence, never rerun')
    return outputs


def noise_fingerprint(folder, run):
    """The fingerprint that the run recorded of its own noise: 64 hexadecimal digits, or None when the run declares none."""
    if run.get('noise_fingerprint') is None:
        return None
    text = frozen_file(folder, run['noise_fingerprint']).decode('ascii', 'replace').strip()
    require(re.fullmatch('[0-9a-f]{64}', text) is not None, 'Malformed noise fingerprint')
    return text


def check_noise(folders):
    """Which runs drew the same noise? Reads the state files of the evidence folders; changes nothing."""
    seen, without = {}, []
    for folder in folders:
        state = json.loads((folder / 'STATE.json').read_bytes())
        for record in state['records']:
            name = state['machine'] + ':' + record['id']
            if record.get('noise_fingerprint') is None:
                without.append(dict(run=name, status=record['status']))
            else:
                seen.setdefault(record['noise_fingerprint'], []).append(name)
    shared = sorted(v for v in seen.values() if len(v) > 1)
    return dict(runs_with_fingerprint=sum(len(v) for v in seen.values()), distinct_fingerprints=len(seen), shared=shared,
                all_distinct=not shared, runs_without_fingerprint=without)


def runner_environment(repo, m):
    """The environment of a run: that of the launcher, plus the committed simulator start file."""
    env = {k: v for k, v in os.environ.items() if k not in FORBIDDEN_ENVIRONMENT}
    env['SPICE_SCRIPTS'] = str((repo / m['spinit_path']).parent)
    return env


class Shard:
    """The runs of one machine, the state file that records them, and the pool that executes them."""

    def __init__(self, repo, m, machine, out, ngspice, pdk, claim_commit, records, events):
        self.repo, self.m, self.machine, self.out, self.ngspice, self.pdk = repo, m, machine, out, ngspice, pdk
        self.claim_commit, self.records, self.events = claim_commit, records, events
        self.lock = threading.Lock()
        self.env = runner_environment(repo, m)

    def save(self, status):
        with self.lock:
            (self.out / 'STATE.json').write_bytes(encoded(dict(status=status, machine=self.machine, claim_commit=self.claim_commit,
                                                               records=self.records, events=self.events)))

    def one(self, run):
        folder = self.out / run['id']
        folder.mkdir(exist_ok=False)
        substitutions = dict(repo=str(self.repo), out=str(folder), python=sys.executable, ngspice=str(self.ngspice), pdk=str(self.pdk), deck=str(self.repo / run['deck']))
        argv = [s.format(**substitutions) for s in run['argv']]
        record = dict(id=run['id'], scenario=run.get('scenario'), status='started', started_utc=utc(), argv=argv)
        with self.lock:
            self.records.append(record)
        self.save('running')
        start = time.monotonic()
        process = None
        with (folder / 'stdout.log').open('xb') as stdout, (folder / 'stderr.log').open('xb') as stderr:
            try:
                process = subprocess.Popen(argv, cwd=self.repo, stdout=stdout, stderr=stderr, start_new_session=True, env=self.env)
                code = process.wait(timeout=run['timeout_s'])
                record.update(returncode=code, wall_s=time.monotonic() - start)
                require(code == 0, 'Run failed')
                stdout.flush()
                stderr.flush()
                record['required_outputs'] = postflight(folder, run)
                fingerprint = noise_fingerprint(folder, run)
                if fingerprint is not None:
                    record['noise_fingerprint'] = fingerprint
                record.update(status='complete', ended_utc=utc())
            except BaseException as error:
                if process is not None:
                    try:
                        os.killpg(process.pid, signal.SIGTERM)
                    except ProcessLookupError:
                        pass
                    try:
                        process.wait(timeout=CLEANUP_ALLOWANCE_S)
                    except subprocess.TimeoutExpired:
                        try:
                            os.killpg(process.pid, signal.SIGKILL)
                        except ProcessLookupError:
                            pass
                        process.wait()
                kind = 'time-limit' if isinstance(error, subprocess.TimeoutExpired) else 'failed'
                record.update(status=kind + '-never-rerun', wall_s=time.monotonic() - start, ended_utc=utc(), reason=str(error)[:400])
                if not isinstance(error, (Refusal, subprocess.TimeoutExpired, OSError)):
                    self.save('running')
                    raise
            finally:
                stdout.flush()
                stderr.flush()
                os.fsync(stdout.fileno())
                os.fsync(stderr.fileno())
        self.save('running')

    def execute(self, runs):
        self.save('running')
        try:
            with ThreadPoolExecutor(self.m['jobs']) as pool:
                list(pool.map(self.one, runs))
        except BaseException:
            self.save('interrupted')
            raise
        done = all(r['status'] == 'complete' for r in self.records) and len(self.records) == sum(1 for r in self.m['runs'] if r['machine'] == self.machine)
        self.save('complete' if done else 'ended-with-failed-or-lost-runs')
        return dict(machine=self.machine, status='complete' if done else 'ended-with-failed-or-lost-runs', claim_commit=self.claim_commit,
                    runs={r['id']: r['status'] for r in self.records}, output=str(self.out))


def launch(repo, m, machine, out, ngspice, pdk, remote, branch, data, name, environment):
    require(not out.exists(), 'Output exists: use resume-machine after a restart, never a second launch')
    published, marker = published_marker(repo, remote, branch, m, data, name, environment)
    ci = live_ci_gate(m) if m['kind'] == 'registered' else {'kind': 'synthetic-local-fixture-no-GitHub-CI'}
    ref, claim_commit, record = claim(repo, remote, published, m, machine)
    out.mkdir(parents=True, exist_ok=False)
    write_new(out / 'CLAIM.json', encoded(dict(record, claim_ref=ref, claim_commit=claim_commit)))
    write_new(out / 'RUN_ATTEMPT.json', encoded(marker))
    write_new(out / 'ENVIRONMENT.json', encoded(environment))
    write_new(out / 'INVENTORY_AT_LAUNCH.json', encoded(inventory(machine, environment)))
    write_new(out / 'CI_OBSERVED.json', encoded(ci))
    events = [dict(event='launch', utc=utc(), unix=time.time(), boot_unix=boot_unix())]
    shard = Shard(repo, m, machine, out, ngspice, pdk, claim_commit, [], events)
    return shard.execute([r for r in m['runs'] if r['machine'] == machine])


def resume(repo, m, machine, out, ngspice, pdk, remote, branch, data, name, environment, assume_restarted=False):
    """After a restart of the machine only. Started runs are lost; runs never started go on."""
    require(out.is_dir() and (out / 'STATE.json').is_file() and (out / 'CLAIM.json').is_file(), 'Nothing to resume: no launched shard in this output directory')
    state = json.loads((out / 'STATE.json').read_bytes())
    mine = json.loads((out / 'CLAIM.json').read_bytes())
    require(state.get('machine') == machine and mine.get('machine') == machine, 'This output directory belongs to another machine')
    got = git(repo, 'ls-remote', '--heads', remote, claim_ref(m, machine)).decode().split()
    require(got and got[0] == mine['claim_commit'] == state['claim_commit'], 'The remote claim is not the claim of this shard')
    published_marker(repo, remote, branch, m, data, name, environment)
    last = max(e['unix'] for e in state['events'])
    require(m['kind'] == 'synthetic' and assume_restarted or boot_unix() > last,
            'The machine did not restart after the shard was last started: resume is allowed after a restart only')
    if m['kind'] == 'registered':
        write_new(out / f"CI_OBSERVED_AT_RESUME_{len(state['events'])}.json", encoded(live_ci_gate(m)))
    write_new(out / f"INVENTORY_AT_RESUME_{len(state['events'])}.json", encoded(inventory(machine, environment)))
    lost = []
    for record in state['records']:
        if record['status'] == 'started':
            record.update(status='lost-started-before-restart-never-rerun', lost_recorded_utc=utc())
            lost.append(record['id'])
    known = {r['id'] for r in state['records']}
    remaining = [r for r in m['runs'] if r['machine'] == machine and r['id'] not in known]
    for run in remaining:
        require(not (out / run['id']).exists(), 'A run without a record has a folder: ' + run['id'])
    state['events'].append(dict(event='resume-after-restart', utc=utc(), unix=time.time(), boot_unix=boot_unix(), lost=lost,
                                never_started=[r['id'] for r in remaining]))
    shard = Shard(repo, m, machine, out, ngspice, pdk, state['claim_commit'], state['records'], state['events'])
    return shard.execute(remaining)


def collect(out, destination, interrupted=False):
    out = out.resolve()
    destination = destination.resolve()
    require(not destination.is_relative_to(out), 'Collection destination must be outside the evidence tree')
    require(out.is_dir() and not destination.exists(), 'Require existing evidence and a new destination')
    state = json.loads((out / 'STATE.json').read_bytes()) if (out / 'STATE.json').exists() else dict(status='unknown')
    require(state['status'] != 'running' or interrupted, 'Stop all processes first; explicitly declare an interrupted running state')
    destination.mkdir(parents=True, exist_ok=False)
    files = []
    for p in sorted(out.rglob('*')):
        require(not p.is_symlink(), 'Evidence symlink cannot be silently copied or omitted')
        require(p.is_dir() or p.is_file(), 'Unsupported evidence file type; no silent omission')
        if p.is_file():
            rel = p.relative_to(out)
            data = p.read_bytes()
            write_new(destination / rel, data)
            require(p.read_bytes() == data, 'Source changed during collection; preserve both versions and stop')
            files.append(dict(path=rel.as_posix(), bytes=len(data), sha256=sha(data)))
    manifest = dict(interrupted_declared=interrupted, status=state['status'], files=files,
                    rule='Every surviving regular file copied byte for byte; no rerun, compression or deletion')
    write_new(destination / 'SURVIVORS.json', encoded(manifest))
    return manifest


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('command', choices=('identity', 'inventory', 'preflight', 'plan', 'prepare', 'run-machine', 'resume-machine', 'collect', 'check-noise'))
    p.add_argument('--repo', type=Path, default=Path.cwd())
    p.add_argument('--manifest', type=Path)
    p.add_argument('--ngspice', type=Path)
    p.add_argument('--pdk', type=Path)
    p.add_argument('--remote', default='origin')
    p.add_argument('--branch')
    p.add_argument('--machine', choices=('a', 'b'))
    p.add_argument('--out', type=Path)
    p.add_argument('--destination', type=Path)
    p.add_argument('--evidence', type=Path, nargs='+', help='check-noise: the evidence folders of the machines')
    p.add_argument('--interrupted', action='store_true')
    p.add_argument('--assume-restarted', action='store_true', help='synthetic fixtures only')
    a = p.parse_args()
    repo = a.repo.resolve()
    if a.command == 'collect':
        result = collect(a.out.resolve(), a.destination.resolve(), a.interrupted)
    elif a.command == 'check-noise':
        require(a.evidence, 'Evidence folders are required')
        result = check_noise([x.resolve() for x in a.evidence])
    elif a.command in ('identity', 'inventory'):
        require(a.ngspice is not None and a.pdk is not None, 'ngspice and PDK are required')
        actual = identity(a.ngspice.resolve(), a.pdk.resolve())
        require(actual == EXPECTED, 'Environment does not match the pinned one: ' + json.dumps(actual))
        if a.command == 'identity':
            result = actual
        else:
            require(a.machine is not None and a.out is not None, 'Machine and output file are required')
            result = inventory(a.machine, actual)
            write_new(a.out.resolve(), encoded(result))
    else:
        require(a.manifest is not None and a.ngspice is not None and a.pdk is not None, 'Manifest, ngspice and PDK are required')
        ngspice = a.ngspice.resolve()
        pdk = a.pdk.resolve()
        m, data, name, environment = preflight(repo, a.manifest, ngspice, pdk)
        if a.command == 'preflight':
            result = dict(environment=environment, budget=check_budget(m['runs'], m['budget_s'], m['jobs']),
                          shards={x: [r['id'] for r in m['runs'] if r['machine'] == x] for x in ('a', 'b')})
        elif a.command == 'plan':
            result = marker_value(repo, m, data, name, environment)
        elif a.command == 'prepare':
            if m['kind'] == 'registered':
                result_ci = live_ci_gate(m)
            result = marker_value(repo, m, data, name, environment)
            result['created_utc'] = utc()
            if m['kind'] == 'registered':
                result['ci_at_prepare'] = result_ci
            write_new(repo / m['marker_path'], encoded(result))
        else:
            require(a.branch and a.machine and a.out is not None, 'Branch, machine and output are required')
            call = launch if a.command == 'run-machine' else resume
            extra = dict(assume_restarted=a.assume_restarted) if a.command == 'resume-machine' else {}
            result = call(repo, m, a.machine, a.out.resolve(), ngspice, pdk, a.remote, a.branch, data, name, environment, **extra)
    print(json.dumps(result, indent=2, sort_keys=True))
    if a.command == 'check-noise' and not result['all_distinct']:
        sys.exit(2)


if __name__ == '__main__':
    try:
        main()
    except (Refusal, KeyError, ValueError, OSError) as e:
        print('REFUSED: ' + str(e), file=sys.stderr)
        sys.exit(1)
