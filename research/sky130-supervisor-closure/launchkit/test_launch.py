"""Fast controls of the launch kit; the end-to-end test on an RC circuit is synthetic_test.py."""
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

import launch


def runs(n, machine='a', order=('x', 'y'), estimate=1, timeout=5):
    return [dict(id=f'{machine}{i}', machine=machine, scenario=order[i % len(order)], estimate_s=estimate, timeout_s=timeout) for i in range(n)]


class LaunchTests(unittest.TestCase):
    def test_path_escape_and_noncanonical_paths_refused(self):
        for value in ('../x', 'a/../b', '/tmp/x', 'a//b', 'a\\b', 'a/./b', ''):
            with self.subTest(value=value), self.assertRaises(launch.Refusal):
                launch.relative(value)

    def test_exclusive_marker_never_overwrites(self):
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp) / 'marker.json'
            launch.write_new(p, b'first')
            with self.assertRaises(FileExistsError):
                launch.write_new(p, b'second')
            self.assertEqual(p.read_bytes(), b'first')

    def test_frozen_source_symlink_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'actual').write_bytes(b'code')
            (root / 'link').symlink_to(root / 'actual')
            with self.assertRaises(launch.Refusal):
                launch.frozen_file(root, 'link')

    def test_pinned_environment(self):
        self.assertEqual(launch.EXPECTED['ngspice_version'], '42')
        self.assertEqual(launch.EXPECTED['python_version'], '3.12.3')
        self.assertEqual(launch.EXPECTED['numpy_version'], '2.3.5')
        for key in ('ngspice_sha256', 'python_sha256', 'numpy_record_sha256'):
            self.assertEqual(len(launch.EXPECTED[key]), 64)

    def test_round_robin_makes_every_prefix_balanced(self):
        order = ['x', 'y', 'z']
        good = runs(7, 'a', order) + runs(5, 'b', order)
        launch.round_robin(good, order)
        for machine in ('a', 'b'):
            mine = [r for r in good if r['machine'] == machine]
            for n in range(len(mine) + 1):
                counts = [sum(r['scenario'] == s for r in mine[:n]) for s in order]
                self.assertLessEqual(max(counts) - min(counts), 1)
        bad = runs(4, 'a', order)
        bad[1], bad[2] = bad[2], bad[1]
        with self.assertRaises(launch.Refusal):
            launch.round_robin(bad + runs(3, 'b', order), order)
        with self.assertRaises(launch.Refusal):
            launch.round_robin(good, ['x', 'x'])

    def test_budget_is_a_wall_time_bound_for_both_machines(self):
        both = runs(8, 'a') + runs(8, 'b')
        b = launch.check_budget(both, 400, jobs=4)
        self.assertEqual(b['wall_cap_s']['a'], 8 * 15 / 4 + 15)
        self.assertEqual(b['aggregate_cap_s'], 2 * (8 * 15 / 4 + 15))
        with self.assertRaises(launch.Refusal):
            launch.check_budget(both, 80, jobs=4)
        with self.assertRaises(launch.Refusal):
            launch.check_budget(both, 14401, jobs=4)

    def test_small_estimates_cannot_hide_timeouts_over_budget(self):
        both = runs(1, 'a', estimate=1, timeout=7200) + runs(1, 'b', estimate=1, timeout=7200)
        with self.assertRaises(launch.Refusal):
            launch.check_budget(both, 14400, jobs=1)

    def test_nonfinite_runtime_budget_and_jobs_refused(self):
        for value in (float('nan'), float('inf'), -1, True):
            with self.subTest(value=value):
                with self.assertRaises(launch.Refusal):
                    launch.check_budget(runs(1) + runs(1, 'b'), value, jobs=1)
                with self.assertRaises(launch.Refusal):
                    launch.check_budget(runs(1, estimate=value) + runs(1, 'b'), 30, jobs=1)
                with self.assertRaises(launch.Refusal):
                    launch.check_budget(runs(1, timeout=value) + runs(1, 'b'), 30, jobs=1)
        for jobs in (0, 17, 1.5, None, True):
            with self.assertRaises(launch.Refusal):
                launch.check_budget(runs(1) + runs(1, 'b'), 100, jobs=jobs)

    def test_launcher_gives_the_committed_start_file_and_drops_overrides(self):
        import os
        old = dict(os.environ)
        try:
            os.environ.update(LD_PRELOAD='/x.so', SPICE_SCRIPTS='/elsewhere', PYTHONPATH='/y')
            env = launch.runner_environment(Path('/repo'), dict(spinit_path='kit/runtime/spinit'))
        finally:
            os.environ.clear()
            os.environ.update(old)
        self.assertEqual(env['SPICE_SCRIPTS'], '/repo/kit/runtime')
        self.assertNotIn('LD_PRELOAD', env)
        self.assertNotIn('PYTHONPATH', env)

    def test_collect_preserves_binary_failed_evidence(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            out = root / 'out'
            out.mkdir()
            (out / 'STATE.json').write_text(json.dumps(dict(status='ended-with-failed-or-lost-runs')))
            blob = b'\x00\xffsurvivor\n'
            (out / 'partial.bin').write_bytes(blob)
            report = launch.collect(out, root / 'published')
            self.assertEqual((root / 'published/partial.bin').read_bytes(), blob)
            f = next(x for x in report['files'] if x['path'] == 'partial.bin')
            self.assertEqual(f['sha256'], hashlib.sha256(blob).hexdigest())

    def test_running_collection_requires_explicit_interruption_declaration(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            out = root / 'out'
            out.mkdir()
            (out / 'STATE.json').write_text(json.dumps(dict(status='running')))
            with self.assertRaises(launch.Refusal):
                launch.collect(out, root / 'published')
            self.assertTrue(launch.collect(out, root / 'published', interrupted=True)['interrupted_declared'])

    def test_collection_never_overwrites_nor_follows_symlinks(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            out = root / 'out'
            out.mkdir()
            (root / 'published').mkdir()
            with self.assertRaises(launch.Refusal):
                launch.collect(out, root / 'published')
            (out / 'STATE.json').write_text(json.dumps(dict(status='complete')))
            (root / 'outside').write_bytes(b'outside')
            (out / 'link').symlink_to(root / 'outside')
            with self.assertRaises(launch.Refusal):
                launch.collect(out, root / 'other')

    def test_zero_exit_requires_outputs_and_clean_logs(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'stdout.log').write_bytes(b'')
            (root / 'stderr.log').write_bytes(b'')
            run = dict(required_outputs=['trace.txt'])
            with self.assertRaises(launch.Refusal):
                launch.postflight(root, run)
            (root / 'trace.txt').write_bytes(b'')
            with self.assertRaises(launch.Refusal):
                launch.postflight(root, run)
            (root / 'trace.txt').write_bytes(b'time voltage\n0 0\n')
            self.assertEqual(launch.postflight(root, run)[0]['path'], 'trace.txt')
            (root / 'simulator.log').write_bytes(b'tran simulation(s) aborted\n')
            with self.assertRaises(launch.Refusal):
                launch.postflight(root, dict(required_outputs=['trace.txt'], diagnostic_logs=['simulator.log']))

    def test_noise_fingerprint_is_read_and_shared_ones_are_listed(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            run = dict(noise_fingerprint='noise.sha256')
            (root / 'noise.sha256').write_text('not a digest\n')
            with self.assertRaises(launch.Refusal):
                launch.noise_fingerprint(root, run)
            (root / 'noise.sha256').write_text('ab' * 32 + '\n')
            self.assertEqual(launch.noise_fingerprint(root, run), 'ab' * 32)
            self.assertIsNone(launch.noise_fingerprint(root, dict()))
            for machine, records in (('a', [dict(id='a1', status='complete', noise_fingerprint='11' * 32), dict(id='a2', status='failed-never-rerun')]),
                                     ('b', [dict(id='b1', status='complete', noise_fingerprint='22' * 32), dict(id='b2', status='complete', noise_fingerprint='11' * 32)])):
                (root / machine).mkdir()
                (root / machine / 'STATE.json').write_text(json.dumps(dict(machine=machine, records=records)))
            report = launch.check_noise([root / 'a', root / 'b'])
            self.assertEqual(report['shared'], [['a:a1', 'b:b2']])
            self.assertFalse(report['all_distinct'])
            self.assertEqual((report['runs_with_fingerprint'], report['distinct_fingerprints']), (3, 2))
            self.assertEqual(report['runs_without_fingerprint'], [dict(run='a:a2', status='failed-never-rerun')])
            self.assertTrue(launch.check_noise([root / 'a'])['all_distinct'])

    def ci_fixture(self, extra=None, job_status='success', head='a' * 40, attempts=2):
        run = dict(id=7, workflow_id=3, name='Lean', run_attempt=attempts, head_sha=head, status='completed', conclusion='success', html_url='https://example.invalid/run/7')

        def get(path):
            if path.startswith('actions/runs?'):
                return dict(workflow_runs=[run] + ([extra] if extra else []))
            self.assertIn('/attempts/' + str(attempts) + '/jobs', path)
            return dict(jobs=[dict(id=9, name='lean', status='completed', conclusion=job_status)])
        return dict(kind='registered', source_commit='a' * 40, expected_workflows=['Lean']), get

    def test_ci_uses_exact_head_and_latest_attempt_jobs(self):
        m, get = self.ci_fixture()
        report = launch.live_ci_gate(m, get)
        self.assertEqual(report['head_sha'], 'a' * 40)
        self.assertEqual(report['workflows'][0]['run_attempt'], 2)

    def test_ci_refusals(self):
        m, get = self.ci_fixture(head='b' * 40)
        with self.assertRaises(launch.Refusal):
            launch.live_ci_gate(m, get)
        m, get = self.ci_fixture(job_status='failure')
        with self.assertRaises(launch.Refusal):
            launch.live_ci_gate(m, get)
        extra = dict(id=8, workflow_id=4, name='Extra', run_attempt=1, head_sha='a' * 40, status='completed', conclusion='failure', html_url='https://example.invalid/extra')
        m, get = self.ci_fixture(extra=extra)
        with self.assertRaises(launch.Refusal):
            launch.live_ci_gate(m, get)
        m, get = self.ci_fixture()
        m['expected_workflows'].append('Physical')
        with self.assertRaises(launch.Refusal):
            launch.live_ci_gate(m, get)

    def test_unlisted_committed_runtime_change_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)

            def git(*args):
                return subprocess.check_output(['git', *args], cwd=repo, stderr=subprocess.DEVNULL).decode().strip()
            git('init')
            git('config', 'user.name', 'Synthetic')
            git('config', 'user.email', 'synthetic@example.invalid')
            (repo / 'runner.py').write_text('print(1)\n')
            git('add', '.')
            git('commit', '-m', 'source')
            m = dict(source_commit=git('rev-parse', 'HEAD'), marker_path='RUN_ATTEMPT.json', inventory_a_path='INV_a.json', inventory_b_path='INV_b.json')
            (repo / 'INV_a.json').write_text('{}\n')
            git('add', '.')
            git('commit', '-m', 'inventory')
            launch.runtime_unchanged(repo, m, 'manifest.json', 'HEAD')
            (repo / 'hidden_import.py').write_text('changed = True\n')
            git('add', '.')
            git('commit', '-m', 'unlisted runtime')
            with self.assertRaises(launch.Refusal):
                launch.runtime_unchanged(repo, m, 'manifest.json', 'HEAD')

    def test_protocol_cannot_change_during_implementation(self):
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)

            def git(*args):
                return subprocess.check_output(['git', *args], cwd=repo, stderr=subprocess.DEVNULL).decode().strip()
            git('init')
            git('config', 'user.name', 'Synthetic')
            git('config', 'user.email', 'synthetic@example.invalid')
            original = b'Frozen before implementation\n'
            (repo / 'PROTOCOL.md').write_bytes(original)
            git('add', '.')
            git('commit', '-m', 'protocol')
            (repo / 'PROTOCOL.md').write_bytes(b'Changed after protocol\n')
            git('add', '.')
            git('commit', '-m', 'implementation')
            m = dict(protocol_path='PROTOCOL.md', source_commit=git('rev-parse', 'HEAD'))
            with self.assertRaises(launch.Refusal):
                launch.unchanged_protocol(repo, m, original)


if __name__ == '__main__':
    unittest.main()
