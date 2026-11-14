"""Fast launch-kit controls; the real RC end-to-end test is separate."""
import hashlib
import json
from pathlib import Path
import tempfile
import subprocess
import unittest

import launch


class LaunchTests(unittest.TestCase):
    def test_path_escape_and_noncanonical_paths_refused(self):
        for value in ('../x','a/../b','/tmp/x','a//b','a\\b','a/./b',''):
            with self.subTest(value=value),self.assertRaises(launch.Refusal):
                launch.relative(value)

    def test_exclusive_marker_never_overwrites(self):
        with tempfile.TemporaryDirectory() as tmp:
            p=Path(tmp)/'marker.json';launch.write_new(p,b'first')
            with self.assertRaises(FileExistsError):launch.write_new(p,b'second')
            self.assertEqual(p.read_bytes(),b'first')

    def test_frozen_source_symlink_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);(root/'actual').write_bytes(b'code');(root/'link').symlink_to(root/'actual')
            with self.assertRaises(launch.Refusal):launch.frozen_file(root,'link')

    def test_collect_preserves_binary_failed_evidence(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);out=root/'out';out.mkdir()
            (out/'STATE.json').write_text(json.dumps(dict(status='incomplete-no-relaunch')))
            blob=b'\x00\xffsurvivor\n';(out/'partial.bin').write_bytes(blob)
            report=launch.collect(out,root/'published')
            self.assertEqual((root/'published/partial.bin').read_bytes(),blob)
            f=next(x for x in report['files'] if x['path']=='partial.bin')
            self.assertEqual(f['sha256'],hashlib.sha256(blob).hexdigest())
            self.assertEqual(report['status'],'incomplete-no-relaunch')

    def test_running_collection_requires_explicit_interruption_declaration(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);out=root/'out';out.mkdir()
            (out/'STATE.json').write_text(json.dumps(dict(status='running')))
            with self.assertRaises(launch.Refusal):launch.collect(out,root/'published')
            report=launch.collect(out,root/'published',interrupted=True)
            self.assertTrue(report['interrupted_declared'])
            self.assertEqual(json.loads((root/'published/STATE.json').read_text())['status'],'running')

    def test_collection_never_overwrites_existing_publication(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);out=root/'out';out.mkdir();target=root/'published';target.mkdir()
            with self.assertRaises(launch.Refusal):launch.collect(out,target)

    def test_collection_does_not_follow_symlinks(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);out=root/'out';out.mkdir()
            (out/'STATE.json').write_text(json.dumps(dict(status='complete')))
            (root/'outside').write_bytes(b'outside');(out/'link').symlink_to(root/'outside')
            with self.assertRaises(launch.Refusal):launch.collect(out,root/'published')

    def test_zero_exit_requires_nonempty_regular_outputs(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);(root/'stdout.log').write_bytes(b'');(root/'stderr.log').write_bytes(b'')
            run=dict(required_outputs=['trace.txt'])
            with self.assertRaises(launch.Refusal):launch.postflight(root,run)
            (root/'trace.txt').write_bytes(b'')
            with self.assertRaises(launch.Refusal):launch.postflight(root,run)
            (root/'trace.txt').write_bytes(b'time voltage\n0 0\n')
            self.assertEqual(launch.postflight(root,run)[0]['path'],'trace.txt')

    def test_zero_exit_with_fatal_simulator_log_is_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);(root/'stdout.log').write_bytes(b'');(root/'stderr.log').write_bytes(b'')
            (root/'trace.txt').write_bytes(b'partial trace')
            (root/'simulator.log').write_bytes(b'tran simulation(s) aborted\n')
            with self.assertRaises(launch.Refusal):
                launch.postflight(root,dict(required_outputs=['trace.txt'],diagnostic_logs=['simulator.log']))

    def test_collection_destination_inside_evidence_is_refused_before_creation(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);(root/'STATE.json').write_text(json.dumps(dict(status='complete')))
            target=root/'nested-publication'
            with self.assertRaises(launch.Refusal):launch.collect(root,target)
            self.assertFalse(target.exists())

    def test_small_estimates_cannot_hide_timeouts_over_budget(self):
        runs=[dict(estimate_s=1,timeout_s=7200),dict(estimate_s=1,timeout_s=7200)]
        with self.assertRaises(launch.Refusal):launch.check_budget(runs,14400)
        self.assertEqual(launch.check_budget([dict(estimate_s=2,timeout_s=5)],15)['execution_and_cleanup_cap_s'],15)

    def test_nonfinite_runtime_and_budget_values_refused(self):
        for value in (float('nan'),float('inf'),-1,True):
            with self.subTest(value=value):
                with self.assertRaises(launch.Refusal):launch.check_budget([dict(estimate_s=1,timeout_s=2)],value)
                with self.assertRaises(launch.Refusal):launch.check_budget([dict(estimate_s=value,timeout_s=2)],30)
                with self.assertRaises(launch.Refusal):launch.check_budget([dict(estimate_s=1,timeout_s=value)],30)

    def ci_fixture(self, extra=None, job_status='success', head='a'*40, attempts=2):
        run=dict(id=7,workflow_id=3,name='Lean',run_attempt=attempts,head_sha=head,status='completed',conclusion='success',html_url='https://example.invalid/run/7')
        def get(path):
            if path.startswith('actions/runs?'):
                return dict(workflow_runs=[run]+([extra] if extra else []))
            self.assertIn('/attempts/'+str(attempts)+'/jobs',path)
            return dict(jobs=[dict(id=9,name='lean',status='completed',conclusion=job_status)])
        return dict(kind='registered',source_commit='a'*40,expected_workflows=['Lean']),get

    def test_ci_uses_exact_head_and_latest_attempt_jobs(self):
        m,get=self.ci_fixture();report=launch.live_ci_gate(m,get)
        self.assertEqual(report['head_sha'],'a'*40)
        self.assertEqual(report['workflows'][0]['run_attempt'],2)

    def test_parent_success_does_not_pass_ci(self):
        m,get=self.ci_fixture(head='b'*40)
        with self.assertRaises(launch.Refusal):launch.live_ci_gate(m,get)

    def test_successful_run_with_failed_job_refused(self):
        m,get=self.ci_fixture(job_status='failure')
        with self.assertRaises(launch.Refusal):launch.live_ci_gate(m,get)

    def test_extra_failed_workflow_is_not_ignored(self):
        extra=dict(id=8,workflow_id=4,name='Extra',run_attempt=1,head_sha='a'*40,status='completed',conclusion='failure',html_url='https://example.invalid/extra')
        m,get=self.ci_fixture(extra=extra)
        with self.assertRaises(launch.Refusal):launch.live_ci_gate(m,get)

    def test_missing_expected_workflow_refused(self):
        m,get=self.ci_fixture();m['expected_workflows'].append('Physical')
        with self.assertRaises(launch.Refusal):launch.live_ci_gate(m,get)

    def test_unlisted_committed_runtime_change_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            repo=Path(tmp)
            def git(*args):
                return subprocess.check_output(['git',*args],cwd=repo,stderr=subprocess.DEVNULL).decode().strip()
            git('init');git('config','user.name','Synthetic');git('config','user.email','synthetic@example.invalid')
            (repo/'runner.py').write_text('print(1)\n');git('add','.');git('commit','-m','source');source=git('rev-parse','HEAD')
            (repo/'hidden_import.py').write_text('changed = True\n');git('add','.');git('commit','-m','unlisted runtime')
            with self.assertRaises(launch.Refusal):
                launch.runtime_unchanged(repo,dict(source_commit=source,marker_path='RUN_ATTEMPT.json'),'manifest.json','HEAD')

    def test_protocol_cannot_change_during_implementation(self):
        with tempfile.TemporaryDirectory() as tmp:
            repo=Path(tmp)
            def git(*args):
                return subprocess.check_output(['git',*args],cwd=repo,stderr=subprocess.DEVNULL).decode().strip()
            git('init');git('config','user.name','Synthetic');git('config','user.email','synthetic@example.invalid')
            original=b'Frozen before implementation\n'
            (repo/'PROTOCOL.md').write_bytes(original);git('add','.');git('commit','-m','protocol')
            (repo/'PROTOCOL.md').write_bytes(b'Changed after protocol\n');git('add','.');git('commit','-m','implementation')
            m=dict(protocol_path='PROTOCOL.md',source_commit=git('rev-parse','HEAD'))
            with self.assertRaises(launch.Refusal):launch.unchanged_protocol(repo,m,original)
            (repo/'PROTOCOL.md').write_bytes(original)
            with self.assertRaises(launch.Refusal):launch.unchanged_protocol(repo,m,original)

    def test_pinned_environment_is_ngspice42_not_phase0_44(self):
        self.assertEqual(launch.EXPECTED['ngspice_version'],'42')
        self.assertEqual(launch.EXPECTED['python_version'],'3.12.14')
        self.assertEqual(launch.EXPECTED['numpy_version'],'2.3.5')
        self.assertEqual(len(launch.EXPECTED['ngspice_sha256']),64)


if __name__=='__main__':unittest.main()
