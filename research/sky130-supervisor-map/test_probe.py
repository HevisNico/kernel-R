"""Focused guards for physical evidence extraction; no circuit reruns."""
import gzip
import hashlib
import json
from pathlib import Path
import tempfile
import unittest

import numpy as np

from analyze_saved import native_charge, summarize, classify_action
from probe import analyze, deck, integral


class ProbeTests(unittest.TestCase):
    def test_maintenance_fire_is_never_counted_as_a_service(self):
        a = classify_action(dict(amplitude=.95,service_success=True))
        self.assertTrue(a['pulse_fired_in_window'])
        self.assertFalse(a['requested_service'])
        self.assertIsNone(a['service_success'])

    def test_stimulus_is_visible_inside_ports_and_two_slots_preserve_service_period(self):
        s, starts, stop = deck(dict(name='test', vinit=.384, rlk=1e11, actions=[1, 0, 1]))
        self.assertIn('.global ksen krst kpreb amp', s)
        self.assertIn('v(amp)*{ipk}', s)
        self.assertIn('vdose writefeed sum 0', s)
        self.assertAlmostEqual(starts[2]-starts[0], 440e-6)
        self.assertAlmostEqual(starts[1]-starts[0], 220e-6)
        self.assertGreater(stop, starts[-1]+40e-6)

    def test_ringing_endpoints_cannot_be_silently_counted_as_delivered_charge(self):
        d = np.zeros((5, 10)); d[:, 0] = np.arange(5); d[:, 8] = [1,-1,1,-1,1]
        # A partial interval fabricates a nonzero integral from a zero-charge
        # alternating sequence; native integration exposes the omitted span.
        self.assertNotAlmostEqual(integral(d, 'i(v.x1.vdose)', .25, 4), 0)
        q = native_charge(d, .25, 4)
        self.assertEqual(q['charge_C'], 0)
        self.assertEqual(q['omitted_s'], .75)

    def test_late_fire_does_not_repair_service_failure(self):
        d = np.zeros((8,10)); d[:, 0] = np.array([0,439,444,464,465,470,879,880])*1e-6
        d[:,1] = .384; d[:,2] = 1.25; d[:,4] = .4
        d[4:,3] = 1.8
        r = analyze(d,dict(actions=[1],rlk=1e11),[444e-6],880e-6)
        self.assertFalse(r['actions'][0]['service_success'])
        self.assertEqual(len(r['actions'][0]['fire_times_s']),1)

    def test_incomplete_waveform_is_rejected(self):
        d = np.zeros((2,10)); d[:,0] = [0,.0001]
        with self.assertRaises(AssertionError):
            analyze(d,dict(actions=[1],rlk=1e11),[444e-6],880e-6)

    def test_unfinished_attempt_is_not_dropped(self):
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp)/'case'; p.mkdir()
            (p/'metadata.json').write_text(json.dumps(dict(status='running')))
            with self.assertRaisesRegex(ValueError, 'Unfinished'):
                summarize(Path(tmp))

    def test_corrupt_trace_rejected_before_extraction(self):
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp)/'case'; p.mkdir()
            data = gzip.compress(b'0 0\n',mtime=0)
            m = dict(case={},status='complete',wall_s=1,ngspice_sha256='x',pdk_commit='p',source_sha256={},deck_sha256='d',trace_sha256=hashlib.sha256(data).hexdigest())
            (p/'metadata.json').write_text(json.dumps(m))
            (p/'trace.txt.gz').write_bytes(data+b'X')
            with self.assertRaisesRegex(ValueError,'SHA256'):
                summarize(Path(tmp))


if __name__ == '__main__':
    unittest.main()
