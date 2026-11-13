"""Read phase-0 waveforms, retain failures, and expose numerical limitations."""
import argparse
import gzip
import hashlib
import io
import json
from pathlib import Path

import numpy as np

from probe import HERE, COL, at, integral, analyze, deck


def classify_action(action):
    action = {k:v for k,v in action.items() if k not in ('gross_write_C','gross_write_mV')}
    pulse_fired = action['service_success']
    requested = action['amplitude'] == 1.0
    action.update(pulse_fired_in_window=pulse_fired, requested_service=requested,
                  service_success=pulse_fired if requested else None)
    return action


def native_charge(d, lo, hi):
    """Only complete native solver intervals: no interpolated ringing endpoint.

    This is a finite-step diagnostic, not an enclosure of the missing tails.
    Both covered span and omitted duration must accompany the integral.
    """
    mask = (d[:-1, 0] >= lo) & (d[1:, 0] <= hi)
    dt = np.diff(d[:, 0])[mask]
    v = d[:, COL['i(v.x1.vdose)']]
    return dict(charge_C=float(np.sum(dt*(v[:-1][mask]+v[1:][mask])/2)),
                covered_s=float(np.sum(dt)), omitted_s=float(hi-lo-np.sum(dt)))


def summarize(out):
    attempts, files = [], []
    for path in sorted(out.glob('*/metadata.json')):
        m = json.loads(path.read_text())
        if m['status'] == 'running':
            raise ValueError('Unfinished exploratory attempt: '+path.parent.name)
        record = {k: m[k] for k in ('case', 'status', 'wall_s', 'ngspice_sha256',
                                   'pdk_commit', 'source_sha256', 'deck_sha256')}
        if m['status'] != 'complete':
            record['error'] = m['error']
            attempts.append(record)
            continue
        trace = path.parent/'trace.txt.gz'
        raw = trace.read_bytes()
        sha = hashlib.sha256(raw).hexdigest()
        if sha != m['trace_sha256']:
            raise ValueError('Trace SHA256 mismatch: '+trace.name)
        files.append(dict(path='generated/'+trace.relative_to(out).as_posix(), bytes=len(raw), sha256=sha))
        d = np.loadtxt(io.BytesIO(gzip.decompress(raw)))
        _, starts, stop = deck(m['case'])
        recomputed = analyze(d, m['case'], starts, stop)
        if recomputed != m['result']:
            raise ValueError('Waveform-derived observations differ from metadata: '+path.parent.name)
        actions = []
        for a in recomputed['actions']:
            # The first exploratory extractor integrated arbitrary endpoints of
            # a trapezoid-ringing current. Never present that result as a dose.
            a = classify_action(a)
            lo = a['start_s']-4.1e-6
            hi = lo+(220e-6 if len(m['case']['actions']) > 1 else 440e-6)
            a['native_slot_charge'] = native_charge(d, lo, hi)
            a['native_slot_charge_mV'] = a['native_slot_charge']['charge_C']/30e-12*1000
            a['slot_vsum_change_mV'] = 1000*(at(d, 'v(x1.sum)', hi)-at(d, 'v(x1.sum)', lo))
            a['slot_resistor_loss_mV'] = integral(d, 'v(x1.sum)', lo, hi)/m['case']['rlk']/30e-12*1000
            a['slot_vmem_gain_mV'] = 1000*(at(d, 'v(vmem1)', lo)-at(d, 'v(vmem1)', hi))
            a['net_plus_resistor_mV'] = a['slot_vmem_gain_mV']+a['slot_resistor_loss_mV']
            # This last proxy is explicitly not an independent charge measure.
            actions.append(a)
        record['result'] = {**m['result'], 'actions': actions}
        if not actions:
            lo, hi = 440e-6, m['result']['simulated_s']
            record['result']['idle_period'] = dict(
                vmem_loss_mV=1000*(at(d, 'v(vmem1)', hi)-at(d, 'v(vmem1)', lo)),
                resistor_loss_mV=integral(d, 'v(x1.sum)', lo, hi)/m['case']['rlk']/30e-12*1000,
                supply_energy_J=-1.8*integral(d, 'i(vdd)', lo, hi))
        record['trace_sha256'] = sha
        attempts.append(record)
    return dict(scope='exploratory nominal TT, 27 C, no noise; not a certificate or jump campaign',
                attempts=attempts,
                numerical_warning='Current endpoint interpolation on trapezoid ringing is not a reliable dose. Native-slot integration omits reported tails; net-plus-resistor is only a proxy. Neither is a uniform bound.',
                raw_files=files)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--generated', type=Path, default=HERE/'generated')
    p.add_argument('--check', action='store_true')
    p.add_argument('--check-traces', action='store_true', help='Compare replay hashes, ignoring new wall timings and historical failed setup attempts')
    args = p.parse_args()
    result = summarize(args.generated)
    target = HERE/'RESULTS.json'
    if args.check_traces:
        assert json.loads(target.read_text())['raw_files'] == result['raw_files'], 'Waveform inventory or hashes changed'
        print('PASS: exact replay waveform inventory and SHA256 fingerprints')
    elif args.check:
        assert json.loads(target.read_text()) == result, 'Saved evidence summary changed'
        print('PASS: all retained attempts, waveform SHA256 and extracted action map')
    else:
        target.write_text(json.dumps(result, indent=2)+'\n')


if __name__ == '__main__':
    main()
