"""Summarize already committed refresh evidence; never invoke a simulator.

Run from any directory. --check compares both saved outputs without rewriting
them. Only the historical inputs enumerated below are read.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
from pathlib import Path
import re
from statistics import mean

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
CIRCUIT = REPO / 'research/circuit'
PERIOD_SECONDS = 440e-6
NOMINAL_DOSE_MV = 1.3465
REFRESH_NAMES = (
    'refresh_lk11', 'refresh_lk11_nz', 'refresh_lk12',
    *(f'refresh_mm_{seed}' for seed in range(3001, 3009)),
    'refresh_none', 'refresh_none_nz',
)
RUNTIME_NAMES = (
    'nominal_200ns_retry1', 'nominal_100ns_retry1',
    'mm2064_quiet_retry1', 'mm2064_noise_1_retry1', 'mm2064_noise_2_retry1',
)


def build():
    sources = {}

    def read(path):
        data = path.read_bytes()
        sources[path.relative_to(REPO).as_posix()] = hashlib.sha256(data).hexdigest()
        return data.decode()

    cell = read(CIRCUIT / 'cell.spice')
    assert 'tper=440u' in cell, 'Revisit the period conversion if the circuit changes'
    calibration = json.loads(read(REPO / 'research/adaptive-refresh-experiment/refresh-calibration.json'))
    assert calibration['period_seconds'] == PERIOD_SECONDS
    assert calibration['nominal_dose_mV'] == NOMINAL_DOSE_MV
    read(REPO / 'research/adaptive-refresh-experiment/calibrate_refresh.py')
    read(CIRCUIT / 'run.py')
    read(Path(__file__).resolve())
    records = {}
    for name in REFRESH_NAMES:
        path = CIRCUIT / 'results' / (name + '.csv')
        rows = list(csv.DictReader(read(path).splitlines()))
        assert [int(row['pulse']) for row in rows] == list(range(len(rows)))
        first = next(i for i, row in enumerate(rows) if int(row['fired']))
        tail = rows[first:]
        silent = [int(row['pulse']) for row in tail if not int(row['fired'])]
        losses = [-float(row['step1_mV']) for row in tail if int(row['fired'])]
        writes = [float(row['step1_mV']) for row in tail if not int(row['fired'])]
        volts = [float(row['vmem1']) for row in tail]
        gaps = [b-a for a, b in zip(silent, silent[1:])]
        old = calibration['results'][name]
        assert old['sha256'] == sources[path.relative_to(REPO).as_posix()]
        assert old['first_fire'] == first and old['relapses'] == silent
        assert old['gaps'] == gaps and old['loss_mean_mV'] == mean(losses)
        records[name] = {
            'source': path.relative_to(REPO).as_posix(),
            'total_periods': len(rows), 'first_fire_index_zero_based': first,
            'initial_training_silences': first, 'post_first_fire_periods': len(tail),
            'missed_service_periods_after_first_fire': len(silent),
            'silent_indices_zero_based': silent, 'relapse_gaps_periods': gaps,
            'mean_relapse_gap_periods': mean(gaps) if gaps else None,
            'firing_loss_proxy_mV': {'min': min(losses), 'mean': mean(losses), 'max': max(losses)},
            'silent_net_increment_mV': {'min': min(writes), 'mean': mean(writes), 'max': max(writes)} if writes else None,
            'inferred_gross_dose_mV': mean(writes)+mean(losses) if writes else None,
            'loss_proxy_in_220_unit_scale': 220*mean(losses)/NOMINAL_DOSE_MV,
            'end_of_period_vmem_range_V': [min(volts), max(volts)],
            'end_of_period_vmem_swing_nominal_doses': (max(volts)-min(volts))*1000/NOMINAL_DOSE_MV,
        }
    runtimes = []
    for name in RUNTIME_NAMES:
        directory = CIRCUIT / 'bridge_check/runs' / name
        meta_path, deck_path = directory/'metadata.json', directory/'input.spice'
        meta = json.loads(read(meta_path))
        deck = read(deck_path)
        assert meta['status'] == 'produced_trace' and meta['returncode'] == 0
        assert meta['deck_sha256'] == sources[deck_path.relative_to(REPO).as_posix()]
        match = re.search(r'^tran\s+\S+\s+([\d.e+-]+)\s+0\s+([\d.e+-]+)\s*$', deck, re.MULTILINE)
        assert match, 'Unexpected historical transient command'
        horizon, step = map(float, match.groups())
        periods = round(horizon/PERIOD_SECONDS)
        assert abs(horizon-periods*PERIOD_SECONDS) < 1e-12
        elapsed = meta['finished_unix']-meta['started_unix']
        assert elapsed > 0
        runtimes.append({
            'name': name, 'metadata_source': meta_path.relative_to(REPO).as_posix(),
            'deck_source': deck_path.relative_to(REPO).as_posix(),
            'ngspice_version': meta['ngspice_version'], 'ngspice_sha256': meta['ngspice_sha256'],
            'noise': meta['run']['noise'], 'transient_seconds': horizon,
            'calendar_periods': periods, 'max_step_seconds': step,
            'started_unix': meta['started_unix'], 'finished_unix': meta['finished_unix'],
            'wall_seconds': elapsed, 'wall_seconds_per_period': elapsed/periods,
            'linear_200_period_minutes': elapsed/periods*200/60,
        })
    slow = max(row['wall_seconds_per_period'] for row in runtimes)
    return {
        'kind': 'descriptive phase-0 analysis of previously saved evidence; no new trajectory',
        'period_seconds': PERIOD_SECONDS, 'nominal_dose_mV': NOMINAL_DOSE_MV,
        'refresh': records, 'historical_runtimes': runtimes,
        'illustrative_runtime_projection': {
            'basis': 'slowest of five historical wall-time-per-period ratios; no local throughput guarantee',
            'periods_per_sequence': 200, 'sequences': 8,
            'serial_hours_without_margin': slow*200*8/3600,
            'ideal_two_machine_hours_without_margin': slow*200*8/7200,
        },
        'limitations': [
            'Finite observed extrema are not uniform physical bounds.',
            'Post-first-FIRE counts exclude initial training failures.',
            'Voltage readings are end-of-period averages, not the state at service arrival.',
            'Gross dose is inferred by adding mean firing drift to silent net increment; it is not independently integrated.',
            'Noisy period differences mix observation noise with drift and can be negative.',
            'Observed Vmem ranges do not establish physical storage capacity.',
            'Historical runtime includes host contention; four runs started together and a fifth repeat started later.',
            'No maintenance action, sensor bound, new scheduling threshold, or physical cost is certified here.',
        ],
        'source_sha256': dict(sorted(sources.items())),
    }


def markdown(report):
    lines = [
        '# Previously saved evidence for the SKY130 supervisor map', '',
        'This is a descriptive phase-0 read of historical records. No simulator or',
        'controller is run. Regenerate or verify from the repository root:', '',
        '```sh', 'python3 -B research/sky130-supervisor-map/saved_evidence.py',
        'python3 -B research/sky130-supervisor-map/saved_evidence.py --check', '```', '',
        '[SAVED_EVIDENCE.json](SAVED_EVIDENCE.json) contains every silent index,',
        'gap, range, timing, and SHA-256 of every input used here.', '',
        '## Service loss and voltage proxies', '',
        '| Saved record | Periods from first FIRE | Silent service periods | Mean loss proxy (mV/period) | Inferred gross dose (mV) |',
        '|---|---:|---:|---:|---:|',
    ]
    for name, row in report['refresh'].items():
        dose = row['inferred_gross_dose_mV']
        lines.append(f"| {name} | {row['post_first_fire_periods']} | {row['missed_service_periods_after_first_fire']} | {row['firing_loss_proxy_mV']['mean']:.6f} | {f'{dose:.6f}' if dose is not None else 'none'} |")
    nominal = report['refresh']['refresh_lk11']
    lines += ['',
        f"At 0.1 Tohm, the first FIRE is pulse index {nominal['first_fire_index_zero_based']} (zero based).",
        f"The later silent indices are {nominal['silent_indices_zero_based']}, with gaps",
        f"{nominal['relapse_gaps_periods']}. A silent service period is a failure even",
        'though it also recharges the cell. The initial training silences are excluded',
        'from the table and require an explicit service-start convention.', '',
        'The firing-period loss proxy is the negative of the recorded full-period',
        '`step1_mV`. The silent step is a **net** increment. Adding the mean firing',
        'loss gives an inferred gross dose under a comparable-drift assumption, not',
        'a separate delivered-charge measurement. Using that net increment as a',
        'gross dose would subtract leakage twice.', '',
        'The voltage is an end-of-period average. Its range is not capacity, and',
        'noisy differences are not instantaneous leakage measurements. These data',
        'supply neither a service threshold at pulse arrival nor a sensor-error',
        'bound. Finite extrema do not establish universal bounds.', '',
        '## Historical runtime, before a local estimate', '',
        '| Saved replay | Max step (ns) | Calendar periods | Wall seconds | Linear 200-period estimate (minutes) |',
        '|---|---:|---:|---:|---:|',
    ]
    for row in report['historical_runtimes']:
        lines.append(f"| {row['name']} | {row['max_step_seconds']*1e9:g} | {row['calendar_periods']} | {row['wall_seconds']:.2f} | {row['linear_200_period_minutes']:.2f} |")
    projection = report['illustrative_runtime_projection']
    lines += ['',
        'The successful ngspice42 replays simulated 0.00968 seconds each. Four',
        'started together on the historical host; the second noisy repeat started',
        'later. Millisecond failed starts that produced no transient are excluded.',
        f"At the slowest saved rate, eight 200-period sequences cost {projection['serial_hours_without_margin']:.2f}",
        f"serial hours, or {projection['ideal_two_machine_hours_without_margin']:.2f} hours under ideal two-machine balancing,",
        '**before any reserve**. These are extrapolations, not current-host budget',
        'guarantees. Two policies count as two sequences. Added maintenance pulses',
        'and waveform instrumentation may change runtime. A local representative',
        'timing plus an explicit margin must replace this estimate before preregistration.', '',
        '## Cost and state conventions still to fix', '',
        'Count mandatory service pulses, maintenance attempts, actual writes, analog',
        'observations, preparation and elapsed service periods separately. A firing',
        'maintenance attempt still costs an action. The old weights probe1/write10',
        'are discrete prices, not transistor energy; an energy claim requires supply',
        'power integration including idle/bias and observer overhead.', '',
        'Any prudent comparison needs the same service schedule, physical action',
        'library, hard boundary, initial state and terminal-inventory convention.',
        'Inserting maintenance within a former 440-us period also changes main-charge',
        'recovery. The old pre-pulse rest band must not be imported without checking',
        '`vq` and the protection state under the new schedule.', '',
    ]
    return '\n'.join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    report = build()
    outputs = {
        'SAVED_EVIDENCE.json': json.dumps(report, indent=2, sort_keys=True)+'\n',
        'SAVED_EVIDENCE.md': markdown(report),
    }
    for name, content in outputs.items():
        path = HERE/name
        if args.check:
            assert path.read_bytes() == content.encode(), name+' does not reproduce'
        else:
            path.write_bytes(content.encode())
    print('PASS: 13 historical refresh records and five runtime records; no new trajectory')


if __name__ == '__main__':
    main()
