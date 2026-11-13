"""Frozen repetition plan and exact-binomial analysis; never launches SPICE.

Endpoint flags must come from an independently audited extractor. This module
checks their ledger and computes statistical bounds; it does not validate the
physical/model premises, the noise generator, or the supplied evidence hashes.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE_SHA256 = '01a28a9149bc1f8caa0f4bba1690dde47ccacfb87b727f41f8caac9741f56419'
SOURCE_COMMIT = '7ded279f103dab5beb6c1c671f1acbdf4cff18c0'
K = 100
ALPHA = 0.05
NGSPICE_SHA256 = '820658317b0b54035208da41936fd6871ce924036e5ea4113a4168b821b7fc45'
PDK_COMMIT = '1232782c1b9fab3aacda74d67ce7c92bf7da8105'
ENDPOINTS = ('count_agreement', 'measured_residual_success', 'joint_success')


class PlanError(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise PlanError(message)


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), allow_nan=False).encode()


def sha(data):
    return hashlib.sha256(data).hexdigest()


def hash_string(value):
    return isinstance(value, str) and len(value) == 64 and all(c in '0123456789abcdef' for c in value)


def frozen_source(path=HERE / 'campaign-validation.json'):
    raw = Path(path).read_bytes()
    require(sha(raw) == SOURCE_SHA256, 'frozen campaign report hash mismatch')
    source = json.loads(raw)
    require(source['source_commit'] == SOURCE_COMMIT, 'campaign revision mismatch')
    keys = source['eligible_keys']
    require(len(keys) == 37 and len({tuple(k) for k in keys}) == 37,
            'exactly 37 distinct original eligible ports required')
    require(keys == sorted(keys) and len({c for c, p in keys}) == 35,
            'ordered original 35-cell cohort required')
    require(source['counts']['status3'] == 37, 'original status-3 scope')
    return source


def make_plan(source):
    # Source is accepted only through frozen_source by the CLI. This check also
    # prevents library callers from substituting a newly selected cohort.
    require(source == frozen_source(), 'plan source must equal frozen report')
    grouped = {}
    for cell, port in source['eligible_keys']:
        grouped.setdefault(cell, []).append(port)
    runs = []
    for repeat in range(1, K + 1):
        for cell, ports in sorted(grouped.items()):
            runs.append(dict(trial_id=f'cell{cell}_repeat{repeat:03d}', cell=cell,
                             mismatch_seed=cell, noise_seed=1000000 + 10000 * repeat + cell,
                             repeat_id=repeat, eligible_ports=ports))
    return dict(schema=1, status='NOT_STARTED', repetitions_per_port=K,
                campaign_report_sha256=SOURCE_SHA256, source_commit=SOURCE_COMMIT,
                source_snapshot_sha256=source['snapshot_sha256'],
                eligible_keys=source['eligible_keys'], complete_train_runs=len(runs),
                eligible_port_trials=37 * K,
                readiness_blockers=['Pinned ngspice binary unavailable locally',
                                    'Pinned SKY130 PDK unavailable locally',
                                    'External seeded noise injection UNIMPLEMENTED',
                                    'Noise replay/independence preflight NOT_RUN',
                                    'Per-run residual endpoint extractor NOT_IMPLEMENTED'],
                runtime=dict(ngspice_sha256=NGSPICE_SHA256, pdk_commit=PDK_COMMIT,
                             max_step_ns=200, noise_sample_ns=400, temperature_C=27),
                noise=dict(injection='external_seeded_UNIMPLEMENTED',
                           amplitudes='unchanged pinned research/circuit/noise.json',
                           correlations='preserve original shared channels; do not split by port',
                           seed_supported_by_existing_simulator_wrapper=False),
                frozen_parameters=['D', 'DE', 'kappa', 'd0', 'm', 'ell3',
                                   'status3 eligibility', 'endpoint thresholds'],
                alpha_per_port=ALPHA, alpha_per_port_simultaneous=ALPHA / 37,
                statistical_unit='one complete train per cell and repeat', runs=runs)


def binomial_upper_tail(n, successes, probability):
    """P[X >= successes] for X~Binomial(n, probability), no SciPy."""
    require(type(n) is int and 0 <= n <= 1000, 'binomial n outside supported range')
    require(type(successes) is int and 0 <= successes <= n, 'invalid success count')
    require(0 <= probability <= 1 and math.isfinite(probability), 'invalid probability')
    if successes == 0:
        return 1.0
    if probability == 0:
        return 0.0
    if probability == 1:
        return 1.0
    return min(1.0, math.fsum(math.comb(n, j) * probability ** j *
                             (1 - probability) ** (n - j)
                             for j in range(successes, n + 1)))


def cp_lower(successes, n, alpha=ALPHA):
    """One-sided Clopper-Pearson lower bound, binomial-tail inversion.

    'Exact' denotes the binomial construction, not exact real arithmetic.
    Bisection uses float arithmetic; return its lower endpoint. K=100 is fixed.
    """
    require(type(n) is int and 0 < n <= 1000 and type(successes) is int and 0 <= successes <= n,
            'invalid CP counts')
    require(0 < alpha < 1 and math.isfinite(alpha), 'invalid CP alpha')
    if successes == 0:
        return 0.0
    lo, hi = 0.0, 1.0
    for _ in range(80):
        mid = (lo + hi) / 2
        if mid == lo or mid == hi:
            break
        if binomial_upper_tail(n, successes, mid) < alpha:
            lo = mid
        else:
            hi = mid
    return lo


def analyse(plan, payload):
    """Require the full planned ledger. Failed runs count as failures.

    Count and residual flags are distinct supplied observations; their joint
    event is primary. No simulated or physical result is created here.
    """
    require(plan == make_plan(frozen_source()), 'analysis requires the unchanged frozen plan')
    require(payload.get('plan_sha256') == sha(canonical(plan)), 'record/plan hash mismatch')
    require(hash_string(payload.get('endpoint_extractor_sha256')), 'extractor identity required')
    records = payload.get('records')
    require(isinstance(records, list) and len(records) == len(plan['runs']), 'complete record ledger required')
    expected = {r['trial_id']: r for r in plan['runs']}
    seen, noise_hashes, successes, failures = set(), set(), {}, []
    for cell, port in plan['eligible_keys']:
        successes[cell, port] = dict.fromkeys(ENDPOINTS, 0)
    for record in records:
        require(isinstance(record, dict), 'record must be an object')
        trial = record.get('trial_id')
        require(trial in expected and trial not in seen, 'unknown or duplicate trial')
        seen.add(trial)
        run = expected[trial]
        require(all(type(record.get(k)) is int and record[k] == run[k] for k in
                    ('cell', 'mismatch_seed', 'noise_seed', 'repeat_id')), 'trial identity mismatch')
        status = record.get('status')
        require(status in ('done', 'failed'), 'explicit done/failed status required')
        if status == 'failed':
            require(isinstance(record.get('reason'), str) and record['reason'].strip(), 'failure reason required')
            require(record.get('outcomes') == [], 'failed run must not claim successful outcomes')
            failures.append(dict(trial_id=trial, reason=record['reason']))
            continue
        require(record.get('runtime') == plan['runtime'], 'runtime identity mismatch')
        require(hash_string(record.get('trace_sha256')) and hash_string(record.get('noise_waveform_sha256')),
                'trace and realized-noise identities required')
        require(record['noise_waveform_sha256'] not in noise_hashes, 'realized noise waveform reused across trials')
        noise_hashes.add(record['noise_waveform_sha256'])
        outcomes = record.get('outcomes')
        require(isinstance(outcomes, list) and all(isinstance(o, dict) for o in outcomes), 'outcomes required')
        require(all(type(o.get('port')) is int for o in outcomes) and
                [o['port'] for o in outcomes] == run['eligible_ports'], 'exact eligible port outcomes required')
        for outcome in outcomes:
            require(type(outcome.get('count_agreement')) is bool and
                    type(outcome.get('measured_residual_success')) is bool, 'two distinct Boolean endpoints required')
            counts = successes[run['cell'], outcome['port']]
            count, residual = outcome['count_agreement'], outcome['measured_residual_success']
            counts['count_agreement'] += count
            counts['measured_residual_success'] += residual
            counts['joint_success'] += count and residual
    require(seen == set(expected), 'missing trials')
    per_port = []
    for (cell, port), counts in sorted(successes.items()):
        endpoints = {key: dict(successes=s, trials=K, lower95=cp_lower(s, K),
                              simultaneous_lower95=cp_lower(s, K, ALPHA / 37))
                     for key, s in counts.items()}
        per_port.append(dict(cell=cell, port=port, endpoints=endpoints))
    mean_lower = {key: math.fsum(r['endpoints'][key]['simultaneous_lower95']
                               for r in per_port) / 37 for key in ENDPOINTS}
    return dict(status='RECORDS_ANALYSED_NOT_PHYSICALLY_VALIDATED', plan_sha256=sha(canonical(plan)),
                complete_runs=len(records), eligible_port_trials=37 * K, failed_runs=failures,
                per_port=per_port, mean_simultaneous_lower95=mean_lower,
                primary_endpoint='joint_success',
                scope='Each endpoint family has its own 95% simultaneous coverage over 37 fixed ports; '
                      'no combined 95% claim across all three families, no iid pooling of 3700 observations.',
                assumptions=['Independent identically distributed repeats within each fixed port/stratum.',
                             'Audited endpoint extraction and faithful recorded runtime/noise identities.',
                             'No claim of independence between ports in the same train.',
                             'No validation of the noise generator or physical error model by this analysis.'])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write-plan', type=Path)
    parser.add_argument('--records', type=Path)
    parser.add_argument('--report', type=Path)
    args = parser.parse_args()
    plan = make_plan(frozen_source())
    if args.write_plan:
        args.write_plan.write_text(json.dumps(plan, indent=2) + '\n')
    output = analyse(plan, json.loads(args.records.read_text())) if args.records else {
        k: v for k, v in plan.items() if k != 'runs'}
    if args.report:
        args.report.write_text(json.dumps(output, indent=2) + '\n')
    print(json.dumps(output, indent=2))


if __name__ == '__main__':
    main()
