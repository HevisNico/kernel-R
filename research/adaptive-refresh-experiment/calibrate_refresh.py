"""Post-experiment descriptive calibration from existing circuit CSVs only.
No ngspice invocation, new trajectory, parameter fitting loop or v2 retuning.
"""
import csv
import hashlib
import json
from pathlib import Path
from statistics import mean

ROOT=Path(__file__).resolve().parent
CIRCUIT=ROOT.parent/'circuit'
NOMINAL_DOSE_MV=1.3465  # circuit/PREDICTION.md; not the leaky net step
PERIOD_SECONDS=440e-6  # circuit/run.py TPER; TU=20us is a different unit


def summarize(path):
    with path.open(newline='') as f:
        rows=list(csv.DictReader(f))
    assert [int(r['pulse']) for r in rows]==list(range(len(rows)))
    first=next(i for i,r in enumerate(rows) if int(r['fired']))
    tail=rows[first:]
    rel=[int(r['pulse']) for r in tail if not int(r['fired'])]
    losses=[-float(r['step1_mV']) for r in tail if int(r['fired'])]
    steps=[float(r['step1_mV']) for r in tail if not int(r['fired'])]
    gap=[b-a for a,b in zip(rel,rel[1:])]
    avg=mean(losses)
    # Inferring gross dose assumes the mean firing-period drift also applies
    # during a writing period; it is not a separate measurement of write charge.
    gross=mean(steps)+avg if steps else None
    return dict(source=str(path.relative_to(CIRCUIT)),sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                rows=len(rows),first_fire=first,relapses=rel,gaps=gap,
                mean_gap=mean(gap) if gap else None,firing_samples=len(losses),
                loss_min_mV=min(losses),loss_mean_mV=avg,loss_max_mV=max(losses),
                net_write_min_mV=min(steps) if steps else None,
                net_write_mean_mV=mean(steps) if steps else None,
                net_write_max_mV=max(steps) if steps else None,
                inferred_gross_write_mV=gross,
                inferred_balance_periods=gross/avg if gross and avg>0 else None,
                loss_in_220_unit_scale=220*avg/NOMINAL_DOSE_MV)


def main():
    paths=sorted((CIRCUIT/'results').glob('refresh_*.csv'))
    results={p.stem:summarize(p) for p in paths}
    a=results['refresh_lk11']; b=results['refresh_lk12']
    sources=['run.py','PREDICTION.md','analyze.py']
    report=dict(kind='descriptive post-experiment analysis of existing records',
                circuit_snapshot='ebaac53a49f2f904b9feb07e071c3b5af18746fa',
                nominal_dose_mV=NOMINAL_DOSE_MV,period_seconds=PERIOD_SECONDS,
                methods_sha256={p:hashlib.sha256((CIRCUIT/p).read_bytes()).hexdigest() for p in sources},
                results=results)
    (ROOT/'refresh-calibration.json').write_text(json.dumps(report,indent=2)+'\n')
    lines=['# R refresh calibration from existing records', '',
           'Descriptive analysis performed after the v2 experiment. No circuit run, v1/v2',
           'rerun or tuning was performed. This analysis does not change either protocol.', '',
           '## Method and units', '',
           '`circuit/run.py` defines a period as 440 microseconds; its 20-microsecond',
           'latency unit is different. `step1_mV = 1000*(previous_vmem1-current_vmem1)`:',
           'positive steps move toward higher gain. All recorded steps span a complete',
           'period. We use only periods at/after the first FIRE, exactly as the existing',
           '`refresh_view` analysis does. Silent periods thereafter are relapses.', '',
           'Leakage proxy = negative of the step on a firing period. A relapse step is',
           'the **net** write increment after that period\'s losses. An inferred gross dose',
           'adds the mean firing-period leakage proxy to the mean relapse increment.',
           'That addition assumes comparable drift in firing and writing periods; it',
           'does not measure the delivered write charge independently.', '',
           '| Record | Relapses | Mean gap (periods) | Mean leakage proxy (mV/period) | Mean net relapse step (mV) | Inferred gross dose (mV) |',
           '|---|---:|---:|---:|---:|---:|']
    fmt=lambda x:'—' if x is None else f'{x:.6f}'
    for name,r in results.items():
        lines.append(f'| {name} | {len(r["relapses"])} | {fmt(r["mean_gap"])} | {fmt(r["loss_mean_mV"])} | {fmt(r["net_write_mean_mV"])} | {fmt(r["inferred_gross_write_mV"])} |')
    lines += ['', '## Nominal 0.1 teraohm interpretation', '',
              f'Observed relapse gaps: {a["gaps"]}; mean {a["mean_gap"]:.6f} periods.',
              f'Observed firing-period loss proxy ranges from {a["loss_min_mV"]:.6f} to {a["loss_max_mV"]:.6f} mV,',
              f'with mean {a["loss_mean_mV"]:.9f} mV/period.',
              f'Net relapse step is {a["net_write_mean_mV"]:.6f} mV. The inferred gross dose is',
              f'{a["inferred_gross_write_mV"]:.9f} mV, close to the separately stated nominal dose 1.3465 mV.',
              f'The inferred gross-dose/leak ratio is {a["inferred_balance_periods"]:.6f} periods.',
              'Using 1.288 mV as both a net increment and an independent delivered dose would',
              'double-count leakage in a model that already subtracts it every period.', '',
              f'With 220 units representing the declared 1.3465 mV nominal dose, the mean loss',
              f'proxy is {a["loss_in_220_unit_scale"]:.6f} abstract units per period, versus the',
              'preregistered approximation 10. This is a voltage scale calibration only:',
              'it does not map the service floor 100, initial reserve 440 or capacity 660 to',
              'the physical two-port read specification.', '',
              'The 1-teraohm record supplies an independent consistency comparison:',
              f'gaps {b["gaps"]}, mean loss {b["loss_mean_mV"]:.9f} mV/period, inferred gross dose',
              f'{b["inferred_gross_write_mV"]:.9f} mV. Quantization/rounding is material at this smaller drift.', '',
              '## What this does not establish', '',
              '- Observed minima/maxima are finite-sample extrema, not universal physical bounds.',
              '- Noisy firing-step proxies can be negative; they combine read noise and drift.',
              '  They cannot be used directly as a nonnegative per-tick leakage oracle.',
              '- The CSVs summarize periods and do not certify intra-period safety, delivered',
              '  dose timing, a sensor error bound or the scalar-to-hybrid state correspondence.',
              '- These constant-leak runs do not establish B=10 over H=41 under temperature',
              '  changes, ageing or an injected leakage jump.',
              '- The next physical bridge must obtain waveform-based dose/loss enclosures,',
              '  justify the observer and state map, then preregister a transistor jump trial.', '',
              'The accompanying JSON records every source hash, relapse index, gap and range.',
              'Regenerate with `python3 -B calibrate_refresh.py`; this reads stored records only.', '']
    (ROOT/'R_CALIBRATION.md').write_text('\n'.join(lines))
    print(f'Analyzed {len(paths)} existing refresh CSVs; no new simulation.')


if __name__=='__main__':
    main()
