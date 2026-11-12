"""Apply the frozen finite-grid OLS rule, retaining every invalid sweep."""
import csv
import gzip
import json
from pathlib import Path
import numpy as np

HERE = Path(__file__).resolve().parent


def read_curve(folder, run):
    meta = json.loads((folder / 'metadata.json').read_text())
    if meta['status'] != 'produced_trace':
        raise ValueError(meta['status'])
    with gzip.open(folder / 'dc.txt.gz', 'rt') as fh:
        data = np.loadtxt(fh)
    if data.shape != (141, 3) or not np.isfinite(data).all():
        raise ValueError('invalid shape or nonfinite DC data')
    x = data[:, 1]
    if not np.allclose(x, np.linspace(.35, .42, 141), rtol=0, atol=1e-12):
        raise ValueError('voltage grid differs from protocol')
    gain = -data[:, 2] / run['input_A']
    if np.any(gain <= 0):
        raise ValueError('nonpositive gain')
    return x, np.log(gain)


def fit_reference(x, y):
    slope, intercept = np.linalg.lstsq(np.column_stack((x, np.ones(len(x)))), y, rcond=None)[0]
    beta = -float(slope)
    if not np.isfinite([beta, intercept]).all() or beta <= 0:
        raise ValueError('invalid or nonpositive log-gain slope')
    return beta, float(intercept)


def main():
    manifest = json.loads((HERE / 'gain_manifest.json').read_text())
    summaries, samples = [], []
    for temp in (-40, 27, 125):
        curves, failures = [], []
        for run in manifest['runs']:
            if run['temperature_C'] != temp:
                continue
            try:
                x, y = read_curve(HERE / 'gain_runs' / run['name'], run)
                curves.append((run, x, y))
            except (OSError, ValueError, KeyError) as exc:
                failures.append(dict(run=run['name'], reason=str(exc)))
        if failures:
            summaries.append(dict(temperature_C=temp, status='not_evaluable', failures=failures))
            continue
        reference = next(c for c in curves if c[0]['divisor'] == 1 and c[0]['vq_V'] == 1.25)
        try:
            beta, intercept = fit_reference(reference[1], reference[2])
        except ValueError as exc:
            summaries.append(dict(temperature_C=temp,status='not_evaluable',reason=str(exc)))
            continue
        max_residual = 0.0
        for run, x, y in curves:
            residual = y - (intercept - beta*x)
            max_residual = max(max_residual, float(np.max(np.abs(residual))))
            for v, loggain, r in zip(x, y, residual):
                samples.append(dict(run=run['name'],temperature_C=temp,vmem_V=v,
                                    log_gain=loggain,residual=r))
        ref_error = float(np.max(np.abs(reference[2] - (intercept - beta*reference[1]))))
        summaries.append(dict(temperature_C=temp,status='analyzed',beta_per_V=beta,
                              inverse_beta_V=1/beta,intercept=intercept,
                              reference_max_abs_log_error=ref_error,
                              all_grid_max_abs_log_error=max_residual,
                              nominal_dose=beta*(400e-15/30e-12)*.1,
                              samples=sum(len(c[1]) for c in curves)))
    (HERE/'gain_summary.json').write_text(json.dumps(summaries,indent=2)+'\n')
    if samples:
        with (HERE/'gain_samples.csv').open('w',newline='') as fh:
            writer=csv.DictWriter(fh,fieldnames=samples[0],lineterminator='\n')
            writer.writeheader();writer.writerows(samples)
    print(json.dumps(summaries,indent=2))


if __name__ == '__main__':
    main()
