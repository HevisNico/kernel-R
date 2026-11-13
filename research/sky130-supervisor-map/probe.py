"""Exploratory, nominal action map only; never the registered jump campaign."""
import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import time

import numpy as np

HERE = Path(__file__).resolve().parent
CIRCUIT = HERE.parent / 'circuit'
PDK_COMMIT = '1232782c1b9fab3aacda74d67ce7c92bf7da8105'
SIGNALS = ['v(vmem1)', 'v(vq)', 'v(p)', 'v(x1.sum)', 'v(x1.a)',
           'v(x1.b)', 'v(x1.si)', 'i(v.x1.vdose)', 'i(vdd)']
COL = {s: i+1 for i, s in enumerate(SIGNALS)}


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def deck(case):
    text = (CIRCUIT / 'cell.spice').read_text()
    text = text.replace('.global ksen krst kpreb', '.global ksen krst kpreb amp')
    # The transistor circuit is unchanged except a zero-volt current probe.
    text = text.replace('xmsi x si sum 0', 'vdose writefeed sum 0\nxmsi x si writefeed 0')
    # Pulse amplitude is part of the ideal stimulus, not a device modification.
    text = text.replace('({ipk}*exp(', '(v(amp)*{ipk}*exp(')
    for port in (1, 2):
        old = next(l for l in text.splitlines() if l.startswith(f'x{port} '))
        selection = ' ta=440u tb=1 tj=2' if port == 1 and case['actions'] else ' ta=1 tb=1 tj=2'
        text = text.replace(old, old.split(' ta=')[0]+selection)
    # In paired diagnostics a service every 440 us has a maintenance slot midway.
    paired = len(case['actions']) > 1
    slot = 220e-6 if paired else 440e-6
    starts = [440e-6 + 4.1e-6 + i*slot for i in range(len(case['actions']))]
    stop = 440e-6 + max(1, len(case['actions']))*slot
    amps = case['actions'] or [0.0]
    amp = str(amps[-1])
    for i in reversed(range(len(amps)-1)):
        amp = f'(time < {440e-6+(i+1)*slot:.12g} ? {amps[i]} : {amp})'
    lines = ['* Phase 0 action probe: '+case['name'], '.lib "pdk/models/sky130.lib.spice" tt']
    lines += text.splitlines()[1:-1]
    lines += [f'bamp amp 0 v={amp}', f'.param tper={slot:.12g} vinit={case["vinit"]:.12g} rlk={case["rlk"]:.12g}',
              '.option temp=27', '.save '+ ' '.join(SIGNALS), '.control',
              f'tran 1u {stop:.12g} 0 {case.get("max_step_s", 200e-9):.12g}',
              'set wr_singlescale', 'set numdgt=16',
              'wrdata trace.txt '+' '.join(SIGNALS), 'quit', '.endc', '.end']
    return '\n'.join(lines)+'\n', starts, stop


def at(d, signal, t):
    return float(np.interp(t, d[:, 0], d[:, COL[signal]]))


def integral(d, signal, lo, hi):
    mask = (d[:, 0] > lo) & (d[:, 0] < hi)
    ts = np.r_[lo, d[mask, 0], hi]
    vs = np.r_[at(d, signal, lo), d[mask, COL[signal]], at(d, signal, hi)]
    return float(np.trapezoid(vs, ts))


def crossings(d, signal, lo, hi, rise=True):
    t, v = d[:, 0], d[:, COL[signal]]
    ids = np.flatnonzero(((v[:-1] < .9) & (v[1:] >= .9)) if rise else ((v[:-1] >= .9) & (v[1:] < .9)))
    found = [float(t[i]+(t[i+1]-t[i])*(.9-v[i])/(v[i+1]-v[i])) for i in ids]
    return [x for x in found if lo <= x < hi]


def analyze(d, case, starts, stop):
    assert d.shape[1] == len(SIGNALS)+1 and np.isfinite(d).all()
    assert d[-1, 0] >= stop-1e-12 and np.all(np.diff(d[:, 0]) >= 0)
    out = []
    for i, start in enumerate(starts):
        lo, hi = start-1e-6, (starts[i+1]-4.1e-6 if i+1 < len(starts) else stop)-1e-6
        fires = crossings(d, 'v(p)', lo, hi)
        entry, exit_ = crossings(d, 'v(x1.a)', lo, hi), crossings(d, 'v(x1.b)', lo, hi)
        steering = crossings(d, 'v(x1.si)', lo, hi)
        pre = at(d, 'v(vmem1)', start-1e-9)
        post = at(d, 'v(vmem1)', hi)
        gross = integral(d, 'i(v.x1.vdose)', lo, hi)
        loss = integral(d, 'v(x1.sum)', lo, hi)/case['rlk']
        out.append(dict(amplitude=case['actions'][i], start_s=start,
            fire_times_s=fires, service_success=len(fires)==1 and start <= fires[0] <= start+20e-6,
            entry_times_s=entry, exit_times_s=exit_, steering_times_s=steering,
            pre_vmem_V=pre, post_vmem_V=post, net_gain_mV=1000*(pre-post),
            pre_vq_V=at(d, 'v(vq)', start-1e-9), pre_protection_V=at(d, 'v(p)', start-1e-9),
            gross_write_C=gross, gross_write_mV=gross/30e-12*1000,
            imposed_loss_C=loss, imposed_loss_mV=loss/30e-12*1000,
            supply_energy_J=-1.8*integral(d, 'i(vdd)', lo, hi)))
    return dict(actions=out, simulated_s=stop, rows=len(d),
                final_vmem_V=at(d, 'v(vmem1)', stop),
                supply_energy_J=-1.8*integral(d, 'i(vdd)', 0, stop))


def run(case, out, ngspice, pdk, runtime):
    out.mkdir(parents=True, exist_ok=False)
    (out/'pdk').symlink_to(pdk.resolve(), target_is_directory=True)
    shutil.copyfile(CIRCUIT/'blocks.spice', out/'blocks.spice')
    shutil.copyfile(CIRCUIT/'spiceinit.txt', out/'.spiceinit')
    text, starts, stop = deck(case)
    (out/'input.spice').write_text(text)
    meta = dict(case=case, ngspice_sha256=digest(ngspice), pdk_commit=PDK_COMMIT,
                source_sha256={p.name: digest(p) for p in (CIRCUIT/'cell.spice', CIRCUIT/'blocks.spice', Path(__file__))},
                deck_sha256=digest(out/'input.spice'), status='running')
    (out/'metadata.json').write_text(json.dumps(meta, indent=2)+'\n')
    env = dict(os.environ, SPICE_SCRIPTS=str(runtime.resolve()))
    if (runtime/'tmpfile.so').exists():
        (out/'tmp').mkdir()
        env.update(LD_PRELOAD=str((runtime/'tmpfile.so').resolve()), TMPDIR=str((out/'tmp').resolve()))
    began = time.monotonic()
    try:
        r = subprocess.run([str(ngspice.resolve()), '-b', 'input.spice'], cwd=out, env=env,
                           capture_output=True, timeout=900)
        (out/'stdout.log').write_bytes(r.stdout)
        (out/'stderr.log').write_bytes(r.stderr)
        meta.update(returncode=r.returncode, wall_s=time.monotonic()-began)
        if r.returncode or not (out/'trace.txt').exists():
            raise RuntimeError('Simulator failed; retained logs: '+str(out))
        d = np.loadtxt(out/'trace.txt')
        meta['result'] = analyze(d, case, starts, stop)
        raw = (out/'trace.txt').read_bytes()
        (out/'trace.txt.gz').write_bytes(gzip.compress(raw, mtime=0))
        meta['trace_sha256'] = digest(out/'trace.txt.gz')
        meta['status'] = 'complete'
    except Exception as exc:
        meta.update(status='failed', error=str(exc), wall_s=time.monotonic()-began)
        raise
    finally:
        (out/'metadata.json').write_text(json.dumps(meta, indent=2)+'\n')
    print(json.dumps(meta), flush=True)
    return meta


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--ngspice', type=Path, required=True)
    p.add_argument('--pdk', type=Path, required=True)
    p.add_argument('--runtime', type=Path, required=True)
    p.add_argument('--cases', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    args = p.parse_args()
    assert subprocess.check_output(['git', '-C', str(args.pdk), 'rev-parse', 'HEAD'], text=True).strip() == PDK_COMMIT
    for case in json.loads(args.cases.read_text()):
        run(case, args.output/case['name'], args.ngspice, args.pdk, args.runtime)


if __name__ == '__main__':
    main()
