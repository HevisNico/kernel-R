"""Cross-check first reports and gains with an independent event integrator."""
import csv
import sys

import numpy as np
from scipy.integrate import solve_ivp

import run as r


def integrate(p, setting, arrival):
    cap, lm, ls, le, M, high, low, factor, fire = p
    method, _, current, duration = setting
    x = np.array([.1, .025, np.log(1.2), .08, 100.])
    t, main, aux, error_start, at_cap, at_recovery_cap = 0., 0, 0, -100., False, False
    shots = []
    trained_gain = None
    for left, right, raw in ((0., 1., True), (1., arrival, False),
                             (arrival, arrival+1, True), (arrival+1, 20., False)):
        if left == arrival:
            trained_gain = np.exp(x[2])
        while t < right:
            target_q = (fire, .25, .1)[main]
            target_m = (1., .8, high, low)[aux]
            timer_end = error_start+duration
            timer_active = method != "R" and t < timer_end
            stop = min(right, timer_end) if timer_active else right

            def rhs(now, y):
                q, m, z, b, energy = y
                pulse = r.A*np.exp(-r.A*(now-left)) if raw else 0.
                input_drive = np.exp(z)*pulse
                qdot = (.5*(.1-q)+input_drive, -r.A*q, -b*q)[main]
                mdot = .5*(.025-m)+M*pulse if aux == 0 else -(lm, ls, le)[aux-1]*m
                zdot = 0.
                if main == 0 and not at_cap and energy > 0:
                    if method == "R" and aux == 3:
                        zdot = 8*le*m
                    if method == "timer" and timer_active:
                        zdot = current*factor
                    if method == "decay" and timer_active:
                        zdot = 8*le*high*np.exp(-le*(now-error_start))
                bdot = .5*lm*m if main != 0 and aux == 1 and not at_recovery_cap and energy > 0 else 0.
                work = (input_drive, r.A*q, 1.1)[main] + (M*pulse if aux == 0 else -mdot) + zdot+bdot
                return [qdot, mdot, zdot, bdot, 10*(100-energy)-work]

            events = []
            for index, threshold, direction in ((0,target_q,1 if main == 0 else -1),
                    (1,target_m,1 if aux == 0 else -1),
                    (2,np.log(cap) if not at_cap else np.inf,1),
                    (3,1.1 if not at_recovery_cap else np.inf,1)):
                def event(now, y, i=index, limit=threshold):
                    return y[i]-limit
                event.direction = direction
                event.terminal = True
                events.append(event)
            sol = solve_ivp(rhs, (t,stop), x, method="DOP853", rtol=2e-12, atol=2e-13,
                            max_step=.1, events=events)
            assert sol.success and np.min(sol.y[4])>0
            t, x = sol.t[-1], sol.y[:,-1]
            for idx, event in enumerate(sol.t_events):
                if len(event) == 0:
                    continue
                if idx == 0:
                    x[0] = target_q
                    if main == 0:
                        shots.append(t)
                    main = (main+1)%3
                elif idx == 1:
                    x[1] = target_m
                    aux = (aux+1)%4
                    if aux == 3:
                        error_start = t
                elif idx == 2:
                    x[2], at_cap = np.log(cap), True
                else:
                    x[3], at_recovery_cap = 1.1, True
    return shots, trained_gain


nodes, weights = np.polynomial.legendre.leggauss(32)
points = r.sample_points()
points[500,0,2] = 1
points[500,0,4] = 1
points[500,0,5] = 1
points[500,0,7] = 1
settings = [r.BASE_SETTINGS[0], r.BASE_SETTINGS[1], r.BASE_SETTINGS[-1],
            *r.TIMED_SETTINGS[:3]]
writer = csv.writer(sys.stdout, lineterminator="\n")
writer.writerow(["setting", "point", "cell", "port", "arrival",
                 "dop853_latency", "reduced_latency", "dop853_gain", "reduced_gain"])
for setting in settings:
    box = r.realizations(points, .1, .05, .003, .1)
    prep = r.prepare(box, setting, nodes, weights)
    for point, cell, port, arrival in ((0,0,0,16.95), (101,1,0,17.05), (501,0,1,17.35), (500,0,0,17.05)):
        shots, actual_gain = integrate(box[point,cell,port], setting, arrival)
        assert len(shots)==1 and shots[0]>arrival
        residual,gain,fire = (a[point,cell,port] for a in prep[:3])
        ready = lambda t: .1+residual*np.exp(-.5*(arrival+t-1))+gain*r.response(t)
        expected = float(r.crossings(ready, np.array(fire), .9))
        assert abs(expected-(shots[0]-arrival))<5e-9, (setting, shots, expected)
        assert abs(gain-actual_gain)<5e-9, (setting, gain, actual_gain)
        writer.writerow([setting[1], point, cell, port, arrival,
                         shots[0]-arrival, expected, actual_gain, gain])
