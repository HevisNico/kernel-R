"""Independent fixed-step simulation of the B->A phase with drift, noise and pulse amplitude.

Evidence only (explicit Euler, step 1e-4). It shares no code with bounds.py. Each physical
parameter oscillates inside its box; the disturbance is adversarial: it pushes the main charge
up in READY, slows FAST/SLOW and the auxiliary decays, and drives auxiliaries upward in READY.
Usage: python simulate_noise.py <epsilon> <nu> <alpha> [seed]
"""
import math, random, sys

A = math.log(4); K = 0.5; R = 0.1; RM = 0.025; DT = 1e-4


def h(t):
    return A / (A - K) * (math.exp(-K * t) - math.exp(-A * t))


NOM = dict(C=4.0, Lm=math.log(1.25) / 0.02, Ls=math.log(8) / 1.06, Le=math.log(4) / 0.15, M=(1 - RM) / h(0.02))


class Cell:
    def __init__(self, eps, nu, alpha, rng, gains):
        self.eps, self.nu, self.alpha, self.rng = eps, nu, alpha, rng
        self.q, self.mode = R, 0
        self.z = [math.log(g) for g in gains]; self.b = 0.18
        self.m = [RM] * 3; self.am = [0] * 3; self.raw = [[] for _ in range(3)]
        self.phase = {(p, j): (rng.uniform(0, 6.3), rng.uniform(0.2, 3.0)) for p in NOM for j in range(3)}
        self.out = []; self.doses = [0.0] * 3

    def par(self, p, j, t):
        ph, w = self.phase[p, j]
        return NOM[p] * (1 + self.eps * math.sin(w * t + ph))

    def amp(self, t):
        return 1 + self.alpha * math.sin(3.1 * t)

    def current(self, j, t):
        return sum(A * math.exp(-A * (t - f)) for f in self.raw[j] if 0 <= t - f < 1) * self.amp(t)

    def step(self, t):
        nu = self.nu
        if self.mode == 0:
            dq = -K * (self.q - R) + sum(math.exp(self.z[j]) * self.current(j, t) for j in range(3)) + nu
        elif self.mode == 1:
            dq = -A * self.q + nu
        else:
            dq = -self.b * self.q + nu
        self.q += dq * DT
        if self.mode == 0 and self.q >= 1:
            self.mode = 1; self.q = 1.0; self.out.append(t)
        elif self.mode == 1 and self.q <= 0.25:
            self.mode = 2; self.q = 0.25
        elif self.mode == 2 and self.q <= R:
            self.mode = 0; self.q = R
        for j in range(3):
            am, m = self.am[j], self.m[j]
            if am == 0:
                dm = -K * (m - RM) + self.par('M', j, t) * self.current(j, t) + nu
            else:
                L = self.par(('Lm', 'Ls', 'Le')[am - 1], j, t)
                dm = -L * m + nu
                if am == 1 and self.mode != 0:
                    self.b = min(1.1, self.b + 0.5 * L * m * DT)
                if am == 3 and self.mode == 0 and self.z[j] < math.log(self.par('C', j, t)):
                    dz = 8 * L * m * DT; self.z[j] += dz; self.doses[j] += dz
            m += dm * DT
            if am == 0 and m >= 1: am, m = 1, 1.0
            elif am == 1 and m <= 0.8: am, m = 2, 0.8
            elif am == 2 and m <= 0.1: am, m = 3, 0.1
            elif am == 3 and m <= RM: am, m = 0, RM
            self.am[j], self.m[j] = am, m


def run(eps, nu, alpha, seed=1):
    rng = random.Random(seed)
    B = Cell(eps, nu, alpha, rng, (0.3, 0.3, 0.3)); A_ = Cell(eps, nu, alpha, rng, (0.3, 0.3, 0.3))
    B.raw[2] = [8.0 * k for k in range(16)]
    routed = set(); g0 = math.exp(A_.z[2])
    for n in range(int(139.9 / DT)):
        t = n * DT
        B.step(t)
        for f in B.out:
            if f not in routed:
                routed.add(f); A_.raw[2].append(f + rng.uniform(0.3, 0.4))
        A_.step(t)
    return dict(B=len(B.out), A=len(A_.out), A_log_dose_total=A_.doses[2], A_gain_ratio=math.exp(A_.z[2]) / g0,
                A_b=A_.b, A_mode_at_end=A_.mode)


if __name__ == '__main__':
    eps, nu, alpha = (float(x) for x in sys.argv[1:4])
    seed = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    print(dict(eps=eps, nu=nu, alpha=alpha, seed=seed, **run(eps, nu, alpha, seed)))
