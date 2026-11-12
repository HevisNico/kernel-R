"""Observation-only policies. No plant state, jump time or noise schedule."""
from dataclasses import dataclass
from pathlib import Path
import subprocess

SERVICE, VARIATION, DOSE, CAPACITY, CAP = 100, 10, 220, 660, 40
ROOT = Path(__file__).resolve().parent
FOUNDATIONS = ROOT.parent / 'self-certifying-learning'


@dataclass(frozen=True)
class Observation:
    time: int
    reserve_report: int
    rate_report: int
    delivered: bool

    @property
    def lower_before(self):
        return self.reserve_report - 2

    @property
    def lower_after(self):
        return (min(CAPACITY, self.lower_before + DOSE)
                if self.delivered else self.lower_before)


@dataclass(frozen=True)
class Decision:
    lower: int
    action: str
    delay: int
    anchor: int | None = None
    reopened: bool = False
    bound: int = 0
    carried: int | None = None
    old_bound: int | None = None
    lease_end: int | None = None
    ambiguous: bool = False
    invalidated: bool = False


class Baseline:
    def __init__(self, name):
        if name not in ('naive', 'prudent'):
            raise ValueError(name)
        self.name = name

    def decide(self, obs):
        spacing = 1 if self.name == 'prudent' or obs.lower_before < SERVICE else CAP
        bound = obs.rate_report + 1 + VARIATION
        if obs.lower_after < SERVICE + 2 * bound:
            return Decision(obs.lower_after, 'write', 1, bound=bound)
        return Decision(obs.lower_after, 'wait', spacing, bound=bound)


class Contract:
    """Calls the preregistered adaptive Lean policy and existing interval review."""
    name = 'adaptive'

    def __init__(self, stderr):
        self.anchor = None
        self.last = None
        self.last_time = None
        self.process = subprocess.Popen(
            ['lake', 'env', 'lean', '--run', str(ROOT / 'Bridge.lean')],
            cwd=FOUNDATIONS, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
            stderr=stderr, text=True, bufsize=1)
        ready = self.process.stdout.readline().strip()
        if ready != 'READY':
            self.process.terminate()
            self.process.wait(timeout=30)
            self.process.stdin.close()
            self.process.stdout.close()
            raise RuntimeError('Lean bridge failed before readiness: ' + ready)

    def decide(self, obs):
        if self.anchor is None:
            self.anchor = obs.rate_report
        carried, old_bound = None, None
        if self.last is not None:
            if obs.time != self.last_time + self.last.delay or obs.time > self.last_time + 41:
                raise RuntimeError('Missed action endpoint or expired lease')
            old_bound = self.last.bound
            carried = (self.last.lower - old_bound*self.last.delay
                       if self.last.action == 'wait'
                       else min(CAPACITY, self.last.lower + DOSE - old_bound))
        self.process.stdin.write(
            f'{obs.reserve_report} {obs.rate_report} {self.anchor} {int(obs.delivered)} '
            f'{carried if carried is not None else -1} {old_bound if old_bound is not None else -1}\n')
        self.process.stdin.flush()
        reply = self.process.stdout.readline().strip()
        parts = reply.split()
        if len(parts) != 8 or parts[2] not in ('wait', 'write', 'refuse'):
            raise RuntimeError(f'Invalid Lean reply: {reply!r}')
        lower, bound, action, delay, anchor, reopened, ambiguous, invalidated = parts
        self.anchor = int(anchor)
        result = Decision(int(lower), action, int(delay), self.anchor, bool(int(reopened)),
                          int(bound), carried, old_bound, obs.time+41,
                          bool(int(ambiguous)), bool(int(invalidated)))
        self.last, self.last_time = result, obs.time
        return result

    def close(self):
        self.process.stdin.close()
        code = self.process.wait(timeout=30)
        self.process.stdout.close()
        if code:
            raise RuntimeError(f'Lean bridge exit status {code}')
