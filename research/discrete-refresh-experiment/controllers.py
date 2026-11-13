"""Observation-only policies. No plant state, jump time or noise schedule."""
from dataclasses import dataclass
from pathlib import Path
import subprocess

SERVICE, CEILING, DOSE, CAPACITY, CAP = 100, 22, 220, 660, 40
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


class Baseline:
    def __init__(self, name):
        if name not in ('naive', 'prudent'):
            raise ValueError(name)
        self.name = name

    def decide(self, obs):
        spacing = 1 if self.name == 'prudent' or obs.lower_before < SERVICE else CAP
        if obs.lower_after < SERVICE + 2 * CEILING:
            return Decision(obs.lower_after, 'write', 1)
        return Decision(obs.lower_after, 'wait', spacing)


class Contract:
    """Every decision calls the existing Lean choose/review definitions."""
    name = 'contract'

    def __init__(self, stderr):
        self.anchor = None
        self.process = subprocess.Popen(
            ['lake', 'env', 'lean', '--run', str(ROOT / 'Bridge.lean')],
            cwd=FOUNDATIONS, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
            stderr=stderr, text=True, bufsize=1)
        if self.process.stdout.readline().strip() != 'READY':
            raise RuntimeError('Lean bridge failed before readiness; inspect stderr')

    def decide(self, obs):
        if self.anchor is None:
            self.anchor = obs.rate_report
        self.process.stdin.write(
            f'{obs.reserve_report} {obs.rate_report} {self.anchor} {int(obs.delivered)}\n')
        self.process.stdin.flush()
        reply = self.process.stdout.readline().strip()
        parts = reply.split()
        if len(parts) != 5 or parts[1] not in ('wait', 'write', 'refuse'):
            raise RuntimeError(f'Invalid Lean reply: {reply!r}')
        lower, action, delay, anchor, reopened = parts
        self.anchor = int(anchor)
        return Decision(int(lower), action, int(delay), self.anchor, bool(int(reopened)))

    def close(self):
        self.process.stdin.close()
        code = self.process.wait(timeout=30)
        self.process.stdout.close()
        if code:
            raise RuntimeError(f'Lean bridge exit status {code}')
