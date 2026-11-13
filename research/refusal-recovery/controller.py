"""Executable recovery adapter; future physics and the permit source are trusted.

The Lean decision kernels are proved; this Python orchestration is tested,
not a proved refinement. No experiment or campaign is launched here.
"""
from dataclasses import dataclass
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parent


@dataclass(frozen=True)
class Observation:
    time: int
    reserve_report: int
    rate_report: int
    delivered: bool
    measured_at: int | None = None


@dataclass(frozen=True)
class Permit:
    generation: int
    issued: int
    expires: int
    bound: int
    decisions: int


@dataclass(frozen=True)
class Decision:
    mode: str
    action: str
    lower: int
    sampled_safe_pre: bool
    delay: int
    generation: int
    invalidated: bool = False


class Supervisor:
    def __init__(self, *, now, repair_budget, phase_budget, pending=False,
                 previous_generation=0, probe_price=1, write_price=10):
        if min(now, repair_budget, phase_budget, previous_generation,
               probe_price, write_price) < 0:
            raise ValueError('Budgets, dates, prices and generation must be nonnegative')
        self.generation = previous_generation + 1
        self.due, self.pending = now, pending
        self.repair_budget = self.fuel = repair_budget
        self.phase_budget = self.permits_left = phase_budget
        self.probe_price, self.write_price = probe_price, write_price
        self.probes = self.recovery_writes = self.active_writes = 0
        self.mode, self.permit, self.remaining = 'recovery-unguaranteed', None, 0
        self.process = subprocess.Popen(
            ['lake', 'env', 'lean', '--run', 'Bridge.lean'], cwd=ROOT,
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            text=True, bufsize=1)
        if self.process.stdout.readline().strip() != 'READY':
            self.close()
            raise RuntimeError('Recovery bridge failed readiness')

    @property
    def cost(self):
        return self.probe_price * self.probes + self.write_price * (
            self.recovery_writes + self.active_writes)

    @property
    def cost_limit(self):
        actions = self.repair_budget + 8 * self.phase_budget
        return self.probe_price * (actions + 1) + self.write_price * actions

    def _query(self, mode, obs, permit, fuel):
        values = [mode, self.generation, self.due, int(self.pending), fuel,
                  obs.time if obs.measured_at is None else obs.measured_at,
                  obs.reserve_report, int(obs.delivered)]
        values += ([-1, 0, 0, 0, 0] if permit is None else
                   [permit.generation, permit.issued, permit.expires,
                    permit.bound, permit.decisions])
        values.append(obs.rate_report)
        self.process.stdin.write(' '.join(map(str, values)) + '\n')
        self.process.stdin.flush()
        reply = self.process.stdout.readline().strip().split()
        if len(reply) != 4 or reply[0] not in (
                'repair', 'resume', 'exhausted', 'fault', 'write', 'wait', 'refuse'):
            raise RuntimeError('Invalid bridge reply: ' + repr(reply))
        return reply[0], int(reply[1]), bool(int(reply[2])), int(reply[3])

    def _fault(self):
        self.mode, self.due, self.permit = 'fault-unguaranteed', None, None
        return Decision(self.mode, 'fault', 0, False, 0, self.generation)

    def decide(self, obs, permit=None):
        if self.due is None:
            raise RuntimeError('Terminal supervisor; no automatic budget refill')
        try:
            return self._decide(obs, permit)
        except (RuntimeError, ValueError, TypeError, AttributeError, BrokenPipeError):
            return self._fault()

    def _decide(self, obs, permit):
        self.probes += 1
        if obs is None or obs.time != self.due or obs.delivered != self.pending:
            return self._fault()
        if obs.measured_at is not None and obs.measured_at != self.due:
            return self._fault()
        invalidated = False
        if self.mode == 'authorized-conditional':
            action, lower, safe, delay = self._query(1, obs, self.permit, self.remaining)
            if action == 'refuse':
                invalidated = max(0, obs.rate_report - 1) > self.permit.bound
                self.generation += 1
                self.permit, self.remaining = None, 0
                self.mode = 'recovery-unguaranteed'
        if self.mode == 'recovery-unguaranteed':
            supplied = permit if self.permits_left else None
            action, lower, safe, delay = self._query(0, obs, supplied, self.fuel)
            if action == 'resume':
                self.permits_left -= 1
                self.permit, self.remaining = supplied, supplied.decisions
                self.mode = 'authorized-conditional'
                action, lower, safe, delay = self._query(1, obs, supplied, self.remaining)
                if action in ('refuse', 'fault'):
                    return self._fault()
        if action in ('repair', 'write', 'wait'):
            if delay <= 0:
                return self._fault()
            if action == 'repair':
                self.fuel -= 1
                self.recovery_writes += 1
            else:
                self.remaining -= 1
                self.active_writes += int(action == 'write')
            self.pending = action in ('repair', 'write')
            self.due = obs.time + delay
        else:
            self.mode = action + '-unguaranteed'
            self.due, self.permit = None, None
            self.pending = False
        return Decision(self.mode, action, lower, safe, delay, self.generation, invalidated)

    def close(self):
        if self.process.poll() is None:
            self.process.stdin.close()
            try:
                self.process.wait(timeout=10)
            except subprocess.TimeoutExpired:
                self.process.kill()
                self.process.wait(timeout=10)
        self.process.stdout.close()
        self.process.stderr.close()

    def __enter__(self):
        return self

    def __exit__(self, *_):
        self.close()
