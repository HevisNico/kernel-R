"""External registered-model authorization; no truth or sensor inputs."""
import json
from pathlib import Path
import sys
from schema import AUTHORIZE, N, EXPIRY, BOUND, PHASE_SIZE, PHASE_BUDGET

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / 'refusal-recovery'))
from controller import Permit


class Authority:
    def __init__(self, events):
        self.events = events
        self.root = None
        self.tokens = []

    def _append(self, event):
        self.events.write(json.dumps(event, sort_keys=True) + '\n')
        self.events.flush()

    def tick(self, time):
        if time == AUTHORIZE and self.root is None:
            self.root = dict(kind='root', time=time, issued=AUTHORIZE, expires=EXPIRY,
                             bound=BOUND, service=100, dose=220, capacity=660, latency=1,
                             justification='RecoveryV4.root_ceiling_from_registered_plant')
            self._append(self.root)
            return True
        return False

    def offer(self, time, generation, mode, remaining):
        if self.root is None or not AUTHORIZE <= time < N or len(self.tokens) >= PHASE_BUDGET:
            return None
        if mode == 'recovery-unguaranteed':
            target = generation
        elif mode == 'authorized-conditional' and remaining == 0:
            target = generation + 1
        else:
            return None
        event = dict(kind='token', time=time, generation=target, issued=time,
                     expires=EXPIRY, bound=BOUND, decisions=PHASE_SIZE)
        self.tokens.append(event)
        self._append(event)
        return Permit(target, time, EXPIRY, BOUND, PHASE_SIZE)

    def snapshot(self):
        return {'root': self.root, 'tokens': self.tokens}
