"""Registered generators. Import is inert; never call before the single batch."""
import random
from common import N


def known(outside=False):
    return dict(name='outside' if outside else 'known',seed=None,kind='outside' if outside else 'replication',
                rates=[10 if t<661 else (170 if outside else 140) for t in range(N+1)],
                reserve_errors=[(7*t+1)%5-2 for t in range(N+1)],
                rate_errors=[(5*t+2)%3-1 for t in range(N+1)])


def seeded(seed):
    if seed not in range(2026111301,2026111313):
        raise ValueError('Unregistered scenario seed')
    plant = random.Random(seed)
    reserve = random.Random(seed+100000)
    sensor = random.Random(seed+200000)
    if seed<=2026111304:
        initial=10*plant.randrange(16)
        jump=plant.randrange(1,1321)
        after=10*plant.randrange(16)
        rates=[initial if t<jump else after for t in range(N+1)]
        kind='jump'
    elif seed<=2026111308:
        rate=10*plant.randrange(16)
        rates=[rate]
        for t in range(1,N+1):
            if t%20==0:
                rate=max(0,min(150,rate+plant.choice((-10,0,10))))
            rates.append(rate)
        kind='walk'
    else:
        rates=[10*plant.randrange(16) for _ in range(N+1)]
        kind='jitter'
    return dict(name='seed'+str(seed),seed=seed,kind=kind,rates=rates,
                reserve_errors=[reserve.randint(-2,2) for _ in range(N+1)],
                rate_errors=[sensor.randint(-1,1) for _ in range(N+1)])


def batch():
    yield known()
    for seed in range(2026111301,2026111313):
        yield seeded(seed)
    yield known(outside=True)
