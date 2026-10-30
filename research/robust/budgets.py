import sys
from decimal import Decimal as D
from decimal_intervals import I, configure
from bounds import derive, Refusal
configure(60)
def ok(eps, nu, alpha, Q):
    try: derive(I, eps, nu, alpha, Q); return True, ''
    except Refusal as e: return False, str(e)
for eps in ('0.003', '0.1'):
    print(eps, 'nu=0,alpha=0:', ok(eps, '0', '0', '0.03'))
    for Q in ('0.03', '0.05', '0.08'):
        lo_, hi_ = D(0), D('0.02')
        for _ in range(30):
            m = (lo_ + hi_) / 2
            (lo_, hi_) = (m, hi_) if ok(eps, str(m), '0', Q)[0] else (lo_, m)
        print(f'  eps {eps} Q {Q}: max nu ~ {lo_:.6f}  first failure above: {ok(eps, str(hi_), "0", Q)[1]}')
    lo_, hi_ = D(0), D('0.5')
    for _ in range(30):
        m = (lo_ + hi_) / 2
        (lo_, hi_) = (m, hi_) if ok(eps, '0', str(m), '0.03')[0] else (lo_, m)
    print(f'  eps {eps}: max alpha (nu=0) ~ {lo_:.5f}  fails on: {ok(eps, "0", str(hi_), "0.03")[1]}')
