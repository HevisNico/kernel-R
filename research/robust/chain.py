"""Exact rational finite-chain contract, conditional on the local written theorem."""
from fractions import Fraction as F
import argparse, json
from pathlib import Path
from bounds import Refusal, require
from verify import verify


def schedule(n, k, period=None):
    require(type(n) is int and n >= 1, 'N must be a positive integer')
    require(type(k) is int and k >= 3*n+1, 'K must be at least 3*N+1')
    minimum = F(15,2) + F(n-1,2)
    p = max(F(8), minimum) if period is None else F(period)
    require(p >= minimum, 'period too short for the accumulated latency/delay uncertainty')
    return p


def contract(certificate, n, k, period=None):
    report = verify(certificate, emit=False)
    cert=json.loads(Path(certificate).read_text())
    p=schedule(n,k,period)
    counts=[k-3*(i+1) for i in range(n)]
    q=F(cert['bounds']['main_reopen_bound'][1])
    nodes=[]
    for i in range(n):
        nodes.append(dict(index=i, inputs=k-3*i, emissions=counts[i], full_error_doses=3,
                          minimum_input_gap=str(p-F(i,2)),
                          first_output_window=[str(3*(i+1)*p+F(4*i,5)+F(1,2)),
                                               str(3*(i+1)*p+F(13*i,10)+F(9,10))],
                          last_output_window=[str((k-1)*p+F(4*i,5)+F(1,2)),
                                              str((k-1)*p+F(13*i,10)+F(9,10))]))
    return dict(status='CONDITIONAL_PREPARED_CHAIN_CONTRACT',
                local_certificate_sha256=report['certificate_sha256'],
                N=n, K=k, period=str(p), nodes=nodes,
                root_emissions=k-3*n, total_emissions=n*k-3*n*(n+1)//2,
                all_ready_by=str((k-1)*p+F(13*(n-1),10)+q),
                scope='prepared chain; depth-dependent period; written induction, not full Lean semantics')


if __name__=='__main__':
    a=argparse.ArgumentParser(); a.add_argument('certificate'); a.add_argument('--n',type=int,required=True)
    a.add_argument('--k',type=int,required=True); a.add_argument('--period'); args=a.parse_args()
    print(json.dumps(contract(args.certificate,args.n,args.k,args.period),indent=2))
