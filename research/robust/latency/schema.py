SOURCES=('schema.py','obligations.py','certify.py','verify.py','THEOREM.md')


def metadata():
    return dict(schema_version=1,status='CERTIFIED_NOISE_DEPENDENT_LATENCY_RADIUS',
                reference='first crossing of .1 + g*h(t)=1 for the same cell and its actual fixed learned gain g',
                radius='each regular latency differs from its reference by at most delta; two errors may differ by 2*delta',
                first_output='a nonnegative advance plus a one-sided delay error <=delta',
                chain='T >= 7.5 + 2*sum_{i=0}^{N-2}(sigma_i+delta_i)',
                preparation='the pinned robust birth certificate and its widened local section',
                trust='authentic sources; integer interval arithmetic; written first-crossing/packet proof, not Lean')
