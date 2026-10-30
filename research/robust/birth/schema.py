"""Pinned semantics for a birth warm-up and its widened-section continuation."""
SOURCES=('obligations.py','local_bounds.py','schema.py','certify.py','verify.py','THEOREM.md',
         '../bounds.py','../integer_intervals.py','../decimal_intervals.py',
         '../THEOREM_ROBUST.md','../THEOREM_N.md','../periodic/THEOREM.md')


def metadata():
    return dict(schema_version=1,status='CERTIFIED_ROBUST_BIRTH_ENTRY_AND_LOCAL_CONTINUATION',
                birth=dict(modes='main and all auxiliaries READY',q=['.09999','.10001'],
                           m_each=['.02499','.02501'],log_gains='ln(.3,1.2,.3) + independent [-1e-5,1e-5]',
                           b=['.07999','.08001'],E=['50','100'],currents='none'),
                physics=dict(parameters='measurable C,Lm,Ls,Le,M in relative epsilon boxes',
                             noise='measurable additive disturbances |w|<=nu on q and each m in every mode',
                             amplitude='measurable received multiplier in [1-alpha,1+alpha]',
                             pulse='canonical unit-support emission independent of noisy FAST exit',
                             energy='unchanged noise-free reserve law'),
                protocol=dict(warmup='16 port-0 pulses at 0,8,...,120 on each cell; all intercell routes closed',
                              cut='159.9',chain_start='160',chain_port=2,resets='none',settings_copies='none'),
                entry=dict(main='READY',aux='all READY',currents='none',
                           q='entry_q',m_each='entry_m',b='entry_recovery',E=['50','100'],
                           port2_log_gain='unchanged birth value',warmup_emissions_per_cell=12,
                           port0_full_ERRORs=3,full_protected_MARKs=1),
                continuation=dict(local='three silent port-2 inputs then one response per input; minimum gap 7.5',
                                  noisy_period='T >= 7.5 + .5*(N-1)',
                                  noiseless_identical_waveform_period='T >= 7.5 + 2*sum(sigma_i)',
                                  root_count='K-3*N, for K>=3*N+1',
                                  root_eight='K=3*N+8',probes='isolated frozen port-2 probe: 0/8 before, 8/8 after'),
                trust='authentic verifier and imports; Python integer arithmetic; written hybrid comparison and induction, not full Lean semantics')
