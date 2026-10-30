"""Versioned certificate semantics, shared by producer and trusted verifier."""
SOURCES = ('bounds.py', 'certify.py', 'contract.py', 'decimal_intervals.py',
           'integer_intervals.py', 'verify.py', 'chain.py',
           'THEOREM_ROBUST.md', 'THEOREM_N.md')


def metadata():
    return dict(
        schema_version=2,
        status='CERTIFIED_ROBUST_LOCAL_PREPARED_SECTION',
        model=dict(
            drift='measurable per-port C, Lm, Ls, Le, M in the nominal relative box',
            noise='measurable additive disturbances bounded by nu on q and each m in every mode; E is noise-free',
            amplitude='measurable received-current multipliers in [1-alpha,1+alpha]; support [arrival,arrival+1)',
            emission='canonical one-unit waveform triggered by firing, independent of the noisy FAST exit time',
            kernel='other R laws unchanged; continuous first-crossing semantics'),
        section=dict(main_mode='READY', aux_modes='all READY', no_active_currents=True,
                     q=['0.09999','0.10001'], m_each=['0.02499','0.02501'],
                     active_port=2, active_log_gain='ln(3/10) + [-1e-5,1e-5]',
                     other_gains='positive and initially below their own caps',
                     b=['0.17999','0.18001'], E=['50','100']),
        protocol=dict(B_source='16 pulses at 0,8,...,120 on B port 2',
                      route='B -> A port 2; each delay in [0.3,0.4]',
                      other_inputs='none', measurement='139.9'),
        conclusion=dict(B_emissions=13, A_emissions=10, A_full_error_doses=3,
                        A_final_log_gain='initial log gain + D1 + D2 + D3; each Di in gain_log_dose',
                        A_recovery='unchanged', isolated_probe_before='0/8',
                        isolated_probe_after='8/8', probe_period='20'),
        trusted_base=['authentic execution of the verifier and all its imports',
                      'Python runtime and integer interval implementation',
                      'written hybrid-flow argument; not a Lean formalization'])
