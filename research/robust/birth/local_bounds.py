"""Sufficient inequalities of the robust local theorem (drift, bounded noise, pulse amplitude).

derive(I, epsilon, nu, alpha, Q) evaluates every enclosure and strict obligation with the
interval class I. The certifier calls it with outward Decimal intervals, the checker with
integer fixed-point intervals. Formulas are shared; arithmetic is independent. The written
argument is THEOREM_ROBUST.md; each obligation names the step it serves.
"""


class Refusal(RuntimeError):
    pass


def require(condition, message):
    if not condition:
        raise Refusal(message)


def derive(I, epsilon, nu, alpha, Q, recovery_interval):
    eps, nu, alpha, Q = I(epsilon), I(nu), I(alpha), I(Q)
    for name, x in (('epsilon', eps), ('nu', nu), ('alpha', alpha), ('Q', Q)):
        require(x.lo == x.hi, name + ' must be exact')
    require(0 < eps.lo < 1 and nu.lo >= 0 and 0 <= alpha.lo < 1 and Q.lo > 0, 'parameter range')
    span = lambda x, y: I(x.lo, y.hi)
    lo = lambda x: I(x.lo)
    hi = lambda x: I(x.hi)
    a = I(4).ln(); k = I('0.5'); r = I('0.1'); rm = I('0.025'); delta = I('0.00001')
    factor = span(1 - eps, 1 + eps)
    amp = span(1 - alpha, 1 + alpha)
    h = lambda t: a / (a - k) * ((-k * I(t)).exp() - (-a * I(t)).exp())
    cap = I(4) * factor
    lm = (I('1.25').ln() / I('0.02')) * factor
    ls = (I(8).ln() / I('1.06')) * factor
    le = (I(4).ln() / I('0.15')) * factor
    mult = ((1 - rm) / h('0.02')) * factor
    b = I(recovery_interval)
    bounds = dict(epsilon=eps, nu=nu, alpha=alpha, section_excess=Q, a=a, kappa=k, cap=cap,
                  Lm=lm, Ls=ls, Le=le, M=mult, b=b)
    obligations = []

    def lt(name, left, right):
        left = I(left); right = I(right)
        bounds[name + '.left'] = left; bounds[name + '.right'] = right
        require(left.hi < right.lo, name)
        obligations.append(dict(name=name, relation='strict_lt', left=name + '.left', right=name + '.right'))

    # Step 0. h increases on [0,1]: its maximum is at ln(a/kappa)/(a-kappa).
    lt('h_increases_through_raw_window', 1, (a / k).ln() / (a - k))

    def duration(x0, x1, rate):
        """Exit time of x'=-L(t)x+w, |w|<=nu, L(t) in rate, from x0 down to x1 (Step 2)."""
        lt(f'decay_{x0}_{x1}_dominates_noise', hi(nu / lo(rate)), I(x1))
        fast = (1 / hi(rate)) * ((I(x0) + nu / hi(rate)) / (I(x1) + nu / hi(rate))).ln()
        slow = (1 / lo(rate)) * ((I(x0) - nu / lo(rate)) / (I(x1) - nu / lo(rate))).ln()
        return span(fast, slow)

    # Step 1. Auxiliary first crossing in (0.015, 0.03) under drift of M, noise and amplitude.
    md = delta + nu / k                       # auxiliary rest deviation at every input
    bounds['aux_rest_deviation'] = md
    up_aux = lambda t: rm + md + hi(mult) * hi(amp) * h(t) + nu * I(t)
    low_aux = lambda t: rm - md + lo(mult) * lo(amp) * h(t) - nu * I(t)
    lt('aux_rest_below_threshold', rm + md, 1)
    lt('aux_below_threshold_until_0.015', up_aux('0.015'), 1)
    lt('aux_above_threshold_by_0.03', 1, low_aux('0.03'))
    tau = I('0.015', '0.03')

    # Step 2. Protected auxiliary phases with drifting rates and noise.
    t_mark = duration('1', '0.8', lm)
    t_silent = duration('0.8', '0.1', ls)
    t_error = duration('0.1', '0.025', le)
    mark = tau + t_mark; error = mark + t_silent; finish = error + t_error
    bounds.update(mark_duration=t_mark, silent_duration=t_silent, error_duration=t_error,
                  mark_end=mark, error_start=error, aux_finish=finish)

    # Step 3. ERROR gain dose: 8*(m_start - m_end + integral of noise).
    dose = I(8) * (I('0.075') + span(-nu * hi(t_error), nu * hi(t_error)))
    bounds['gain_log_dose'] = dose
    initial_gain = I('0.3') * I('-0.00001', '0.00001').exp()
    gains = [initial_gain * (I(j) * dose).exp() for j in range(4)]
    learned = gains[3]
    bounds.update(initial_gain=initial_gain, learned_gain=learned)

    # Step 4. Main latency bracket, FAST and SLOW with noise (b unchanged).
    rootlo = I('0.5'); roothi = I('0.9'); delay = I('0.3', '0.4')
    gap = I(8) + rootlo + lo(delay) - roothi - hi(delay)
    t_fast = duration('1', '0.25', a)
    t_slow = duration('0.25', '0.1', b)
    reopen = roothi + hi(t_fast) + hi(t_slow)
    bounds.update(min_input_gap=gap, fast_duration=t_fast, slow_duration=t_slow, main_reopen_bound=reopen)
    lt('aux_cycle_ends_after_raw_pulse', 1, lo(finish))
    lt('aux_cycle_ends_before_next_input', hi(finish), gap)
    lt('learned_gain_below_all_caps', learned, lo(cap))
    lt('mark_finishes_before_any_main_firing', hi(mark), rootlo)
    lt('main_fires_before_error_begins', roothi, lo(error))
    lt('error_finishes_during_main_fast', hi(finish), rootlo + lo(t_fast))
    lt('main_reopens_after_raw_pulse', 1, rootlo + lo(t_fast) + lo(t_slow))
    lt('main_reopens_before_next_input', reopen, gap)

    # Step 5. Silent inputs: no first crossing, and the excess returns below Q.
    lower_excess = -(delta + nu / k)
    rest_excess = nu / k
    lt('arbitrary_initial_silence_inside_section', delta + rest_excess, Q)
    lt('rest_noise_inside_section', rest_excess, Q)
    overlap = I(0, max(0 * error.lo, (1 - lo(error)).hi))
    density = a * (-a * lo(error)).exp()
    carry = None
    for j in range(3):
        g = gains[j]
        jump = hi(g) * (hi(dose).exp() - 1)
        peak = r + Q + hi(g) * hi(amp) * h(1) + nu + jump * hi(amp) * density * overlap
        carry = (peak - r) * (-k * (gap - 1)).exp() + nu / k
        bounds.update({f'gain_before_{j}': g, f'peak_bound_{j}': peak, f'carry_bound_{j}': carry})
        lt(f'silent_{j}_no_first_crossing', peak, 1)
        # After raw end q-r <= max(peak-r, nu/kappa) (convex combination of the two).
        lt(f'silent_{j}_stays_below_threshold_after_raw_end', r + rest_excess, 1)
        lt(f'silent_{j}_excess_returns_inside_section', carry, Q)

    # Step 6. Learned inputs fire once, from an excess below max(carry_2, nu/kappa).
    start_excess = carry if carry.hi > rest_excess.hi else rest_excess
    early = r + start_excess + hi(learned) * hi(amp) * h('0.5') + nu * I('0.5')
    late = r + lower_excess + lo(learned) * lo(amp) * h('0.9') - nu * I('0.9')
    bounds.update(learned_start_excess=start_excess, learned_upper_at_0_5=early, learned_lower_at_0_9=late)
    lt('learned_below_threshold_until_0.5', early, 1)
    lt('learned_above_threshold_by_0.9', 1, late)

    # Step 7. Retained probes: before learning 0/8 and after 8/8 at period 20.
    lt('probe_gap_exceeds_cycle', reopen, I(20))
    lt('probe_aux_cycle_ends', hi(finish), I(20))

    # Step 8. Energy: pump keeps E in [50,100] (E itself is noise-free).
    W = (3 * hi(cap) + 3 * hi(mult) + 1) * a * hi(amp) + I('1.1') + I('4.5') * hi(lm) + I('2.4') * hi(le)
    bounds['work_bound'] = W
    lt('reserve_gate_stays_open', W, 500)

    # Step 9. Calendar of the B->A phase.
    root = span(rootlo, roothi)
    bounds['A_gain_complete_by'] = I(40) + roothi + hi(delay) + hi(finish)
    bounds['A_first_emission'] = I(48) + 2 * root + delay
    bounds['A_last_return_by'] = I(120) + roothi + hi(delay) + reopen
    bounds['B_last_return_by'] = I(120) + reopen
    lt('A_learning_complete_before_first_response', bounds['A_gain_complete_by'], lo(bounds['A_first_emission']))
    lt('A_quiescent_before_measurement', bounds['A_last_return_by'], I('139.9'))
    lt('B_quiescent_before_measurement', bounds['B_last_return_by'], I('139.9'))
    return bounds, obligations
