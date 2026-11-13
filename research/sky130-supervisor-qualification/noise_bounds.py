"""One-sided Clopper--Pearson bounds on independent repeated whole runs.

No claim that periods within a run are independent. The common success
probability and independence between repeats are statistical assumptions.
Reference: scipy.stats.binomtest(..., alternative='greater').proportion_ci
(method='exact'), https://docs.scipy.org/doc/scipy/reference/generated/
scipy.stats._result_classes.BinomTestResult.proportion_ci.html
"""
import math


def lower_success(successes, trials, alpha=.05):
    if type(successes) is not int or type(trials) is not int or not 0<=successes<=trials or trials<1:
        raise ValueError('Require integer 0 <= successes <= trials, trials >= 1')
    if not 0<alpha<1:raise ValueError('alpha must lie in (0,1)')
    if successes==0:return 0.0
    if successes==trials:return alpha**(1/trials)
    # P_p[X >= successes] increases with p. Invert that tail at alpha.
    def tail(p):
        return math.fsum(math.exp(math.lgamma(trials+1)-math.lgamma(j+1)-math.lgamma(trials-j+1)
                                 +j*math.log(p)+(trials-j)*math.log1p(-p))
                         for j in range(successes,trials+1))
    lo,hi=0.0,1.0
    for _ in range(80):
        mid=(lo+hi)/2
        if tail(mid)<alpha:lo=mid
        else:hi=mid
    return lo


def summarize(trials,alpha=.05):
    if not trials:raise ValueError('No repeated runs')
    if len({t['trial_id'] for t in trials})!=len(trials):raise ValueError('Duplicate trial')
    if len({t['stratum'] for t in trials})!=1:raise ValueError('Do not silently pool heterogeneous cells/scenarios')
    for t in trials:
        if type(t['completed']) is not bool or type(t['all_services_pass']) is not bool:
            raise ValueError('Explicit completion and success booleans required')
    # An interrupted run is retained conservatively as unsuccessful, not dropped.
    k=sum(t['completed'] and t['all_services_pass'] for t in trials)
    return dict(unit='independent repetition of the same complete run',successes=k,trials=len(trials),
                lower_success_probability=lower_success(k,len(trials),alpha),alpha=alpha,
                assumptions='independent repeats, common success probability in this declared stratum',
                gaussian_absolute_error_bound=None)
