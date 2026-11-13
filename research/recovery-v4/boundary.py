"""Claims refer to their own pre/post boundary; no interval extrapolation."""


def truth_flags(time, pre, post, alarm_detected, sampled_safe, guaranteed_pre, guaranteed_post):
    return dict(truth_unsafe_pre=int(time > 0 and pre < 100),
                truth_unsafe_post=int(time > 0 and post < 100),
                truth_undetected=int(time > 0 and pre < 100 and not alarm_detected),
                truth_false_sample=int(bool(sampled_safe) and pre < 100),
                truth_false_guarantee_pre=int(bool(guaranteed_pre) and pre < 100),
                truth_false_guarantee_post=int(bool(guaranteed_post) and post < 100))
