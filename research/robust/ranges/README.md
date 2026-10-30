# Range certificates for the robust slow chain

The published robust certificates hold at eight points (ε, ν, α). These range certificates
cover every noise bound and every amplitude deviation in closed ranges, at ε = 0.003 and 0.1:

| Ranges | Pieces | Latency radius δ (ε = 0.003 / 0.1) |
|---|---|---|
| ν ∈ [0, 0.002], α = 0 | 4 | 0.00745 / 0.00748 |
| ν = 0, α ∈ [0, 0.09] | 1 | 0.22240 / 0.22240 |
| ν ∈ [0, 0.0015], α ∈ [0, 0.05] | 1 | 0.11023 / 0.11089 |

Each certificate covers the birth entry, the local continuation (all local obligations with
the widened recovery band) and the latency radius. Its chain consequence is the one of
`latency/THEOREM.md`: T ≥ 7.5 + 2 Σ (δᵢ + σᵢ), now for every (ν, α) in the ranges. δ is one
radius valid on the whole range.

## Why interval evaluation covers a range

Every formula of the pinned derivations is an interval expression. Evaluated with ν and α
as intervals, it encloses its value for every ν and α in them, by the inclusion property of
interval arithmetic. A strict inequality checked on those enclosures therefore holds at every
point. Two things in the pinned sources assume point parameters, and only these are patched
by `load.py`, each patch checked by its exact number of occurrences:

1. the checks that ν and α are exact (ε and the section excess stay exact);
2. the zero-disturbance branch of the latency radius, which tested `nu.lo == 0 and
   alpha.lo == 0`. On a range [0, ν_max] that test would accept δ = 0 for the whole range.
   It now tests `nu.hi` and `alpha.hi`.

The pinned files themselves are not modified, so the eight point certificates and the
generated Lean evidence keep their source hashes. Each range certificate records the hashes
of the three pinned sources it patches.

## Pieces

ν appears several times in some formulas, for instance in the SLOW exit time
ln((1/4 − ν/b)/(1/10 − ν/b)). Interval evaluation then takes different values of ν in the
numerator and the denominator, and overestimates. The certifier splits each range into
2ᵏ closed pieces with exact decimal cuts. Adjacent pieces share their cut, so they cover the
range (rule 2, exhaustive case split), and the overestimation shrinks with the piece width.
The split is the smallest power of two that makes every piece pass, up to 64.

## Reproduce

Python 3.12 standard library only.

```sh
python -B ranges/tests.py
python -B ranges/verify.py ranges/certificates/eps0.1_nu0-0.002_alpha0-0.json
python -B ranges/certify.py --epsilon 0.1 --nu 0:0.002 --alpha 0:0 --out /tmp/range.json
```

`tests.py` checks that zero-width ranges reproduce every published birth and latency point
certificate bound for bound, that the zero-radius trap is refused, that ranges beyond the
budget are refused, and that tampered certificates are refused.

## Scope

These certificates do not change the status of the theorems: the hybrid arguments remain
written by hand, the formulas are shared by the Decimal certifier and the integer verifier,
and the Lean evidence still covers the eight published points only.
