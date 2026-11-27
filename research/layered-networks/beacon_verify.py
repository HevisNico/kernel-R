"""The draw's beacon: a drand round, verified, and the round fixed by the announce commit's push time (the owner's rule,
relayed 2026-11-25). Development only.

The rule (FREEZE.txt):
- ROUND is the first drand quicknet round whose time is at least 600 s after the GitHub push time t of the FIRST
  commit on branch evidence/combined-draw that adds DRAW_ANNOUNCE.txt. A round's time is genesis + (round − 1)·period.
- So round = ceil((t + 600 − genesis) / period) + 1. When t + 600 − genesis is an exact multiple of the period, the
  round whose time equals t + 600 counts ("at least").

The check of a round (`verify`):
- **Scheme** bls-unchained-g1-rfc9380 (quicknet). The public key is a compressed G2 point (96 bytes), the signature a
  compressed G1 point (48 bytes), each exactly that length in lowercase hex: decompression ignores leading zero bytes,
  so a padded signature would verify and change sha256(signature); it is refused.
- **The message** is sha256(round as an 8-byte big-endian integer).
- **The hash to G1** is RFC 9380's BLS12381G1_XMD:SHA-256_SSWU_RO_, with DST "BLS_SIG_BLS12381G1_XMD:SHA-256_SSWU_RO_NUL_".
- **Valid** iff e(signature, g2) = e(H(message), public key), with both points on the curve and in their subgroups.
- **Also checked:** randomness = sha256(signature bytes).
- **Library:** py_ecc 8.0.0, pinned in research/layered-networks/requirements_beacon.txt.

  beacon_verify.py round CHAIN.json PUSH_TIME_ISO        the round the rule fixes
  beacon_verify.py verify CHAIN.json ROUND.json          exit 0 iff the round's signature and randomness hold
CHAIN.json: {"public_key": hex, "genesis_time": int, "period": int, "schemeID": "bls-unchained-g1-rfc9380", "hash": hex}
(drand's /info). ROUND.json: {"round": int, "signature": hex, "randomness": hex} (drand's /public/<round>).
"""
import datetime
import hashlib
import json
import math
from pathlib import Path
import sys

QUICKNET = dict(hash="52db9ba70e0cc0f6eaf7803dd07447a1f5477735fd3f661792ba94600c84e971",
                schemeID="bls-unchained-g1-rfc9380")
DST = b"BLS_SIG_BLS12381G1_XMD:SHA-256_SSWU_RO_NUL_"
DELAY_S = 600


def parse_time(t):
    """An ISO-8601 time with its UTC offset (…Z or +00:00), as an aware datetime (microsecond resolution)."""
    d = datetime.datetime.fromisoformat(str(t).replace("Z", "+00:00"))
    if d.tzinfo is None:
        raise ValueError("the push time must carry its UTC offset")
    return d


def round_after(chain, push_time, delay_s=DELAY_S):
    """The first round whose time genesis + (round-1)*period is at least push_time + delay_s."""
    t = parse_time(push_time)
    epoch = datetime.datetime(1970, 1, 1, tzinfo=datetime.timezone.utc)
    us = (t - epoch) // datetime.timedelta(microseconds=1) + delay_s * 10 ** 6
    g_us, p_us = int(chain["genesis_time"]) * 10 ** 6, int(chain["period"]) * 10 ** 6
    r = -(-(us - g_us) // p_us) + 1                       # exact integer ceiling
    assert g_us + (r - 1) * p_us >= us and (r == 1 or g_us + (r - 2) * p_us < us)
    return max(r, 1)


def round_time(chain, r):
    return int(chain["genesis_time"]) + (int(r) - 1) * int(chain["period"])


def message(r):
    return hashlib.sha256(int(r).to_bytes(8, "big")).digest()


def verify(chain, rnd):
    from py_ecc.bls.hash_to_curve import hash_to_G1
    from py_ecc.bls.point_compression import decompress_G1, decompress_G2
    from py_ecc.optimized_bls12_381 import G2, curve_order, is_on_curve, b, b2, multiply, pairing, Z1, Z2
    out = dict(round=int(rnd["round"]))
    if chain.get("schemeID") != "bls-unchained-g1-rfc9380":
        return dict(out, ok=False, why=f"scheme {chain.get('schemeID')} is not bls-unchained-g1-rfc9380")
    hexes = lambda x, n: isinstance(x, str) and len(x) == 2 * n and all(c in "0123456789abcdef" for c in x)
    if not hexes(rnd.get("signature"), 48) or not hexes(chain.get("public_key"), 96):
        return dict(out, ok=False, why="the signature is not exactly 48 bytes (96 lowercase hex characters), or the "
                                       "public key not exactly 96 bytes: a padded or re-written point is refused")
    sig_b, pk_b = bytes.fromhex(rnd["signature"]), bytes.fromhex(chain["public_key"])
    out["randomness_ok"] = hashlib.sha256(sig_b).hexdigest() == rnd["randomness"].lower()
    try:
        S = decompress_G1(int.from_bytes(sig_b, "big"))
        P = decompress_G2((int.from_bytes(pk_b[:48], "big"), int.from_bytes(pk_b[48:], "big")))
    except Exception as e:
        return dict(out, ok=False, why=f"point decoding: {e!r}")
    sub = (is_on_curve(S, b) and is_on_curve(P, b2) and multiply(S, curve_order) == Z1
           and multiply(P, curve_order) == Z2)
    H = hash_to_G1(message(rnd["round"]), DST, hashlib.sha256)
    lhs = pairing(G2, S)                                  # e(S, g2): py_ecc's pairing takes (G2 point, G1 point)
    rhs = pairing(P, H)
    out.update(subgroups_ok=bool(sub), signature_ok=bool(lhs == rhs))
    out["ok"] = out["randomness_ok"] and out["subgroups_ok"] and out["signature_ok"]
    return out


if __name__ == "__main__":
    c, *a = sys.argv[1:] or ["help"]
    if c == "round":
        chain = json.loads(Path(a[0]).read_text())
        r = round_after(chain, a[1])
        print(json.dumps(dict(push_time=a[1], delay_s=DELAY_S, round=r, round_time_unix=round_time(chain, r))))
    elif c == "verify":
        res = verify(json.loads(Path(a[0]).read_text()), json.loads(Path(a[1]).read_text()))
        print(json.dumps(res))
        sys.exit(0 if res["ok"] else 1)
    else:
        sys.exit(__doc__)
