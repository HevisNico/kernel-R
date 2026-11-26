"""Tests of beacon_verify.py (no network). Run with py_ecc 8.0.0: python -B tests/test_beacon_verify.py

- hash_to_G1 against RFC 9380's own test vector (J.9.1, BLS12381G1_XMD:SHA-256_SSWU_RO_, msg ""), so that the hash used
  by quicknet's scheme is checked offline.
- A round signed here with quicknet's scheme (a G1 signature on sha256(round), the public key on G2, both compressed)
  verifies. A changed signature, round, randomness or public key does not.
- The round rule: the first round whose time is at least the push time + 600 s, including the exact boundary.
NOT covered offline: a round actually published by drand (the network refuses drand's hosts here); verifying one is
the first step of the draw.
"""
import hashlib
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import beacon_verify as BV  # noqa: E402
from py_ecc.bls.hash_to_curve import hash_to_G1  # noqa: E402
from py_ecc.bls.point_compression import compress_G1, compress_G2  # noqa: E402
from py_ecc.optimized_bls12_381 import G2, multiply, normalize  # noqa: E402


def test_rfc9380_hash_to_g1_vector():
    P = normalize(hash_to_G1(b"", b"QUUX-V01-CS02-with-BLS12381G1_XMD:SHA-256_SSWU_RO_", hashlib.sha256))
    assert int(P[0]) == 0x052926add2207b76ca4fa57a8734416c8dc95e24501772c814278700eed6d1e4e8cf62d9c09db0fac349612b759e79a1
    assert int(P[1]) == 0x08ba738453bfed09cb546dbb0783dbb3a5f1f566ed67bb6be0e8c67e2e81a4cc68ee29813bb7994998f3eae0c9c6a265


def signed(sk, r):
    S = multiply(hash_to_G1(BV.message(r), BV.DST, hashlib.sha256), sk)
    sig = compress_G1(S).to_bytes(48, "big")
    a, b = compress_G2(multiply(G2, sk))
    pk = a.to_bytes(48, "big") + b.to_bytes(48, "big")
    chain = dict(public_key=pk.hex(), genesis_time=1692803367, period=3, schemeID="bls-unchained-g1-rfc9380")
    return chain, dict(round=r, signature=sig.hex(), randomness=hashlib.sha256(sig).hexdigest())


def test_verify_roundtrip_and_tampering():
    chain, rnd = signed(0x1234567890abcdef1234567890abcdef, 1000)
    assert BV.verify(chain, rnd)["ok"]
    assert not BV.verify(chain, dict(rnd, round=1001))["ok"]                       # another round's message
    assert not BV.verify(chain, dict(rnd, randomness="00" * 32))["randomness_ok"]
    other, _ = signed(0x42, 1000)
    assert not BV.verify(dict(chain, public_key=other["public_key"]), rnd)["ok"]   # another key
    _, r2 = signed(0x1234567890abcdef1234567890abcdef, 1001)
    assert not BV.verify(chain, dict(rnd, signature=r2["signature"], randomness=r2["randomness"]))["ok"]
    assert not BV.verify(dict(chain, schemeID="pedersen-bls-chained"), rnd)["ok"]


def test_round_rule():
    c = dict(genesis_time=1692803367, period=3)
    r = BV.round_after(c, "2026-12-01T12:00:00Z")
    import datetime
    t = int(datetime.datetime(2026, 12, 1, 12, tzinfo=datetime.timezone.utc).timestamp()) + 600
    assert BV.round_time(c, r) >= t > BV.round_time(c, r - 1)
    exact = BV.round_time(c, 5000) - 600                                           # push time 600 s before round 5000
    iso = datetime.datetime.fromtimestamp(exact, datetime.timezone.utc).isoformat()
    assert BV.round_after(c, iso) == 5000                                          # "at least": the round at t + 600 counts
    iso1 = datetime.datetime.fromtimestamp(exact, datetime.timezone.utc) + datetime.timedelta(microseconds=1)
    assert BV.round_after(c, iso1.isoformat()) == 5001
    try:
        BV.round_after(c, "2026-12-01T12:00:00")
        raise AssertionError("a time without its offset was accepted")
    except ValueError:
        pass


if __name__ == "__main__":
    n = 0
    for k, f in list(globals().items()):
        if k.startswith("test_"):
            f()
            n += 1
            print("ok", k)
    print(f"{n} tests passed")
