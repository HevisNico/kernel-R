"""beacon_verify.py and beacon_chain.py on rounds published by drand quicknet (no network).
Run with py_ecc 8.0.0: python -B tests/test_beacon_published.py

The data: /info and rounds 1000000, 20000000 and 34278954, as fetched from api.drand.sh and api2.drand.sh (byte for byte
identical) and relayed by the coordinator on 2026-11-25.
- Every round verifies against the published public key.
- Changing one byte of the signature, the round number or the key fails.
- The chain hash, recomputed offline, is 52db9ba7…
"""
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import beacon_chain as BC  # noqa: E402
import beacon_verify as BV  # noqa: E402

ROUNDS = [
    dict(round=1000000, randomness="b22aad4794f7451896f7a371aa46106fd84d919f3f569acd5b2fddf1d1440af3",
         signature="83ad29e4c409f9470fc2ef02f90214df49e02b441a1a241a82d622d9f608ef98fd8b11a029f1bee9d9e83b45088abe72"),
    dict(round=20000000, randomness="f39c98df5525968e6622e0c63edb3d1f9c5607cf780db78abdded36e4b3dba95",
         signature="96892582a33552a7b67ba44ef09c3ccd535bbebe760c93ecf45be8958d0c0f06390c6d19d7bf492eb806af7eef6b125c"),
    dict(round=34278954, randomness="ca4a4015bcf54c6951e39ee81c085a65742d5794a66a9dceccb400d8cd97764e",
         signature="8fe9e583f82cdb77b61bf625b8e8f51782fbb4da2776f56455dc227b0e46e857fb6354a12b554bd530f8c8a5285f126d"),
]


def flip(hexs, i=10):
    b = bytearray(bytes.fromhex(hexs))
    b[i] ^= 0x01
    return b.hex()


def test_chain_hash_offline():
    assert BC.chain_hash(BC.QUICKNET) == BC.CHAIN_HASH and BC.check()
    assert BC.chain_hash(dict(BC.QUICKNET, public_key=flip(BC.QUICKNET["public_key"]))) != BC.CHAIN_HASH
    assert BC.chain_hash(dict(BC.QUICKNET, genesis_time=BC.QUICKNET["genesis_time"] + 1)) != BC.CHAIN_HASH


def test_published_rounds_verify():
    for r in ROUNDS:
        res = BV.verify(BC.QUICKNET, r)
        assert res["ok"], res


def test_one_byte_changes_fail():
    r = ROUNDS[2]
    assert not BV.verify(BC.QUICKNET, dict(r, signature=flip(r["signature"])))["ok"]          # signature byte
    assert not BV.verify(BC.QUICKNET, dict(r, round=r["round"] ^ 0x01))["ok"]                 # round number
    bad_key = dict(BC.QUICKNET, public_key=flip(BC.QUICKNET["public_key"], 60))
    assert not BV.verify(bad_key, r)["ok"]                                                    # key byte


if __name__ == "__main__":
    n = 0
    for k, f in list(globals().items()):
        if k.startswith("test_"):
            f()
            n += 1
            print("ok", k)
    print(f"{n} tests passed")
