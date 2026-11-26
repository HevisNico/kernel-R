"""The drand chain the draw uses, pinned, and its chain hash recomputed offline (the owner's approval, relayed
2026-11-25). Development only.

drand's chain hash is the sha256 of:
- the period as a 4-byte big-endian integer;
- the genesis time as an 8-byte big-endian integer;
- the public key's bytes;
- the groupHash bytes;
- the beacon ID ("quicknet").
The scheme ID is not part of it. This is reproduced offline from /info. It gives
52db9ba70e0cc0f6eaf7803dd07447a1f5477735fd3f661792ba94600c84e971 for quicknet, which is the chain hash the freeze names.
So the frozen hash pins the public key, the genesis, the period and the group.

QUICKNET is /info as fetched from api.drand.sh and api2.drand.sh (identical, byte for byte) on 2026-11-25.

  beacon_chain.py check [INFO.json]     exit 0 iff the chain hash of INFO (default: QUICKNET) is the frozen one, and
                                        INFO equals QUICKNET field for field
"""
import hashlib
import json
from pathlib import Path
import struct
import sys

CHAIN_HASH = "52db9ba70e0cc0f6eaf7803dd07447a1f5477735fd3f661792ba94600c84e971"
QUICKNET = {"public_key": "83cf0f2896adee7eb8b5f01fcad3912212c437e0073e911fb90022d3e760183c8c4b450b6a0a6c3ac6a5776a2d1064510d"
                          "1fec758c921cc22b0e17e63aaf4bcb5ed66304de9cf809bd274ca73bab4af5a6e9c76a4bc09e76eae8991ef5ece45a",
            "period": 3, "genesis_time": 1692803367, "hash": CHAIN_HASH,
            "groupHash": "f477d5c89f21a17c863a7f937c6a6d15859414d2be09cd448d4279af331c5d3e",
            "schemeID": "bls-unchained-g1-rfc9380", "metadata": {"beaconID": "quicknet"}}


def chain_hash(info):
    h = hashlib.sha256()
    h.update(struct.pack(">I", int(info["period"])))
    h.update(struct.pack(">q", int(info["genesis_time"])))
    h.update(bytes.fromhex(info["public_key"]))
    h.update(bytes.fromhex(info["groupHash"]))
    bid = (info.get("metadata") or {}).get("beaconID") or ""
    if bid not in ("", "default"):
        h.update(bid.encode())
    return h.hexdigest()


def check(info=QUICKNET):
    return chain_hash(info) == CHAIN_HASH and info.get("hash") == CHAIN_HASH and all(info.get(k) == v for k, v in QUICKNET.items())


if __name__ == "__main__":
    a = sys.argv[1:]
    if a and a[0] == "check":
        info = json.loads(Path(a[1]).read_text()) if len(a) > 1 else QUICKNET
        ok = check(info)
        print(json.dumps(dict(chain_hash=chain_hash(info), frozen=CHAIN_HASH, ok=ok)))
        sys.exit(0 if ok else 1)
    sys.exit(__doc__)
