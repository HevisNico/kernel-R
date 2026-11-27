"""The campaign's seed draw (CAMPAIGN_PLAN_DRAFT.md §8; PREDICTION draft, 2026-11-24). Development only.

  draw_seeds.py scan EXCLUDED.json [REPO]               the frozen exclusion list, from every fetched branch
  draw_seeds.py draw BEACON ROUND EXCLUDED.json DRAW.json [NOT1=60 ANDOR3=49 XOR3=49]
  draw_seeds.py print EXCLUDED.json                     the list in full (for PREDICTION.md), ranges collapsed

**The exclusion list (scan).**
- **Where:** every branch under refs/remotes/origin, each fetched by name, plus HEAD.
- **Which lines:** every line of a tracked text file (`git grep -I`) that names a seed. That is a line matching
  `seed` (any case: seed, seeds, setseed, noise_seed, SEED), `FAKEPID`, or `rehearsal` / `dry run` next to a number.
- **What is taken from each line:** every integer of 4 to 7 digits, and every range `a–b` or `a-b` between two such
  integers with b − a ≤ 2000, expanded.
- **Why so wide:** more than is used is excluded (a year, a size), never less. Over-exclusion only removes candidates
  from the draw.
- **What is recorded:** the refs scanned, with their tips, and the sha256 of the list.

**The draw.**
- A candidate seed is S = 10000 + (H mod 90000), with H the SHA-256 of `"<beacon>|<round>|<group>|<k>"` read as a
  big-endian integer, for k = 0, 1, 2, …, group by group in GROUP_ORDER (NOT1, ANDOR3, XOR3), whatever the order the
  sizes are given in. <beacon> is the canonical writing of drand's randomness, 64 lowercase hex characters: any other
  writing is refused (canonical_beacon), so one signed value gives one list. <round> is an integer.
- **Rejected:** an S that is excluded, already drawn, or whose noise seeds 10 S + n (n = 0..3) are excluded.
- The first N accepted S of each group are its seeds, in draw order.
- **Checked (an error, not an assert):** no drawn seed and no noise seed of one is in the exclusion list, and all are
  distinct.
- Deterministic: the same beacon, round and list give the same DRAW.json bytes.
"""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
LO, SPAN = 10000, 90000
LINE = re.compile(r"(?i)seed|fakepid|rehearsal|dry.run")
INT = re.compile(r"(?<![0-9.])([0-9]{4,7})(?![0-9])")
RANGE = re.compile(r"(?<![0-9.])([0-9]{4,7})\s*(?:–|-|\.\.)\s*([0-9]{4,7})(?![0-9])")
DEFAULT_N = dict(NOT1=60, ANDOR3=49, XOR3=49)
GROUP_ORDER = ("NOT1", "ANDOR3", "XOR3")      # the draw's group order, pinned (not the order of the sizes given)


def canon(obj):
    return (json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True) + "\n").encode()


def numbers(line):
    out = set(int(x) for x in INT.findall(line))
    for a, b in RANGE.findall(line):
        a, b = int(a), int(b)
        if a < b <= a + 2000:
            out.update(range(a, b + 1))
    return out


def scan(repo):
    repo = Path(repo)
    refs = subprocess.run(["git", "-C", str(repo), "for-each-ref", "--format=%(refname) %(objectname)", "refs/remotes/origin"],
                          capture_output=True, text=True, check=True).stdout.split("\n")
    refs = [r.split() for r in refs if r.strip()]
    head = subprocess.run(["git", "-C", str(repo), "rev-parse", "HEAD"], capture_output=True, text=True, check=True).stdout.strip()
    refs.append(["HEAD", head])
    seen_tips, excluded, per_ref = set(), set(), {}
    for name, tip in refs:
        if tip in seen_tips:
            per_ref[name] = dict(tip=tip, same_tree_as_scanned=True)
            continue
        seen_tips.add(tip)
        g = subprocess.run(["git", "-C", str(repo), "grep", "-I", "-h", "-i", "-E", r"seed|fakepid|rehearsal|dry.run", tip],
                           capture_output=True, text=True)
        found = set()
        for line in g.stdout.splitlines():
            if LINE.search(line):
                found |= numbers(line)
        excluded |= found
        per_ref[name] = dict(tip=tip, numbers=len(found))
    seeds = sorted(excluded)
    return dict(format="layered-excluded-seeds/1", rule=__doc__.split("**The draw.**")[0].split("**The exclusion list (scan).**")[1].strip(),
                refs=per_ref, count=len(seeds), seeds=seeds, seeds_sha256=hashlib.sha256(canon(seeds)).hexdigest())


MAX_EXCLUDED_FRACTION = 0.20     # N5: a list excluding more of the draw range than this is refused


def excluded_fraction(excluded):
    """The share of the draw range's candidates S (10000 <= S < 100000) that the list rejects: S itself excluded, or
    one of its noise seeds 10 S + n (n = 0..3)."""
    ex = set(excluded["seeds"])
    return sum(1 for s in range(LO, LO + SPAN) if s in ex or any(10 * s + j in ex for j in range(4))) / SPAN


def canonical_beacon(beacon):
    """The beacon's ONE accepted writing: the 32 bytes of drand's randomness, as 64 lowercase hex characters (or the
    32 bytes themselves). Any other writing of the same value (upper or mixed case, spaces, a 0x prefix) is refused,
    so that one verified value gives one list of seeds."""
    if isinstance(beacon, (bytes, bytearray)):
        if len(beacon) != 32:
            raise ValueError(f"the beacon is {len(beacon)} bytes, not 32")
        return bytes(beacon).hex()
    if not isinstance(beacon, str) or len(beacon) != 64 or any(c not in "0123456789abcdef" for c in beacon):
        raise ValueError(f"the beacon {beacon!r} is not 64 lowercase hex characters (32 bytes)")
    return beacon


def draw(beacon, rnd, excluded, n=DEFAULT_N):
    """The draw, from one canonical beacon (canonical_beacon), an integer round, and the groups in GROUP_ORDER whatever
    the order of `n`. Every check raises (python -O cannot remove it)."""
    beacon = canonical_beacon(beacon)
    if not isinstance(rnd, int) or isinstance(rnd, bool) or rnd < 1:
        raise ValueError(f"the round {rnd!r} is not a positive integer")
    if set(n) - set(GROUP_ORDER) or any(not isinstance(v, int) or isinstance(v, bool) or v < 1 for v in n.values()):
        raise ValueError(f"the sizes {n!r} are not positive integers for groups of {GROUP_ORDER}")
    ex = set(excluded["seeds"])
    if hashlib.sha256(canon(sorted(ex))).hexdigest() != excluded["seeds_sha256"]:
        raise ValueError("the exclusion list was altered")
    drawn, groups, tried = set(), {}, {}
    for g in (x for x in GROUP_ORDER if x in n):        # a fixed order: `drawn` is shared across the groups
        k_n, out, k = n[g], [], 0
        while len(out) < k_n:
            h = int.from_bytes(hashlib.sha256(f"{beacon}|{rnd}|{g}|{k}".encode()).digest(), "big")
            s = LO + h % SPAN
            k += 1
            if s in ex or s in drawn or any(10 * s + j in ex for j in range(4)):
                continue
            out.append(s)
            drawn.add(s)
        groups[g], tried[g] = out, k
    allseeds = [s for v in groups.values() for s in v]
    if len(set(allseeds)) != len(allseeds) or set(allseeds) & ex or {10 * s + j for s in allseeds for j in range(4)} & ex:
        raise ValueError("the drawn seeds are not distinct, or one of them or of their noise seeds is excluded")
    return dict(format="layered-draw/1", beacon=beacon, round=rnd, n={g: n[g] for g in GROUP_ORDER if g in n},
                groups=groups, candidates_tried=tried, excluded_sha256=excluded["seeds_sha256"],
                excluded_count=excluded["count"], draw_script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())


def collapse(seeds):
    out, i = [], 0
    while i < len(seeds):
        j = i
        while j + 1 < len(seeds) and seeds[j + 1] == seeds[j] + 1:
            j += 1
        out.append(str(seeds[i]) if i == j else f"{seeds[i]}–{seeds[j]}")
        i = j + 1
    return out


if __name__ == "__main__":
    c, *a = sys.argv[1:] or ["help"]
    if c == "scan":
        r = scan(a[1] if len(a) > 1 else HERE.parents[1])
        Path(a[0]).write_bytes(canon(r))
        print(f"{r['count']} excluded integers from {len(r['refs'])} refs; sha256 {r['seeds_sha256']}")
    elif c == "draw":
        beacon, rnd, exf, out, *ns = a
        n = dict(DEFAULT_N, **{k: int(v) for k, v in (x.split("=") for x in ns)}) if ns else DEFAULT_N
        r = draw(beacon, int(rnd), json.loads(Path(exf).read_text()), n)
        Path(out).write_bytes(canon(r))
        print(json.dumps({g: v[:5] + ["..."] for g, v in r["groups"].items()}))
    elif c == "print":
        r = json.loads(Path(a[0]).read_text())
        print(f"Excluded ({r['count']} integers, sha256 {r['seeds_sha256']}):")
        print(", ".join(collapse(r["seeds"])))
    else:
        sys.exit(__doc__)
