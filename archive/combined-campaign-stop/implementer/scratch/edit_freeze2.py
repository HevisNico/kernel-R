from pathlib import Path
p = Path("FREEZE.txt"); t = p.read_text()
def rep(a, b):
    global t
    assert t.count(a) == 1, (t.count(a), a[:80])
    t = t.replace(a, b)

# ---- the variables
rep("""    H=<the 64 hex characters that ORDER 2 step (r3) printed after "sha256">
    S=  HS=
    [end]""", """    H=<the 64 hex characters that ORDER 2 step (r3) printed after "sha256">
    S=  HS=  VS=
    [end]""")
rep("""    S=EXCLUDED_SECOND_SCAN.json
    HS=<the 64 hex characters that ORDER 3 step (3) printed after "scan_sha256">
    [end]
  (H and HS are KEPT from step (3)'s printed line: the announce block publishes the list and the second scan's raw
  output only if the copied files have those sha256.)""", """    S=EXCLUDED_SECOND_SCAN.json
    HS=<the 64 hex characters that ORDER 3 step (3) printed after "scan_sha256">
    VS=<the 64 hex characters that ORDER 3 step (3b), [block verify-scan] on the SECOND machine, printed after "VS">
    [end]
  (H and HS are KEPT from step (3)'s printed line, VS from step (3b)'s: the announce block publishes the list and the
  second scan's raw output only if the copied files have those sha256, and only if VS, the sha256 of the second
  machine's own reproduction of the scan, equals HS.)""")

# ---- [block check-list]: F3 (the scan read with an explicit refusal), F1 level 1, F2 (pre_announce)
rep("""        sb = open('EXCLUDED_SECOND_SCAN.json', 'rb').read(); scan = json.loads(sb)
        r, info, _ = A.check_draw(dict(draw='DRAW_REHEARSAL.json'""", """        try:
            sb = open('EXCLUDED_SECOND_SCAN.json', 'rb').read(); scan = json.loads(sb)
        except (OSError, ValueError) as e:
            print('REFUSED: EXCLUDED_SECOND_SCAN.json is missing, unreadable or not JSON:', e, '- push nothing'); sys.exit(1)
        A.check_scan(sb, 'EXCLUDED_SECOND_SCAN.json')
        r, info, _ = A.check_draw(dict(draw='DRAW_REHEARSAL.json'""")
rep("""        second_scan='EXCLUDED_SECOND_SCAN.json'), dict(announce=dict(push_utc=now)), tempfile.mkdtemp(), '$F', True, 'campaign')""",
    """        second_scan='EXCLUDED_SECOND_SCAN.json'), dict(announce=dict(push_utc=now)), tempfile.mkdtemp(), '$F', True, 'campaign',
        pre_announce=True)""")
rep("""       - the second scan's raw output, EXCLUDED_SECOND_SCAN.json, re-read: a superset of the freeze's list;""",
    """       - the second scan's raw output, EXCLUDED_SECOND_SCAN.json, re-read (missing, unreadable or not JSON: an explicit
         refusal), consistent in itself (analysis.check_scan: canonical bytes, draw_seeds.scan's format and rule,
         sorted unique integer seeds, count and seeds_sha256, refs of the scan's shape, HEAD at main's tip), and a
         superset of the freeze's list;""")
rep("""       - analysis.check_rehearsal_seeds, with now as the campaign announce's earliest time and second_scan=, which
         rebuilds the exact union too (analysis.campaign_list).""", """       - analysis.check_rehearsal_seeds, with now as the campaign announce's earliest time and second_scan=, which
         rebuilds the exact union too (analysis.campaign_list). It is called with pre_announce=True, a function
         argument: the announce does not exist yet, so there is no second_scan_sha256 to compare. No command-line key
         reaches it: analysis.py campaign always requires the announce's second_scan_sha256.""")

# ---- ORDER 3 step (3b): the independent reproduction, before the announce
rep("""     If (3) fails, the list is rebuilt from (1) and rechecked; nothing is pushed until (3) passes. The two sha256 that
     (3) prints are KEPT as H and HS (block vars-campaign). The announce block refuses, with no commit and no push,
     unless its copies of X and S have exactly those sha256. The published list is therefore the scan's output with
     the "added" field, which names what was added, and the scan's output itself is published beside it.""",
"""     If (3) fails, the list is rebuilt from (1) and rechecked; nothing is pushed until (3) passes. The two sha256 that
     (3) prints are KEPT as H and HS (block vars-campaign). The announce block refuses, with no commit and no push,
     unless its copies of X and S have exactly those sha256. The published list is therefore the scan's output with
     the "added" field, which names what was added, and the scan's output itself is published beside it.
     (3b) THE SCAN REPRODUCED, INDEPENDENTLY, BEFORE THE ANNOUNCE (F1, level 2). On a SECOND machine, while the push
     hold is in force (no branch of origin may change between the scan and its reproduction), with its own clean
     clone of the freeze and its own pinned Python ([block vars] there), in a new working folder outside any clone:
       - copy the first machine's EXCLUDED_SECOND_SCAN.json into that folder as SCAN_TO_VERIFY.json (nothing else is
         copied; the verifier fetches everything itself);
       - run [block second-scan] verbatim there: the verifier's own scan, EXCLUDED_SECOND_SCAN.json, from its own
         fetch of every branch by name;
       - run [block verify-scan] there. It takes its OWN git ls-remote --heads, NOW, and refuses unless the branch
         inventory the scan to verify records (names AND tips) is exactly that one (a branch missing, extra or at
         another tip refuses) and its HEAD is main's tip; it refuses unless the scan to verify is consistent in itself
         (analysis.check_scan); it refuses unless the verifier's reproduction is the scan to verify, byte for byte. It
         prints the reproduction's sha256 after "VS", KEPT as VS (block vars-campaign). Then, and only then, it
         publishes its record on its own single-use branch evidence/combined-scan-verify, by one creating push of one
         commit (VERIFY.txt, its printed result; VERIFY_LSREMOTE.txt, its own ls-remote; SCAN_LSREMOTE.txt, the
         ls-remote of its own [block second-scan]), never pushed again, never forced, never deleted. The branch is
         created BEFORE the announce, so the announce comes after a public record of the reproduction.
       The campaign announce refuses, with no commit and no push, unless VS equals HS.
    [block verify-scan]
    ( set -e
      ! git rev-parse --is-inside-work-tree >/dev/null 2>&1 || { echo "REFUSED: started inside a git work tree: no commit, no push"; exit 1; }
      [ -f SCAN_TO_VERIFY.json ] || { echo "REFUSED: SCAN_TO_VERIFY.json (the first machine's EXCLUDED_SECOND_SCAN.json) is missing: no commit, no push"; exit 1; }
      [ -f EXCLUDED_SECOND_SCAN.json ] || { echo "REFUSED: EXCLUDED_SECOND_SCAN.json (this machine's own [block second-scan]) is missing: no commit, no push"; exit 1; }
      [ -f SCAN_LSREMOTE.txt ] || { echo "REFUSED: SCAN_LSREMOTE.txt (this machine's own [block second-scan]) is missing: no commit, no push"; exit 1; }
      [ ! -e VERIFY_LSREMOTE.txt ] || { echo "REFUSED: VERIFY_LSREMOTE.txt already exists: no commit, no push"; exit 1; }
      [ ! -e record ] || { echo "REFUSED: record already exists: no commit, no push"; exit 1; }
      git ls-remote --heads https://github.com/HevisNico/kernel-R > VERIFY_LSREMOTE.txt    # this machine's own inventory, now
      python -B -c "if True:
          import hashlib, sys; sys.path.insert(0, '$L'); import analysis as A
          sv, sr = open('SCAN_TO_VERIFY.json', 'rb').read(), open('EXCLUDED_SECOND_SCAN.json', 'rb').read()
          problems = A.verify_scan(sv, sr, open('VERIFY_LSREMOTE.txt').read())
          for x in problems: print('PROBLEM:', x)
          print('the scan is reproduced' if not problems else 'THE SCAN IS NOT REPRODUCED: no announce, push nothing',
          'scan_sha256', hashlib.sha256(sv).hexdigest(), 'VS', hashlib.sha256(sr).hexdigest()); sys.exit(0 if not problems else 1)" > VERIFY.txt || { cat VERIFY.txt; exit 1; }
      cat VERIFY.txt
      # the record, on its own single-use branch, by one creating push of one commit
      V=evidence/combined-scan-verify
      test -z "$(git ls-remote https://github.com/HevisNico/kernel-R refs/heads/$V)" || { echo "REFUSED: $V already exists: no commit, no push"; exit 1; }
      mkdir record
      cd record
      git init -q
      git checkout -q --orphan $V
      git fetch -q --depth 1 https://github.com/HevisNico/kernel-R refs/heads/main     # the owner identity, from main, never printed
      git config user.name "$(git log -1 --format=%an FETCH_HEAD)"
      git config user.email "$(git log -1 --format=%ae FETCH_HEAD)"
      cp ../VERIFY.txt ../VERIFY_LSREMOTE.txt ../SCAN_LSREMOTE.txt .
      [ "$(git rev-parse --show-toplevel)" = "$(pwd -P)" ] || { echo "REFUSED: the repository is not this new folder: no commit, no push"; exit 1; }
      [ "$(git symbolic-ref --short HEAD)" = "$V" ] || { echo "REFUSED: HEAD is not the orphan $V: no commit, no push"; exit 1; }
      ! git rev-parse -q --verify HEAD >/dev/null || { echo "REFUSED: the new repository already has a commit: no commit, no push"; exit 1; }
      git add VERIFY.txt VERIFY_LSREMOTE.txt SCAN_LSREMOTE.txt
      git commit -q -m "Scan verify (campaign)"               # the owner identity, set above
      O=$(git log -1 --format='%an %ae' FETCH_HEAD)
      [ "$(git log -1 --format='%an %ae' HEAD)" = "$O" ] && [ "$(git log -1 --format='%cn %ce' HEAD)" = "$O" ] || { echo "REFUSED: the commit's author or committer is not main's (the owner): no push"; exit 1; }
      git push -q https://github.com/HevisNico/kernel-R HEAD:refs/heads/$V
      echo "verify record pushed: $V $(git rev-parse HEAD)" )
    [end]""")
rep("""  4. The campaign: blocks vars-campaign, announce, draw.""", """  4. The campaign (after (3b) passed and its record is published): blocks vars-campaign, announce, draw.""")

# ---- [block announce]: VS
rep("""      if [ "$M" = campaign ]; then                            # the second scan's raw output, published with the list
        S=$(realpath -e "$S")
        test ${#HS} = 64 || { echo "REFUSED: HS is not a sha256: no commit, no push"; exit 1; }
      else
        [ -z "$S$HS" ] || { echo "REFUSED: S and HS are for the campaign only: no commit, no push"; exit 1; }
      fi""", """      if [ "$M" = campaign ]; then                            # the second scan's raw output, published with the list
        S=$(realpath -e "$S")
        test ${#HS} = 64 || { echo "REFUSED: HS is not a sha256: no commit, no push"; exit 1; }
        [ "$VS" = "$HS" ] || { echo "REFUSED: VS ($VS), the second machine's reproduction of the scan (ORDER 3 (3b)), is not HS ($HS): no commit, no push"; exit 1; }
      else
        [ -z "$S$HS$VS" ] || { echo "REFUSED: S, HS and VS are for the campaign only: no commit, no push"; exit 1; }
      fi""")
rep("""  The announce is checked against H (and, for the campaign, HS), kept from a check made BEFORE it: for rehearsal 2, H
  is the sha256 of the final EXCLUDED_REHEARSAL2.json, printed by ORDER 2 step (r3); for the campaign, H names the
  final list EXCLUDED_SECOND.json and HS the source scan EXCLUDED_SECOND_SCAN.json, both printed by ORDER 3 step (3).
  It is not checked against a sha256 it computes itself.""", """  The announce is checked against H (and, for the campaign, HS and VS), kept from checks made BEFORE it: for rehearsal
  2, H is the sha256 of the final EXCLUDED_REHEARSAL2.json, printed by ORDER 2 step (r3); for the campaign, H names the
  final list EXCLUDED_SECOND.json and HS the source scan EXCLUDED_SECOND_SCAN.json, both printed by ORDER 3 step (3),
  and VS the second machine's independent reproduction of that scan, printed by ORDER 3 step (3b), which must equal
  HS. It is not checked against a sha256 it computes itself.""")
p.write_text(t)
print("ok")
