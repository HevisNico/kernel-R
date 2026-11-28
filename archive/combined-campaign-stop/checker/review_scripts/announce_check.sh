python() { "$PY" "$@"; }
    python -B -c "if True:
        import sys, tempfile; sys.path.insert(0, '$L'); import analysis as A
        R = '$TWINR'
        c, s, v = A.scan_verify_record(R, '$HS', open('$S', 'rb').read(), '$F')
        t = A.record_created(R, c, tempfile.mkdtemp())
        print('the scan verify record', A.VERIFY_BRANCH, c, 'created', t, 'verified scan_sha256', s, 'VS', v)" || { echo "REFUSED: the published scan verify record (evidence/combined-scan-verify) does not verify HS ($HS) for the freeze F ($F), or its branch is not single-use: no commit, no push"; exit 1; }
echo "BLOCK CHECK PASSED (the announce would continue to its commit)"
