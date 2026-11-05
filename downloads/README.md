# Archived reciprocal prototype

`R_Reciprocal_Prototype.zip` is a frozen research snapshot, not a mirror of
the current checkout. Use [the maintained simulation sources](../experiments/reciprocal/README.md)
for current code and [the reproduction guide](../docs/EXPERIMENTS_AND_REPRODUCTION.md#rebuild-the-zip)
to build a new archive in `dist/`.

The committed snapshot has SHA-256
`34d49bab7ad29d357cbae8ac24fd278623c707fe2f442cc07d0b2166a351b03e`.
Its internal `05_Verification/SHA256SUMS.json` covers every payload file.
The verifier also rejects extra, duplicate, corrupt or unsafe entries:

```sh
python -B tools/prepare_recordings.py --verify-only
```

The research CI runs this verification through the project-layout tests.
Recorded Lean evidence is reproduced from the authenticated observations;
the archived simulation source is not substituted for the maintained engine.
Updating the archive is an explicit snapshot update requiring review of its
pinned identity and recorded evidence, rather than an automatic refresh.
