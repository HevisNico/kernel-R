# Amendment 1: where the virtual environment must be

Written on 2026-11-14, before the manifest, the inventories and the attempt
marker of the campaign exist, and before any launch. `PREDICTION.md` is not
changed. No frozen file is changed: the files listed in `plan.FROZEN` are,
byte for byte, those of commit `1d11533`, the head that the independent
review approved.

## What was found

Machine b, preparing its environment, ran the `identity` check of the
launcher with a virtual environment at `/home/user/campaign/python`. The
check refused: six of the seven pinned values matched, the numpy record hash
did not (`064d9206…c06e` instead of the pinned `064003bd…e2fb`). Machine b
stopped and reported, without working around it.

The cause: the pinned value is the SHA-256 of the file `RECORD` that pip
writes when it installs numpy. That file lists the hashes of two small
scripts, `bin/f2py` and `bin/numpy-config`, whose first line is the absolute
path of the interpreter of the virtual environment. The hash therefore
depends on where the virtual environment is. The pinned value was taken with
the virtual environment at

    /home/user/owner-prep/venv312

and holds only there. The second launch kit did not say so; its README gives
another path as an example, with which the check cannot pass.

## The rule

Both machines create their virtual environment at exactly
`/home/user/owner-prep/venv312`:

```sh
/usr/bin/python3.12 -m venv /home/user/owner-prep/venv312
/home/user/owner-prep/venv312/bin/python -m pip install numpy==2.3.5
```

and run the launcher with that interpreter. The check of the launcher is not
changed and stays exact: Python 3.12.3 and numpy 2.3.5 are identical on the
two machines, by hash, as `PREDICTION.md` requires. Nothing else of the
environment depends on a path: the simulator is `/usr/bin/ngspice` and the
PDK is identified by its commit. For the decks of the two machines to carry
the same model path, both keep the PDK at `/home/user/campaign/pdk`.

Checked before this file was committed: machine a created a second virtual
environment at the path machine b had used and obtained exactly the value
machine b reported (`064d9206…c06e`); with the path of the pin it obtains the
pinned value. On these containers the hash depends on the path and on nothing
else. Machine b's own check at the pinned path is made by the launcher, which
refuses to write its inventory and to launch if the value differs.

## What follows for the manifest

The implementation commit of the manifest (`source_commit`) is the commit
that adds this file, not `1d11533`: the launcher refuses any file that
appears after the implementation commit other than the manifest, the two
inventories and the attempt marker. The launcher checks that every CI job is
green on that exact commit before the marker is written, and again at each
launch.

## Where the evidence goes, in detail

`PREDICTION.md` says that the waveforms of the whole runs go unchanged to
the private repository `HevisNico/kernel-R-circuit`. Each machine pushes the
whole of its collected evidence there, on its own branch:
`supervisor-campaign-1/machine-a` and `supervisor-campaign-1/machine-b`,
under `11-supervisor-campaign/`. The decks, logs, records, fingerprints,
small waveforms, the SHA-256 list of everything and the generated report are
then committed to this repository by machine a, which runs the one analysis.
