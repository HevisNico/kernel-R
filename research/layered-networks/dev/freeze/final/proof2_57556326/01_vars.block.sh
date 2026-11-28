L=/tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/frz/f3/P7/kernel-R/research/layered-networks
F=$(git -C "$L" rev-parse HEAD)
PY=/tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/prefreeze2/venvA/bin/python
python() { "$PY" "$@"; }                                # every `python` in the blocks is the pinned one
PATH=$HOME/.elan/bin:$PATH python -B "$L/envcheck_layered4.py" check > ENVCHECK.json
python -c "import json, sys; sys.exit(0 if json.load(open('ENVCHECK.json'))['ok'] is True else 1)" && echo "envcheck ok" || { echo "REFUSED: envcheck_layered4 is not ok with $PY: stop"; false; }
