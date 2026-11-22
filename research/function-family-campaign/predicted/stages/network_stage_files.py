"""The campaign's network stage files (amendments 2 and 2c), from the pushed PREDICTED.json. Data in, JOBS files out:
no simulation, no frozen file changed. Not frozen code itself; its output is pushed and reviewed before any launch.

  network_stage_files.py PREDICTED.json OUT_DIR [--no-check]

For each machine Mn and stage Q, N1, N2, N3 (the frozen manifests.network_plan, which refuses a record whose network
runs are not sections 4 and 7's), OUT_DIR/JOBS_<stage>_<Mn>.json in dosedev2.many's form:
  {"folder": "$O/campaign-runs/Mn/<stage>", "waves": [[{"id", "limit_s", "argv"}, ...]]}
  argv: family_net.py run REPO $O/campaign-runs/Mn/<id> <id> <seed> <member> <stage> <kind> <round> PREDICTED NGSPICE PDK
  limit_s: amendment 2's rule, 10 x ceil(2 x r x n / 10), n the slots of the run's own calendar
           (family_net.network on the record's needs and unary ports), r amendment 2's table. It is the hard timeout:
           a run cut there is missing, never replaced.
A stage with no job gets no file. Every job is checked with `family_net.py check` against PREDICTED.json (admitted,
and its noise seed equal to the record's), unless --no-check. OUT_DIR/STAGE_FILES.json lists every job with n, r and
its limit; OUT_DIR/JOBS_SHA256SUMS covers the files.
"""
import hashlib
import json
import math
from pathlib import Path
import subprocess
import sys

O = "/home/user/owner-prep"
W = O + "/wt"
PY = O + "/venv312-dev/bin/python"
REPO = W + "/campaign-6-impl"
NET = W + "/ffnet/research/function-family-campaign/net/family_net.py"
NGSPICE, PDK = "/usr/bin/ngspice", O + "/pdk-src"
PRED_ON_MACHINE = O + "/predicted/PREDICTED.json"          # where each machine puts the pushed record, checked
# amendment 2's r, seconds per slot: (member, kind) -> r
R = {("X1", "quiet"): 37.50, ("X1", "noisy"): 49.00, ("X1", "untrained"): 19.00,
     ("X2", "quiet"): 44.27, ("X2", "noisy"): 50.00, ("X2", "untrained"): 19.00,
     ("F4", "quiet"): 45.91, ("F4", "noisy"): 55.45, ("F4", "untrained"): 16.50,
     ("F2", "quiet"): 42.56, ("F2", "noisy"): 74.96, ("F2", "untrained"): 13.25,
     ("F3", "quiet"): 37.56, ("F3", "noisy"): 55.08, ("F3", "untrained"): 11.25}
CONTROL = dict(quiet="skew", untrained="untrained", noisy=None)


def limit_of(member, kind, n):
    """Amendment 2: 10 x ceil(2 x r x n / 10), exactly (r has two decimals: computed in hundredths)."""
    r100 = round(R[(member, kind)] * 100)
    return 10 * math.ceil(2 * r100 * n / 1000)


def generate(pred_path, out, check=True, net_cmd=None):
    import family_net as N
    import manifests as MF
    N.paths(REPO)
    pred = json.loads(Path(pred_path).read_text())
    assert pred["mode"] == "campaign", "refused: not a campaign record"
    plan = MF.network_plan(pred)
    out = Path(out)
    out.mkdir(parents=True, exist_ok=False)
    listing, files = [], {}
    for m, stages in plan.items():
        for st, jobs in stages.items():
            if not jobs:
                continue
            wave = []
            for j in jobs:
                n = len(N.network(j["member"], j["needs"], j["unary_ports"] or {}, CONTROL[j["kind"]])[1])
                lim = limit_of(j["member"], j["kind"], n)
                rnd = j["round"] if j["kind"] == "noisy" else 0
                argv = [PY, "-B", NET, "run", REPO, f"{O}/campaign-runs/{m}/{j['id']}", j["id"], str(j["seed"]), j["member"], st,
                        j["kind"], str(rnd), PRED_ON_MACHINE, NGSPICE, PDK]
                wave.append(dict(id=j["id"], limit_s=lim, argv=argv))
                row = dict(machine=m, stage=st, id=j["id"], seed=j["seed"], member=j["member"], kind=j["kind"], round=rnd,
                           noise_seed=j.get("noise_seed"), slots=n, r_s_per_slot=R[(j["member"], j["kind"])], limit_s=lim)
                if check:
                    cmd = (net_cmd or [PY, "-B", NET]) + ["check", REPO, str(j["seed"]), j["member"], st, j["kind"], str(rnd), str(pred_path)]
                    p = subprocess.run(cmd, capture_output=True, text=True)
                    assert p.returncode == 0, f"refused by family_net check: {j['id']}: {p.stderr.strip()[-300:]}"
                    a = json.loads(p.stdout.strip().splitlines()[-1])
                    assert a["noise_id"] == j.get("noise_seed"), f"{j['id']}: noise seed {a['noise_id']} is not the record's {j.get('noise_seed')}"
                    row["checked"] = "admitted by family_net check"
                listing.append(row)
            name = f"JOBS_{st}_{m}.json"
            (out / name).write_text(json.dumps(dict(folder=f"{O}/campaign-runs/{m}/{st}", waves=[wave]), indent=1) + "\n")
            files[name] = hashlib.sha256((out / name).read_bytes()).hexdigest()
    ids = [x["id"] for x in listing]
    assert sorted(ids) == sorted(r["id"] for r in pred["network_runs"]) and len(set(ids)) == len(ids), "refused: not exactly the record's runs"
    (out / "STAGE_FILES.json").write_text(json.dumps(dict(record_sha256=hashlib.sha256(Path(pred_path).read_bytes()).hexdigest(),
                                                          rule="amendment 2: 10 x ceil(2 x r x n / 10)", jobs=listing), indent=1) + "\n")
    files["STAGE_FILES.json"] = hashlib.sha256((out / "STAGE_FILES.json").read_bytes()).hexdigest()
    (out / "JOBS_SHA256SUMS").write_text("".join(f"{h}  {k}\n" for k, h in sorted(files.items())))
    return listing


if __name__ == "__main__":
    assert __debug__, "refused: not with python -O"
    a = sys.argv[1:]
    rows = generate(a[0], a[1], check="--no-check" not in a)
    by = {}
    for r in rows:
        by.setdefault((r["machine"], r["stage"]), []).append(r["id"])
    for k, v in sorted(by.items()):
        print(k[0], k[1], len(v), "jobs")
    print(len(rows), "jobs in all; every one checked" if "--no-check" not in a else "jobs, NOT checked")
