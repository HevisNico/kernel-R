"""Amendment 2, section 3: the proof of the save, on test rounds from 910 (no criterion uses them).

  vproof.py WORK PROOF_A2.json

Identity: one draw of each kind made with and without the save (VAL_NOSAVE=1), the saved vectors byte-identical
(raw_nodate_sha256: the raw file's vectors, without its dated header; and y_sha256, or the stored values); the train,
whose save is the router's and unchanged, made twice. Memory: one full-length draw of each kind with the save, four at
a time, its peak memory recorded. Stops at the first differing pair.
"""
import json, os, subprocess, sys, time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

HERE = Path(__file__).resolve().parent
PY = "/home/user/owner-prep/venv312/bin/python"

PAIRS = [("hold", ["frozen", "7101", "hold", "all", "-", "0.01", "910", "model"]),
         ("window", ["frozen", "7101", "window", "a", "1", "0.002", "911", "model"]),
         ("fire", ["frozen", "7101", "fire", "a", "-", "0.002", "912", "model"]),
         ("pulse", ["frozen", "7101", "pulse", "a", "1", "0.002", "913", "model"]),
         ("v6", ["preset", "7101", "914"]),
         ("v8", ["seeding", "7101", "915"])]
MEMORY = [("hold2", ["frozen", "7101", "hold", "all", "-", "0.08", "920", "model"]),
          ("hold1", ["frozen", "nominal", "hold", "a", "1", "0.08", "920", "model"]),
          ("window", ["frozen", "7101", "window", "a", "1", "0.02", "921", "model"]),
          ("fire", ["frozen", "7101", "fire", "a", "-", "0.02", "922", "model"]),
          ("pulse", ["frozen", "7101", "pulse", "a", "1", "0.02", "923", "model"]),
          ("injected", ["frozen", "7101", "hold", "all", "-", "0.08", "-", "injected"]),
          ("v6", ["preset", "7101", "924"]),
          ("v8", ["seeding", "7101", "925"])]


def run(work, name, args, nosave=False):
    kind = args[0]
    out = Path(work) / (name if kind == "train" else f"{name}.json")
    env = dict(os.environ, VAL_SAMPLES=str(Path(work) / "samples"))
    if nosave:
        env["VAL_NOSAVE"] = "1"
    t0 = time.time()
    p = subprocess.Popen([PY, "-B", str(HERE / "vrun.py"), kind, str(out)] + args[1:], env=env,
                         stdout=subprocess.DEVNULL, stderr=open(str(out) + ".stderr", "w"))
    _, status, ru = os.wait4(p.pid, 0)
    r = json.loads(((out / "meta.json") if kind == "train" else out).read_text()) if os.waitstatus_to_exitcode(status) == 0 else {}
    return dict(name=name, exit=os.waitstatus_to_exitcode(status), wall_s=time.time() - t0, peak_rss_MB=ru.ru_maxrss / 1024,
                save=r.get("save"), raw_nodate_sha256=r.get("raw_nodate_sha256"), y_sha256=r.get("y_sha256"),
                y=r.get("y") if kind == "seeding" else None, u_V=r.get("u_V"))


def main(work, out):
    Path(work).mkdir(parents=True, exist_ok=True)
    res = dict(identity=[], train=None, memory=[])
    jobs = []
    for kind, args in PAIRS:
        jobs += [(f"id_{kind}_save", args, False), (f"id_{kind}_nosave", args, True)]
    jobs += [("id_train_a", ["train", "7101", "916"], False), ("id_train_b", ["train", "7101", "916"], False)]
    with ThreadPoolExecutor(4) as ex:
        got = {j[0]: r for j, r in zip(jobs, ex.map(lambda j: run(work, *j), jobs))}
    ok = True
    for kind, _ in PAIRS:
        a, b = got[f"id_{kind}_save"], got[f"id_{kind}_nosave"]
        same = a["exit"] == 0 and b["exit"] == 0 and a["raw_nodate_sha256"] is not None and \
            a["raw_nodate_sha256"] == b["raw_nodate_sha256"] and a["y_sha256"] == b["y_sha256"] and a["y"] == b["y"] and a["u_V"] == b["u_V"]
        res["identity"].append(dict(kind=kind, identical=same, **{f"{k}_save": a[k] for k in ("exit", "peak_rss_MB", "raw_nodate_sha256", "y_sha256")},
                                    **{f"{k}_nosave": b[k] for k in ("exit", "peak_rss_MB", "raw_nodate_sha256", "y_sha256")}))
        ok &= same
    a, b = got["id_train_a"], got["id_train_b"]
    res["train"] = dict(identical=a["exit"] == 0 and b["exit"] == 0 and a["raw_nodate_sha256"] == b["raw_nodate_sha256"] and a["raw_nodate_sha256"] is not None,
                        raw_nodate_sha256=[a["raw_nodate_sha256"], b["raw_nodate_sha256"]], peak_rss_MB=[a["peak_rss_MB"], b["peak_rss_MB"]],
                        exit=[a["exit"], b["exit"]])
    ok &= res["train"]["identical"]
    res["identity_pass"] = bool(ok)
    Path(out).write_text(json.dumps(res, indent=1) + "\n")
    print("identity", ok, flush=True)
    if not ok:
        return
    with ThreadPoolExecutor(4) as ex:
        mem = list(ex.map(lambda j: run(work, f"mem_{j[0]}", j[1]), MEMORY))
    res["memory"] = [{k: m[k] for k in ("name", "exit", "wall_s", "peak_rss_MB")} for m in mem]
    res["memory_all_exit_0"] = all(m["exit"] == 0 for m in mem)
    Path(out).write_text(json.dumps(res, indent=1) + "\n")
    print("memory", [(m["name"], m["exit"], round(m["peak_rss_MB"]), round(m["wall_s"])) for m in mem], flush=True)


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
