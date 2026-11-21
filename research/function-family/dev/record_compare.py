"""Compare an installed numpy RECORD with the RECORD inside the wheel it came from, line by line.
  record_compare.py WHEEL SITE_PACKAGES_RECORD [OTHER_RECORD...]"""
import hashlib, json, sys, zipfile
def lines(text):
    return dict((l.split(",")[0], l.split(",", 1)[1]) for l in text.splitlines() if l.strip())
whl, *recs = sys.argv[1:]
z = zipfile.ZipFile(whl)
name = next(n for n in z.namelist() if n.endswith(".dist-info/RECORD"))
w = lines(z.read(name).decode())
out = dict(wheel=whl, wheel_sha256=hashlib.sha256(open(whl, "rb").read()).hexdigest(), wheel_record_entries=len(w))
for r in recs:
    t = open(r).read()
    i = lines(t)
    same = [k for k in w if k in i and i[k] == w[k]]
    differ = [k for k in w if k in i and i[k] != w[k]]
    only_installed = sorted(k for k in i if k not in w)
    only_wheel = sorted(k for k in w if k not in i)
    out[r] = dict(record_sha256=hashlib.sha256(t.encode()).hexdigest(), entries=len(i), identical_to_wheel=len(same),
                  differing=differ, only_in_installed=only_installed, only_in_wheel=only_wheel,
                  code_files_identical=all(not k.startswith("numpy") or k.endswith("RECORD") for k in differ + only_wheel))
print(json.dumps(out, indent=1))
