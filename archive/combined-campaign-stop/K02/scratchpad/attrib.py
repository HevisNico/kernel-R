import json, os, subprocess, sys, collections
sys.path.insert(0, os.path.expanduser('~/runner/kernel-R/research/layered-networks'))
import draw_seeds as d
H = os.path.expanduser('~')
old = set(json.load(open(H+'/runner/kernel-R/research/layered-networks/EXCLUDED.json'))['seeds'])
new = json.load(open(H+'/runner/scan_final/EXCLUDED_SECOND_SCAN.json'))
added = set(new['seeds']) - old
repo = H+'/runner/scan_final/scanrepo'
per = collections.OrderedDict(); hit = collections.Counter()
for name, info in new['refs'].items():
    if 'numbers' not in info: continue
    g = subprocess.run(["git","-C",repo,"grep","-I","-h","-i","-E",r"seed|fakepid|rehearsal|dry.run",info['tip']],capture_output=True,text=True)
    found=set()
    for line in g.stdout.splitlines():
        if d.LINE.search(line): found |= d.numbers(line)
    assert len(found)==info['numbers'], name
    c = found & added
    if c: per[name.replace('refs/remotes/origin/','')] = c; hit.update(c)
only = collections.Counter()
for n,c in per.items():
    only[n] = sum(1 for x in c if hit[x]==1)
print("added", len(added), "covered", len(set(hit)))
for n,c in sorted(per.items(), key=lambda kv:-len(kv[1])):
    print(f"{n}: {len(c)} (only here: {only[n]})")
