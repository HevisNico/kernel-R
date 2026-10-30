"""Embed recorded simulations in the self-contained viewer fragment."""
from pathlib import Path
import argparse,json,re,html
from simulate import CONFIGS,PHASES,EDGES


def make_viewer(results,target):
    runs={}
    for name in CONFIGS:
        r=json.loads((results/(name+'.json')).read_text())
        samples=[]
        for snap in r['samples']:
            row=[round(snap['time'],3)]
            for c in snap['cells']:row += [round(g,6) for g in c['gains']]+[round(c['b'],6),round(c['E'],3),c['main_mode'],int(c['alive'])]
            samples.append(row)
        runs[name]=dict(samples=samples,spikes=[[round(o['time'],5),o['node']] for o in r['outputs']],
                        copies=[[c['time'],c['source'],c['target']] for c in r['copies']])
    phase_labels=['A learns','A teaches B','B explores, A relearns','B teaches C',
                  'C speeds up, B and A relearn','Open exchange and final quiet']
    phases=[(start,end,label) for (start,end,_),label in zip(PHASES,phase_labels)]
    data=dict(runs=runs,phases=phases,edges=EDGES,configs=CONFIGS)
    template=Path(__file__).with_name('viewer_template.html').read_text()
    target.write_text(template.replace('__R_DATA__',json.dumps(data,separators=(',',':'),ensure_ascii=False)))
    print(target,target.stat().st_size,'bytes')
    return data
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--results',type=Path,required=True);p.add_argument('--target',type=Path,required=True);p.add_argument('--standalone-template',type=Path);p.add_argument('--standalone-target',type=Path)
    a=p.parse_args();data=make_viewer(a.results,a.target)
    if a.standalone_template:
        if not a.standalone_target:p.error('--standalone-target is required with --standalone-template')
        document=a.standalone_template.read_text()
        match=re.search(r'data-srcdoc="([^"]*)"',document)
        if not match:raise ValueError('standalone iframe template not found')
        frame=html.unescape(match.group(1))
        # Refresh labels and controls as well as recordings in exported viewers.
        fragment=a.target.read_text()
        pattern=r'<div id="r-reciproque">.*?\n</div>'
        frame,count=re.subn(pattern,lambda m:fragment.rstrip(),frame,count=1,flags=re.S)
        if count!=1:raise ValueError('viewer fragment not found')
        frame=re.sub(r'<title>.*?</title>','<title>R — reciprocal learning</title>',frame,count=1,flags=re.S)
        document=re.sub(r'<title>.*?</title>','<title>R — reciprocal learning</title>',document,count=1,flags=re.S)
        document=document.replace('title="R — apprentissage réciproque"','title="R — reciprocal learning"')
        # Recompute the span after changing the document title.
        match=re.search(r'data-srcdoc="([^"]*)"',document)
        document=document[:match.start(1)]+html.escape(frame,quote=True)+document[match.end(1):]
        a.standalone_target.write_text(document)
        print(a.standalone_target)
