"""Three living R cells exchanging pulses and bounded settings.

Numerical exploratory network, not an extension of the A22 certificate. Direct
hybrid ODE integration, positive wire delays, staged introductions and lessons.
The q/m/z/b/E equations are R; settings copies and edge gates are an external protocol.
"""
from pathlib import Path
import argparse,heapq,itertools,json,math,time,hashlib
import numpy as np
from scipy.integrate import solve_ivp

A=math.log(4);K=.5;R=.1;RM=.025;BMAX=1.1
NOMINAL=np.array([4,math.log(1.25)/.02,math.log(8)/1.06,A/.15,
 (1-RM)/(A/(A-K)*(math.exp(-K*.02)-math.exp(-A*.02)))])
NAMES=['A','B','C'];ROOT=Path(__file__).resolve().parents[2]
END=1000.;DELAY=.35
PHASES=[(0,160,'A apprend'),(160,320,'A enseigne à B'),(320,480,'B découvre, A réapprend'),
        (480,640,'B enseigne à C'),(640,800,'C accélère, B et A réapprennent'),(800,1000,'Échanges ouverts et silence final')]
EDGES=[dict(source=0,target=1,port=1,windows=[(160,310),(800,1000)]),
       dict(source=1,target=0,port=2,windows=[(320,470),(640,780),(800,1000)]),
       dict(source=1,target=2,port=1,windows=[(480,630),(800,1000)]),
       dict(source=2,target=1,port=2,windows=[(640,780),(800,1000)])]
COPIES=[(160,0,1),(470,1,0),(480,1,2),(800,2,1),(800,1,0)]
SOURCES=[(float(t),0,0,'monde_A') for t in list(range(0,121,8))+list(range(160,281,8))]
SOURCES += [(float(t),1,2,'nouveauté_B') for t in list(range(320,441,8))+list(range(480,601,8))]
SOURCES += [(float(t),2,0,'cadence_C') for t in range(640,737,4)]
SOURCES += [(float(t),0,0,'test_ouvert') for t in range(820,861,4)]
CONFIGS={'complet':dict(pulses=True,settings=True,reverse=True,plastic=True),
         'impulsions':dict(pulses=True,settings=False,reverse=True,plastic=True),
         'reglages':dict(pulses=False,settings=True,reverse=True,plastic=True),
         'sans_transfert':dict(pulses=False,settings=False,reverse=False,plastic=True),
         'sans_retour':dict(pulses=True,settings=False,reverse=False,plastic=True),
         'sans_plasticite':dict(pulses=True,settings=False,reverse=True,plastic=False)}


def plain(x):
    if isinstance(x,np.generic):return x.item()
    if isinstance(x,dict):return {k:plain(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)):return [plain(v) for v in x]
    return x


class Network:
    def __init__(self,configuration='complet',rtol=1e-9,atol=1e-11,max_step=.15):
        self.configuration=configuration;self.cfg=CONFIGS[configuration]
        self.rtol=rtol;self.atol=atol;self.max_step=max_step
        self.y=np.array([[R,RM,RM,RM,*np.log([.3,1.2,.3]),.08,100.] for _ in range(3)])
        self.main=np.zeros(3,dtype=int);self.aux=np.zeros((3,3),dtype=int);self.alive=np.array([True,False,False])
        self.raw=np.zeros((3,3),dtype=bool);self.origin=np.zeros((3,3));self.t=0.
        self.queue=[];self.sequence=itertools.count();self.outputs=[];self.arrivals=[];self.copies=[];self.samples=[]
        self.transitions=0;self.min_energy=100.;self.root_groups_near=0
        self.add(160,'birth',(1,));self.add(480,'birth',(2,))
        for when,src,dst in COPIES:self.add(when,'copy',(src,dst))
        for when,node,port,label in SOURCES:
            self.add(when,'on',(node,port,label));self.add(when+1,'off',(node,port,label))
        for when in sorted(set([float(x) for x in range(0,1001,2)]+[159.9,309.9,319.9,459.9,469.9,479.9,629.9,639.9,779.9,789.9,799.9])):
            self.add(when,'sample',())
    def add(self,when,kind,payload):heapq.heappush(self.queue,(float(when),next(self.sequence),kind,payload))
    def snapshot(self):
        return dict(time=self.t,cells=[dict(name=NAMES[i],alive=bool(self.alive[i]),q=float(self.y[i,0]),
                    gains=np.exp(self.y[i,4:7]).tolist(),b=float(self.y[i,7]),E=float(self.y[i,8]),
                    main_mode=int(self.main[i]),aux_modes=self.aux[i].tolist()) for i in range(3)])
    def pulse_routes(self,source,when):
        if not self.cfg['pulses']:return []
        return [e for e in EDGES if e['source']==source and self.alive[e['target']] and
                (self.cfg['reverse'] or e['target']>e['source']) and any(lo<=when<hi for lo,hi in e['windows'])]
    def process_external(self):
        while self.queue and self.queue[0][0]<=self.t+2e-10:
            when,_,kind,payload=heapq.heappop(self.queue)
            if kind=='birth':self.alive[payload[0]]=True
            elif kind=='on':
                node,port,label=payload
                if not self.alive[node]:raise RuntimeError('input before birth')
                if self.raw[node,port]:raise RuntimeError('raw pulse overlap')
                self.raw[node,port]=True;self.origin[node,port]=when
                self.arrivals.append(dict(time=when,node=node,port=port,source=label))
            elif kind=='off':
                node,port,_=payload;self.raw[node,port]=False
            elif kind=='copy' and self.cfg['settings']:
                src,dst=payload
                if any(self.main[i]!=0 or any(self.aux[i]) or any(self.raw[i]) for i in [src,dst]):
                    raise RuntimeError(f'settings transfer outside quiescence at {when}')
                before=self.y[dst,4:8].copy()
                self.y[dst,4:7]=np.minimum(math.log(4),np.maximum(self.y[dst,4:7],self.y[src,4:7]))
                self.y[dst,7]=min(BMAX,max(self.y[dst,7],self.y[src,7]))
                self.copies.append(dict(time=when,source=src,target=dst,before=before.tolist(),after=self.y[dst,4:8].tolist()))
            elif kind=='sample':self.samples.append(self.snapshot())
    def rhs(self,now,flat):
        v=flat.reshape(3,9);out=np.zeros_like(v)
        for i in range(3):
            if not self.alive[i]:continue
            q=v[i,0];m=v[i,1:4];z=v[i,4:7];b=v[i,7];E=v[i,8]
            p=np.where(self.raw[i],A*np.exp(-A*(now-self.origin[i])),0.)
            drive=float(np.dot(np.exp(z),p))
            out[i,0]=K*(R-q)+drive if self.main[i]==0 else -A*q if self.main[i]==1 else -b*q
            for j in range(3):
                phase=self.aux[i,j];rate=[0,NOMINAL[1],NOMINAL[2],NOMINAL[3]][phase]
                out[i,j+1]=K*(RM-m[j])+NOMINAL[4]*p[j] if phase==0 else -rate*m[j]
                if self.cfg['plastic'] and E>0 and self.main[i]==0 and phase==3 and z[j]<math.log(4)-1e-10:
                    out[i,j+4]=8*NOMINAL[3]*m[j]
            if self.cfg['plastic'] and E>0 and self.main[i]!=0 and b<BMAX-1e-10:
                out[i,7]=.5*sum(NOMINAL[1]*m[j] for j in range(3) if self.aux[i,j]==1)
            wm=drive if self.main[i]==0 else A*q if self.main[i]==1 else 1.1
            wa=sum(NOMINAL[4]*p[j] if self.aux[i,j]==0 else [0,NOMINAL[1],NOMINAL[2],NOMINAL[3]][self.aux[i,j]]*m[j] for j in range(3))
            work=wm+wa+float(np.sum(out[i,4:7]))+out[i,7]
            out[i,8]=10*(100-E)-work
        return out.ravel()
    def root_specs(self):
        specs=[]
        for i in range(3):
            if not self.alive[i]:continue
            specs.append(('main',i,0,[1.,.25,R][self.main[i]],1 if self.main[i]==0 else -1))
            for j in range(3):
                specs.append(('aux',i,j+1,[1.,.8,.1,RM][self.aux[i,j]],1 if self.aux[i,j]==0 else -1))
                if self.cfg['plastic'] and self.y[i,j+4]<math.log(4)-1e-10:specs.append(('gcap',i,j+4,math.log(4),1))
            if self.cfg['plastic'] and self.y[i,7]<BMAX-1e-10:specs.append(('bcap',i,7,BMAX,1))
        return specs
    def advance(self,boundary):
        if all(self.main[i]==0 and not any(self.aux[i]) and not any(self.raw[i]) for i in range(3) if self.alive[i]):
            dt=boundary-self.t
            for i in range(3):
                if self.alive[i]:
                    self.y[i,0]=R+(self.y[i,0]-R)*math.exp(-K*dt)
                    self.y[i,1:4]=RM+(self.y[i,1:4]-RM)*math.exp(-K*dt)
                    self.y[i,8]=100+(self.y[i,8]-100)*math.exp(-10*dt)
            self.t=boundary;return
        specs=self.root_specs();functions=[]
        for _,i,j,target,direction in specs:
            def event(now,flat,i=i,j=j,target=target):return flat[i*9+j]-target
            event.direction=direction;event.terminal=True;functions.append(event)
        old=self.t
        sol=solve_ivp(self.rhs,(self.t,boundary),self.y.ravel(),method='DOP853',rtol=self.rtol,atol=self.atol,
                      max_step=self.max_step,events=functions)
        if not sol.success:raise RuntimeError(sol.message)
        self.min_energy=min(self.min_energy,float(sol.y.reshape(3,9,-1)[:,8,:].min()))
        self.t=float(sol.t[-1]);self.y=sol.y[:,-1].reshape(3,9)
        actual={i for i,a in enumerate(sol.t_events) if len(a)}
        if actual:
            near={n for n,(_,i,j,target,_) in enumerate(specs) if abs(self.y[i,j]-target)<2e-9}
            self.root_groups_near+=int(len(near)>1);actual.update(near)
        for n in sorted(actual):
            kind,i,j,target,_=specs[n];self.y[i,j]=target
            if kind=='main':
                if self.main[i]==0:
                    self.main[i]=1;self.outputs.append(dict(time=self.t,node=i))
                    for edge in self.pulse_routes(i,self.t):
                        dst=edge['target'];port=edge['port'];when=self.t+DELAY
                        self.add(when,'on',(dst,port,NAMES[i]));self.add(when+1,'off',(dst,port,NAMES[i]))
                elif self.main[i]==1:self.main[i]=2
                else:self.main[i]=0
            elif kind=='aux':self.aux[i,j-1]=(self.aux[i,j-1]+1)%4
        self.transitions+=len(actual)
        if self.t<=old and not actual:raise RuntimeError('no solver progress')
        if self.transitions>20000:raise RuntimeError('hybrid event budget exhausted')
    def run(self):
        started=time.perf_counter()
        while self.t<END-1e-9:
            self.process_external()
            boundary=min(END,self.queue[0][0] if self.queue else END)
            self.advance(boundary)
        self.process_external()
        return plain(dict(configuration=self.configuration,status='SIMULATED',samples=self.samples,
                          outputs=self.outputs,arrivals=self.arrivals,copies=self.copies,
                          min_observed_energy=self.min_energy,near_root_groups=self.root_groups_near,
                          transitions=self.transitions,elapsed_seconds=time.perf_counter()-started,
                          solver=dict(rtol=self.rtol,atol=self.atol,max_step=self.max_step)))


def run_all(dest):
    dest.mkdir(parents=True,exist_ok=True)
    plan=dict(scope='Exploratory numerical three-cell reciprocal R network; no theorem or hardware claim',
              sources=SOURCES,edges=EDGES,copies=COPIES,phases=PHASES,delay=DELAY,configurations=CONFIGS,
              source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              notes=['All introduced cells remain alive','Settings copy is an external bounded max operation, not R plasticity',
                     'No state reset or teacher removal','The first five phases use turn-taking edge gates; the last opens both directions',
                     'R gains and recovery can only increase; learned content here means port responsiveness and cadence, not semantic memory'])
    (dest/'plan.json').write_text(json.dumps(plain(plan),indent=2,ensure_ascii=False)+'\n')
    results=[]
    for name in CONFIGS:
        try:r=Network(name).run()
        except Exception as exc:r=dict(configuration=name,status='ERROR',error=repr(exc));results.append(r);raise
        results.append(r);(dest/(name+'.json')).write_text(json.dumps(r,separators=(',',':'),ensure_ascii=False)+'\n')
        print(name,len(r['outputs']),'firings',round(r['elapsed_seconds'],2),'s','E_min',r['min_observed_energy'],flush=True)
    return results
if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--out',type=Path,default=ROOT/'audit_runs'/'reciprocal')
    args=parser.parse_args();run_all(args.out)
