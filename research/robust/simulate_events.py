"""Independent event-localized floating-point R simulator (not an interval proof).

No import from bounds, certifier or integer arithmetic. DOP853 locates guards;
known current/history discontinuities split integration. Physical state is never
reset between inputs. Endpoint assignments only enforce the model's guards.
"""
import math
from dataclasses import dataclass
import numpy as np
from scipy.integrate import solve_ivp

A=math.log(4); KAPPA=.5; R=.1; RM=.025
M0=(1-RM)/(A/(A-KAPPA)*(math.exp(-KAPPA*.02)-math.exp(-A*.02)))
NOM=np.array([4., math.log(1.25)/.02, math.log(8)/1.06, A/.15, M0])
SCENARIOS=('oscillatory','slow_positive','fast_negative','switching')


@dataclass
class History:
    epsilon: float
    nu: float
    alpha: float
    scenario: str
    seed: int=7
    cell: int=0

    def __post_init__(self):
        if self.scenario not in SCENARIOS: raise ValueError('unknown history')
        rng=np.random.default_rng(self.seed+7919*self.cell)
        self.phase=rng.uniform(0,2*math.pi,(3,5))
        self.omega=rng.uniform(.11,1.9,(3,5))
        self.noisephase=rng.uniform(0,2*math.pi,4)

    def values(self,t,main,aux):
        if self.scenario=='oscillatory':
            factor=np.sin(self.omega*t+self.phase)
            noise=self.nu*np.sin(t*.71+self.noisephase)
            amp=1+self.alpha*math.sin(1.13*t+self.phase[2,4])
        elif self.scenario=='switching':
            tick=int(math.floor(t/2.5))
            factor=np.where((np.arange(15).reshape(3,5)+tick+self.cell)%2,1.,-1.)
            noise=self.nu*np.where((np.arange(4)+tick+self.cell)%2,1.,-1.)
            amp=1+self.alpha*(1 if (tick+self.cell)%2 else -1)
        else:
            slow=self.scenario=='slow_positive'
            factor=np.full((3,5),-1. if slow else 1.)
            noise=np.full(4,self.nu if slow else -self.nu)
            amp=1-self.alpha if slow else 1+self.alpha
        return NOM[None,:]*(1+self.epsilon*factor),noise,amp

    def breaks(self,end):
        return list(np.arange(2.5,end,2.5)) if self.scenario=='switching' else []


def initial_state(edge=0, gain=None, recovery=None):
    y=np.zeros(12)
    y[0]=R+edge*1e-5; y[1:4]=RM+edge*1e-5
    y[4:7]=math.log(.3)+edge*1e-5
    y[7]=.18+edge*1e-5; y[8]=50. if edge<=0 else 100.
    if gain is not None: y[4:7]=gain
    if recovery is not None: y[7]=recovery
    return y


def simulate(arrivals, history, *, end=None, rtol=1e-9, atol=1e-11,
             max_step=.25, plastic=True, state=None, modes=None):
    arrivals=np.array(arrivals,dtype=float)
    if len(arrivals) and (arrivals[0]<0 or np.any(np.diff(arrivals)<=1)):
        raise ValueError('inputs must be nonoverlapping and nonnegative')
    if end is None: end=float(arrivals[-1]+10) if len(arrivals) else 10.
    if end<0: raise ValueError('negative horizon')
    y=initial_state() if state is None else np.array(state,dtype=float).copy()
    initial=y.copy(); main=0 if modes is None else modes[0]
    aux=[0,0,0] if modes is None else list(modes[1]); raw=False; origin=0.
    outputs=[]; transitions=[]; errors=[]; error_open={}; inputs=[]
    for j,mode in enumerate(aux):
        if mode==3: error_open[j]=(0.,float(y[j+4]),float(y[j+9]))
    extrema_min=y.copy(); extrema_max=y.copy(); nfev=0
    calendar={0.:[],float(end):[]}
    for t in history.breaks(end): calendar.setdefault(float(t),[])
    for i,t in enumerate(arrivals):
        if t<=end: calendar.setdefault(float(t),[]).append(('on',i))
        if t+1<=end: calendar.setdefault(float(t+1),[]).append(('off',i))
    times=sorted(calendar)

    def apply_calendar(t):
        nonlocal raw,origin
        for kind,i in sorted(calendar[t]):
            if kind=='off': raw=False
            else:
                inputs.append(dict(time=t, main=main, aux=list(aux),
                                   q=float(y[0]), m=y[1:4].tolist(), gain=math.exp(y[6])))
                raw=True; origin=t

    apply_calendar(0.)
    for start,stop in zip(times,times[1:]):
        t=start
        # The coefficient value at a jump endpoint belongs to the open segment
        # being integrated. This changes only a measure-zero point of the ODE.
        def rhs(now,v):
            teval=min(now,float(np.nextafter(stop,-math.inf)))
            par,w,amp=history.values(teval,main,aux)
            pulse=A*math.exp(-A*(now-origin))*amp if raw else 0.
            drive=math.exp(v[6])*pulse
            dv=np.zeros(12)
            if main==0: dv[0]=KAPPA*(R-v[0])+drive+w[0]; work=drive
            elif main==1: dv[0]=-A*v[0]+w[0]; work=A*v[0]
            else: dv[0]=-v[7]*v[0]+w[0]; work=1.1
            for j,mode in enumerate(aux):
                m=v[j+1]
                if mode==0:
                    admitted=par[j,4]*pulse if j==2 else 0.
                    dv[j+1]=KAPPA*(RM-m)+admitted+w[j+1]
                    work+=admitted
                else:
                    drain=par[j,mode]*m
                    dv[j+1]=-drain+w[j+1]; work+=drain
                    if mode==3: dv[j+9]=w[j+1]
                    if plastic and v[8]>0:
                        if mode==3 and main==0 and v[j+4]<math.log(par[j,0]):
                            dv[j+4]=8*drain
                        if mode==1 and main!=0 and v[7]<1.1:
                            dv[7]+=.5*drain
            work+=float(np.sum(dv[4:8]))
            dv[8]=10*(100-v[8])-work
            return dv

        while t<stop:
            guards=[]
            thresholds=[(1.,1) if main==0 else ((.25,-1) if main==1 else (.1,-1))]
            thresholds += [(1.,1) if mode==0 else ((.8,.1,.025)[mode-1],-1) for mode in aux]
            for idx,(threshold,direction) in enumerate(thresholds):
                def event(now,v,idx=idx,threshold=threshold): return v[idx]-threshold
                event.direction=direction; event.terminal=True; guards.append(event)
            sol=solve_ivp(rhs,(t,stop),y,method='DOP853',rtol=rtol,atol=atol,
                          events=guards,max_step=max_step)
            if not sol.success: raise RuntimeError(sol.message)
            nfev+=sol.nfev
            extrema_min=np.minimum(extrema_min,np.min(sol.y,axis=1))
            extrema_max=np.maximum(extrema_max,np.max(sol.y,axis=1))
            previous=t; t=float(sol.t[-1]); y=sol.y[:,-1].copy()
            hit=[i for i,e in enumerate(sol.t_events) if len(e)]
            if hit:
                # Independent coordinate guards at exactly the same state commute.
                hit += [i for i,(v,_) in enumerate(thresholds) if i not in hit and abs(y[i]-v)<2e-12]
                for idx in sorted(hit):
                    y[idx]=thresholds[idx][0]
                    if idx==0:
                        old=main; main=(main+1)%3
                        if old==0: outputs.append(t)
                        transitions.append(dict(time=t,coordinate='q',old=old,new=main))
                    else:
                        j=idx-1; old=aux[j]; aux[j]=(old+1)%4
                        if aux[j]==3:
                            error_open[j]=(t,float(y[j+4]),float(y[j+9]))
                        if old==3:
                            e,z,w0=error_open.pop(j)
                            errors.append(dict(port=j,start=e,end=t,dose=float(y[j+4])-z,
                                               noise_integral=float(y[j+9])-w0,
                                               physical_dose=.6+8*(float(y[j+9])-w0)))
                        transitions.append(dict(time=t,coordinate='m'+str(j),old=old,new=aux[j]))
            elif t<stop:
                raise RuntimeError('solver stopped without an event')
            if t==previous and not hit: raise RuntimeError('zero progress')
        apply_calendar(stop)
    return dict(inputs=inputs,outputs=outputs,errors=errors,transitions=transitions,
                initial=initial.tolist(),state=y.tolist(),main=main,aux=aux,raw=raw,
                extrema_min=extrema_min.tolist(),extrema_max=extrema_max.tolist(),nfev=nfev,end=end)


def run_chain(n,k,period,epsilon,nu,alpha,scenario,seed=7,**solver):
    arrivals=[float(period)*i for i in range(k)]; nodes=[]
    for i in range(n):
        history=History(epsilon,nu,alpha,scenario,seed,i)
        edge=(-1,0,1)[(seed+i)%3]
        result=simulate(arrivals,history,state=initial_state(edge),**solver)
        nodes.append(result)
        # All deliveries are kept in a feed-forward chain. Edge uncertainty can
        # alternate between both endpoints, or vary continuously with the seed.
        arrivals=[t+(.3 if (j+i+seed)%2 else .4) for j,t in enumerate(result['outputs'])]
    return dict(n=n,k=k,period=float(period),epsilon=epsilon,nu=nu,alpha=alpha,
                scenario=scenario,seed=seed,nodes=nodes)
