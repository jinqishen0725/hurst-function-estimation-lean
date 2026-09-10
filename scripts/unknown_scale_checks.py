"""Actual-model diagnostics for files 15--17, not asymptotic certification."""
from pathlib import Path
import math,json
import numpy as np
ROOT=Path(__file__).resolve().parents[1]
MU0=-float(np.euler_gamma)-math.log(2)
lgamma=np.vectorize(math.lgamma,otypes=[float])
def logD(h):return .5*(math.log(math.pi)-lgamma(2*h+1)-np.log(np.sin(math.pi*h)))
def kernel(t,h):
    a=h[:,None]+h[None,:]
    B=.5*np.exp(2*logD(a/2)-logD(h)[:,None]-logD(h)[None,:])
    return B*(t[:,None]**a+t[None,:]**a-np.abs(t[:,None]-t[None,:])**a)
def weights(t,centers,b,degree):
    out=[]
    for s in centers:
        z=(t-s)/b; K=np.maximum(1-z*z,0)**3
        A=np.stack([z**j for j in range(degree+1)],axis=1)
        e=np.zeros(degree+1);e[0]=1
        w=K*(A@np.linalg.solve(A.T@(K[:,None]*A),e))
        assert np.max(np.abs(w@A-e))<2e-12
        out.append(w)
    return np.array(out)
def frozen_cross(h,k,a,b):
    return -.5*(np.abs(k)**(2*h)-np.abs(k+b)**(2*h)-np.abs(k-a)**(2*h)+np.abs(k+b-a)**(2*h))/(a*b)**h
def logcov(r):return 2*np.arcsin(np.clip(r,-1,1))**2
counter=[]
for n in (256,1024,4096):
    h=.875; psi=.25; L=math.log(n); b=n**(-.5); N=n*b;m=math.floor(1/(4*b))
    t=(np.arange(n-2)+.5)/n
    centers=(np.arange(m)+.5)/m;centers=centers[centers>.1]
    W=weights(t,centers,b,0); nu=W.mean(axis=0)
    assert abs(nu.sum()-1)<1e-12 and np.min(nu)>=0 and m<=1/(3*b)
    d1=1-L/math.log(2);d2=L/math.log(2); var=0.
    allid=np.arange(n-2)
    for start in range(0,n-2,128):
        ix=allid[start:start+128];k=allid[None,:]-ix[:,None]
        block=d1*d1*logcov(frozen_cross(h,k,1,1))
        block+=2*d1*d2*logcov(frozen_cross(h,k,1,2))
        block+=d2*d2*logcov(frozen_cross(h,k,2,2))
        var+=float(nu[ix]@block@nu)
    assert var>0
    old=L*L*(m**(-1)*N**(-2*psi)+m**(2*psi-2)*n**(-2*psi)*sum(k**(-2*psi) for k in range(1,m+1)))
    c=h*(2*h-1);coeff=(2**psi-1)/math.log(2)
    limit=4*c*c*coeff*coeff*.9**(-2*psi)/((1-2*psi)*(2-2*psi))
    counter.append(dict(n=n,m=m,actual_variance=var,old_rhs_without_unspecified_constant=old,
        ratio_to_old_rhs=var/old,n_to_2psi_over_L2_times_variance=n**(2*psi)/L**2*var,
        predicted_positive_limit=limit,max_n_times_combined_weight=float(n*np.max(nu))))
rng=np.random.default_rng(9172026);simulation=[]
for n in (128,256):
    t=(np.arange(n)+.5)/n;L=math.log(n);b=(n*L*L)**(-.2);N=n*b
    m=math.ceil(1/b);centers=(np.arange(m)+.5)/m;centers=centers[(centers>=.25)&(centers<=.75)]
    for q in (1,2):
        h0=.62 if q==1 else .75;h=h0+.04*np.sin(2*np.pi*t);sigma=1.3
        C=kernel(t,h)*sigma*sigma;ev,U=np.linalg.eigh((C+C.T)/2)
        assert ev[0]>-1e-10
        samples=(U*np.sqrt(np.maximum(ev,0)))@rng.normal(size=(n,2000))
        count=n-2*q;tb=t[:count];Ds=[]
        for a in (1,2):
            D=np.zeros((count,samples.shape[1]))
            for j in range(q+1):D+=(-1)**j*math.comb(q,j)*samples[a*j:a*j+count]
            Ds.append(D)
        W=weights(tb,centers,b,1);wt=weights(tb,[.5],b,1)[0]
        G1=W@np.log(Ds[0]**2);G2=W@np.log(Ds[1]**2);P=(G2-G1)/(2*math.log(2))
        ell=np.zeros_like(P) if q==1 else np.log(4-2**(2*np.clip(P,0,.95)))
        shat=np.mean(G1+2*L*P-ell-MU0,axis=0)
        x=wt@np.log(Ds[0]**2)-shat
        if q==1:hh=np.clip((MU0-x)/(2*L),0,1)
        else:
            lo=np.zeros_like(x);hi=np.full_like(x,1-1/(n+2))
            for _ in range(45):
                mid=(lo+hi)/2;fx=MU0-2*L*mid+np.log(4-2**(2*mid))
                go_right=fx>x;lo=np.where(go_right,mid,lo);hi=np.where(go_right,hi,mid)
            hh=(lo+hi)/2
        assert np.all(np.isfinite(shat)) and np.all((hh>=0)&(hh<=1))
        nu=W.mean(axis=0)
        simulation.append(dict(n=n,q=q,replicates=2000,bandwidth=b,average_centers=len(centers),
            max_n_times_absolute_combined_weight=float(n*np.max(np.abs(nu))),
            scale_bias=float(np.mean(shat-math.log(sigma*sigma))),
            scale_MSE=float(np.mean((shat-math.log(sigma*sigma))**2)),
            H_bias=float(np.mean(hh-h0)),H_MSE=float(np.mean((hh-h0)**2)),
            H_MSE_over_predicted_rate=float(np.mean((hh-h0)**2)/((n*L*L)**(-.8)))))
report=dict(scope='Finite exact Gaussian log-covariance diagnostics and reproducible Monte Carlo on actual mBm covariance. Neither is an asymptotic proof.',
    all_checks_passed=True,counterexample_diagnostics=counter,actual_backfitting_simulations=simulation)
(ROOT/'verification/unknown_scale_checks.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
