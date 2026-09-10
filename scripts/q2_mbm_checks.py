"""Finite consistency checks for the written q=2 repair; not a proof of rates/CLTs."""
from pathlib import Path
import json, math
import numpy as np
ROOT = Path(__file__).resolve().parents[1]
lgamma = np.vectorize(math.lgamma, otypes=[float])
def logD(h):
    return .5*(math.log(math.pi)-lgamma(2*h+1)-np.log(np.sin(math.pi*h)))
def kernel(t,h):
    a=h[:,None]+h[None,:]
    B=.5*np.exp(2*logD(a/2)-logD(h)[:,None]-logD(h)[None,:])
    return B*(t[:,None]**a+t[None,:]**a-np.abs(t[:,None]-t[None,:])**a)
def frozen(h,k):
    out=np.zeros_like(k,dtype=float)
    a=(1.,-2.,1.)
    for i in range(3):
        for j in range(3):out-=.5*a[i]*a[j]*np.abs(k+j-i)**(2*h)
    return out
rows=[]
for n in (128,256,512):
    t=(np.arange(n)+.5)/n; L=math.log(n)
    for kind in ('brownian','constant_065','varying_sine'):
        hfun=(lambda x:np.full_like(np.asarray(x),.5,dtype=float)) if kind=='brownian' else ((lambda x:np.full_like(np.asarray(x),.65,dtype=float)) if kind=='constant_065' else (lambda x:.6+.05*np.sin(2*np.pi*np.asarray(x))))
        h=hfun(t); C=kernel(t,h); a=(1.,-2.,1.); D=np.zeros((n-2,n-2))
        for i in range(3):
            for j in range(3): D+=a[i]*a[j]*C[i:i+n-2,j:j+n-2]
        tb=t[:-2]; hb=h[:-2]; scale=n**hb
        CW=D*scale[:,None]*scale[None,:]; CW=(CW+CW.T)/2
        vv=np.diag(CW); assert np.all(vv>0)
        rr=CW/np.sqrt(vv[:,None]*vv[None,:])
        interior=(tb>=.125)&(tb+2/n<=.875)
        ind=np.flatnonzero(interior); R=rr[np.ix_(ind,ind)]
        eigmin=float(np.linalg.eigvalsh(R)[0]); assert eigmin>-1e-8
        defect=float(np.max(np.abs(vv[interior]-(4-2**(2*hb[interior])))))
        frozen_error=None
        if kind!='varying_sine':
            lag=ind[:,None]-ind[None,:]
            frozen_error=float(np.max(np.abs(CW[np.ix_(ind,ind)]-frozen(float(h[0]),lag))))
            assert frozen_error<1e-7,(n,kind,frozen_error)
        b=(n*L*L)**(-.2); N=n*b
        for target in (.4,.5,.6):
            z=(tb-target)/b; mask=np.abs(z)<1
            assert np.all(interior[mask])
            zz=z[mask]; K=(1-zz*zz)**3; AA=np.stack((np.ones_like(zz),zz),axis=1)
            M=AA.T@(K[:,None]*AA)/N
            ww=K*(AA@np.linalg.solve(M,np.array([1.,0.])))/N
            assert np.max(np.abs(ww@AA-np.array([1.,0.])))<1e-12
            ht=float(hfun(target)); Gmean=float(ww@(-2*L*hb[mask]+np.log(vv[mask])))
            bias=Gmean-(-2*L*ht+math.log(4-2**(2*ht)))
            ids=np.flatnonzero(mask); Rlocal=rr[np.ix_(ids,ids)]
            # Cov(log Y_i^2,log Y_j^2) <= E[g(Z)^2] r_ij^2.
            # Report the deterministic correlation sum without using a log-moment constant.
            proxy=float(np.abs(ww)@(Rlocal*Rlocal)@np.abs(ww))
            rows.append(dict(n=n,case=kind,t=target,bandwidth=b,
                covariance_min_eigenvalue=eigmin,constant_model_max_error=frozen_error,
                variance_defect_over_log_n_over_n=defect/(L/n),
                bias_over_claimed_scale=abs(bias)/(L*(b*b+1/n)),
                N_times_absolute_weighted_squared_correlation= N*proxy,
                absolute_correlation_row_sum=float(np.max(np.sum(np.abs(R),axis=1))),
                gram_condition_number=float(np.linalg.cond(M))))
report=dict(scope='Finite formula, positivity, polynomial-reproduction checks and rate diagnostics only; not proof certification or CLT verification.',
    cases=rows,all_checks_passed=True,
    max_constant_model_error=max(x['constant_model_max_error'] or 0 for x in rows),
    max_bias_scale_ratio=max(x['bias_over_claimed_scale'] for x in rows),
    max_scaled_correlation_proxy=max(x['N_times_absolute_weighted_squared_correlation'] for x in rows))
(ROOT/'verification/q2_mbm_checks.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='cases'},indent=2))
