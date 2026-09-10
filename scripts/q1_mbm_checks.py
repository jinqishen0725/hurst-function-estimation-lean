"""Finite actual-model checks for files 12--14. No asymptotic proof certification."""
from pathlib import Path
import math,json
import numpy as np
ROOT=Path(__file__).resolve().parents[1]
lgamma=np.vectorize(math.lgamma,otypes=[float])
def logD(h):return .5*(math.log(math.pi)-lgamma(2*h+1)-np.log(np.sin(math.pi*h)))
def kernel(t,h):
    a=h[:,None]+h[None,:]
    B=.5*np.exp(2*logD(a/2)-logD(h)[:,None]-logD(h)[None,:])
    return B*(t[:,None]**a+t[None,:]**a-np.abs(t[:,None]-t[None,:])**a)
def frozen(h,k):return .5*(np.abs(k+1)**(2*h)+np.abs(k-1)**(2*h)-2*np.abs(k)**(2*h))
rows=[]
for n in (128,256,512,1024):
    target=.5; L=math.log(n); b=n**(-.35); N=n*b
    times=(np.arange(n)+.5)/n
    ids=np.flatnonzero(np.abs((times-target)/b)<=1+1/N)
    assert ids[-1]+1<n
    tt=times[np.arange(ids[0],ids[-1]+2)]; tb=tt[:-1]; z=(tb-target)/b
    K=np.maximum(1-z*z,0)**3; design=np.stack((np.ones_like(z),z),axis=1)
    gram=design.T@(K[:,None]*design)/N
    f=K*(design@np.linalg.solve(gram,np.array([1.,0.])))
    w=f/N
    assert np.max(np.abs(w@design-[1,0]))<1e-12
    for h0 in (.62,.75,.82):
        psi=2-2*h0
        for slope in (0.,.06):
            hs=h0+slope*(tt-target)
            C=kernel(tt,hs)
            DC=C[1:,1:]-C[1:,:-1]-C[:-1,1:]+C[:-1,:-1]
            scale=n**hs[:-1]; CW=DC*scale[:,None]*scale[None,:]; CW=(CW+CW.T)/2
            vv=np.diag(CW); assert np.all(vv>0)
            R=CW/np.sqrt(vv[:,None]*vv[None,:])
            eig,U=np.linalg.eigh(R); assert eig[0]>-1e-9
            lag=ids[:,None]-ids[None,:]; RF=frozen(h0,lag)
            raw_error=float(np.max(np.abs(CW-RF)))
            if slope==0:assert raw_error<2e-8,(n,h0,raw_error)
            bias=float(w@(-2*L*hs[:-1]+np.log(vv))+2*L*h0)
            norm=(N**.5 if h0<.75 else ((N/math.log(N))**.5 if h0==.75 else N**psi))
            var2=float(2*w@(R*R)@w)
            # Check the spectral/cycle correspondence on the actual Gaussian matrix.
            T=N**(psi-1)*(f[:,None]*R)
            sqrtR=(U*np.sqrt(np.maximum(eig,0)))@U.T
            AQ=N**(psi-1)*(sqrtR*f[None,:])@sqrtR
            lam=np.linalg.eigvalsh((AQ+AQ.T)/2)
            tr2=float(np.trace(T@T)); tr3=float(np.trace(T@T@T))
            error=max(abs(tr2-float(np.sum(lam**2))),abs(tr3-float(np.sum(lam**3))))
            assert error<1e-8,(n,h0,slope,error)
            assert tr3>0 # Positive weights for this symmetric local-linear design.
            rows.append(dict(n=n,H_at_target=h0,slope=slope,N=N,
                constant_model_error=raw_error if slope==0 else None,
                variance_defect_over_claimed_scale=float(np.max(np.abs(vv-1)))/(L/n+n**(-psi)),
                bias_over_claimed_scale=abs(bias)/(L*b*b+L/n+n**(-psi)),
                normalized_second_chaos_variance=norm**2*var2,
                long_scaling_covariance_HS_distance_to_frozen=float(N**(psi-1)*np.linalg.norm(R-RF)),
                cycle_spectral_max_error=error,long_scaling_third_cumulant=8*tr3,
                min_correlation_eigenvalue=float(eig[0])))
report=dict(scope='Finite actual-covariance, weight, positivity, and spectral/cycle identities; rate diagnostics only, not proof or limit verification.',
    all_checks_passed=True,cases=rows,
    max_constant_model_error=max(r['constant_model_error'] or 0 for r in rows),
    max_cycle_spectral_error=max(r['cycle_spectral_max_error'] for r in rows),
    critical_limit_variance_for_this_kernel=9/16*(350/429))
(ROOT/'verification/q1_mbm_checks.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='cases'},indent=2))
print(json.dumps([r for r in rows if r['H_at_target']==.82 and r['slope']==.06],indent=2))
