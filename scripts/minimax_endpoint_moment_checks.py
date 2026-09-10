"""Finite formula/Monte Carlo checks for proofs 19 and 20; not proof certification."""
from pathlib import Path
import json,math
import numpy as np
ROOT=Path(__file__).resolve().parents[1]
lgamma=np.vectorize(math.lgamma,otypes=[float])
def logD(h):return .5*(math.log(math.pi)-lgamma(2*h+1)-np.log(np.sin(math.pi*h)))
def kernel(s,t,h,k):
    a=h+k; B=.5*np.exp(2*logD(a/2)-logD(h)-logD(k))
    return B*(s**a+t**a-np.abs(s-t)**a)
def symmetric(M):return (M+M.T)/2
endpoint=[]
for n in (64,128,256,512):
    L=math.log(2*n);m=math.ceil((n*L*L)**(1/3));eps=.003
    t=(np.arange(n)+.5)/n; prev=np.r_[0.,t[:-1]];ell=t-prev
    cell=np.minimum((m*t).astype(int),m-1);z=m*t-cell-.5;v=.25-z*z
    phi=np.zeros(n);use=v>0;phi[use]=np.exp(4-1/v[use])
    for case in ('alternating','all_bumps','sparse'):
        theta=(np.arange(m)%2==0) if case=='alternating' else (np.ones(m,dtype=bool) if case=='all_bumps' else (np.arange(m)%5==0))
        h=.5+eps/m*theta[cell]*phi;hp=np.r_[h[0],h[:-1]]
        s=t[:,None];u=t[None,:];sp=prev[:,None];up=prev[None,:]
        hj=h[:,None];hk=h[None,:];hjp=hp[:,None];hkp=hp[None,:];scale=1/np.sqrt(ell[:,None]*ell[None,:])
        Sigma=scale*(kernel(s,u,hj,hk)-kernel(s,up,hj,hkp)-kernel(sp,u,hjp,hk)+kernel(sp,up,hjp,hkp))
        A=scale*(kernel(s,u,hj,hk)-kernel(s,up,hj,hk)-kernel(sp,u,hj,hk)+kernel(sp,up,hj,hk))
        Q=scale*(kernel(s,up,hj,hk)-kernel(sp,up,hj,hk)-kernel(s,up,hj,hkp)+kernel(sp,up,hj,hkp))
        R=scale*(kernel(sp,up,hj,hk)-kernel(sp,up,hjp,hk)-kernel(sp,up,hj,hkp)+kernel(sp,up,hjp,hkp))
        defect=float(np.max(np.abs(Sigma-A-Q-Q.T-R)));assert defect<1e-9
        ev=np.linalg.eigvalsh(symmetric(Sigma));ea=np.linalg.eigvalsh(symmetric(A));er=np.linalg.eigvalsh(symmetric(R))
        assert ev[0]>.25 and ev[-1]<2.25
        assert er[0]>-1e-8
        vnorm=math.sqrt(max(0,float(er[-1])))
        lower=max(0,math.sqrt(float(ea[0]))-vnorm)**2
        upper=(math.sqrt(float(ea[-1]))+vnorm)**2
        assert ev[0]>=lower-1e-7 and ev[-1]<=upper+1e-7
        E=symmetric(Sigma)-np.eye(n);kl=float(.5*np.sum((ev-1)-np.log(ev)))
        frob=float(np.sum(E*E));assert kl<=4*frob+1e-10
        a=eps/m;b=16*eps
        endpoint.append(dict(n=n,m=m,case=case,fixed_amplitude=eps,
            a_bound_times_log=a*L,fixed_Lipschitz_bound=b,b_bound_times_log=b*L,
            reconstruction_max_error=defect,lambda_min=float(ev[0]),lambda_max=float(ev[-1]),
            Gram_lower_bound=lower,Gram_upper_bound=upper,variation_operator_norm=vnorm,
            KL=kl,KL_over_m=kl/m,KL_over_claimed_scale=kl/((n*a*a+b*b)*L*L)))
rng=np.random.default_rng(1920);moments=[];samples=16000
mu0=-float(np.euler_gamma)-math.log(2)
for n in (128,256,512):
    L=math.log(n);t=(np.arange(n)+.5)/n
    for q in (1,2):
        h=.71+.02*np.sin(2*np.pi*t) if q==1 else .89+.03*np.sin(2*np.pi*t)
        C=kernel(t[:,None],t[None,:],h[:,None],h[None,:]);count=n-q
        D=sum((-1)**(i+j)*math.comb(q,i)*math.comb(q,j)*C[i:i+count,j:j+count] for i in range(q+1) for j in range(q+1))
        vv=np.diag(D);assert np.min(vv)>0
        R=symmetric(D/np.sqrt(vv[:,None]*vv[None,:]));ev,vec=np.linalg.eigh(R);assert ev[0]>-1e-8
        Y=(vec*np.sqrt(np.maximum(ev,0)))@rng.normal(size=(count,samples))
        g=np.log(Y*Y)-mu0;p=float(q);b=(n*L*L)**(-1/(2*p+1));N=n*b
        for target in (0.,.5,1.):
            z=(t[:count]-target)/b;use=np.abs(z)<1;zz=z[use];K=(1-zz*zz)**2
            AA=np.stack([zz**j for j in range(q)],axis=1);M=AA.T@(K[:,None]*AA)/N;e=np.eye(q)[0]
            w=K*(AA@np.linalg.solve(M,e))/N
            ids=np.flatnonzero(use);Rc=np.clip(R[np.ix_(ids,ids)],-1,1)
            exact_var=float(w@(2*np.arcsin(Rc)**2)@w);samp=w@g[use]
            empirical_var=float(np.mean(samp*samp));rel=abs(empirical_var/exact_var-1)
            assert rel<.15,(n,q,target,rel)
            moments.append(dict(n=n,q=q,target=target,samples=samples,
                exact_variance=exact_var,empirical_second_moment=empirical_var,variance_relative_error=rel,
                N_scaled_second_moment=float(np.mean((np.sqrt(N)*samp)**2)),
                N_squared_scaled_fourth_moment=float(np.mean((np.sqrt(N)*samp)**4)),
                N_cubed_scaled_sixth_moment=float(np.mean((np.sqrt(N)*samp)**6))))
report=dict(scope='Finite actual p=1 covariance/Gram/KL checks and exploratory Gaussian-log moment Monte Carlo. High empirical moments can be noisy; none of these calculations certify asymptotic or uniform bounds.',
    all_checks_passed=True,endpoint_cases=endpoint,moment_cases=moments,
    max_reconstruction_error=max(r['reconstruction_max_error'] for r in endpoint),
    minimum_covariance_eigenvalue=min(r['lambda_min'] for r in endpoint),
    maximum_covariance_eigenvalue=max(r['lambda_max'] for r in endpoint),
    max_second_moment_MC_relative_error=max(r['variance_relative_error'] for r in moments))
(ROOT/'verification/minimax_endpoint_moment_checks.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ('endpoint_cases','moment_cases')},indent=2))
print('endpoint cases:',len(endpoint),'moment cases:',len(moments))
