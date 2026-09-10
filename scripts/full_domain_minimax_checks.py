"""Finite boundary checks for proof 18; no asymptotic or proof certification."""
from pathlib import Path
import json, math
import numpy as np
ROOT = Path(__file__).resolve().parents[1]
lgamma = np.vectorize(math.lgamma, otypes=[float])
def logD(h):
    return .5*(math.log(math.pi)-lgamma(2*h+1)-np.log(np.sin(math.pi*h)))
def cov_parts(t,h):
    a=h[:,None]+h[None,:]
    B=.5*np.exp(2*logD(a/2)-logD(h)[:,None]-logD(h)[None,:])
    return B*(t[:,None]**a+t[None,:]**a), -B*np.abs(t[:,None]-t[None,:])**a

def difference(C,q,step=1,count=None):
    count = len(C)-step*q if count is None else count
    out=np.zeros((count,count))
    for i in range(q+1):
        for j in range(q+1):
            out+=(-1)**(i+j)*math.comb(q,i)*math.comb(q,j)*C[i*step:i*step+count,j*step:j*step+count]
    return (out+out.T)/2

def weights(tb,target,b,n,degree):
    z=(tb-target)/b; use=np.abs(z)<1; zz=z[use]
    K=(1-zz*zz)**2; A=np.stack([zz**j for j in range(degree+1)],axis=1)
    M=A.T@(K[:,None]*A)/(n*b); e=np.eye(degree+1)[0]
    w=K*(A@np.linalg.solve(M,e))/(n*b)
    defect=float(np.max(np.abs(w@A-e)))
    assert defect<1e-10
    return use,w,float(np.linalg.eigvalsh(M)[0]),defect

def vq(h,q):return np.ones_like(np.asarray(h)) if q==1 else 4-2**(2*np.asarray(h))
def frozen(h,k,q):
    ans=np.zeros_like(k,dtype=float)
    for i in range(q+1):
        for j in range(q+1):ans-=.5*(-1)**(i+j)*math.comb(q,i)*math.comb(q,j)*np.abs(k+j-i)**(2*h)
    return ans
rows=[]; covariance_rows=[]
for n in (128,256,512):
    t=(np.arange(n)+.5)/n; L=math.log(n)
    for q in (1,2):
        p=1.5 if q==1 else 3.; degree=math.ceil(p)-1
        b=(n*L*L)**(-1/(2*p+1))
        for case in ('constant','varying_low','varying_high'):
            if case=='constant':hfun=lambda x:np.zeros_like(np.asarray(x))+.65
            elif case=='varying_low':hfun=lambda x:.2+.1*np.asarray(x)
            elif q==1:hfun=lambda x:.70+.03*np.sin(2*np.pi*np.asarray(x))
            else:hfun=lambda x:.88+.04*np.sin(2*np.pi*np.asarray(x))
            h=hfun(t); bg,sg=cov_parts(t,h); C=bg+sg
            D=difference(C,q); tb=t[:-q]; hb=h[:-q]; scale=n**hb
            normalized=D*scale[:,None]*scale[None,:]; vv=np.diag(normalized)
            assert np.all(vv>0)
            R=normalized/np.sqrt(vv[:,None]*vv[None,:]); R=np.clip(R,-1,1)
            eigmin=float(np.linalg.eigvalsh(R)[0]); assert eigmin>-1e-7
            bgdiff=difference(bg,q)*scale[:,None]*scale[None,:]
            hstar=.74 if q==1 else .95; psi=2-2*hstar
            ebg=(n**-1+n**-psi)*L**2 if q==1 else n**-2*L**4
            err=None
            if case=='constant':
                lag=np.arange(n-q)[:,None]-np.arange(n-q)[None,:]
                err=float(np.max(np.abs(normalized-frozen(.65,lag,q))))
                assert err<2e-7
            covariance_rows.append(dict(n=n,q=q,case=case,
                background_over_global_bound=float(np.max(np.abs(bgdiff)))/ebg,
                max_squared_correlation_row_sum=float(np.max(np.sum(R*R,axis=1))),
                diagonal_defect_over_bound=float(np.max(np.abs(vv-vq(hb,q))))/(L/n+ebg),
                correlation_min_eigenvalue=eigmin,constant_frozen_error=err))
            targets=(0.,1/n,b/2,.5,1-b/2,1-1/n,1.)
            for target in targets:
                use,w,emin,moment_error=weights(tb,target,b,n,degree)
                ids=np.flatnonzero(use); RR=R[np.ix_(ids,ids)]
                logcov=2*np.arcsin(RR)**2
                variance=float(w@logcov@w)
                mean=float(w@(-2*L*hb[use]+np.log(vv[use])))
                ht=float(hfun(target)); truth=-2*L*ht+float(np.log(vq(ht,q)))
                bias=mean-truth
                risk_bound=(variance+bias*bias)/(4*L*L)
                rows.append(dict(n=n,q=q,p=p,case=case,target=target,
                    minimum_gram_eigenvalue=emin,moment_error=moment_error,
                    N_times_log_variance=n*b*variance,
                    inverse_MSE_upper_bound_over_rate=risk_bound/(b**(2*p)),
                    weight_l1=float(np.sum(np.abs(w)))))
# Exact algebraic scale equivariance of the internal scale estimate and full-domain input.
n=256; t=(np.arange(n)+.5)/n; x=np.random.default_rng(1818).normal(size=n)
shift_defects=[]
for q in (1,2):
    L=math.log(n); p=2.; b=(n*L*L)**(-1/(2*p+1)); degree=1
    count=n-2*q; centers=np.linspace(.25,.75,max(2,math.ceil(.5/b)))
    def transformed_inputs(data):
        logs=[]
        for a in (1,2):
            d=sum((-1)**j*math.comb(q,j)*data[a*j:a*j+count] for j in range(q+1))
            logs.append(np.log(d*d))
        pieces=[]
        for s in centers:
            use,w,_,_=weights(t[:count],s,b,n,degree)
            g1=w@logs[0][use]; g2=w@logs[1][use]; pilot=(g2-g1)/(2*math.log(2))
            clipped=np.clip(pilot,0,1-.025)
            # mu0 cancels in this shift check, so use zero for that fixed constant.
            pieces.append(g1+2*L*pilot-float(np.log(vq(clipped,q))))
        shat=float(np.mean(pieces))
        count1=n-q
        dd=sum((-1)**j*math.comb(q,j)*data[j:j+count1] for j in range(q+1))
        ll=np.log(dd*dd); outputs=[]
        for s in (0.,.5,1.):
            use,w,_,_=weights(t[:count1],s,b,n,degree)
            outputs.append(float(w@ll[use])-shat)
        return shat,np.array(outputs)
    s0,g0=transformed_inputs(x); s1,g1=transformed_inputs(7*x)
    defect=max(abs(s1-s0-math.log(49)),float(np.max(np.abs(g1-g0))))
    assert defect<1e-10
    shift_defects.append(dict(q=q,defect=defect))
report=dict(scope='Finite actual-covariance, endpoint weights, log-variance and exact scale-equivariance checks only; not a proof of uniform asymptotic rates.',
    all_checks_passed=True,covariance_cases=covariance_rows,target_cases=rows,scale_equivariance=shift_defects,
    max_moment_error=max(r['moment_error'] for r in rows),
    minimum_gram_eigenvalue=min(r['minimum_gram_eigenvalue'] for r in rows),
    max_squared_correlation_row_sum=max(r['max_squared_correlation_row_sum'] for r in covariance_rows),
    max_inverse_MSE_bound_over_rate=max(r['inverse_MSE_upper_bound_over_rate'] for r in rows))
(ROOT/'verification/full_domain_minimax_checks.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ('target_cases','covariance_cases')},indent=2))
print('covariance cases:',len(covariance_rows),'target cases:',len(rows))
