"""Deterministic numerical diagnostics for the written minimax repair.
These checks validate formulas on finite examples; they are not a proof.
"""
from pathlib import Path
import math,json
import numpy as np
ROOT=Path(__file__).resolve().parents[1]
lgamma=np.vectorize(math.lgamma,otypes=[float])
def logD(h):
    h=np.asarray(h,dtype=float)
    return .5*(math.log(math.pi)-lgamma(2*h+1)-np.log(np.sin(math.pi*h)))
def kernel(s,t,h,k):
    alpha=h+k
    coeff=.5*np.exp(2*logD(alpha/2)-logD(h)-logD(k))
    return coeff*(s**alpha+t**alpha-np.abs(s-t)**alpha)
def verify_case(n,kind):
    t=(np.arange(1,n+1)-.5)/n
    prev=np.r_[0,t[:-1]]
    ell=t-prev
    L=math.log(2*n)
    m=max(2,math.ceil((n*L*L)**.2))
    if kind=='brownian':
        h=np.full(n,.5);a=0.;b=0.
    elif kind.startswith('constant'):
        a=.02/L**2;b=0.;h=np.full(n,.5+(1 if kind.endswith('plus') else -1)*a)
    elif kind=='sine':
        a=.05/m**2;b=2*math.pi*m*a
        h=.5+a*np.sin(2*math.pi*m*t)
    elif kind=='bump':
        a=.05/m**2;b=16*.05/m
        cell=np.minimum((m*t).astype(int),m-1)
        x=m*t-cell-.5
        v=.25-x*x
        bump=np.zeros(n);mask=v>0
        bump[mask]=np.exp(4-1/v[mask])
        theta=(np.arange(m)%3!=1).astype(float)
        h=.5+a*theta[cell]*bump
    hp=np.r_[h[0],h[:-1]]
    s=t[:,None];sp=prev[:,None];u=t[None,:];up=prev[None,:]
    hj=h[:,None];hjp=hp[:,None];hk=h[None,:];hkp=hp[None,:]
    scale=1/np.sqrt(ell[:,None]*ell[None,:])
    Sigma=scale*(kernel(s,u,hj,hk)-kernel(s,up,hj,hkp)
                 -kernel(sp,u,hjp,hk)+kernel(sp,up,hjp,hkp))
    A=scale*(kernel(s,u,hj,hk)-kernel(s,up,hj,hk)
             -kernel(sp,u,hj,hk)+kernel(sp,up,hj,hk))
    Q=scale*(kernel(s,up,hj,hk)-kernel(sp,up,hj,hk)
             -kernel(s,up,hj,hkp)+kernel(sp,up,hj,hkp))
    R=scale*(kernel(sp,up,hj,hk)-kernel(sp,up,hjp,hk)
             -kernel(sp,up,hj,hkp)+kernel(sp,up,hjp,hkp))
    reconstruction=float(np.max(np.abs(Sigma-(A+Q+Q.T+R))))
    assert reconstruction<5e-10,(n,kind,reconstruction)
    diag_error=float(np.max(np.abs(np.diag(A)-ell**(2*h-1))))
    assert diag_error<5e-10,(n,kind,diag_error)
    E=(Sigma+Sigma.T)/2-np.eye(n)
    eig=np.linalg.eigvalsh(E)
    assert np.min(eig)>-1,(n,kind,np.min(eig))
    kl=float(.5*np.sum(eig-np.log1p(eig)))
    frob=float(np.sum(E*E))
    op=float(np.max(np.abs(eig)))
    assert op<.5,(n,kind,op)
    assert kl<=.5*frob+1e-11,(kl,frob)
    if kind=='brownian':assert np.max(np.abs(E))<5e-10
    target=(n*a*a+b*b)*L*L
    return dict(n=n,case=kind,m=m,a=a,b=b,smallness=(a+b)*L,
                reconstruction_max_error=reconstruction,diagonal_formula_max_error=diag_error,
                operator_norm=op,KL=kl,Frobenius_squared=frob,
                KL_over_claimed_scale=kl/target if target else None,
                mixed_entry_ratio=float(np.max(np.abs(Q)))/(b*L/n) if b else None,
                variation_entry_ratio=float(np.max(np.abs(R)))/(b*b/n) if b else None)
rows=[verify_case(n,kind) for n in (64,128,256)
      for kind in ('brownian','constant_plus','constant_minus','sine','bump')]
report={'scope':'Finite numerical consistency checks only; the proof is direct_proofs/09_minimax_lower_bound_complete.md',
        'cases':rows,'all_checks_passed':True,
        'max_reconstruction_error':max(x['reconstruction_max_error'] for x in rows),
        'max_KL_ratio':max(x['KL_over_claimed_scale'] or 0 for x in rows)}
(ROOT/'verification/minimax_kl_checks.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='cases'},indent=2))
