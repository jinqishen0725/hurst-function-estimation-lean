"""Deterministic numerical diagnostics; not Lean proofs or Monte Carlo.
Requires numpy. Long-double covariance evaluation reduces cancellation.
The Gaussian log-square covariance identity is used as an analytic input.
"""
import json, math
from fractions import Fraction
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parents[1]

def critical_variance(N):
    z = np.arange(-N, N+1, dtype=float)/N
    f = 35/32*(1-z*z)**3
    w = f/f.sum()
    size = 1 << (2*len(w)-1).bit_length()
    W = np.fft.rfft(w, size)
    ac = np.fft.irfft(W*W.conj(), size)[:len(w)]
    k = np.arange(1, len(w), dtype=np.longdouble)
    rho = ((k+1)**np.longdouble(1.5)+(k-1)**np.longdouble(1.5)-2*k**np.longdouble(1.5))/2
    cov = np.asarray(2*np.arcsin(rho)**2, dtype=float)
    var = ac[0]*math.pi**2/2+2*np.dot(ac[1:], cov)
    return {"N": N, "N_var_over_logN": float(N*var/math.log(N))}

integral = Fraction(35,32)**2 * sum(Fraction((-1)**j*math.comb(6,j)*2,2*j+1) for j in range(7))
check = {
    "description": "Numerical evidence only; does not certify probability-limit statements",
    "kernel": "f(z)=(35/32)(1-z^2)^3 for |z|<1, zero otherwise; p=1",
    "integral_f_squared_exact": str(integral),
    "corrected_critical_limit": float(Fraction(9,16)*integral),
    "printed_formula_using_definition_of_ch": float(Fraction(9,16)*Fraction(35,32)**2),
    "printed_formula_using_erroneous_1D_remark_ch": float(Fraction(9,4)*Fraction(35,32)**2),
    "critical_variance": [critical_variance(n) for n in [128,512,2048,8192,32768,131072]],
    "printed_bump_values": [{"x":x,"kappa":math.exp(-1/(x+.5)-1/(x-.5))} for x in [0,.25,.4,.45]],
    "q1_missing_inverse_example": {"log_n":1,"c":0,"H_domain":"(0,1)","G_range":"(-2,0)","omitted_input":-3},
}
rows = check["critical_variance"]
check["critical_log_slope"] = [(b["N_var_over_logN"]*math.log(b["N"])-a["N_var_over_logN"]*math.log(a["N"]))/math.log(b["N"]/a["N"]) for a,b in zip(rows,rows[1:])]
assert integral > 0
assert check['critical_variance'][-1]['N_var_over_logN'] < check['critical_variance'][0]['N_var_over_logN']
(ROOT/'verification/numerical_checks.json').write_text(json.dumps(check,indent=2)+'\n')
print(json.dumps(check,indent=2))
