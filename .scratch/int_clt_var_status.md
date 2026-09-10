# INT-CLT / INT-VAR status

## Lean-complete internal results

- `Hurst/ShortMemoryCLTApplicability.lean`
  - `localPolynomialWeights_sqrt_envelope`: the largest normalized local weight tends to zero.
  - `hurstHolder_stride_first_finiteHermite_CLT`: q1, `b < 3/4`; all actual-model nondegeneracy, correlation-row, weight-energy, and infinitesimal-weight conditions are discharged, conditional only on the weighted-array CLT and the truncated variance limit.
  - `hurstHolder_grid_second_finiteHermite_CLT`: q2, `b < 1`; same discharge.
  - log-tail transfer and optimal-bandwidth wrappers exist for both q1 and q2.
- `Hurst/WeightEnergyLimit.lean`
  - exact finite-sample weight-energy expansion;
  - square-kernel midpoint quadrature;
  - `(n δ_n) ∑ᵢ w_{n,i}² → ∫_{-1}^1 ω_r(x)² dx` at every fixed interior point.

Both modules build without `sorry`, `admit`, `axiom`, or `unsafe`.  `#print axioms`
reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Exact external theorem boundary

`BardetSurgailisTheoremOnePartTwoScalarPolynomial` records the scalar-polynomial
specialization of Bardet--Surgailis, *Journal of Multivariate Analysis* 114
(2013), Theorem 1(ii), arXiv:1104.4732v2.  The applicable displayed conditions
are (3.1), (3.2), (3.5), and (3.6): uniform covariance-power rows, vanishing
average covariance-power tails, uniform Gaussian-L2 profile convergence, and a
positive variance limit.

`WeightedFiniteHermiteTriangularCLT` is deliberately **not** identified with
that citation.  It remains an internal open premise until the shrinking-window
reindexing and equivalent-kernel profile bridge are formalized.

## Minimal remaining variance gap

For each fixed lag, prove:

1. `(n δ_n) ∑ᵢ w_{n,i} w_{n,i+k} → ∫ ω_r²` (shifted-weight Riemann sum);
2. actual standardized correlation at lag `k` tends to the frozen correlation;
3. use the already available summable correlation envelope to pass from fixed
   lags to the complete Hermite-polynomial covariance sum.

After these, the truncated variance premise in the q1/q2 wrappers disappears.
The remaining probability input is then the cited triangular-array CLT plus its
local reindex/profile applicability bridge.
