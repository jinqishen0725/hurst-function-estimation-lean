# Mainline repair coordination — 2026-09-26

The user explicitly authorized parallel subagents in the current Codex thread.
This supersedes the historical no-subagent instruction in the takeover taskbook.
Baseline: `56c4d3b`. The existing dirty `ZCODE_VALIDATION_MONITOR.md` is preserved.
No Git commit or remote publication is authorized by this work plan.

## Ownership

| Owner | Files / objective |
|---|---|
| Root | Propagate eventual cardinality through P5 and `FullChainEndpoint`; `NormalizedLogVariance`, `NormalizedLogProjection`, `SignedInterleavedLaw`, `SignedPowerLimit`; integration and validation |
| `hilbert_basis_closeout` | `IntervalL2Basis`, `WeightedRieszSpectrumClosed`, then `ActualQ1SignedClosed` |
| `normalized_energy_repair` | `NormalizedHermiteEnergy`, `NormalizedActualEnergy`, `NormalizedActualRemainder` |
| `signed_spectrum_repair` | `GeneralSignedPowerMatching`: continuous tests, constructed signed ordering, coordinate matching, square tails, and interleaved-row chaos convergence |

Each owner validates small modules and reports actual theorem signatures and
remaining premises. Shared source files and status documents are edited only by
the root. No UI interaction or messages to the ZCode session are involved.

## Acceptance boundaries

- The existing all-k spectral identity is usable, but the external `HilbertBasis ℕ`
  input must be internally constructed before calling the model wrapper closed.
- Removing `hm : ∀ n, 0 < card n` does not repair the unnormalized `hE2` or the
  restriction to vanishing negative spectral mass.
- General signed matching must not assume its desired coordinate convergence or
  L² matching as an unexplained premise.
- Build and axiom checks establish formal correctness of the stated theorem;
  actual-model applicability is a separate required check.

## Current validation

Integration in progress. This is not a full-mainline completion claim.

Already passed targeted compilation:

- `lake build Hurst.WeightedRieszSpectrumClosed`: basis and closed equivalent-kernel
  spectrum; exit 0, 8930 jobs. The final signature has only `r`, `0 < psi`,
  `2 * psi < 1`, `0 < c`; no supplied basis or measurability/integrability package.
- `lake build Hurst.FullChainEndpoint`: eventual-cardinality repair propagated
  through P5; exit 0, 8885 jobs. Other old endpoint premises remain explicitly
  documented in that file.
- `NormalizedHermiteEnergy` and `NormalizedActualEnergy`: compile and foundation-only
  axiom checks passed; source copies and hashes are in the matching directories
  under `verification/checkpoints/2026-09-26-*`.
- `NormalizedLogVariance`: standalone and Lake compilation passed.
- `SignedInterleavedLaw`: standalone compilation passed; formal Lake build pending.

The final integration record will be added below after all branches are checked.

## Mathematical connections and remaining boundaries

1. **M1 basis:** normalized disjoint interval indicators supply an infinite
   orthonormal sequence. Extend it to a Hilbert basis, prove its index countable
   and infinite, then reindex by the natural numbers. The supplied-basis loophole
   is removed by an actual construction.
2. **General signed matching:** the second power bounds support and square mass.
   Weierstrass approximation gives continuous square-weighted tests; positive
   and negative powers follow for orders at least three. Square each sign and
   reuse nonnegative peeling, then take square roots. `antitoneResort` plus
   layer-cake identities provides the target ordering with multiplicities.
   Total second-power convergence supplies the uniform tails. This replaces
   the threshold-counting route in written proof 23; a separate Portmanteau
   proof is not required by this implementation.
3. **Finite law:** sorting positive and negative coefficients separately gives
   a permutation of the original row padded with zeros. `SignedInterleavedLaw`
   proves this, including empty rows and repeated eigenvalues. `SignedPowerLimit`
   transports back to the original finite Gaussian spaces and constructs `Q`.
4. **Normalized energy:** actual-to-Riesz mesh approximation plus bounded reference
   energy yields `S^(2*psi-2) * sum rho^2 = O(1)`. The near/far decomposition
   yields `S^(2*psi) * sum |w_i*w_j|*|rho_ij|^4 -> 0`. These are the correct
   normalizations; the unnormalized `sum rho^2 = O(1)` is not restored.
5. **Scalar rate obligations:** `NormalizedActualRemainder` keeps explicit cutoff
   and tail-envelope convergence. Its envelope premise quantifies over every
   fixed admissible covariance/tail constant, so two independent existential
   witnesses are not accidentally identified. The polynomial-bandwidth
   instantiation remains to be connected before this interface counts as a
   fully instantiated actual-model log endpoint.
6. **Final estimator:** normalized variance and clipping are separate proved
   interfaces. The clipping theorem still takes a center-band condition and
   row nondegeneracy. These, the scalar rates, the unit/spectral weight identities,
   and expectation/truth/unknown-scale endpoint assembly must be tracked
   explicitly. Old `FullChainEndpoint` still uses `hE2` and `hNegMass`; its name
   is not evidence of completion.
