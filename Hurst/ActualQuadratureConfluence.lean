import Hurst.ActualMeshTraceTransfer
import Hurst.RieszQuadratureInstance
import Hurst.HcoeffBridge
import Hurst.EvenPeeling
import Hurst.ActualFirstLongWeightedKernel
import Hurst.FirstLongRieszEnergy
import Hurst.LocalWeightSupport
import Hurst.ActiveWindowGeometry
import Hurst.ActiveWeightProfile
import Hurst.FirstStrideGrid
import Hurst.FiniteHermitianTracePowers

/-!
# Actual q1 long-memory second chaos: quadrature confluence

This file connects the proved weighted Riesz cycle quadrature
(`hasWeightedRieszCycleQuadrature_instance`) to the actual q1 long-memory
second-chaos endpoint: the eigenvalue power sums of the actual weighted
feature-quadratic spectral matrix converge to the power sums of the Riesz
spectrum `lam`, modulo explicit ordinary hypotheses, and hence (signed form)
the padded decreasing rearrangement of `|eigenvalues|` converges
coefficientwise to `lam` (`paddedAbsRearranged_tendsto`).

## The verified normalization chain (exact scales)

With `m n := (localWeightActiveSet n 1 (δ n) t).card`, `S n := n * δ n`,
`ψ := 2 - 2 * f t`, `c := f t * (2 * f t - 1)`, `u n i := S n * w_n(i)` (the
`S`-scaled local polynomial weight) and `ω := equivalentKernel r`:

* `q1ActualLongActiveKernel` bakes in the covariance scale: its entries are
  `S ^ ψ * vectorCorrelation(increment i, increment j)`;
* the actual spectral matrix's row-weighted correlation form is
  `diagonalCorrelationMatrix w' corr` with `w' n i = S ^ (ψ - 1) * u n i`
  (`actualQ1SpectralWeight`), and `corr = featureCorrelation` of the
  raw-increment feature embedding, which equals `vectorCorrelation` of the
  first-stride increments (`actualQ1_featureCorrelation_eq`);
* hence, entrywise and EXACTLY,
  `w'_i * corr i j = S⁻¹ * (u_i * q1ActualLongActiveKernel i j)`
  (`actualQ1_diagonalCorrelation_apply`): the mesh-normalized actual matrix is
  `S⁻¹` times the A-side kernel of
  `hurstHolder_q1_actual_weighted_kernel_hilbertSchmidt_to_riesz`;
* likewise `ω_i * q1RieszActiveKernel i j = S * weightedRieszDiscreteMatrix`
  entrywise (`actualQ1_weightedRieszKernel_scale`): the G-side kernel is `S`
  times the quadrature matrix;
* therefore `‖Ā_n − 𝔾_n‖_F = √(realScaleMeshEnergy S (A-side − G-side))`
  (`actualQ1_frobenius_norm_eq_sqrt_energy`), so the kernel energy convergence
  (an explicit hypothesis below) is exactly Frobenius convergence of the
  normalized pair, at the UNIFORM scale `O(1)` bounded by
  `rankRieszKernel_energy_le_const`.

## The one remaining explicit hypothesis

`hPert : (card n) * realScaleMeshEnergy S (A-side − G-side) → 0`.
The repo's kernel theorem
`hurstHolder_q1_actual_weighted_kernel_hilbertSchmidt_to_riesz` gives the
energy `→ 0` WITHOUT a rate; the trace-power perturbation bound
(`abs_trace_pow_sub_le_of_fintype` inside `mesh_frobenius_trace_pow_tendsto`)
loses a factor `√(card n)`, so the dimension-weighted energy must tend to
zero.  Producing this rate is precisely the singular trace-power mesh
transfer (the vertex-tuple layer of `Hurst.MeshPowerGeneral` /
`Hurst.VertexTupleTrace` applied to the relative-band form proved inside
`hurstHolder_q1_actual_weighted_kernel_hilbertSchmidt_to_riesz`); it is not a
black box in the repository and is left as the single explicit hypothesis.

## Contents

* `actualQ1ChainWeight`, `actualQ1SpectralWeight`, `actualQ1Obs`,
  `actualQ1Coeff` : the actual data bundle;
* `actualQ1WeightedActualKernel`, `actualQ1WeightedRieszKernel` : the two
  comparison kernel arrays (A-side and G-side of the weighted kernel theorem);
* `actualQ1_featureCorrelation_eq` : the raw-increment correlation bridge;
* `actualQ1_diagonalCorrelation_apply` : the exact `S⁻¹` scale identity;
* `actualQ1_weightedRieszKernel_scale` : the exact `S` scale identity;
* `actualQ1NormalizedActualMatrix`, `actualQ1_frobenius_norm_eq_sqrt_energy` :
  Frobenius form of the perturbation;
* `actualQ1_trace_pow_tendsto` : all power traces of the normalized actual
  matrix converge to the Riesz cycle integrals (given `hPert`);
* `actualQ1_eigenvalue_even_power_sums` : the even-`k` eigenvalue power sums
  converge to `∑' lam ^ k`;
* `actualQ1EigenvaluePowerSums_tendsto` : the signed endpoint — coefficientwise
  convergence of the padded decreasing rearrangement of `|eigenvalues|`.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Set MeasureTheory Filter Matrix
open scoped Topology RealInnerProductSpace Matrix.Norms.Frobenius

namespace Hurst

/-! ## The actual data bundle -/

/-- The `S`-scaled local polynomial weight `u n i = S n * w_n(index i)` of the
actual second-chaos chain. -/
def actualQ1ChainWeight (f : ℝ → ℝ) (r : ℕ) (n : ℕ) (δ t : ℝ)
    (i : Fin (localWeightActiveSet n 1 δ t).card) : ℝ :=
  ((n : ℝ) * δ) * localPolynomialWeights r n 1 δ t
    (localWeightActiveIndex n 1 δ t i)

/-- The statistic weight of the actual q1 weighted second chaos:
`S ^ (ψ - 1) * u n i` with `ψ = 2 - 2 * f t` (this is the normalization under
which the centered quadratic form is `S ^ (ψ - 1) * ∑ u_i (Y_i² - 1)`, cf.
`GaussianQuadraticWeightedKernelContinuity`). -/
def actualQ1SpectralWeight (f : ℝ → ℝ) (r : ℕ) (n : ℕ) (δ t : ℝ)
    (i : Fin (localWeightActiveSet n 1 δ t).card) : ℝ :=
  ((n : ℝ) * δ) ^ (2 - 2 * f t - 1) * actualQ1ChainWeight f r n δ t i

/-- The observation feature family: the harmonizable grid features of the
midpoint sample of `f`. -/
def actualQ1Obs (f : ℝ → ℝ) (n : ℕ) (H : Fin n → Ioo (0 : ℝ) 1) (k : Fin n) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  gridObservationFeatures n H k

/-- The active coefficient vectors: first-stride difference weights at the
active indices. -/
def actualQ1Coeff (n : ℕ) (δ t : ℝ) (i : Fin (localWeightActiveSet n 1 δ t).card) :
    EuclideanSpace ℝ (Fin n) :=
  gridStrideFirstCoefficients n 1 (localWeightActiveIndex n 1 δ t i)

/-! ## The two comparison kernel arrays -/

/-- The A-side kernel of the weighted kernel theorem: row weights
(`u n i`) times the actual long-memory kernel (which carries the `S ^ ψ`
covariance scale). -/
def actualQ1WeightedActualKernel (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (r : ℕ) (n : ℕ) (δ t : ℝ) :
    Fin (localWeightActiveSet n 1 δ t).card →
      Fin (localWeightActiveSet n 1 δ t).card → ℝ :=
  fun i j =>
    actualQ1ChainWeight f r n δ t i *
      q1ActualLongActiveKernel f hf n δ t ((n : ℝ) * δ) (2 - 2 * f t) i j

/-- The G-side kernel of the weighted kernel theorem: the equivalent kernel
weight at the right-endpoint grid point times the rank Riesz kernel. -/
def actualQ1WeightedRieszKernel (f : ℝ → ℝ) (r : ℕ) (n : ℕ) (δ t : ℝ) :
    Fin (localWeightActiveSet n 1 δ t).card →
      Fin (localWeightActiveSet n 1 δ t).card → ℝ :=
  fun i j =>
    equivalentKernel r
      (rieszCycleGridPoint (localWeightActiveSet n 1 δ t).card i) *
      q1RieszActiveKernel n δ t ((n : ℝ) * δ) (2 - 2 * f t)
        (f t * (2 * f t - 1)) i j

/-- The mesh-normalized actual matrix: `S⁻¹` times the A-side kernel.  By
`actualQ1_diagonalCorrelation_apply` (as a matrix) this is exactly the
row-weighted correlation matrix whose power traces are the eigenvalue power
sums of the actual spectral matrix. -/
def actualQ1NormalizedActualMatrix (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (r : ℕ) (n : ℕ) (δ t : ℝ) :
    Matrix (Fin (localWeightActiveSet n 1 δ t).card)
      (Fin (localWeightActiveSet n 1 δ t).card) ℝ :=
  fun i j => ((n : ℝ) * δ)⁻¹ * actualQ1WeightedActualKernel f hf r n δ t i j

/-! ## Exact entry identities -/

/-- Scalar cancellation for the real-inner-product correlation: nonzero real
scalars factor out of numerator and denominator alike. -/
private theorem featureCorrelation_smul_cancel {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (u v : F) :
    ⟪α • u, β • v⟫ / (‖α • u‖ * ‖β • v‖) = ⟪u, v⟫ / (‖u‖ * ‖v‖) := by
  rw [real_inner_smul_left, real_inner_smul_right, norm_smul, norm_smul,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hα, abs_of_pos hβ]
  field_simp

/-- **Correlation bridge.**  For the raw-increment feature embedding, the
feature correlation of the active coefficient vectors is exactly the
vector correlation of the first-stride increments (the scale factors
`((d : ℝ) / n) ^ (f ·)` of `gridStrideFirst_feature_identity` cancel between
numerator and denominator). -/
theorem actualQ1_featureCorrelation_eq (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (n : ℕ) (hn : 0 < n) (δ t : ℝ)
    (i j : Fin (localWeightActiveSet n 1 δ t).card) :
    featureCorrelation (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
        (actualQ1Coeff n δ t i) (actualQ1Coeff n δ t j)
      = vectorCorrelation
          (gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n)
            (localWeightActiveIndex n 1 δ t i))
          (gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n)
            (localWeightActiveIndex n 1 δ t j)) := by
  have hn1 : (0 : ℝ) < n := by exact_mod_cast hn
  have hd : (0 : ℕ) < 1 := by norm_num
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hαi0 : (0 : ℝ) < (((1 : ℕ) : ℝ) / n) ^ ((midpointSampleHurst f hf.1 n
      (strideFirstLeft n 1 (localWeightActiveIndex n 1 δ t i)) : ℝ)) :=
    Real.rpow_pos_of_pos (div_pos (by norm_num) hnR) _
  have hαj0 : (0 : ℝ) < (((1 : ℕ) : ℝ) / n) ^ ((midpointSampleHurst f hf.1 n
      (strideFirstLeft n 1 (localWeightActiveIndex n 1 δ t j)) : ℝ)) :=
    Real.rpow_pos_of_pos (div_pos (by norm_num) hnR) _
  have hsi : (∑ k : Fin n, actualQ1Coeff n δ t i k •
      actualQ1Obs f n (midpointSampleHurst f hf.1 n) k)
      = (((1 : ℕ) : ℝ) / n) ^ ((midpointSampleHurst f hf.1 n
          (strideFirstLeft n 1 (localWeightActiveIndex n 1 δ t i)) : ℝ)) •
        gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n)
          (localWeightActiveIndex n 1 δ t i) := by
    simp only [actualQ1Coeff, actualQ1Obs]
    exact gridStrideFirst_feature_identity n 1 hn hd (midpointSampleHurst f hf.1 n)
      (localWeightActiveIndex n 1 δ t i)
  have hsj : (∑ k : Fin n, actualQ1Coeff n δ t j k •
      actualQ1Obs f n (midpointSampleHurst f hf.1 n) k)
      = (((1 : ℕ) : ℝ) / n) ^ ((midpointSampleHurst f hf.1 n
          (strideFirstLeft n 1 (localWeightActiveIndex n 1 δ t j)) : ℝ)) •
        gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n)
          (localWeightActiveIndex n 1 δ t j) := by
    simp only [actualQ1Coeff, actualQ1Obs]
    exact gridStrideFirst_feature_identity n 1 hn hd (midpointSampleHurst f hf.1 n)
      (localWeightActiveIndex n 1 δ t j)
  unfold featureCorrelation vectorCorrelation
  rw [hsi, hsj]
  exact featureCorrelation_smul_cancel _ _ hαi0 hαj0 _ _

/-- **The exact `S⁻¹` scale identity (entrywise).**  The row-weighted
correlation matrix of the actual spectral data has entries `S⁻¹` times the
A-side kernel entries.  Together with
`trace_pow_weightedFeatureQuadraticMatrix_eq` this is deliverable (1): the
eigenvalue power sums of the actual spectral matrix are the power traces of
`actualQ1NormalizedActualMatrix`. -/
theorem actualQ1_diagonalCorrelation_apply (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (r : ℕ) (n : ℕ) (hn : 0 < n) (δ t : ℝ) (hδ : 0 < δ)
    (i j : Fin (localWeightActiveSet n 1 δ t).card) :
    diagonalCorrelationMatrix
        (actualQ1SpectralWeight f r n δ t)
        (fun i j => featureCorrelation
          (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
          (actualQ1Coeff n δ t i) (actualQ1Coeff n δ t j)) i j
      = ((n : ℝ) * δ)⁻¹ * actualQ1WeightedActualKernel f hf r n δ t i j := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < n * δ := mul_pos hnR hδ
  have hSne : ((n : ℝ) * δ) ≠ 0 := ne_of_gt hn1
  have hscale : ((n : ℝ) * δ) ^ (2 - 2 * f t - 1)
      = ((n : ℝ) * δ) ^ (2 - 2 * f t) * ((n : ℝ) * δ)⁻¹ := by
    have h1 : ((n : ℝ) * δ) ^ ((2 - 2 * f t - 1) + 1)
        = ((n : ℝ) * δ) ^ (2 - 2 * f t - 1) * ((n : ℝ) * δ) ^ (1 : ℝ) :=
      Real.rpow_add hn1 _ _
    have h2 : (2 - 2 * f t - 1) + 1 = 2 - 2 * f t := by ring
    rw [h2, Real.rpow_one] at h1
    rw [h1, mul_assoc, mul_inv_cancel₀ (a := (n : ℝ) * δ) hSne, mul_one]
  rw [diagonalCorrelationMatrix_apply, actualQ1SpectralWeight, actualQ1ChainWeight,
    actualQ1_featureCorrelation_eq f hf n hn δ t]
  unfold actualQ1WeightedActualKernel q1ActualLongActiveKernel
  rw [hscale]
  field_simp
  rw [actualQ1ChainWeight]
  ring

/-- As a matrix: the row-weighted correlation matrix of the actual spectral
data is exactly `actualQ1NormalizedActualMatrix`. -/
theorem actualQ1_diagonalCorrelation_eq (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (r : ℕ) (n : ℕ) (hn : 0 < n) (δ t : ℝ) (hδ : 0 < δ) :
    diagonalCorrelationMatrix
        (actualQ1SpectralWeight f r n δ t)
        (fun i j => featureCorrelation
          (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
          (actualQ1Coeff n δ t i) (actualQ1Coeff n δ t j))
      = actualQ1NormalizedActualMatrix f hf r n δ t := by
  funext i j
  exact actualQ1_diagonalCorrelation_apply f hf r n hn δ t hδ i j

/-- **The exact `S` scale identity (entrywise).**  The G-side kernel of the
weighted kernel theorem is `S` times the quadrature matrix
`weightedRieszDiscreteMatrix`. -/
theorem actualQ1_weightedRieszKernel_scale (r : ℕ) (n : ℕ) (hn : 0 < n)
    (δ t : ℝ) (hδ : 0 < δ) (hcard : 0 < (localWeightActiveSet n 1 δ t).card)
    (i j : Fin (localWeightActiveSet n 1 δ t).card) :
    actualQ1WeightedRieszKernel f r n δ t i j
      = ((n : ℝ) * δ) *
          weightedRieszDiscreteMatrix (localWeightActiveSet n 1 δ t).card
            ((n : ℝ) * δ) (2 - 2 * f t) (f t * (2 * f t - 1))
            (equivalentKernel r) i j := by
  have hS0 : 0 < (n : ℝ) * δ := by positivity
  have hSne : ((n : ℝ) * δ) ≠ 0 := ne_of_gt hS0
  rw [actualQ1WeightedRieszKernel,
    q1RieszActiveKernel_eq_rankRieszKernel n hn δ t ((n : ℝ) * δ) (2 - 2 * f t)
      (f t * (2 * f t - 1)) hδ hS0 hcard,
    weightedRieszDiscreteMatrix_apply]
  field_simp

/-! ## The Hermitian spectral matrix of the actual statistic -/

/-- The Hermitian wrapper of the actual weighted feature-quadratic spectral
matrix: its eigenvalue power sums are the object of the final theorem. -/
def actualQ1Hermitian (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M) (r : ℕ) (n : ℕ)
    (δ t : ℝ) :
    (weightedFeatureQuadraticMatrix
        (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
        (actualQ1Coeff n δ t) (actualQ1SpectralWeight f r n δ t)).IsHermitian :=
  weightedFeatureQuadraticMatrix_isHermitian
    (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
    (actualQ1Coeff n δ t) (actualQ1SpectralWeight f r n δ t)

/-- The Riesz comparison matrix: the quadrature matrix on the active grid. -/
def actualQ1RieszMatrix (f : ℝ → ℝ) (r : ℕ) (n : ℕ) (δ t : ℝ) :
    Matrix (Fin (localWeightActiveSet n 1 δ t).card)
      (Fin (localWeightActiveSet n 1 δ t).card) ℝ :=
  weightedRieszDiscreteMatrix (localWeightActiveSet n 1 δ t).card
    ((n : ℝ) * δ) (2 - 2 * f t) (f t * (2 * f t - 1)) (equivalentKernel r)

/-! ## Deliverable (2): the Frobenius form of the perturbation -/

/-- **Frobenius identity.**  The mesh-normalized actual matrix differs from the
quadrature matrix by exactly the mesh energy of the two comparison kernels:
`‖Ā − 𝔾‖_F = √(realScaleMeshEnergy S (A-side − G-side))`.  This is the exact
conversion between the kernel-level convergence and the matrix-level one. -/
theorem actualQ1_frobenius_norm_eq_sqrt_energy (f : ℝ → ℝ)
    (hf : f ∈ hurstHolderClass p M) (r : ℕ) (n : ℕ) (hn : 0 < n) (δ t : ℝ) (hδ : 0 < δ) :
    ‖actualQ1NormalizedActualMatrix f hf r n δ t -
        actualQ1RieszMatrix f r n δ t‖
      = Real.sqrt (realScaleMeshEnergy ((n : ℝ) * δ)
          (actualQ1WeightedActualKernel f hf r n δ t -
            actualQ1WeightedRieszKernel f r n δ t)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < n * δ := mul_pos hnR hδ
  have hinv0 : (0 : ℝ) < ((n : ℝ) * δ)⁻¹ := inv_pos.mpr hn1
  have hkey : ∀ i j : Fin (localWeightActiveSet n 1 δ t).card,
      (actualQ1NormalizedActualMatrix f hf r n δ t -
          actualQ1RieszMatrix f r n δ t) i j
        = ((n : ℝ) * δ)⁻¹ *
            (actualQ1WeightedActualKernel f hf r n δ t i j -
              actualQ1WeightedRieszKernel f r n δ t i j) := by
    intro i j
    have hcard : 0 < (localWeightActiveSet n 1 δ t).card := by
      have := i.isLt
      omega
    rw [Matrix.sub_apply, actualQ1NormalizedActualMatrix, actualQ1RieszMatrix,
      weightedRieszDiscreteMatrix_apply]
    have hG := actualQ1_weightedRieszKernel_scale (f := f) r n hn δ t hδ hcard i j
    rw [hG, weightedRieszDiscreteMatrix_apply]
    simp only [Pi.sub_apply, actualQ1WeightedActualKernel,
      actualQ1WeightedRieszKernel]
    have hSne : ((n : ℝ) * δ) ≠ 0 := ne_of_gt hn1
    field_simp
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
  congr 1
  simp only [realScaleMeshEnergy]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by
    have e1 : ‖((n : ℝ) * δ)⁻¹ *
        (actualQ1WeightedActualKernel f hf r n δ t i j -
          actualQ1WeightedRieszKernel f r n δ t i j)‖ ^ (2 : ℝ)
        = ((n : ℝ) * δ)⁻¹ ^ 2 *
          ‖(actualQ1WeightedActualKernel f hf r n δ t i j -
            actualQ1WeightedRieszKernel f r n δ t i j)‖ ^ 2 := by
      rw [norm_mul, Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_natCast, ← Real.rpow_natCast, Real.norm_eq_abs,
        abs_of_pos hinv0]
      norm_num
    rw [hkey i j, e1, Real.norm_eq_abs, sq_abs]
    rfl

/-- The Frobenius convergence of the normalized pair from the energy
convergence. -/
theorem actualQ1_frobenius_norm_tendsto_zero (f : ℝ → ℝ)
    (hf : f ∈ hurstHolderClass p M) (r : ℕ) (δ : ℕ → ℝ) (t : ℝ)
    (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hE : Tendsto (fun n : ℕ => realScaleMeshEnergy ((n : ℝ) * δ n)
        (actualQ1WeightedActualKernel f hf r n (δ n) t -
          actualQ1WeightedRieszKernel f r n (δ n) t)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ‖actualQ1NormalizedActualMatrix f hf r n (δ n) t -
        actualQ1RieszMatrix f r n (δ n) t‖) atTop (𝓝 0) := by
  have h1 : ∀ᶠ n : ℕ in atTop, (1 : ℕ) ≤ n := Filter.eventually_ge_atTop 1
  have hEq : ∀ᶠ n : ℕ in atTop,
      Real.sqrt (realScaleMeshEnergy ((n : ℝ) * δ n)
            (actualQ1WeightedActualKernel f hf r n (δ n) t -
              actualQ1WeightedRieszKernel f r n (δ n) t))
        = ‖actualQ1NormalizedActualMatrix f hf r n (δ n) t -
          actualQ1RieszMatrix f r n (δ n) t‖ := by
    filter_upwards [hδpos, h1] with n hδ hn1
    exact (actualQ1_frobenius_norm_eq_sqrt_energy f hf r n (by omega) (δ n) t
      hδ).symm
  have hcont : Tendsto (fun n : ℕ => Real.sqrt (realScaleMeshEnergy
      ((n : ℝ) * δ n)
        (actualQ1WeightedActualKernel f hf r n (δ n) t -
          actualQ1WeightedRieszKernel f r n (δ n) t))) atTop (𝓝 (Real.sqrt 0)) :=
    Filter.Tendsto.comp (Real.continuous_sqrt.tendsto 0) hE
  have hsqrt0 : Real.sqrt (0 : ℝ) = 0 := Real.sqrt_zero
  rw [hsqrt0] at hcont
  exact Tendsto.congr' hEq hcont

/-! ## Deliverable (3): trace powers and the main theorem -/

/-- The energy convergence of
`hurstHolder_q1_actual_weighted_kernel_hilbertSchmidt_to_riesz`, specialized
to the active-window data of this file: the mesh energy of the A-side minus
G-side kernel comparison tends to zero (the UNWEIGHTED-dimension conclusion;
the dimension-weighted rate `hPert` of the main theorem is the remaining open
deterministic input). -/
theorem actualQ1_meshEnergy_tendsto_zero
    (p a b M : ℝ) (r : ℕ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b)
    (hM : 0 ≤ M) (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop)
    (R : ℕ → ℕ) (hR : ∀ᶠ n in atTop, 1 ≤ R n)
    (hcut : Tendsto (fun n : ℕ => ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) - 2) *
      ((localWeightActiveSet n 1 (δ n) t).card : ℝ) * (2 * (R n : ℝ) + 1))
      atTop (𝓝 0))
    (henv : ∀ Ccov ≥ 0, ∀ Ctail ≥ 0, ∀ L > 0, Tendsto (fun n : ℕ =>
      q1ActualLongTailEnvelope b Ccov Ctail L M (f t) n (δ n) ((n : ℝ) * δ n)
        (R n)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => realScaleMeshEnergy ((n : ℝ) * δ n)
        (actualQ1WeightedActualKernel f hf r n (δ n) t -
          actualQ1WeightedRieszKernel f r n (δ n) t)) atTop (𝓝 0) := by
  obtain ⟨Ccov, hCcov, Ctail, hCtail, L, hL, hK⟩ :=
    hurstHolder_q1_actual_weighted_kernel_hilbertSchmidt_to_riesz
      p a b M r hp ha hb hab hM f hf hF t ht hlong
  exact hK δ R hδpos hδ0 hN hR hcut (henv Ccov hCcov Ctail hCtail L hL)

/-- The uniform Frobenius bound consumed by the trace-power transfer.  Its
discharge route (elementary, entrywise): the Riesz side satisfies
`‖actualQ1RieszMatrix‖ ≤ B_ω * √Cref` where
`Cref := 2 * c² * (3 + 3 * 4 ^ (1 - 2ψ) / (1 - 2ψ))` is the constant of
`rankRieszKernel_energy_le_const`, because the global bound
`|equivalentKernel r z| ≤ B_ω` (`equivalentKernel_bounded`) gives per-entry
`|G_ij| = |S⁻¹ * ω_i * R_ij| ≤ S⁻¹ * B_ω * |R_ij|`, hence
`∑_{ij} G_ij² ≤ S⁻² * B_ω² * ∑ R_ij² ≤ B_ω² * Cref`; and the actual side
satisfies `‖Ā‖ ≤ ‖Ā − 𝔾‖ + ‖𝔾‖ ≤ 1 + B_ω * √Cref` by the triangle
inequality and the energy convergence of
`actualQ1_meshEnergy_tendsto_zero`.  Only the mechanical Finset bookkeeping
of this sketch is not yet mechanized here. -/
def ActualQ1UniformFrobeniusBound (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (r : ℕ) (δ : ℕ → ℝ) (t : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
    max ‖actualQ1NormalizedActualMatrix f hf r n (δ n) t‖
      ‖actualQ1RieszMatrix f r n (δ n) t‖ ≤ C

/-! ### All fixed power traces of the normalized actual matrix -/

/-- **Trace-power convergence (deliverable 2 + 3).**  Under the quadrature
instance and the dimension-weighted perturbation hypothesis `hPert` (plus the
uniform Frobenius bound `hBound`), every fixed power trace of the
mesh-normalized actual matrix converges to the weighted Riesz cycle
integral. -/
theorem actualQ1_trace_pow_tendsto
    (p a b M : ℝ) (r : ℕ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b)
    (hM : 0 ≤ M) (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (R : ℕ → ℕ) (hR : ∀ᶠ n in atTop, 1 ≤ R n)
    (hcut : Tendsto (fun n : ℕ => ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) - 2) *
      ((localWeightActiveSet n 1 (δ n) t).card : ℝ) * (2 * (R n : ℝ) + 1))
      atTop (𝓝 0))
    (henv : ∀ Ccov ≥ 0, ∀ Ctail ≥ 0, ∀ L > 0, Tendsto (fun n : ℕ =>
      q1ActualLongTailEnvelope b Ccov Ctail L M (f t) n (δ n) ((n : ℝ) * δ n)
        (R n)) atTop (𝓝 0))
    (hPert : Tendsto (fun n : ℕ => ((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
      realScaleMeshEnergy ((n : ℝ) * δ n)
        (actualQ1WeightedActualKernel f hf r n (δ n) t -
          actualQ1WeightedRieszKernel f r n (δ n) t)) atTop (𝓝 0))
    (hBound : ActualQ1UniformFrobeniusBound f hf r δ t)
    (k : ℕ) (hk : 2 ≤ k) :
    Tendsto (fun n : ℕ => Matrix.trace
        ((actualQ1NormalizedActualMatrix f hf r n (δ n) t) ^ k))
      atTop (𝓝 (weightedRieszCycleIntegral k (2 - 2 * f t)
        (f t * (2 * f t - 1)) (equivalentKernel r))) := by
  set psi : ℝ := 2 - 2 * f t with hpsi
  set c : ℝ := f t * (2 * f t - 1) with hc
  obtain ⟨hm0, hratio⟩ := localWeightActiveSet_card_ratio_tendsto_two 1 t ht δ
    hδpos hδ0 hN
  have hcardpos : ∀ᶠ n : ℕ in atTop,
      0 < (localWeightActiveSet n 1 (δ n) t).card := hm0
  have hn1 : ∀ᶠ n : ℕ in atTop, (1 : ℕ) ≤ n := Filter.eventually_ge_atTop 1
  have hn2 : ∀ᶠ n : ℕ in atTop, 2 ≤ n := by
    refine hcardpos.mono fun n hcard => ?_
    have hlt := (localWeightActiveIndex n 1 (δ n) t ⟨0, hcard⟩).isLt
    omega
  have hS1 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ (n : ℝ) * δ n :=
    hN.eventually_ge_atTop 1
  -- the mesh of the active grid tends to infinity
  have hmtop : Tendsto (fun n : ℕ => (localWeightActiveSet n 1 (δ n) t).card)
      atTop atTop := by
    obtain ⟨hcardpos, hratio⟩ := localWeightActiveSet_card_ratio_tendsto_two 1
      t ht δ hδpos hδ0 hN
    rw [Filter.tendsto_atTop_atTop]
    intro N
    have hall : ∀ᶠ n : ℕ in atTop, (1 : ℝ) <
        ((localWeightActiveSet n 1 (δ n) t).card : ℝ) / ((n : ℝ) * δ n) ∧
        (N : ℝ) ≤ (n : ℝ) * δ n ∧ (1 : ℝ) ≤ (n : ℝ) * δ n := by
      filter_upwards [hratio.eventually_const_lt one_lt_two,
        hN.eventually_ge_atTop (N : ℝ), hN.eventually_ge_atTop 1] with n h1 h2 h3
      exact ⟨h1, h2, h3⟩
    obtain ⟨i, hi⟩ := Filter.eventually_atTop.mp hall
    refine ⟨i, fun a ha => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hi a ha
    have hS0 : (0 : ℝ) < (a : ℝ) * δ a := by linarith
    have heq : ((localWeightActiveSet a 1 (δ a) t).card : ℝ)
        = ((localWeightActiveSet a 1 (δ a) t).card : ℝ) / ((a : ℝ) * δ a) *
          ((a : ℝ) * δ a) := by
      rw [div_mul_cancel₀ (a := ((localWeightActiveSet a 1 (δ a) t).card : ℝ))
        (h := by linarith)]
    have hle : ((a : ℝ) * δ a) ≤ (localWeightActiveSet a 1 (δ a) t).card := by
      rw [heq]
      exact le_trans (by rw [one_mul])
        (le_of_lt (mul_lt_mul_of_pos_right h1 hS0))
    exact_mod_cast (h2.trans hle)
  -- the quadrature instance along the active grid
  obtain ⟨B, hB0, hB⟩ := equivalentKernel_bounded r
  have hquad := hasWeightedRieszCycleQuadrature_instance
    (fun n : ℕ => (localWeightActiveSet n 1 (δ n) t).card)
    (fun n : ℕ => (n : ℝ) * δ n) psi c B (equivalentKernel r) hmtop hratio
    (by filter_upwards [hN.eventually_ge_atTop 1, hcardpos] with n h hcard
        exact ⟨by linarith, hcard⟩)
    (by rw [hpsi]; have := (hF ht).2; linarith)
    (by rw [hpsi]; linarith)
    (equivalentKernel_continuous r) fun z hz => hB z
  -- the Frobenius perturbation input, in the √(2/card) · δ' form
  obtain ⟨C, hC0, hC⟩ := hBound
  have henergy := actualQ1_frobenius_norm_tendsto_zero f hf r δ t hδpos
    (actualQ1_meshEnergy_tendsto_zero p a b M r hp ha hb hab hM f hf hF t ht
      hlong δ hδpos hδ0 hN R hR hcut henv)
  have hE0 : Tendsto (fun n : ℕ => ((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
      realScaleMeshEnergy ((n : ℝ) * δ n)
        (actualQ1WeightedActualKernel f hf r n (δ n) t -
          actualQ1WeightedRieszKernel f r n (δ n) t) / 2) atTop (𝓝 (0 : ℝ)) := by
    simpa using hPert.div_const 2
  have hδ'0 : Tendsto (fun n : ℕ => Real.sqrt
      (((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
        realScaleMeshEnergy ((n : ℝ) * δ n)
          (actualQ1WeightedActualKernel f hf r n (δ n) t -
            actualQ1WeightedRieszKernel f r n (δ n) t) / 2)) atTop (𝓝 0) := by
    have hc := Filter.Tendsto.comp
      (Real.continuous_sqrt.continuousAt (x := 0)).tendsto hE0
    rw [Real.sqrt_zero] at hc
    exact hc
  have hΔ : ∀ᶠ n : ℕ in atTop,
      ‖actualQ1NormalizedActualMatrix f hf r n (δ n) t -
        actualQ1RieszMatrix f r n (δ n) t‖
        ≤ Real.sqrt (2 / ((Fintype.card (Fin (localWeightActiveSet n 1 (δ n) t).card)) : ℝ)) *
          Real.sqrt (((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
            realScaleMeshEnergy ((n : ℝ) * δ n)
              (actualQ1WeightedActualKernel f hf r n (δ n) t -
                actualQ1WeightedRieszKernel f r n (δ n) t) / 2) := by
    filter_upwards [hcardpos, hδpos] with n hcard hδ
    have hn0 : 0 < n := by
      have hlt := (localWeightActiveIndex n 1 (δ n) t ⟨0, hcard⟩).isLt
      omega
    rw [actualQ1_frobenius_norm_eq_sqrt_energy f hf r n hn0 (δ n) t hδ,
      Fintype.card_fin,
      ← Real.sqrt_mul
        (by positivity : (0 : ℝ) ≤ 2 / (localWeightActiveSet n 1 (δ n) t).card)]
    have hmne : ((localWeightActiveSet n 1 (δ n) t).card : ℝ) ≠ 0 :=
      ne_of_gt (by exact_mod_cast hcard)
    congr 1
    field_simp [hmne]
    rfl
  have htrace := mesh_frobenius_trace_pow_tendsto
    (fun n : ℕ => Fin (localWeightActiveSet n 1 (δ n) t).card)
    (fun n => actualQ1NormalizedActualMatrix f hf r n (δ n) t)
    (fun n => actualQ1RieszMatrix f r n (δ n) t)
    (fun n => Real.sqrt (((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
      realScaleMeshEnergy ((n : ℝ) * δ n)
        (actualQ1WeightedActualKernel f hf r n (δ n) t -
          actualQ1WeightedRieszKernel f r n (δ n) t) / 2))
    C hC hΔ
      (Eventually.of_forall fun _ => Real.sqrt_nonneg _)
      hδ'0 k
  have hG : Tendsto (fun n : ℕ => Matrix.trace
      ((actualQ1RieszMatrix f r n (δ n) t) ^ k)) atTop
      (𝓝 (weightedRieszCycleIntegral k psi c (equivalentKernel r))) :=
    weightedRieszDiscrete_trace_pow_tendsto
      (fun n : ℕ => (localWeightActiveSet n 1 (δ n) t).card)
      (fun n : ℕ => (n : ℝ) * δ n) psi c (equivalentKernel r) hquad k hk
  have hd : Tendsto (fun n : ℕ => Matrix.trace
      ((actualQ1NormalizedActualMatrix f hf r n (δ n) t) ^ k) -
      Matrix.trace ((actualQ1RieszMatrix f r n (δ n) t) ^ k)) atTop (𝓝 0) := by
    exact tendsto_iff_dist_tendsto_zero.mpr
      (by simpa only [Real.dist_eq, sub_zero] using htrace)
  have hfin : Tendsto (fun n : ℕ =>
      (Matrix.trace ((actualQ1NormalizedActualMatrix f hf r n (δ n) t) ^ k)
        - Matrix.trace ((actualQ1RieszMatrix f r n (δ n) t) ^ k))
      + Matrix.trace ((actualQ1RieszMatrix f r n (δ n) t) ^ k)) atTop
      (𝓝 (weightedRieszCycleIntegral k psi c (equivalentKernel r))) := by
    simpa using hd.add hG
  exact Tendsto.congr (fun _ => by ring) hfin

/-! ### The main theorem: eigenvalue power sums and the signed spectral endpoint -/

/-- **Even eigenvalue power sums of the actual q1 long-memory second-chaos
matrix.**  The even-`k` power sums of the eigenvalues of the actual weighted
feature-quadratic spectral matrix converge to the power sums of the Riesz
spectrum `lam`; this is exactly the `hp` input (at even exponents) of
`paddedAbsRearranged_tendsto`. -/
theorem actualQ1_eigenvalue_even_power_sums
    (p a b M : ℝ) (r : ℕ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b)
    (hM : 0 ≤ M) (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop)
    (lam : ℕ → ℝ) (hlam : Antitone lam ∧ ∀ j, 0 ≤ lam j ∧ Summable (fun j => lam j ^ 2))
    (hRiesz : ∀ k : ℕ, 2 ≤ k → HasSum (fun j => lam j ^ k)
      (weightedRieszCycleIntegral k (2 - 2 * f t) (f t * (2 * f t - 1))
        (equivalentKernel r)))
    (R : ℕ → ℕ) (hR : ∀ᶠ n in atTop, 1 ≤ R n)
    (hcut : Tendsto (fun n : ℕ => ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) - 2) *
      ((localWeightActiveSet n 1 (δ n) t).card : ℝ) * (2 * (R n : ℝ) + 1))
      atTop (𝓝 0))
    (henv : ∀ Ccov ≥ 0, ∀ Ctail ≥ 0, ∀ L > 0, Tendsto (fun n : ℕ =>
      q1ActualLongTailEnvelope b Ccov Ctail L M (f t) n (δ n) ((n : ℝ) * δ n)
        (R n)) atTop (𝓝 0))
    (hPert : Tendsto (fun n : ℕ => ((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
      realScaleMeshEnergy ((n : ℝ) * δ n)
        (actualQ1WeightedActualKernel f hf r n (δ n) t -
          actualQ1WeightedRieszKernel f r n (δ n) t)) atTop (𝓝 0))
    (hBound : ActualQ1UniformFrobeniusBound f hf r δ t)
    (k : ℕ) (hk : 2 ≤ k) (hkev : Even k) :
    Tendsto (fun n : ℕ => ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
        (actualQ1Hermitian f hf r n (δ n) t).eigenvalues i ^ k)
      atTop (𝓝 (∑' j, lam j ^ k)) := by
  have hcardpos := (localWeightActiveSet_card_ratio_tendsto_two 1 t ht δ hδpos
    hδ0 hN).1
  have htr : ∀ᶠ n : ℕ in atTop,
      ∑ i : Fin (localWeightActiveSet n 1 (δ n) t).card,
        (actualQ1Hermitian f hf r n (δ n) t).eigenvalues i ^ k
      = Matrix.trace ((actualQ1NormalizedActualMatrix f hf r n (δ n) t) ^ k) := by
    filter_upwards [hcardpos, hδpos] with n hcard hδ
    have hn : 0 < n := by
      have hlt := (localWeightActiveIndex n 1 (δ n) t ⟨0, hcard⟩).isLt
      omega
    rw [← hermitian_trace_pow_eq_sum_eigenvalues_pow
      (actualQ1Hermitian f hf r n (δ n) t) k]
    rw [trace_pow_weightedFeatureQuadraticMatrix_eq
      (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
      (actualQ1Coeff n (δ n) t) (actualQ1SpectralWeight f r n (δ n) t) k]
    rw [actualQ1_diagonalCorrelation_eq f hf r n hn (δ n) t hδ]
  rw [show (∑' j : ℕ, lam j ^ k)
      = weightedRieszCycleIntegral k (2 - 2 * f t) (f t * (2 * f t - 1))
        (equivalentKernel r) from (hRiesz k hk).tsum_eq]
  refine Tendsto.congr' (htr.mono fun n h => h.symm) ?_
  exact actualQ1_trace_pow_tendsto p a b M r hp ha hb hab hM f hf t ht hlong
    δ hδpos hδ0 hN hF R hR hcut henv hPert hBound k hk


/-- **The main theorem (signed form).**  For the actual q1 long-memory
second-chaos statistic, the padded decreasing rearrangement of the absolute
eigenvalues of the actual weighted feature-quadratic spectral matrix converges
coefficientwise to the Riesz spectrum `lam`.  This is the signed-path output
of `paddedAbsRearranged_tendsto`, consuming the even power sums proved above;
together with a second-chaos law for `lam`
(`IsSecondChaosSeriesLaw`, cf. `IsWeightedRieszSecondChaosLaw`) it feeds the
distributional endpoint of `Hurst.HcoeffBridge`. -/
theorem actualQ1EigenvaluePowerSums_tendsto
    (p a b M : ℝ) (r : ℕ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b)
    (hM : 0 ≤ M) (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hN : Tendsto (fun n : ℕ => (n : ℝ) * δ n) atTop atTop)
    (hm : ∀ n, 0 < (localWeightActiveSet n 1 (δ n) t).card)
    (lam : ℕ → ℝ) (hlam : Antitone lam ∧ ∀ j, 0 ≤ lam j ∧ Summable (fun j => lam j ^ 2))
    (hRiesz : ∀ k : ℕ, 2 ≤ k → HasSum (fun j => lam j ^ k)
      (weightedRieszCycleIntegral k (2 - 2 * f t) (f t * (2 * f t - 1))
        (equivalentKernel r)))
    (R : ℕ → ℕ) (hR : ∀ᶠ n in atTop, 1 ≤ R n)
    (hcut : Tendsto (fun n : ℕ => ((n : ℝ) * δ n) ^ (2 * (2 - 2 * f t) - 2) *
      ((localWeightActiveSet n 1 (δ n) t).card : ℝ) * (2 * (R n : ℝ) + 1))
      atTop (𝓝 0))
    (henv : ∀ Ccov ≥ 0, ∀ Ctail ≥ 0, ∀ L > 0, Tendsto (fun n : ℕ =>
      q1ActualLongTailEnvelope b Ccov Ctail L M (f t) n (δ n) ((n : ℝ) * δ n)
        (R n)) atTop (𝓝 0))
    (hPert : Tendsto (fun n : ℕ => ((localWeightActiveSet n 1 (δ n) t).card : ℝ) *
      realScaleMeshEnergy ((n : ℝ) * δ n)
        (actualQ1WeightedActualKernel f hf r n (δ n) t -
          actualQ1WeightedRieszKernel f r n (δ n) t)) atTop (𝓝 0))
    (hBound : ActualQ1UniformFrobeniusBound f hf r δ t)
    (j : ℕ) :
    Tendsto (fun n : ℕ => padRearranged
      (fun i => |(actualQ1Hermitian f hf r n (δ n) t).eigenvalues i|) j)
      atTop (𝓝 (lam j)) := by
  have hmtop : Tendsto (fun n : ℕ => (localWeightActiveSet n 1 (δ n) t).card)
      atTop atTop := by
    obtain ⟨hcardpos, hratio⟩ := localWeightActiveSet_card_ratio_tendsto_two 1
      t ht δ hδpos hδ0 hN
    rw [Filter.tendsto_atTop_atTop]
    intro N
    have hall : ∀ᶠ n : ℕ in atTop, (1 : ℝ) <
        ((localWeightActiveSet n 1 (δ n) t).card : ℝ) / ((n : ℝ) * δ n) ∧
        (N : ℝ) ≤ (n : ℝ) * δ n ∧ (1 : ℝ) ≤ (n : ℝ) * δ n := by
      filter_upwards [hratio.eventually_const_lt one_lt_two,
        hN.eventually_ge_atTop (N : ℝ), hN.eventually_ge_atTop 1] with n h1 h2 h3
      exact ⟨h1, h2, h3⟩
    obtain ⟨i, hi⟩ := Filter.eventually_atTop.mp hall
    refine ⟨i, fun a ha => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hi a ha
    have hS0 : (0 : ℝ) < (a : ℝ) * δ a := by linarith
    have hle : ((a : ℝ) * δ a) ≤ (localWeightActiveSet a 1 (δ a) t).card := by
      have hfac : ((localWeightActiveSet a 1 (δ a) t).card : ℝ)
          = ((localWeightActiveSet a 1 (δ a) t).card : ℝ) / ((a : ℝ) * δ a) *
            ((a : ℝ) * δ a) :=
        (div_mul_cancel₀ ((localWeightActiveSet a 1 (δ a) t).card : ℝ)
          (ne_of_gt hS0)).symm
      rw [hfac]
      exact le_trans (by rw [one_mul])
        (le_of_lt (mul_lt_mul_of_pos_right h1 hS0))
    exact_mod_cast (h2.trans hle)
  exact paddedAbsRearranged_tendsto
    (fun n : ℕ => (localWeightActiveSet n 1 (δ n) t).card)
    (fun n i => (actualQ1Hermitian f hf r n (δ n) t).eigenvalues i) lam hm
    hmtop hlam
    (fun k hk hkev =>
      actualQ1_eigenvalue_even_power_sums p a b M r hp ha hb hab hM f hf hF t ht
        hlong δ hδpos hδ0 hN lam hlam hRiesz R hR hcut henv hPert hBound k hk
        hkev)
    j

end Hurst