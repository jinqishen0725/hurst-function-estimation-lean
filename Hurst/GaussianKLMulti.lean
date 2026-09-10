/-
Adapted from StatLean/Stat-Lean, commit 855b6afb69fead1bef066111732ed44df181040e,
StatLean/Minimaxity/ForMathlib/GaussianKLMulti.lean. Apache-2.0; see third_party/StatLean/LICENSE.
Local changes: imports/namespace adapted; scalar proof reused from Hurst; mean-shift corollary omitted; public lemmas declared as theorems for audit.
-/
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Moments.Variance
import Hurst.KLDataProcessing
import Hurst.KLProduct
import Hurst.GaussianKL

/-!
# KL divergence between centered multivariate Gaussians

Closed form for the Kullback–Leibler divergence between two zero-mean multivariate Gaussian
distributions on $\mathbb{R}^d$. For positive-definite covariance matrices $A, B \in
\mathbb{R}^{d \times d}$,
$$
D\bigl(\mathcal{N}(0,A) \,\|\, \mathcal{N}(0,B)\bigr)
  = \tfrac{1}{2}\Bigl(\log\det B - \log\det A + \operatorname{tr}(B^{-1}A) - d\Bigr).
$$

This is the special case (equal, zero means) of the general two-Gaussian KL formula
$D(\mathcal{N}(\mu_0,\Sigma_0)\,\|\,\mathcal{N}(\mu_1,\Sigma_1)) = \tfrac12\bigl(\log\frac{\det
\Sigma_1}{\det\Sigma_0} - d + \operatorname{tr}(\Sigma_1^{-1}\Sigma_0) +
(\mu_1-\mu_0)^\top\Sigma_1^{-1}(\mu_1-\mu_0)\bigr)$ that underlies Wainwright's example.

A companion corollary, the equal-(scalar)-covariance mean-shift formula
$D\bigl(\mathcal{N}(\mu, cI) \,\|\, \mathcal{N}(\nu, cI)\bigr) = \|\mu-\nu\|^2/(2c)$ for $c>0$,
is the multivariate analogue of the one-dimensional equal-variance KL and feeds the
linear-regression minimax example.

**Note on hypotheses.** The main theorem requires both $A$ and $B$ to be *positive definite*
(not merely positive semidefinite); this is needed for $\det B \neq 0$, $B^{-1}$, and the
whitening square root $B^{-1/2}$ to exist, and is implicit in the textbook's reference to
$\operatorname{tr}(B^{-1}A)$ and $\log\det A$.

**Reference.** M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax lower bounds), §15.6, Example 15.13(a).
The mean-shift corollary is Example 15.13(b).

**Proof formalization notes.** The proof is the standard reduction to one dimension:

1. KL divergence is invariant under an invertible linear push-forward (`klDiv_map_eq_of_comp`,
   from the data-processing inequality `klDiv_map_le` applied in both directions).
2. **Whitening.** Push forward by $B^{-1/2}$ (via `CFC.sqrt B⁻¹`); this sends
   $\mathcal{N}(0,B) \mapsto \mathcal{N}(0,I)$ and $\mathcal{N}(0,A) \mapsto \mathcal{N}(0,C)$
   with $C = B^{-1/2} A B^{-1/2}$.
3. **Diagonalize.** Push forward by the orthogonal $U^\top$ from the spectral theorem; this keeps
   $\mathcal{N}(0,I)$ fixed and turns $\mathcal{N}(0,C)$ into $\mathcal{N}(0, \operatorname{diag}
   \Lambda)$.
4. **Tensorize.** $\mathcal{N}(0, \operatorname{diag}\Lambda)$ and $\mathcal{N}(0,I)$ are products
   of one-dimensional Gaussians, so KL tensorizes (`klDiv_pi_eq_sum`).
5. **One dimension.** $D(\mathcal{N}(0,a) \,\|\, \mathcal{N}(0,1)) = \tfrac12(a - 1 - \log a)$
   (`klDiv_gaussianReal_zero`).
6. **Assemble** using $\operatorname{tr} C = \sum_i \Lambda_i$, $\log\det C = \sum_i \log\Lambda_i$,
   $\operatorname{tr} C = \operatorname{tr}(B^{-1}A)$, $\det C = \det A/\det B$.

**Bibliographic comments.** The Kullback–Leibler divergence originates with S. Kullback and
R. A. Leibler, "On Information and Sufficiency," *Annals of Mathematical Statistics*, 22(1):79–86,
1951. The closed-form expression for the KL divergence between two multivariate Gaussian
distributions is folklore with no single seminal source: it is a direct computation from
the Gaussian density and is reproduced in standard references (e.g. Wainwright 2019, Example 15.13;
C. M. Bishop, *Pattern Recognition and Machine Learning*, Springer, 2006; T. M. Cover and J. A.
Thomas, *Elements of Information Theory*, 2nd ed., Wiley, 2006). The centered, zero-mean case
formalized here is the special case retaining only the determinant and trace terms.
-/

open MeasureTheory ProbabilityTheory InformationTheory Matrix WithLp
open scoped ENNReal NNReal RealInnerProductSpace MatrixOrder

namespace Hurst

/-! ### Generic KL push-forward invariance -/

/-- KL divergence is invariant under a measurable map admitting a measurable left inverse.
Both push-forwards are probability measures; equality follows by applying the data-processing
inequality `klDiv_map_le` to `f` and to its inverse `g`. -/
theorem klDiv_map_eq_of_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β} {g : β → α} (hf : Measurable f) (hg : Measurable g) (hgf : g ∘ f = id)
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    klDiv (μ.map f) (ν.map f) = klDiv μ ν := by
  haveI : IsProbabilityMeasure (μ.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  haveI : IsProbabilityMeasure (ν.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  refine le_antisymm (klDiv_map_le hf μ ν) ?_
  have h := klDiv_map_le hg (μ.map f) (ν.map f)
  rwa [Measure.map_map hg hf, Measure.map_map hg hf, hgf, Measure.map_id, Measure.map_id] at h

/-- KL divergence is invariant under push-forward by a measurable equivalence. -/
private lemma klDiv_map_measurableEquiv_eq {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    klDiv (μ.map e) (ν.map e) = klDiv μ ν :=
  klDiv_map_eq_of_comp e.measurable e.symm.measurable
    (by funext x; exact e.symm_apply_apply x) μ ν

/-- Reuse the already verified scalar variance-change formula. -/
private lemma klDiv_gaussianReal_zero (a : ℝ≥0) (ha : a ≠ 0) :
    klDiv (gaussianReal 0 a) (gaussianReal 0 1) =
      ENNReal.ofReal (2⁻¹ * ((a : ℝ) - 1 - Real.log (a : ℝ))) := by
  simpa only [div_eq_mul_inv, mul_comm] using klDiv_gaussianReal_centered_unit a ha

private lemma adjoint_toEuclideanCLM {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) :
    ContinuousLinearMap.adjoint (toEuclideanCLM (𝕜 := ℝ) M) = toEuclideanCLM (𝕜 := ℝ) Mᵀ := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [inner_toEuclideanCLM, real_inner_comm, inner_toEuclideanCLM, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose, dotProduct_comm]

/-! ### Push-forward of a centered multivariate Gaussian under a linear map -/

/-- **Linear push-forward of a centered multivariate Gaussian.** For a real matrix `M` and a
positive-semidefinite covariance `S`, the push-forward of `𝒩(0,S)` under `x ↦ Mx` is
`𝒩(0, M S Mᵀ)`. Proved via `IsGaussian.ext` (equal means, equal covariance bilinear form). -/
private lemma map_multivariateGaussian_clm {d : ℕ} (M S : Matrix (Fin d) (Fin d) ℝ)
    (hS : S.PosSemidef) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S).map (toEuclideanCLM (𝕜 := ℝ) M)
      = multivariateGaussian 0 (M * S * Mᵀ) := by
  have hSMSM : (M * S * Mᵀ).PosSemidef := by
    have h := hS.mul_mul_conjTranspose_same M
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have algiden : ∀ (u v : Fin d → ℝ),
      (Mᵀ *ᵥ u) ⬝ᵥ S *ᵥ (Mᵀ *ᵥ v) = u ⬝ᵥ (M * S * Mᵀ) *ᵥ v := by
    intro u v
    rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec,
      Matrix.mulVec_transpose, Matrix.vecMul_vecMul, ← Matrix.mul_assoc]
  refine IsGaussian.ext ?_ ?_
  · simp only [id_eq]
    rw [ContinuousLinearMap.integral_id_map IsGaussian.integrable_id,
      integral_id_multivariateGaussian, integral_id_multivariateGaussian, map_zero]
  · ext u v
    rw [covarianceBilin_map IsGaussian.memLp_two_id (toEuclideanCLM (𝕜 := ℝ) M) u v,
      covarianceBilin_multivariateGaussian hS, covarianceBilin_multivariateGaussian hSMSM,
      adjoint_toEuclideanCLM]
    simp only [ofLp_toEuclideanCLM]
    exact algiden _ _

/-! ### Tensorization of KL over a finite product -/

/-- **Additivity of KL over a finite product** (non-i.i.d. chain rule):
`D(∏ᵢ μᵢ ‖ ∏ᵢ νᵢ) = ∑ᵢ D(μᵢ ‖ νᵢ)`. -/
theorem klDiv_pi_eq_sum : ∀ {d : ℕ} (μ ν : Fin d → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)],
    klDiv (Measure.pi μ) (Measure.pi ν) = ∑ i, klDiv (μ i) (ν i)
  | 0, μ, ν, _, _ => by
      have hpi : Measure.pi μ = Measure.pi ν := by
        rw [Measure.pi_of_empty, Measure.pi_of_empty]
      simp [hpi, klDiv_self]
  | (n + 1), μ, ν, _, _ => by
      have ih := klDiv_pi_eq_sum (fun j => μ (Fin.succAbove 0 j)) (fun j => ν (Fin.succAbove 0 j))
      rw [← klDiv_map_measurableEquiv_eq
            (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0)
          (Measure.pi μ) (Measure.pi ν),
        (measurePreserving_piFinSuccAbove μ 0).map_eq,
        (measurePreserving_piFinSuccAbove ν 0).map_eq,
        klDiv_prod_eq_add, ih, Fin.sum_univ_succAbove (fun i => klDiv (μ i) (ν i)) 0]

/-! ### A diagonal centered Gaussian is a product of one-dimensional Gaussians -/

/-- The multivariate Gaussian with mean `m` and diagonal covariance `diag Λ` is the product of the
one-dimensional Gaussians `𝒩(mᵢ, Λᵢ)`. -/
theorem multivariateGaussian_diagonal_eq_pi {d : ℕ} (m : EuclideanSpace ℝ (Fin d))
    (Λ : Fin d → ℝ) (hΛ : ∀ i, 0 ≤ Λ i) :
    multivariateGaussian m (Matrix.diagonal Λ)
      = (Measure.pi (fun i => gaussianReal (m i) (Λ i).toNNReal)).map (toLp 2) := by
  have hdiag : (Matrix.diagonal Λ).PosSemidef := Matrix.PosSemidef.diagonal (fun i => hΛ i)
  refine Measure.ext_of_charFun ?_
  ext t
  have hcoe : ∀ i, ((Λ i).toNNReal : ℝ) = Λ i := fun i => Real.coe_toNNReal _ (hΛ i)
  have hquad : (t : Fin d → ℝ) ⬝ᵥ (Matrix.diagonal Λ) *ᵥ t = ∑ i, Λ i * t i ^ 2 := by
    rw [Matrix.dotProduct_mulVec]
    unfold dotProduct
    simp only [Matrix.vecMul_diagonal]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hinner : (inner ℝ t m : ℝ) = ∑ i, t i * m i := by
    have h : (inner ℝ t m : ℝ) = ofLp m ⬝ᵥ star (ofLp t) := rfl
    rw [h]
    unfold dotProduct
    exact Finset.sum_congr rfl fun i _ => by simp [mul_comm]
  have hterm : ∀ i, charFun (gaussianReal (m i) (Λ i).toNNReal) (t i)
      = Complex.exp ((t i : ℂ) * (m i : ℂ) * Complex.I - (Λ i : ℂ) * (t i : ℂ) ^ 2 / 2) := by
    intro i
    rw [charFun_gaussianReal]
    push_cast [hcoe i]
    ring_nf
  rw [charFun_multivariateGaussian hdiag, charFun_pi]
  simp_rw [hterm, ← Complex.exp_sum]
  congr 1
  rw [hquad, hinner]
  push_cast
  rw [Finset.sum_mul, Finset.sum_div, ← Finset.sum_sub_distrib]

/-! ### Main theorem -/

/-- KL divergence between two centered multivariate Gaussians (Wainwright Example 15.13(a), μ=0):
`D(𝒩(0,A) ‖ 𝒩(0,B)) = ½ (log det B − log det A + tr(B⁻¹A) − d)`. -/
theorem klDiv_multivariateGaussian_zero {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.PosDef) (hB : B.PosDef) :
    klDiv (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) A)
          (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) B)
      = ENNReal.ofReal (2⁻¹ * (Real.log B.det - Real.log A.det + (B⁻¹ * A).trace - d)) := by
  classical
  -- units / nonzero determinants
  have hBdetU : IsUnit B.det := isUnit_iff_ne_zero.mpr hB.det_pos.ne'
  have hAdetne : A.det ≠ 0 := hA.det_pos.ne'
  have hBdetne : B.det ≠ 0 := hB.det_pos.ne'
  -- whitening matrix `R = B^{-1/2}`
  set R : Matrix (Fin d) (Fin d) ℝ := CFC.sqrt B⁻¹ with hR_def
  have hBinv0 : (0 : Matrix (Fin d) (Fin d) ℝ) ≤ B⁻¹ :=
    Matrix.nonneg_iff_posSemidef.mpr hB.inv.posSemidef
  have hRR : R * R = B⁻¹ := by rw [hR_def]; exact CFC.sqrt_mul_sqrt_self B⁻¹ hBinv0
  have hRsa : IsSelfAdjoint R := by rw [hR_def]; exact IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg B⁻¹)
  have hRtransp : Rᵀ = R := by
    have h : star R = R := hRsa
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  -- commutation `R * B = B * R`
  have hBcomm : Commute B⁻¹ B := by
    unfold Commute SemiconjBy
    rw [Matrix.nonsing_inv_mul B hBdetU, Matrix.mul_nonsing_inv B hBdetU]
  have hcomm : Commute R B := by rw [hR_def]; exact hBcomm.cfcₙ_nnreal NNReal.sqrt
  have hRBR : R * B * R = 1 := by
    rw [Matrix.mul_assoc, ← hcomm.eq, ← Matrix.mul_assoc, hRR, Matrix.nonsing_inv_mul B hBdetU]
  -- `R` is a unit
  have hRunit : IsUnit R := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    intro h0
    have hsq : R.det * R.det = B⁻¹.det := by rw [← Matrix.det_mul, hRR]
    rw [h0, mul_zero] at hsq
    exact hB.inv.det_pos.ne' hsq.symm
  have hRmulVecInj : Function.Injective R.mulVec := Matrix.mulVec_injective_of_isUnit hRunit
  -- the whitened covariance `C = R A R`
  set C : Matrix (Fin d) (Fin d) ℝ := R * A * R with hC_def
  have hC : C.PosDef := by
    rw [hC_def]
    have h := hA.conjTranspose_mul_mul_same hRmulVecInj
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial, hRtransp] at h
  -- determinant and trace of `C`
  have hCdetB : C.det * B.det = A.det := by
    have h1 : C.det * B.det = A.det * ((R * R).det * B.det) := by
      rw [hC_def]; simp only [Matrix.det_mul]; ring
    rw [h1, hRR, ← Matrix.det_mul, Matrix.nonsing_inv_mul B hBdetU, Matrix.det_one, mul_one]
  have hlogdetC : Real.log C.det = Real.log A.det - Real.log B.det := by
    rw [eq_div_of_mul_eq hBdetne hCdetB, Real.log_div hAdetne hBdetne]
  have htraceC : C.trace = (B⁻¹ * A).trace := by
    rw [hC_def, Matrix.trace_mul_cycle, hRR]
  -- spectral data
  set Λ : Fin d → ℝ := hC.1.eigenvalues with hΛ_def
  have hΛpos : ∀ i, 0 < Λ i := fun i => hC.eigenvalues_pos i
  have hΛnonneg : ∀ i, 0 ≤ Λ i := fun i => (hΛpos i).le
  set U : Matrix (Fin d) (Fin d) ℝ := (hC.1.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)
    with hU_def
  have hstarU : star U = Uᵀ := by
    rw [hU_def, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  have hUUt : U * Uᵀ = 1 := by
    have h := Unitary.coe_mul_star_self hC.1.eigenvectorUnitary
    rwa [Unitary.coe_star, ← hU_def, hstarU] at h
  have hUtU : Uᵀ * U = 1 := by
    have h := Unitary.coe_star_mul_self hC.1.eigenvectorUnitary
    rwa [← hU_def, hstarU] at h
  have hUtCU : Uᵀ * C * U = Matrix.diagonal Λ := by
    have h := hC.1.conjStarAlgAut_star_eigenvectorUnitary (𝕜 := ℝ)
    rw [Unitary.conjStarAlgAut_star_apply, ← hU_def, hstarU] at h
    rw [h, hΛ_def]
    simp only [RCLike.ofReal_real_eq_id, Function.id_comp]
  -- Step 1: whitening
  have hcomp1 : (toEuclideanCLM (𝕜 := ℝ) (R * B)) ∘ (toEuclideanCLM (𝕜 := ℝ) R) = id := by
    funext x
    change toEuclideanCLM (𝕜 := ℝ) (R * B) (toEuclideanCLM (𝕜 := ℝ) R x) = x
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, hRBR, map_one, ContinuousLinearMap.one_apply]
  have hwhiten : klDiv (multivariateGaussian 0 A) (multivariateGaussian 0 B)
      = klDiv (multivariateGaussian 0 C)
          (multivariateGaussian 0 (1 : Matrix (Fin d) (Fin d) ℝ)) := by
    rw [← klDiv_map_eq_of_comp (f := toEuclideanCLM (𝕜 := ℝ) R)
        (g := toEuclideanCLM (𝕜 := ℝ) (R * B))
        (by fun_prop) (by fun_prop) hcomp1
        (multivariateGaussian 0 A) (multivariateGaussian 0 B),
      map_multivariateGaussian_clm R A hA.posSemidef,
      map_multivariateGaussian_clm R B hB.posSemidef, hRtransp, ← hC_def, hRBR]
  -- Step 2: diagonalization
  have hcomp2 : (toEuclideanCLM (𝕜 := ℝ) U) ∘ (toEuclideanCLM (𝕜 := ℝ) Uᵀ) = id := by
    funext x
    change toEuclideanCLM (𝕜 := ℝ) U (toEuclideanCLM (𝕜 := ℝ) Uᵀ x) = x
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, hUUt, map_one, ContinuousLinearMap.one_apply]
  have hdiagonalize : klDiv (multivariateGaussian 0 C) (multivariateGaussian 0 1)
      = klDiv (multivariateGaussian 0 (Matrix.diagonal Λ))
          (multivariateGaussian 0 (1 : Matrix (Fin d) (Fin d) ℝ)) := by
    rw [← klDiv_map_eq_of_comp (f := toEuclideanCLM (𝕜 := ℝ) Uᵀ) (g := toEuclideanCLM (𝕜 := ℝ) U)
        (by fun_prop) (by fun_prop) hcomp2
        (multivariateGaussian 0 C) (multivariateGaussian 0 1),
      map_multivariateGaussian_clm Uᵀ C hC.posSemidef,
      map_multivariateGaussian_clm Uᵀ (1 : Matrix (Fin d) (Fin d) ℝ) Matrix.PosSemidef.one,
      Matrix.transpose_transpose, hUtCU, Matrix.mul_one, hUtU]
  -- Step 3: tensorization
  have htensor : klDiv (multivariateGaussian 0 (Matrix.diagonal Λ)) (multivariateGaussian 0 1)
      = ∑ i, klDiv (gaussianReal 0 (Λ i).toNNReal) (gaussianReal 0 1) := by
    rw [multivariateGaussian_diagonal_eq_pi 0 Λ hΛnonneg,
      show (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (1 : Matrix (Fin d) (Fin d) ℝ))
          = (Measure.pi (fun _ => gaussianReal 0 1)).map (toLp 2) by
        rw [multivariateGaussian_zero_one, ← map_pi_eq_stdGaussian],
      klDiv_map_eq_of_comp (f := toLp 2) (g := ofLp) (by fun_prop) (by fun_prop)
        (by funext x; rfl), klDiv_pi_eq_sum]
    simp only [WithLp.ofLp_zero, Pi.zero_apply]
  -- Step 4 + 5: one-dimensional KL and assembly
  have hterm : ∀ i, klDiv (gaussianReal 0 (Λ i).toNNReal) (gaussianReal 0 1)
      = ENNReal.ofReal (2⁻¹ * (Λ i - 1 - Real.log (Λ i))) := by
    intro i
    rw [klDiv_gaussianReal_zero (Λ i).toNNReal (Real.toNNReal_pos.mpr (hΛpos i)).ne',
      Real.coe_toNNReal _ (hΛnonneg i)]
  have hsumΛ : ∑ i, Λ i = (B⁻¹ * A).trace := by
    rw [← htraceC, hC.1.trace_eq_sum_eigenvalues]
    simp only [hΛ_def, RCLike.ofReal_real_eq_id, id_eq]
  have hsumlog : ∑ i, Real.log (Λ i) = Real.log A.det - Real.log B.det := by
    rw [← hlogdetC, hC.1.det_eq_prod_eigenvalues]
    simp only [hΛ_def, RCLike.ofReal_real_eq_id, id_eq]
    rw [Real.log_prod (fun i _ => (hΛpos i).ne')]
  rw [hwhiten, hdiagonalize, htensor, Finset.sum_congr rfl (fun i _ => hterm i),
    ← ENNReal.ofReal_sum_of_nonneg (fun i _ =>
      mul_nonneg (by norm_num) (by linarith [Real.log_le_sub_one_of_pos (hΛpos i)]))]
  congr 1
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, hsumΛ, hsumlog]
  ring

end Hurst
