import Hurst.GaussianRotation
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal RealInnerProductSpace
namespace Hurst

def diagonalRotationCLM : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (Real.sqrt 2)⁻¹ •
    ((ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ).prod
      (ContinuousLinearMap.fst ℝ ℝ ℝ - ContinuousLinearMap.snd ℝ ℝ ℝ))

theorem diagonalRotationCLM_apply (z : ℝ × ℝ) : diagonalRotationCLM z = diagonalRotation z := by
  apply Prod.ext <;> simp [diagonalRotationCLM, diagonalRotation] <;> ring

theorem gaussian_standard_pair_law {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ)
    (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P)
    (hX0 : (∫ ω, X ω ∂P) = 0) (hY0 : (∫ ω, Y ω ∂P) = 0)
    (hX1 : Var[X; P] = 1) (hY1 : Var[Y; P] = 1) :
    P.map (fun ω => (X ω, Y ω)) = correlatedGaussianPair (cov[X, Y; P]) := by
  let U : Ω → ℝ := fun ω => (X ω + Y ω) / Real.sqrt 2
  let V : Ω → ℝ := fun ω => (X ω - Y ω) / Real.sqrt 2
  have hUV : HasGaussianLaw (fun ω => (U ω, V ω)) P := by
    convert! hXY.map_fun diagonalRotationCLM using 1
    funext ω
    rw [diagonalRotationCLM_apply]
    rfl
  have hX := hXY.fst.memLp_two
  have hY := hXY.snd.memLp_two
  have hXi := hX.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hYi := hY.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hU0 : (∫ ω, U ω ∂P) = 0 := by
    rw [show U = fun ω => (X ω + Y ω) / Real.sqrt 2 from rfl, integral_div,
      integral_add hXi hYi, hX0, hY0]
    simp
  have hV0 : (∫ ω, V ω ∂P) = 0 := by
    rw [show V = fun ω => (X ω - Y ω) / Real.sqrt 2 from rfl, integral_div,
      integral_sub hXi hYi, hX0, hY0]
    simp
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hU1 : Var[U; P] = 1 + cov[X, Y; P] := by
    dsimp [U]
    simp only [div_eq_mul_inv]
    rw [variance_mul_const, variance_fun_add hX hY, hX1, hY1, inv_pow, hs]
    ring
  have hV1 : Var[V; P] = 1 - cov[X, Y; P] := by
    dsimp [V]
    simp only [div_eq_mul_inv]
    rw [variance_mul_const, variance_fun_sub hX hY, hX1, hY1, inv_pow, hs]
    ring
  have hcov : cov[U, V; P] = 0 := by
    dsimp [U, V]
    simp only [div_eq_mul_inv]
    rw [covariance_mul_const_left, covariance_mul_const_right]
    change cov[X + Y, X - Y; P] * (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 0
    rw [covariance_sub_right (hX.add hY) hX hY,
      covariance_add_left hX hY hX, covariance_add_left hX hY hY,
      covariance_self hXY.fst.aemeasurable, covariance_self hXY.snd.aemeasurable,
      covariance_comm Y X, hX1, hY1]
    ring
  have hind := hUV.indepFun_of_covariance_eq_zero hcov
  have hmap := hind.map_prod_eq_prod_map_map hUV.fst.aemeasurable hUV.snd.aemeasurable
  rw [hUV.fst.map_eq_gaussianReal, hUV.snd.map_eq_gaussianReal, hU0, hV0, hU1, hV1] at hmap
  have heq := congrArg (fun μ : Measure (ℝ × ℝ) => μ.map diagonalRotation) hmap
  rw [AEMeasurable.map_map_of_aemeasurable (by exact diagonalRotationEquiv.measurable.aemeasurable) hUV.aemeasurable] at heq
  change P.map (fun ω => diagonalRotation (U ω, V ω)) = correlatedGaussianPair (cov[X, Y; P]) at heq
  have he : (fun ω => diagonalRotation (U ω, V ω)) = (fun ω => (X ω, Y ω)) := by
    funext ω
    exact diagonalRotation_involutive (X ω, Y ω)
  rwa [he] at heq

/-- Even centered Gaussian transforms have a uniform rank-two covariance bound. -/
theorem gaussian_even_covariance_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ) (hXm : Measurable X) (hYm : Measurable Y)
    (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P)
    (hX0 : (∫ ω, X ω ∂P) = 0) (hY0 : (∫ ω, Y ω ∂P) = 0)
    (hX1 : Var[X; P] = 1) (hY1 : Var[Y; P] = 1)
    (f g : ℝ → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hf2 : MemLp f 2 (gaussianReal 0 1)) (hg2 : MemLp g 2 (gaussianReal 0 1))
    (hf0 : (∫ x, f x ∂gaussianReal 0 1) = 0) (hg0 : (∫ x, g x ∂gaussianReal 0 1) = 0)
    (hgeven : ∀ x, g (-x) = g x) :
    |cov[fun ω => f (X ω), fun ω => g (Y ω); P]| ≤
      4 * (cov[X, Y; P]) ^ 2 * Real.sqrt (∫ x, (f x) ^ 2 ∂gaussianReal 0 1) *
        Real.sqrt (∫ x, (g x) ^ 2 ∂gaussianReal 0 1) := by
  have hXmap : P.map X = gaussianReal 0 1 := by
    rw [hXY.fst.map_eq_gaussianReal, hX0, hX1]
    norm_num
  have hYmap : P.map Y = gaussianReal 0 1 := by
    rw [hXY.snd.map_eq_gaussianReal, hY0, hY1]
    norm_num
  have hmpX : MeasurePreserving X P (gaussianReal 0 1) := ⟨hXm, hXmap⟩
  have hmpY : MeasurePreserving Y P (gaussianReal 0 1) := ⟨hYm, hYmap⟩
  have hF : MemLp (fun ω => f (X ω)) 2 P := hf2.comp_measurePreserving hmpX
  have hG : MemLp (fun ω => g (Y ω)) 2 P := hg2.comp_measurePreserving hmpY
  have hF0 : (∫ ω, f (X ω) ∂P) = 0 := by
    rw [← integral_map hXm.aemeasurable hf.aestronglyMeasurable, hXmap, hf0]
  have hG0 : (∫ ω, g (Y ω) ∂P) = 0 := by
    rw [← integral_map hYm.aemeasurable hg.aestronglyMeasurable, hYmap, hg0]
  have hFsq : (∫ ω, (f (X ω)) ^ 2 ∂P) = ∫ x, (f x) ^ 2 ∂gaussianReal 0 1 := by
    rw [← integral_map hXm.aemeasurable (hf.pow_const 2).aestronglyMeasurable, hXmap]
  have hGsq : (∫ ω, (g (Y ω)) ^ 2 ∂P) = ∫ x, (g x) ^ 2 ∂gaussianReal 0 1 := by
    rw [← integral_map hYm.aemeasurable (hg.pow_const 2).aestronglyMeasurable, hYmap]
  have hCov : cov[fun ω => f (X ω), fun ω => g (Y ω); P] = ∫ ω, f (X ω) * g (Y ω) ∂P := by
    simp only [covariance, hF0, hG0, sub_zero]
  rw [hCov]
  by_cases hsmall : |cov[X, Y; P]| ≤ 1 / 2
  · have hpair := gaussian_standard_pair_law P X Y hXY hX0 hY0 hX1 hY1
    have hInt : (∫ ω, f (X ω) * g (Y ω) ∂P) =
        ∫ z, f z.1 * g z.2 ∂correlatedGaussianPair (cov[X, Y; P]) := by
      rw [← hpair, integral_map (hXm.prodMk hYm).aemeasurable
        (show Measurable (fun z : ℝ × ℝ => f z.1 * g z.2) by fun_prop).aestronglyMeasurable]
    rw [hInt]
    apply (correlatedGaussianPair_even_integral_bound _ hsmall f g hf hg hf2 hg2 hf0 hg0 hgeven).trans
    gcongr
    norm_num
  · have hρ : 1 ≤ 4 * (cov[X, Y; P]) ^ 2 := by
      have hh : (1 / 2 : ℝ) < |cov[X, Y; P]| := lt_of_not_ge hsmall
      nlinarith [sq_abs (cov[X, Y; P]), sq_nonneg (|cov[X, Y; P]| - 1 / 2)]
    have hCS := abs_integral_mul_le_sqrt_integrals P (fun ω => f (X ω)) (fun ω => g (Y ω)) hF hG
    rw [hFsq, hGsq] at hCS
    calc
      _ ≤ Real.sqrt (∫ x, (f x) ^ 2 ∂gaussianReal 0 1) * Real.sqrt (∫ x, (g x) ^ 2 ∂gaussianReal 0 1) := hCS
      _ ≤ (4 * (cov[X, Y; P]) ^ 2) *
          (Real.sqrt (∫ x, (f x) ^ 2 ∂gaussianReal 0 1) * Real.sqrt (∫ x, (g x) ^ 2 ∂gaussianReal 0 1)) := by
        exact le_mul_of_one_le_left (by positivity) hρ
      _ = _ := by ring

end Hurst
