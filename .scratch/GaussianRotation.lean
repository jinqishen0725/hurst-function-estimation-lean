import Hurst.GaussianSymmetry
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.InnerProductSpace.ProdL2

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal RealInnerProductSpace
namespace Hurst

def diagonalRotation (z : ℝ × ℝ) : ℝ × ℝ :=
  ((z.1 + z.2) / Real.sqrt 2, (z.1 - z.2) / Real.sqrt 2)

theorem diagonalRotation_involutive : Function.Involutive diagonalRotation := by
  intro z
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Prod.ext <;> dsimp [diagonalRotation] <;> field_simp <;> rw [hs] <;> ring

def diagonalRotationEquiv : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) where
  toFun := diagonalRotation
  invFun := diagonalRotation
  left_inv := diagonalRotation_involutive
  right_inv := diagonalRotation_involutive
  measurable_toFun := by change Measurable diagonalRotation; unfold diagonalRotation; fun_prop
  measurable_invFun := by change Measurable diagonalRotation; unfold diagonalRotation; fun_prop

def gaussianRotationIsometry : WithLp 2 (ℝ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℝ × ℝ) where
  toFun x := WithLp.toLp 2 (diagonalRotation (WithLp.ofLp x))
  invFun x := WithLp.toLp 2 (diagonalRotation (WithLp.ofLp x))
  left_inv x := by change WithLp.toLp 2 (diagonalRotation (diagonalRotation (WithLp.ofLp x))) = x; rw [diagonalRotation_involutive (WithLp.ofLp x)]
  right_inv x := by change WithLp.toLp 2 (diagonalRotation (diagonalRotation (WithLp.ofLp x))) = x; rw [diagonalRotation_involutive (WithLp.ofLp x)]
  map_add' x y := by
    apply WithLp.ofLp_injective
    apply Prod.ext <;> simp [diagonalRotation] <;> ring
  map_smul' c x := by
    apply WithLp.ofLp_injective
    apply Prod.ext <;> simp [diagonalRotation] <;> ring
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
    simp only [WithLp.fst, WithLp.snd, diagonalRotation, Real.norm_eq_abs, sq_abs]
    change ((x.ofLp.1 + x.ofLp.2) / Real.sqrt 2) ^ 2 + ((x.ofLp.1 - x.ofLp.2) / Real.sqrt 2) ^ 2 = x.ofLp.1 ^ 2 + x.ofLp.2 ^ 2
    have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    rw [div_pow, div_pow, hs]
    ring

theorem gaussianProduct2_map_standard :
    gaussianProduct2.map (WithLp.toLp 2) = stdGaussian (WithLp 2 (ℝ × ℝ)) := by
  apply Measure.ext_of_charFun
  ext t
  rw [gaussianProduct2, charFun_prod, charFun_gaussianReal, charFun_gaussianReal,
    charFun_stdGaussian]
  simp only [← Complex.ofReal_pow]
  rw [WithLp.prod_norm_sq_eq_of_L2, ← Complex.exp_add]
  congr 1
  simp only [NNReal.coe_one, Complex.ofReal_one, Complex.ofReal_zero, mul_zero, zero_mul, zero_sub,
    Real.norm_eq_abs, sq_abs, WithLp.fst, WithLp.snd]
  push_cast
  ring

theorem diagonalRotation_measurePreserving : MeasurePreserving diagonalRotation gaussianProduct2 gaussianProduct2 := by
  refine ⟨by unfold diagonalRotation; fun_prop, ?_⟩
  apply (MeasurableEquiv.toLp 2 (ℝ × ℝ)).measurableEmbedding.map_injective
  change (gaussianProduct2.map diagonalRotation).map (WithLp.toLp 2) = gaussianProduct2.map (WithLp.toLp 2)
  have hs := stdGaussian_map gaussianRotationIsometry
  rw [← gaussianProduct2_map_standard] at hs
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at hs
  rw [Measure.map_map (by fun_prop) (by unfold diagonalRotation; fun_prop)]
  exact hs

theorem diagonalGaussianRatio_withDensity (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    gaussianProduct2.withDensity (fun z => ENNReal.ofReal (diagonalGaussianRatio a b z)) =
      (gaussianReal 0 ⟨a, ha.le⟩).prod (gaussianReal 0 ⟨b, hb.le⟩) := by
  rw [← gaussianVarianceRatio_withDensity a ha, ← gaussianVarianceRatio_withDensity b hb,
    prod_withDensity (by unfold gaussianVarianceRatio; fun_prop) (by unfold gaussianVarianceRatio; fun_prop)]
  apply congrArg (Measure.withDensity gaussianProduct2)
  funext z
  exact ENNReal.ofReal_mul (gaussianVarianceRatio_pos a z.1 ha).le

theorem diagonalGaussianRatio_integral_reweight (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (A : ℝ × ℝ → ℝ) :
    (∫ z, A z ∂(gaussianReal 0 ⟨a, ha.le⟩).prod (gaussianReal 0 ⟨b, hb.le⟩)) =
      ∫ z, A z * diagonalGaussianRatio a b z ∂gaussianProduct2 := by
  rw [← diagonalGaussianRatio_withDensity a b ha hb,
    integral_withDensity_eq_integral_toReal_smul (by unfold diagonalGaussianRatio gaussianVarianceRatio; fun_prop)
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [] with z
  have hp : 0 ≤ diagonalGaussianRatio a b z := mul_nonneg (gaussianVarianceRatio_pos a z.1 ha).le
    (gaussianVarianceRatio_pos b z.2 hb).le
  rw [ENNReal.toReal_ofReal hp, smul_eq_mul, mul_comm]

theorem gaussianProduct2_product_memLp (f g : ℝ → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hf2 : MemLp f 2 (gaussianReal 0 1)) (hg2 : MemLp g 2 (gaussianReal 0 1)) :
    MemLp (fun z : ℝ × ℝ => f z.1 * g z.2) 2 gaussianProduct2 := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  have hfi := (memLp_two_iff_integrable_sq hf2.aestronglyMeasurable).mp hf2
  have hgi := (memLp_two_iff_integrable_sq hg2.aestronglyMeasurable).mp hg2
  simpa only [mul_pow, gaussianProduct2] using! hfi.mul_prod hgi

def correlatedGaussianPair (ρ : ℝ) : Measure (ℝ × ℝ) :=
  ((gaussianReal 0 (1 + ρ).toNNReal).prod (gaussianReal 0 (1 - ρ).toNNReal)).map diagonalRotation

theorem correlatedGaussianPair_even_integral_bound (ρ : ℝ) (hρ : |ρ| ≤ 1 / 2)
    (f g : ℝ → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hf2 : MemLp f 2 (gaussianReal 0 1)) (hg2 : MemLp g 2 (gaussianReal 0 1))
    (hf0 : (∫ x, f x ∂gaussianReal 0 1) = 0) (hg0 : (∫ x, g x ∂gaussianReal 0 1) = 0)
    (hgeven : ∀ x, g (-x) = g x) :
    |∫ z, f z.1 * g z.2 ∂correlatedGaussianPair ρ| ≤
      2 * ρ ^ 2 * Real.sqrt (∫ x, (f x) ^ 2 ∂gaussianReal 0 1) *
        Real.sqrt (∫ x, (g x) ^ 2 ∂gaussianReal 0 1) := by
  let F : ℝ × ℝ → ℝ := fun z => f z.1 * g z.2
  let A : ℝ × ℝ → ℝ := F ∘ diagonalRotation
  have hF := gaussianProduct2_product_memLp f g hf hg hf2 hg2
  have hA : MemLp A 2 gaussianProduct2 := hF.comp_measurePreserving diagonalRotation_measurePreserving
  have hAsym : ∀ z, A z.swap = A z := by
    intro z
    dsimp [A, F, diagonalRotation]
    rw [add_comm z.2 z.1, show (z.2 - z.1) / Real.sqrt 2 = -((z.1 - z.2) / Real.sqrt 2) by ring, hgeven]
  have hA0 : (∫ z, A z ∂gaussianProduct2) = 0 := by
    dsimp only [A, Function.comp_apply]
    rw [diagonalRotation_measurePreserving.integral_comp diagonalRotationEquiv.measurableEmbedding F]
    change (∫ z, f z.1 * g z.2 ∂(gaussianReal 0 1).prod (gaussianReal 0 1)) = 0
    rw [integral_prod_mul f g, hf0, hg0, mul_zero]
  have hA2 : (∫ z, (A z) ^ 2 ∂gaussianProduct2) =
      (∫ x, (f x) ^ 2 ∂gaussianReal 0 1) * (∫ x, (g x) ^ 2 ∂gaussianReal 0 1) := by
    dsimp only [A, Function.comp_apply]
    rw [diagonalRotation_measurePreserving.integral_comp diagonalRotationEquiv.measurableEmbedding (fun z => (F z) ^ 2)]
    simp only [F, mul_pow, gaussianProduct2]
    exact integral_prod_mul (fun x => (f x) ^ 2) (fun x => (g x) ^ 2)
  have hbound := symmetric_test_reweighting_bound ρ hρ A hA hAsym
  rw [hA0, sub_zero, hA2, Real.sqrt_mul (integral_nonneg (fun x => sq_nonneg (f x)))] at hbound
  have ha : 0 < 1 + ρ := by linarith [(abs_le.mp hρ).1]
  have hb : 0 < 1 - ρ := by linarith [(abs_le.mp hρ).2]
  have hae : (1 + ρ).toNNReal = (⟨1 + ρ, ha.le⟩ : ℝ≥0) := by ext; exact Real.coe_toNNReal _ ha.le
  have hbe : (1 - ρ).toNNReal = (⟨1 - ρ, hb.le⟩ : ℝ≥0) := by ext; exact Real.coe_toNNReal _ hb.le
  have he : (∫ z, f z.1 * g z.2 ∂correlatedGaussianPair ρ) =
      ∫ z, A z * correlationDiagonalRatio ρ z ∂gaussianProduct2 := by
    unfold correlatedGaussianPair
    change (∫ z, F z ∂Measure.map diagonalRotationEquiv _) = _
    rw [integral_map_equiv, hae, hbe, diagonalGaussianRatio_integral_reweight _ _ ha hb]
    rfl
  rw [he]
  simpa only [mul_assoc] using hbound

end Hurst
