import Hurst.GaussianPairLaw

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal RealInnerProductSpace
namespace Hurst

def centeredGaussianLog (x : ℝ) : ℝ := Real.log (x ^ 2) - gaussianLogSquareMean

def gaussianLogSquareVariance : ℝ := ∫ x, (centeredGaussianLog x) ^ 2 ∂gaussianReal 0 1

theorem centeredGaussianLog_measurable : Measurable centeredGaussianLog := by
  unfold centeredGaussianLog
  fun_prop

theorem centeredGaussianLog_memLp_two : MemLp centeredGaussianLog 2 (gaussianReal 0 1) :=
  (log_square_memLp_two_gaussianReal 1 one_ne_zero).sub (memLp_const _)

theorem centeredGaussianLog_mean : (∫ x, centeredGaussianLog x ∂gaussianReal 0 1) = 0 := by
  unfold centeredGaussianLog
  rw [integral_sub ((log_square_memLp_two_gaussianReal 1 one_ne_zero).integrable (by norm_num)) (integrable_const _),
    integral_const]
  simp [gaussianLogSquareMean]

theorem centeredGaussianLog_even (x : ℝ) : centeredGaussianLog (-x) = centeredGaussianLog x := by
  simp [centeredGaussianLog]

theorem gaussianLogSquareVariance_nonneg : 0 ≤ gaussianLogSquareVariance :=
  integral_nonneg (fun x => sq_nonneg (centeredGaussianLog x))

/-- The actual log-square covariance is bounded by a constant times squared Gaussian correlation. -/
theorem gaussian_log_square_covariance_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ) (hXm : Measurable X) (hYm : Measurable Y)
    (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P)
    (hX0 : (∫ ω, X ω ∂P) = 0) (hY0 : (∫ ω, Y ω ∂P) = 0)
    (hX1 : Var[X; P] = 1) (hY1 : Var[Y; P] = 1) :
    |cov[fun ω => Real.log ((X ω) ^ 2), fun ω => Real.log ((Y ω) ^ 2); P]| ≤
      4 * gaussianLogSquareVariance * (cov[X, Y; P]) ^ 2 := by
  have h := gaussian_even_covariance_bound P X Y hXm hYm hXY hX0 hY0 hX1 hY1
    centeredGaussianLog centeredGaussianLog centeredGaussianLog_measurable centeredGaussianLog_measurable
    centeredGaussianLog_memLp_two centeredGaussianLog_memLp_two centeredGaussianLog_mean centeredGaussianLog_mean
    centeredGaussianLog_even
  have hXmap : P.map X = gaussianReal 0 1 := by
    rw [hXY.fst.map_eq_gaussianReal, hX0, hX1]
    norm_num
  have hYmap : P.map Y = gaussianReal 0 1 := by
    rw [hXY.snd.map_eq_gaussianReal, hY0, hY1]
    norm_num
  have hmpX : MeasurePreserving X P (gaussianReal 0 1) := ⟨hXm, hXmap⟩
  have hmpY : MeasurePreserving Y P (gaussianReal 0 1) := ⟨hYm, hYmap⟩
  have hLX : Integrable (fun ω => Real.log ((X ω) ^ 2)) P :=
    ((log_square_memLp_two_gaussianReal 1 one_ne_zero).comp_measurePreserving hmpX).integrable (by norm_num)
  have hLY : Integrable (fun ω => Real.log ((Y ω) ^ 2)) P :=
    ((log_square_memLp_two_gaussianReal 1 one_ne_zero).comp_measurePreserving hmpY).integrable (by norm_num)
  simp only [centeredGaussianLog] at h
  rw [covariance_sub_const_left hLX, covariance_sub_const_right hLY] at h
  change _ ≤ 4 * (cov[X, Y; P]) ^ 2 * Real.sqrt gaussianLogSquareVariance * Real.sqrt gaussianLogSquareVariance at h
  calc
    _ ≤ _ := h
    _ = _ := by
      rw [mul_assoc, ← pow_two, Real.sq_sqrt gaussianLogSquareVariance_nonneg]
      ring

theorem covariance_congr_ae {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X Y X' Y' : Ω → ℝ) (hX : X =ᵐ[P] X') (hY : Y =ᵐ[P] Y') : cov[X, Y; P] = cov[X', Y'; P] := by
  unfold covariance
  rw [integral_congr_ae hX, integral_congr_ae hY]
  apply integral_congr_ae
  filter_upwards [hX, hY] with ω hx hy
  rw [hx, hy]

theorem standard_gaussian_log_inputs {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hXm : Measurable X) (hmap : P.map X = gaussianReal 0 1) :
    Integrable (fun ω => Real.log ((X ω) ^ 2)) P ∧ (∀ᵐ ω ∂P, X ω ≠ 0) := by
  have hmp : MeasurePreserving X P (gaussianReal 0 1) := ⟨hXm, hmap⟩
  refine ⟨((log_square_memLp_two_gaussianReal 1 one_ne_zero).comp_measurePreserving hmp).integrable (by norm_num), ?_⟩
  letI := noAtoms_gaussianReal (μ := 0) (v := 1) one_ne_zero
  have hz : ∀ᵐ x ∂gaussianReal 0 1, x ≠ 0 := (gaussianReal 0 1).ae_ne 0
  rw [← hmap] at hz
  exact (ae_map_iff hXm.aemeasurable (measurableSet_singleton (0 : ℝ)).compl).mp hz

/-- Scale-invariant log covariance for any nondegenerate centered jointly Gaussian pair. -/
theorem gaussian_log_square_covariance_bound_general {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ) (hXm : Measurable X) (hYm : Measurable Y)
    (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P)
    (hX0 : (∫ ω, X ω ∂P) = 0) (hY0 : (∫ ω, Y ω ∂P) = 0)
    (hXv : 0 < Var[X; P]) (hYv : 0 < Var[Y; P]) :
    |cov[fun ω => Real.log ((X ω) ^ 2), fun ω => Real.log ((Y ω) ^ 2); P]| ≤
      4 * gaussianLogSquareVariance * ((cov[X, Y; P]) ^ 2 / (Var[X; P] * Var[Y; P])) := by
  let sx := Real.sqrt (Var[X; P])
  let sy := Real.sqrt (Var[Y; P])
  have hsx : sx ≠ 0 := (Real.sqrt_pos.mpr hXv).ne'
  have hsy : sy ≠ 0 := (Real.sqrt_pos.mpr hYv).ne'
  have hsx2 : sx ^ 2 = Var[X; P] := Real.sq_sqrt hXv.le
  have hsy2 : sy ^ 2 = Var[Y; P] := Real.sq_sqrt hYv.le
  let X' : Ω → ℝ := fun ω => X ω / sx
  let Y' : Ω → ℝ := fun ω => Y ω / sy
  have hmX : Measurable X' := hXm.div_const sx
  have hmY : Measurable Y' := hYm.div_const sy
  let L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
    (sx⁻¹ • ContinuousLinearMap.fst ℝ ℝ ℝ).prod (sy⁻¹ • ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hpair : HasGaussianLaw (fun ω => (X' ω, Y' ω)) P := by
    convert! hXY.map_fun L using 1
    funext ω
    apply Prod.ext <;> simp [X', Y', L, div_eq_mul_inv, mul_comm]
  have hX'0 : (∫ ω, X' ω ∂P) = 0 := by dsimp [X']; rw [integral_div, hX0, zero_div]
  have hY'0 : (∫ ω, Y' ω ∂P) = 0 := by dsimp [Y']; rw [integral_div, hY0, zero_div]
  have hX'1 : Var[X'; P] = 1 := by
    dsimp [X']
    simp only [div_eq_mul_inv]
    rw [variance_mul_const, inv_pow, hsx2, mul_inv_cancel₀ hXv.ne']
  have hY'1 : Var[Y'; P] = 1 := by
    dsimp [Y']
    simp only [div_eq_mul_inv]
    rw [variance_mul_const, inv_pow, hsy2, mul_inv_cancel₀ hYv.ne']
  have hXmap : P.map X' = gaussianReal 0 1 := by rw [hpair.fst.map_eq_gaussianReal, hX'0, hX'1]; norm_num
  have hYmap : P.map Y' = gaussianReal 0 1 := by rw [hpair.snd.map_eq_gaussianReal, hY'0, hY'1]; norm_num
  obtain ⟨hLX, hXne⟩ := standard_gaussian_log_inputs P X' hmX hXmap
  obtain ⟨hLY, hYne⟩ := standard_gaussian_log_inputs P Y' hmY hYmap
  have hAX : (fun ω => Real.log ((X ω) ^ 2)) =ᵐ[P] (fun ω => Real.log (sx ^ 2) + Real.log ((X' ω) ^ 2)) := by
    filter_upwards [hXne] with ω hω
    have he : sx * X' ω = X ω := by dsimp [X']; field_simp
    rw [← he, log_square_scale sx (X' ω) hsx hω]
  have hAY : (fun ω => Real.log ((Y ω) ^ 2)) =ᵐ[P] (fun ω => Real.log (sy ^ 2) + Real.log ((Y' ω) ^ 2)) := by
    filter_upwards [hYne] with ω hω
    have he : sy * Y' ω = Y ω := by dsimp [Y']; field_simp
    rw [← he, log_square_scale sy (Y' ω) hsy hω]
  have hc : cov[fun ω => Real.log ((X ω) ^ 2), fun ω => Real.log ((Y ω) ^ 2); P] =
      cov[fun ω => Real.log ((X' ω) ^ 2), fun ω => Real.log ((Y' ω) ^ 2); P] := by
    rw [covariance_congr_ae P _ _ _ _ hAX hAY, covariance_const_add_left hLX, covariance_const_add_right hLY]
  have hcorr : (cov[X', Y'; P]) ^ 2 = (cov[X, Y; P]) ^ 2 / (Var[X; P] * Var[Y; P]) := by
    dsimp [X', Y']
    simp only [div_eq_mul_inv]
    rw [covariance_mul_const_left, covariance_mul_const_right, mul_pow, mul_pow, inv_pow, inv_pow, hsx2, hsy2]
    ring
  rw [hc]
  have h := gaussian_log_square_covariance_bound P X' Y' hmX hmY hpair hX'0 hY'0 hX'1 hY'1
  rwa [hcorr] at h

end Hurst
