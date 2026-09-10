import Hurst.GaussianLogResidual
import Hurst.HermiteRankBound

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace Hurst

def gaussianLogHermiteCoefficient (n : ℕ) : ℝ := ⟪gaussianHermiteUnit n,gaussianLogLp⟫

theorem gaussian_log_covariance_series {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ)
    (hXY : HasGaussianLaw (fun ω => (X ω,Y ω)) P)
    (hX : MeasurePreserving X P (gaussianReal 0 1))
    (hY : MeasurePreserving Y P (gaussianReal 0 1)) :
    HasSum (fun n => gaussianLogHermiteCoefficient n^2*cov[X,Y;P]^n)
      (cov[centeredGaussianLog ∘ X,centeredGaussianLog ∘ Y;P]) := by
  have hXlaw : HasLaw X (gaussianReal 0 1) P := ⟨hX.measurable.aemeasurable,hX.map_eq⟩
  have hYlaw : HasLaw Y (gaussianReal 0 1) P := ⟨hY.measurable.aemeasurable,hY.map_eq⟩
  have hx0 : (∫ ω,(centeredGaussianLog ∘ X) ω ∂P)=0 := by
    rw [hXlaw.integral_comp centeredGaussianLog_memLp_two.1,centeredGaussianLog_mean]
  have hy0 : (∫ ω,(centeredGaussianLog ∘ Y) ω ∂P)=0 := by
    rw [hYlaw.integral_comp centeredGaussianLog_memLp_two.1,centeredGaussianLog_mean]
  have hs := jointGaussian_hermite_covariance_expansion P X Y hXY hX hY gaussianLogLp gaussianLogLp
  have he : (∫ ω,gaussianLogLp (X ω)*gaussianLogLp (Y ω) ∂P) =
      ∫ ω,centeredGaussianLog (X ω)*centeredGaussianLog (Y ω) ∂P := by
    apply integral_congr_ae
    filter_upwards [hX.quasiMeasurePreserving.ae gaussianLogLp_ae,
      hY.quasiMeasurePreserving.ae gaussianLogLp_ae] with ω hx hy
    rw [hx,hy]
  rw [he] at hs
  rw [covariance_eq_sub (centeredGaussianLog_memLp_two.comp_measurePreserving hX)
    (centeredGaussianLog_memLp_two.comp_measurePreserving hY),hx0,hy0,mul_zero,sub_zero]
  convert hs using 1 <;> first | rfl | (funext n; unfold gaussianLogHermiteCoefficient; ring)

theorem gaussianLog_series_term_nonneg (ρ : ℝ) (n : ℕ) :
    0≤gaussianLogHermiteCoefficient n^2*ρ^n := by
  rcases Nat.even_or_odd n with hn|hn
  · exact mul_nonneg (sq_nonneg _) (hn.pow_nonneg ρ)
  · rw [gaussianLogHermiteCoefficient,gaussianLog_hermite_coefficient_odd n hn]
    simp

theorem gaussian_log_covariance_ge_quadratic {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ)
    (hXY : HasGaussianLaw (fun ω => (X ω,Y ω)) P)
    (hX : MeasurePreserving X P (gaussianReal 0 1))
    (hY : MeasurePreserving Y P (gaussianReal 0 1)) :
    2*cov[X,Y;P]^2 ≤ cov[centeredGaussianLog ∘ X,centeredGaussianLog ∘ Y;P] := by
  have hs := gaussian_log_covariance_series P X Y hXY hX hY
  have he : HasSum (fun n : ℕ => if n=2 then 2*cov[X,Y;P]^2 else 0) (2*cov[X,Y;P]^2) :=
    hasSum_ite_eq 2 _
  apply hasSum_le _ he hs
  intro n
  split_ifs with hn
  · subst n
    simp only [gaussianLogHermiteCoefficient,gaussianLog_hermite_coefficient_two,
      Real.sq_sqrt (show (0:ℝ)≤2 by norm_num),le_refl]
  · exact gaussianLog_series_term_nonneg _ n

theorem gaussian_log_covariance_sharp_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ)
    (hXY : HasGaussianLaw (fun ω => (X ω,Y ω)) P)
    (hX : MeasurePreserving X P (gaussianReal 0 1))
    (hY : MeasurePreserving Y P (gaussianReal 0 1)) :
    |cov[centeredGaussianLog ∘ X,centeredGaussianLog ∘ Y;P]| ≤
      gaussianLogSquareVariance*cov[X,Y;P]^2 := by
  have hXlaw : HasLaw X (gaussianReal 0 1) P := ⟨hX.measurable.aemeasurable,hX.map_eq⟩
  have hYlaw : HasLaw Y (gaussianReal 0 1) P := ⟨hY.measurable.aemeasurable,hY.map_eq⟩
  have hvX : Var[X;P]=1 := by rw [hXlaw.variance_eq,variance_id_gaussianReal]; norm_num
  have hvY : Var[Y;P]=1 := by rw [hYlaw.variance_eq,variance_id_gaussianReal]; norm_num
  have hρ := standard_covariance_abs_le_one P X Y hXY.fst.memLp_two hXY.snd.memLp_two hvX hvY
  have hs := gaussian_log_covariance_series P X Y hXY hX hY
  have hb := gaussianLog_hermite_parseval.mul_left (|cov[X,Y;P]|^2)
  have hc := gaussian_log_covariance_ge_quadratic P X Y hXY hX hY
  rw [abs_of_nonneg (by nlinarith [sq_nonneg (cov[X,Y;P])])]
  have he : cov[centeredGaussianLog ∘ X,centeredGaussianLog ∘ Y;P] ≤
      |cov[X,Y;P]|^2*gaussianLogSquareVariance := by
    apply hasSum_le _ hs hb
    intro n
    have ht := (abs_le.mp (hermite_rank_coefficient_bound _ hρ gaussianLogLp 2
      gaussianLog_hermite_rank_at_least_two n)).2
    simpa only [gaussianLogHermiteCoefficient,pow_two,mul_assoc,mul_comm,mul_left_comm] using ht
  simpa only [sq_abs,mul_comm] using he

end Hurst
