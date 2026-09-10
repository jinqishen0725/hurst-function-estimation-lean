import Hurst.GaussianLogResidual
import Hurst.HermiteRankBound

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace Hurst

theorem gaussianLogResidual_memLp_two : MemLp gaussianLogResidual 2 (gaussianReal 0 1) := by
  exact (Lp.memLp gaussianLogResidualLp).ae_eq gaussianLogResidualLp_ae

theorem gaussianLogResidual_mean : (∫ x,gaussianLogResidual x ∂gaussianReal 0 1)=0 := by
  have hh := standardGaussian_polynomial_memLp_two (gaussianHermite 2)
  have he : gaussianLogResidual = fun x => centeredGaussianLog x-(gaussianHermite 2).eval x := by
    funext x
    simp [gaussianLogResidual,gaussianHermite_two]
  rw [he,integral_sub (centeredGaussianLog_memLp_two.integrable (by norm_num))
    (hh.integrable (by norm_num)),centeredGaussianLog_mean,
    show (∫ x,(gaussianHermite 2).eval x ∂gaussianReal 0 1)=0 from standardGaussian_hermite_mean_succ 1,
    sub_self]

theorem gaussianLogResidual_even (x : ℝ) : gaussianLogResidual (-x)=gaussianLogResidual x := by
  simp only [gaussianLogResidual,centeredGaussianLog_even,neg_sq]

theorem gaussian_log_residual_covariance_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ)
    (hXY : HasGaussianLaw (fun ω => (X ω,Y ω)) P)
    (hX : MeasurePreserving X P (gaussianReal 0 1))
    (hY : MeasurePreserving Y P (gaussianReal 0 1)) :
    |cov[gaussianLogResidual ∘ X,gaussianLogResidual ∘ Y;P]| ≤
      (gaussianLogSquareVariance-2)*cov[X,Y;P]^4 := by
  have hXlaw : HasLaw X (gaussianReal 0 1) P := ⟨hX.measurable.aemeasurable,hX.map_eq⟩
  have hYlaw : HasLaw Y (gaussianReal 0 1) P := ⟨hY.measurable.aemeasurable,hY.map_eq⟩
  have hx0 : (∫ ω,(gaussianLogResidual ∘ X) ω ∂P)=0 := by
    rw [hXlaw.integral_comp gaussianLogResidual_memLp_two.1,gaussianLogResidual_mean]
  have hy0 : (∫ ω,(gaussianLogResidual ∘ Y) ω ∂P)=0 := by
    rw [hYlaw.integral_comp gaussianLogResidual_memLp_two.1,gaussianLogResidual_mean]
  have hb := jointGaussian_hermite_rank_bound P X Y hXY hX hY gaussianLogResidualLp 4 gaussianLogResidual_rank_four
  have he : (∫ ω,gaussianLogResidualLp (X ω)*gaussianLogResidualLp (Y ω) ∂P) =
      ∫ ω,gaussianLogResidual (X ω)*gaussianLogResidual (Y ω) ∂P := by
    apply integral_congr_ae
    filter_upwards [hX.quasiMeasurePreserving.ae gaussianLogResidualLp_ae,
      hY.quasiMeasurePreserving.ae gaussianLogResidualLp_ae] with ω hx hy
    rw [hx,hy]
  rw [he,gaussianLogResidual_norm_sq] at hb
  rw [covariance_eq_sub (gaussianLogResidual_memLp_two.comp_measurePreserving hX)
    (gaussianLogResidual_memLp_two.comp_measurePreserving hY),hx0,hy0,mul_zero,sub_zero]
  simpa only [(show Even (4:ℕ) from by decide).pow_abs,Function.comp_apply,Pi.mul_apply,mul_comm] using hb

end Hurst
