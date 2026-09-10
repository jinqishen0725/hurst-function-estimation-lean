import Hurst.HilbertSchur
import Hurst.HermiteRankBound

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace Hurst

def gaussianArrayPullback {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (P : Measure Ω) (X : ι → Ω → ℝ) (hX : ∀ i,MeasurePreserving (X i) P (gaussianReal 0 1))
    (w : ι → ℝ) : GaussianL2 →L[ℝ] Lp ℝ 2 P :=
  ∑ i,w i • gaussianPullback P (X i) (hX i)

theorem gaussianArrayPullback_ae {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (P : Measure Ω) (X : ι → Ω → ℝ) (hX : ∀ i,MeasurePreserving (X i) P (gaussianReal 0 1))
    (w : ι → ℝ) (f : GaussianL2) :
    gaussianArrayPullback P X hX w f =ᵐ[P] fun ω => ∑ i,w i*f (X i ω) := by
  have hs : gaussianArrayPullback P X hX w f = ∑ i,w i • gaussianPullback P (X i) (hX i) f := by
    simp [gaussianArrayPullback]
  rw [hs]
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i => w i • gaussianPullback P (X i) (hX i) f),
    ae_all_iff.mpr (fun i => Lp.coeFn_smul (w i) (gaussianPullback P (X i) (hX i) f)),
    ae_all_iff.mpr (fun i => gaussianPullback_ae P (X i) (hX i) f)] with ω hsum hsmul hcomp
  rw [hsum]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [Pi.smul_apply,smul_eq_mul,hcomp i] using hsmul i

theorem gaussianArrayPullback_second_moment {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (P : Measure Ω) (X : ι → Ω → ℝ) (hX : ∀ i,MeasurePreserving (X i) P (gaussianReal 0 1))
    (w : ι → ℝ) (f : GaussianL2) :
    (∫ ω,(∑ i,w i*f (X i ω))^2 ∂P)=‖gaussianArrayPullback P X hX w f‖^2 := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [gaussianArrayPullback_ae P X hX w f] with ω hω
  simp only [hω,Real.inner_apply,pow_two]

theorem gaussian_array_rank_second_moment {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (hX : ∀ i,MeasurePreserving (X i) P (gaussianReal 0 1))
    (hpair : ∀ i j,HasGaussianLaw (fun ω => (X i ω,X j ω)) P)
    (w : ι → ℝ) (f : GaussianL2) (k : ℕ) (B : ℝ)
    (hk : ∀ n : ℕ,n<k → ⟪gaussianHermiteUnit n,f⟫=0)
    (hrow : ∀ i,∑ j,|cov[X i,X j;P]|^k≤B) :
    (∫ ω,(∑ i,w i*f (X i ω))^2 ∂P) ≤ ‖f‖^2*B*∑ i,w i^2 := by
  rw [gaussianArrayPullback_second_moment P X hX w f]
  have he : gaussianArrayPullback P X hX w f = ∑ i,w i • gaussianPullback P (X i) (hX i) f := by
    simp [gaussianArrayPullback]
  rw [he]
  apply hilbert_weighted_sum_sq_bound _ w (fun i j => |cov[X i,X j;P]|^k) B (‖f‖^2)
    (sq_nonneg _) (fun _ _ => by positivity) (fun i j => by rw [covariance_comm]) hrow
  intro i j
  rw [gaussianPullback_inner]
  simpa only [mul_comm] using jointGaussian_hermite_rank_bound P (X i) (X j) (hpair i j) (hX i) (hX j) f k hk

end Hurst
