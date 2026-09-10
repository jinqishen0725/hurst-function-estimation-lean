import Hurst.GaussianArrayL2

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace Hurst

theorem hilbert_weighted_sum_sq_double_bound {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (w : ι → ℝ) (A : ι → ι → ℝ) (C : ℝ)
    (hv : ∀ i j,|⟪v i,v j⟫|≤C*A i j) :
    ‖∑ i,w i • v i‖^2 ≤ C*(∑ i,∑ j,|w i| *|w j| *A i j) := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner,inner_sum,inner_smul_left,inner_smul_right,conj_trivial,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  rw [real_inner_comm (v i) (v j)]
  calc
    _ ≤ |w i*(w j*⟪v i,v j⟫)| := le_abs_self _
    _ = |w i| *|w j| *|⟪v i,v j⟫| := by rw [abs_mul,abs_mul]; ring
    _ ≤ |w i| *|w j| *(C*A i j) :=
      mul_le_mul_of_nonneg_left (hv i j) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = _ := by ring

theorem gaussian_array_rank_double_moment {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (hX : ∀ i,MeasurePreserving (X i) P (gaussianReal 0 1))
    (hpair : ∀ i j,HasGaussianLaw (fun ω => (X i ω,X j ω)) P)
    (w : ι → ℝ) (f : GaussianL2) (k : ℕ)
    (hk : ∀ n : ℕ,n<k → ⟪gaussianHermiteUnit n,f⟫=0) :
    (∫ ω,(∑ i,w i*f (X i ω))^2 ∂P)≤
      ‖f‖^2*(∑ i,∑ j,|w i| *|w j| *|cov[X i,X j;P]|^k) := by
  rw [gaussianArrayPullback_second_moment P X hX w f]
  have he : gaussianArrayPullback P X hX w f=∑ i,w i • gaussianPullback P (X i) (hX i) f := by
    simp [gaussianArrayPullback]
  rw [he]
  apply hilbert_weighted_sum_sq_double_bound
  intro i j
  rw [gaussianPullback_inner]
  simpa only [mul_comm] using jointGaussian_hermite_rank_bound P (X i) (X j) (hpair i j) (hX i) (hX j) f k hk

end Hurst
