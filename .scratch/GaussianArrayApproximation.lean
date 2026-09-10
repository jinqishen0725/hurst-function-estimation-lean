import Hurst.GaussianArrayL2
import Hurst.HermitePolynomialTruncation

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

theorem gaussian_array_log_polynomial_error {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (hX : ∀ i,MeasurePreserving (X i) P (gaussianReal 0 1))
    (hpair : ∀ i j,HasGaussianLaw (fun ω => (X i ω,X j ω)) P)
    (w : ι → ℝ) (B : ℝ) (hrow : ∀ i,∑ j,cov[X i,X j;P]^2≤B) (M : ℕ) :
    (∫ ω,(∑ i,w i*(centeredGaussianLog (X i ω)-
      (hermiteTruncationPolynomial gaussianLogLp M).eval (X i ω)))^2 ∂P) ≤
        ‖hermiteTail gaussianLogLp M‖^2*B*∑ i,w i^2 := by
  have he := gaussian_array_rank_second_moment P X hX hpair w (hermiteTail gaussianLogLp M) 2 B
    (gaussianLog_hermiteTail_rank_two M) (by simpa only [sq_abs] using hrow)
  have hid : (∫ ω,(∑ i,w i*(centeredGaussianLog (X i ω)-
      (hermiteTruncationPolynomial gaussianLogLp M).eval (X i ω)))^2 ∂P) =
      ∫ ω,(∑ i,w i*(hermiteTail gaussianLogLp M) (X i ω))^2 ∂P := by
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr (fun i => (hX i).quasiMeasurePreserving.ae
      (gaussianLog_hermiteTail_polynomial_ae M))] with ω hω
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [hω i]
  rwa [hid]

theorem gaussian_array_log_approximation_uniform
    (B W : ℝ) (hB : 0≤B) (hW : 0≤W) (ε : ℝ) (hε : 0<ε) :
    ∃ M₀ : ℕ, ∀ M≥M₀, ∀ N : ℕ,
      ∀ P : Measure (Fin N → ℝ), ∀ _ : IsProbabilityMeasure P,
      ∀ hX : ∀ i,MeasurePreserving (fun x : Fin N → ℝ => x i) P (gaussianReal 0 1),
      (∀ i j,HasGaussianLaw (fun x : Fin N → ℝ => (x i,x j)) P) →
      (∀ i,∑ j,cov[fun x : Fin N → ℝ => x i,fun x => x j;P]^2≤B) →
      ∀ w : Fin N → ℝ, (∑ i,w i^2)≤W →
      (∫ x,(∑ i,w i*(centeredGaussianLog (x i)-
        (hermiteTruncationPolynomial gaussianLogLp M).eval (x i)))^2 ∂P) < ε := by
  have ht : Tendsto (fun M => ‖hermiteTail gaussianLogLp M‖^2*B*W) atTop (𝓝 0) := by
    simpa using ((hermiteTail_norm_sq_tendsto gaussianLogLp).mul_const B).mul_const W
  obtain ⟨M₀,hM₀⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hε))
  refine ⟨M₀,?_⟩
  intro M hM N P hP hX hpair hrow w hw
  letI := hP
  have he := gaussian_array_log_polynomial_error P (fun i x => x i) hX hpair w B hrow M
  exact (he.trans (mul_le_mul_of_nonneg_left hw (mul_nonneg (sq_nonneg _) hB))).trans_lt (hM₀ M hM)

end Hurst
