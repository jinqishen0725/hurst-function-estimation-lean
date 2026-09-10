import Hurst.GaussianHermiteCovariance

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace Hurst

theorem hermite_rank_coefficient_bound (ρ : ℝ) (hρ : |ρ|≤1) (f : GaussianL2) (k : ℕ)
    (hk : ∀ n : ℕ,n<k → ⟪gaussianHermiteUnit n,f⟫=0) (n : ℕ) :
    |ρ^n*⟪gaussianHermiteUnit n,f⟫*⟪gaussianHermiteUnit n,f⟫| ≤
      |ρ|^k*⟪gaussianHermiteUnit n,f⟫^2 := by
  by_cases hn : n<k
  · rw [hk n hn]
    simp
  · have hp := pow_le_pow_of_le_one (abs_nonneg ρ) hρ (Nat.le_of_not_gt hn)
    calc
      |ρ^n*⟪gaussianHermiteUnit n,f⟫*⟪gaussianHermiteUnit n,f⟫| =
          |ρ|^n*⟪gaussianHermiteUnit n,f⟫^2 := by
        rw [mul_assoc,← pow_two,abs_mul,abs_of_nonneg (sq_nonneg ⟪gaussianHermiteUnit n,f⟫),abs_pow]
      _ ≤ _ := mul_le_mul_of_nonneg_right hp (sq_nonneg _)

theorem jointGaussian_hermite_rank_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ)
    (hXY : HasGaussianLaw (fun ω => (X ω,Y ω)) P)
    (hX : MeasurePreserving X P (gaussianReal 0 1))
    (hY : MeasurePreserving Y P (gaussianReal 0 1)) (f : GaussianL2) (k : ℕ)
    (hk : ∀ n : ℕ,n<k → ⟪gaussianHermiteUnit n,f⟫=0) :
    |∫ ω,f (X ω)*f (Y ω) ∂P| ≤ |cov[X,Y;P]|^k*‖f‖^2 := by
  have hXlaw : HasLaw X (gaussianReal 0 1) P := ⟨hX.measurable.aemeasurable,hX.map_eq⟩
  have hYlaw : HasLaw Y (gaussianReal 0 1) P := ⟨hY.measurable.aemeasurable,hY.map_eq⟩
  have hvX : Var[X;P]=1 := by rw [hXlaw.variance_eq,variance_id_gaussianReal]; norm_num
  have hvY : Var[Y;P]=1 := by rw [hYlaw.variance_eq,variance_id_gaussianReal]; norm_num
  have hρ := standard_covariance_abs_le_one P X Y hXY.fst.memLp_two hXY.snd.memLp_two hvX hvY
  have hs := jointGaussian_hermite_covariance_expansion P X Y hXY hX hY f f
  have hb := (gaussianHermite_parseval f).mul_left (|cov[X,Y;P]|^k)
  apply abs_le.mpr
  constructor
  · apply hasSum_le _ hb.neg hs
    intro n
    exact (abs_le.mp (hermite_rank_coefficient_bound _ hρ f k hk n)).1
  · apply hasSum_le _ hs hb
    intro n
    exact (abs_le.mp (hermite_rank_coefficient_bound _ hρ f k hk n)).2

end Hurst
