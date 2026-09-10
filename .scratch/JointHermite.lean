import Hurst.GaussianRegression

noncomputable section
open Set MeasureTheory ProbabilityTheory Polynomial
namespace Hurst

theorem standard_covariance_abs_le_one {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ)
    (hX : MemLp X 2 P) (hY : MemLp Y 2 P)
    (hX1 : Var[X;P]=1) (hY1 : Var[Y;P]=1) : |cov[X,Y;P]|≤1 := by
  have hp := variance_nonneg (X+Y) P
  have hm := variance_nonneg (X-Y) P
  rw [variance_add hX hY,hX1,hY1] at hp
  rw [variance_sub hX hY,hX1,hY1] at hm
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem joint_standardGaussian_hermite {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ)
    (hXY : HasGaussianLaw (fun ω => (X ω,Y ω)) P)
    (hX0 : (∫ ω,X ω ∂P)=0) (hY0 : (∫ ω,Y ω ∂P)=0)
    (hX1 : Var[X;P]=1) (hY1 : Var[Y;P]=1) (n m : ℕ) :
    (∫ ω,(gaussianHermite n).eval (X ω)*(gaussianHermite m).eval (Y ω) ∂P) =
      if n=m then (n.factorial:ℝ)*cov[X,Y;P]^n else 0 := by
  let ρ := cov[X,Y;P]
  let s := Real.sqrt (1-ρ^2)
  have habs : |ρ|≤1 := standard_covariance_abs_le_one P X Y hXY.fst.memLp_two hXY.snd.memLp_two hX1 hY1
  have hs : ρ^2+s^2=1 := by
    rw [show s^2=1-ρ^2 from Real.sq_sqrt (by nlinarith [(abs_le.mp habs).1,(abs_le.mp habs).2])]
    ring
  have hmap := gaussian_standard_pair_law P X Y hXY hX0 hY0 hX1 hY1
  have hF : AEStronglyMeasurable
      (fun z : ℝ × ℝ => (gaussianHermite n).eval z.1*(gaussianHermite m).eval z.2)
      (P.map (fun ω => (X ω,Y ω))) := by fun_prop
  rw [← integral_map hXY.aemeasurable hF,hmap,← standardGaussian_triangular_pair_map ρ s hs,
    integral_map (by fun_prop) (by fun_prop)]
  exact standardGaussian_pair_hermite n m ρ s hs

end Hurst
