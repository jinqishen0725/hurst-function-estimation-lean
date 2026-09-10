import Hurst.HermitePair
import Hurst.GaussianPairLaw

noncomputable section
open Set MeasureTheory ProbabilityTheory Polynomial
open scoped ENNReal NNReal
namespace Hurst

theorem standardGaussian_fst_law :
    HasLaw (Prod.fst : ℝ × ℝ → ℝ) (gaussianReal 0 1) ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
  ⟨by fun_prop,by simp⟩

theorem standardGaussian_affine_pair_law (ρ s : ℝ) (h : ρ^2+s^2=1) :
    HasLaw (fun z : ℝ × ℝ => ρ*z.1+s*z.2) (gaussianReal 0 1)
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  have hY : HasLaw (Prod.snd : ℝ × ℝ → ℝ) (gaussianReal 0 1)
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := ⟨by fun_prop,by simp⟩
  have hind := indepFun_prod (μ := gaussianReal 0 1) (ν := gaussianReal 0 1)
    (X := fun x : ℝ => ρ*x) (Y := fun x : ℝ => s*x) (by fun_prop) (by fun_prop)
  have he := gaussianReal_add_gaussianReal_of_indepFun hind
    (gaussianReal_const_mul standardGaussian_fst_law ρ).map_eq
    (gaussianReal_const_mul hY s).map_eq
  have hv : NNReal.mk (ρ^2) (sq_nonneg ρ)*1+NNReal.mk (s^2) (sq_nonneg s)*1=1 := by
    apply NNReal.coe_injective
    change ρ^2*1+s^2*1=1
    nlinarith
  refine ⟨by fun_prop,?_⟩
  rw [hv,mul_zero,mul_zero,add_zero] at he
  exact he

theorem standardGaussian_triangular_pair_map (ρ s : ℝ) (h : ρ^2+s^2=1) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map (fun z : ℝ × ℝ => (z.1,ρ*z.1+s*z.2)) =
      correlatedGaussianPair ρ := by
  let P := (gaussianReal 0 1).prod (gaussianReal 0 1)
  have hG : HasGaussianLaw (fun z : ℝ × ℝ => z) P := IsGaussian.hasGaussianLaw_id
  have hXY : HasGaussianLaw (fun z : ℝ × ℝ => (z.1,ρ*z.1+s*z.2)) P := by
    simpa [gaussianAffinePairMap] using
      hG.map_fun ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod (gaussianAffinePairMap ρ s))
  have hX := standardGaussian_fst_law
  have hY := standardGaussian_affine_pair_law ρ s h
  have hx0 : (∫ z : ℝ × ℝ,z.1 ∂P)=0 := by
    rw [hX.integral_eq,integral_id_gaussianReal]
  have hy0 : (∫ z : ℝ × ℝ,ρ*z.1+s*z.2 ∂P)=0 := by
    rw [hY.integral_eq,integral_id_gaussianReal]
  have hx1 : Var[Prod.fst;P]=1 := by rw [hX.variance_eq,variance_id_gaussianReal]; norm_num
  have hy1 : Var[fun z : ℝ × ℝ => ρ*z.1+s*z.2;P]=1 := by
    rw [hY.variance_eq,variance_id_gaussianReal]; norm_num
  have hcov : cov[Prod.fst,fun z : ℝ × ℝ => ρ*z.1+s*z.2;P]=ρ := by
    rw [covariance_eq_sub hXY.fst.memLp_two hXY.snd.memLp_two,hx0,hy0,mul_zero,sub_zero]
    simpa [gaussianHermite_one] using standardGaussian_pair_hermite 1 1 ρ s h
  simpa only [hcov] using gaussian_standard_pair_law P Prod.fst _ hXY hx0 hy0 hx1 hy1

end Hurst
