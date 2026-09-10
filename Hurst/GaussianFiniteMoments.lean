import Hurst.GaussianLogCovariance
import Hurst.ScaleMeasurability
import Hurst.FirstScale

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace
namespace Hurst

theorem log_square_memLp_finite_gaussianReal (v : ℝ≥0) (hv : v≠0) (s : ℝ) :
    MemLp (fun x : ℝ => Real.log (x^2)) (ENNReal.ofReal s) (gaussianReal 0 v) := by
  have hm : AEStronglyMeasurable (fun x : ℝ => Real.log (x^2)) (gaussianReal 0 v) :=
    (by fun_prop : Measurable (fun x : ℝ => Real.log (x^2))).aestronglyMeasurable
  by_cases hs : s≤0
  · simpa only [ENNReal.ofReal_eq_zero.mpr hs] using memLp_zero_iff_aestronglyMeasurable.mpr hm
  have hs : 0<s := lt_of_not_ge hs
  obtain ⟨k,hk⟩ := exists_nat_gt s
  have hn : Integrable (fun x : ℝ => ‖Real.log (x^2)‖^(k:ℝ)) (gaussianReal 0 v) := by
    simpa only [Real.rpow_natCast,Real.norm_eq_abs] using integrable_abs_log_square_pow_gaussianReal v hv k
  have hi := integrable_norm_rpow_of_le hm hs.le (Nat.cast_nonneg k) hk.le hn
  apply (integrable_norm_rpow_iff hm (ne_of_gt (ENNReal.ofReal_pos.mpr hs)) (by simp)).mp
  simpa only [ENNReal.toReal_ofReal hs.le] using hi

theorem centeredGaussianLog_memLp_finite (s : ℝ) :
    MemLp centeredGaussianLog (ENNReal.ofReal s) (gaussianReal 0 1) :=
  (log_square_memLp_finite_gaussianReal 1 one_ne_zero s).sub (memLp_const _)

theorem centeredGaussianLog_pow_memLp_two (k : ℕ) :
    MemLp (fun x => centeredGaussianLog x ^ k) 2 (gaussianReal 0 1) := by
  have hg := centeredGaussianLog_memLp_finite (2*k:ℝ)
  have hi := hg.integrable_norm_rpow'
  apply (memLp_two_iff_integrable_sq (by
    exact (by unfold centeredGaussianLog; fun_prop : Measurable (fun x => centeredGaussianLog x^k)).aestronglyMeasurable)).mpr
  convert hi using 1
  funext x
  rw [ENNReal.toReal_ofReal (by positivity),show (2:ℝ)*k = ((k*2:ℕ):ℝ) by push_cast; ring,Real.rpow_natCast,Real.norm_eq_abs,← pow_mul,← abs_pow,pow_mul]
  exact (abs_of_nonneg (sq_nonneg (centeredGaussianLog x^k))).symm

theorem featureGaussian_log_square_memLp_finite {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (a : EuclideanSpace ℝ ι) (h : ∑ i,a i • v i≠0) (s : ℝ) :
    MemLp (fun x => Real.log (⟪a,x⟫^2)) (ENNReal.ofReal s) (featureGaussian v) := by
  have hv : (‖∑ i,a i • v i‖^2).toNNReal≠0 :=
    ne_of_gt (Real.toNNReal_pos.mpr (sq_pos_of_pos (norm_pos_iff.mpr h)))
  have ht := log_square_memLp_finite_gaussianReal _ hv s
  rw [← featureGaussian_linear_map] at ht
  exact ht.comp_of_map (by fun_prop)

theorem gaussianLogStatistic_memLp_finite {ι κ E : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (w : κ → ℝ) (a : κ → EuclideanSpace ℝ ι)
    (h : ∀ j,∑ i,a j i • v i≠0) (s : ℝ) :
    MemLp (gaussianLogStatistic w a) (ENNReal.ofReal s) (featureGaussian v) :=
  memLp_finsetSum _ (fun j _ => (featureGaussian_log_square_memLp_finite v (a j) (h j) s).const_mul (w j))

end Hurst
