import Hurst.Moments
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Distributions.Gaussian.Real

/-! Distribution-level repairs of Theorem 3.4 and Corollary 3.5.
These are full probability theorems conditional on a centered input CLT and
an explicitly stated linearization remainder in probability. They do not
claim that the mBm inputs satisfy those premises. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace Hurst
variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ν : Measure Ω'} [IsProbabilityMeasure ν]

/-- Full distributional reflection, including an o_P(1) remainder. -/
theorem reflected_distribution_limit (X Y : ℕ → Ω → ℝ) (Z : Ω' → ℝ)
    (hX : TendstoInDistribution X atTop Z (fun _ => μ) ν)
    (hY : ∀ n, AEMeasurable (Y n) μ)
    (hrem : TendstoInMeasure μ (fun n ω => Y n ω+X n ω) atTop (fun _ => 0)) :
    TendstoInDistribution Y atTop (fun ω => -Z ω) (fun _ => μ) ν := by
  have hneg := hX.continuous_comp (g := fun x : ℝ => -x) (by fun_prop)
  apply tendstoInDistribution_of_tendstoInMeasure_sub Y (fun ω => -Z ω) hneg _ hY
  change TendstoInMeasure μ (fun n ω => Y n ω - -X n ω) atTop (fun _ => 0)
  simpa only [sub_neg_eq_add] using hrem

/-- Reflection preserves the variance and reverses the mean of a Gaussian law. -/
theorem reflected_gaussian_law (Z : Ω' → ℝ) (m : ℝ) (v : ℝ≥0)
    (hZ : HasLaw Z (gaussianReal m v) ν) :
    HasLaw (fun ω => -Z ω) (gaussianReal (-m) v) ν := gaussianReal_neg hZ

theorem centered_gaussian_reflection (Z : Ω' → ℝ) (v : ℝ≥0)
    (hZ : HasLaw Z (gaussianReal 0 v) ν) :
    HasLaw (fun ω => -Z ω) (gaussianReal 0 v) ν := by
  simpa using reflected_gaussian_law Z 0 v hZ

/-- A nonzero mean correction is a change of law, not a notation convention. -/
theorem corrected_corollary_gaussians_distinct (R : ℝ) (hR : R ≠ 0) (v : ℝ≥0) :
    gaussianReal (-2*R) v ≠ gaussianReal R v ∧
    gaussianReal (2*R) v ≠ gaussianReal R v := by
  constructor <;> intro he
  · have h := (gaussianReal_ext_iff.mp he).1
    apply hR; linarith
  · have h := (gaussianReal_ext_iff.mp he).1
    apply hR; linarith

/-- Corrected Corollary 3.5 as a downstream probability theorem.
X is the normalized centered G estimator, B its normalized deterministic bias,
and Y the normalized H error. The two upstream probabilistic obligations
remain visible in hX and hrem. -/
theorem corrected_corollary_distribution
    (X Y : ℕ → Ω → ℝ) (B : ℕ → ℝ) (Z : Ω' → ℝ) (R : ℝ) (v : ℝ≥0)
    (hX : TendstoInDistribution X atTop Z (fun _ => μ) ν)
    (hZ : HasLaw Z (gaussianReal 0 v) ν)
    (hB : Tendsto B atTop (𝓝 (-2*R)))
    (hY : ∀ n, AEMeasurable (Y n) μ)
    (hrem : TendstoInMeasure μ (fun n ω => Y n ω+(X n ω+B n)) atTop (fun _ => 0)) :
    TendstoInDistribution (fun n ω => X n ω+B n) atTop
      (fun ω => Z ω-2*R) (fun _ => μ) ν ∧
    TendstoInDistribution Y atTop (fun ω => -(Z ω-2*R)) (fun _ => μ) ν ∧
    HasLaw (fun ω => Z ω-2*R) (gaussianReal (-2*R) v) ν ∧
    HasLaw (fun ω => -(Z ω-2*R)) (gaussianReal (2*R) v) ν := by
  have hBp : TendstoInMeasure μ (fun n (_ : Ω) => B n) atTop (fun _ => -2*R) :=
    tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (Eventually.of_forall fun _ => hB)
  have htotal : TendstoInDistribution (fun n ω => X n ω+B n) atTop
      (fun ω => Z ω-2*R) (fun _ => μ) ν := by
    have hadd := hX.add_of_tendstoInMeasure_const hBp (fun _ => aemeasurable_const)
    change TendstoInDistribution (fun n ω => X n ω+B n) atTop
      (fun ω => Z ω+(-2*R)) (fun _ => μ) ν at hadd
    simpa only [sub_eq_add_neg, neg_mul] using hadd
  have hreflect := reflected_distribution_limit _ Y _ htotal hY hrem
  have hglaw : HasLaw (fun ω => Z ω-2*R) (gaussianReal (-2*R) v) ν := by
    simpa using gaussianReal_sub_const hZ (2*R)
  have hhlaw : HasLaw (fun ω => -(Z ω-2*R)) (gaussianReal (2*R) v) ν := by
    simpa only [neg_mul, neg_neg] using reflected_gaussian_law _ (-2*R) v hglaw
  exact ⟨htotal, hreflect, hglaw, hhlaw⟩

end Hurst
