import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Tactic

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Hurst

theorem entire_eq_of_all_derivatives (f g : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f univ) (hg : AnalyticOnNhd ℂ g univ)
    (h : ∀ n : ℕ, iteratedDeriv n f 0 = iteratedDeriv n g 0) : f=g := by
  apply hf.eq_of_eventuallyEq hg (z₀ := 0)
  have hf' := (hf 0 (mem_univ _)).hasFPowerSeriesAt
  have hg' := (hg 0 (mem_univ _)).hasFPowerSeriesAt
  have he : (fun n => iteratedDeriv n f 0/(n.factorial:ℂ)) =
      (fun n => iteratedDeriv n g 0/(n.factorial:ℂ)) := by funext n; rw [h n]
  rw [he] at hf'
  filter_upwards [hf'.eventually_hasSum_sub,hg'.eventually_hasSum_sub] with z hz hz'
  exact hz.unique hz'

theorem finite_measure_eq_of_exponential_moments (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ t : ℝ, Integrable (fun x => Real.exp (t*x)) μ)
    (hν : ∀ t : ℝ, Integrable (fun x => Real.exp (t*x)) ν)
    (hm : ∀ n : ℕ, (∫ x : ℝ,x^n ∂μ) = ∫ x : ℝ,x^n ∂ν) : μ=ν := by
  have hUμ : integrableExpSet id μ = univ := by ext t; simp [integrableExpSet,hμ t]
  have hUν : integrableExpSet id ν = univ := by ext t; simp [integrableExpSet,hν t]
  have haμ : AnalyticOnNhd ℂ (complexMGF id μ) univ :=
    fun z _ => analyticAt_complexMGF (by rw [hUμ,interior_univ]; trivial)
  have haν : AnalyticOnNhd ℂ (complexMGF id ν) univ :=
    fun z _ => analyticAt_complexMGF (by rw [hUν,interior_univ]; trivial)
  apply Measure.ext_of_complexMGF_id_eq
  apply entire_eq_of_all_derivatives _ _ haμ haν
  intro n
  rw [iteratedDeriv_complexMGF (show (0:ℂ).re ∈ interior (integrableExpSet id μ) by rw [hUμ,interior_univ]; trivial),
    iteratedDeriv_complexMGF (show (0:ℂ).re ∈ interior (integrableExpSet id ν) by rw [hUν,interior_univ]; trivial)]
  simp only [id_eq,zero_mul,Complex.exp_zero,mul_one,← Complex.ofReal_pow]
  rw [integral_complex_ofReal,integral_complex_ofReal,hm n]

end Hurst
