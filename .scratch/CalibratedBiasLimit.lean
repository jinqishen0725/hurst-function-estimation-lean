import Hurst.LocalLeadingLimit

noncomputable section
open Set Filter
open scoped Topology
namespace Hurst

def localCalibrationBias (r n q : ℕ) (δ t L : ℝ) (f φ : ℝ → ℝ) (c : ℝ) : ℝ :=
  smooth (localPolynomialWeights r n q δ t) (fun i => -2*L*f (grid n i.val)+φ (f (grid n i.val))+c)-
    (-2*L*f t+φ (f t)+c)

theorem localCalibrationBias_identity (r n q : ℕ) (δ t L : ℝ) (f φ : ℝ → ℝ) (c : ℝ)
    (hdet : IsUnit (localDesignGram r n q δ t).det) :
    localCalibrationBias r n q δ t L f φ c =
      -2*L*(smooth (localPolynomialWeights r n q δ t) (fun i => f (grid n i.val))-f t)+
      (smooth (localPolynomialWeights r n q δ t) (fun i => φ (f (grid n i.val)))-φ (f t)) := by
  have hw : ∑ i,localPolynomialWeights r n q δ t i=1 := by
    simpa using localPolynomialWeights_moments r n q δ t hdet 0
  rw [localCalibrationBias,log_estimator_decomposition _ _ _ _ _ hw]
  ring

theorem localCalibrationBias_leading_tendsto (r q : ℕ) (f φ : ℝ → ℝ) (c : ℝ)
    (hf : ContDiffOn ℝ (r+1) f (Ioo (0:ℝ) 1))
    (hφf : ContDiffOn ℝ (r+1) (φ ∘ f) (Ioo (0:ℝ) 1)) (t : ℝ) (ht : t∈Ioo (0:ℝ) 1)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n in atTop,0<δ n)
    (hδ : Tendsto δ atTop (𝓝 0)) (hN : Tendsto (fun n : ℕ => (n:ℝ)*δ n) atTop atTop) :
    Tendsto (fun n : ℕ => localCalibrationBias r n q (δ n) t (Real.log n) f φ c/
      (Real.log n*(δ n)^(r+1))) atTop
        (𝓝 (-2*((iteratedDeriv (r+1) f t/((r+1).factorial:ℝ))*equivalentKernelMoment r (r+1)))) := by
  have hfL := localPolynomial_bias_leading_tendsto r q f hf t ht δ hδpos hδ hN
  have hφL := localPolynomial_bias_leading_tendsto r q (φ ∘ f) hφf t ht δ hδpos hδ hN
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogInv : Tendsto (fun n : ℕ => (Real.log n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hlog
  have hh := (hfL.const_mul (-2)).add (hφL.mul hlogInv)
  simp only [mul_zero,add_zero] at hh
  obtain ⟨D,hD,hstable⟩ := localPolynomialWeights_eventual_stability r q t ⟨ht.1.le,ht.2.le⟩ δ hδpos hδ hN
  apply hh.congr'
  filter_upwards [hδpos,hstable,hlog.eventually_gt_atTop 0] with n hn hs hln
  rw [localCalibrationBias_identity r n q (δ n) t (Real.log n) f φ c hs.1]
  simp only [Function.comp_apply]
  have hp := pow_ne_zero (r+1) hn.ne'
  field_simp
  <;> ring

end Hurst
