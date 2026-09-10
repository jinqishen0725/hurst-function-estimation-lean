import Hurst.BumpLoss
import Hurst.CodePacking
import Hurst.MidpointKL

noncomputable section
open Set MeasureTheory InformationTheory
namespace Hurst

theorem bumpAlternative_boolean_loss_separation (m : ℕ) (hm : 0 < m) (p ε s : ℝ)
    (hε : 0 ≤ ε) (hs : 0 < s) (θ η : Fin m → Bool)
    (hsep : (m : ℝ) / 8 ≤ (hammingDist θ η : ℝ)) :
    ((∫ x : ℝ, |correctedBump x| ^ s) / 8) * ε ^ s * (m : ℝ) ^ (-p * s) ≤
      ∫ x in Ioo (0 : ℝ) 1, |bumpAlternative m p ε (booleanBumpWeights θ) x -
        bumpAlternative m p ε (booleanBumpWeights η) x| ^ s := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hI := correctedBump_power_integral_pos s hs
  rw [bumpAlternative_boolean_loss_identity m hm p ε s hε hs]
  have he := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsep (show 0 ≤ ε ^ s * (m : ℝ) ^ (-p * s - 1) by positivity)) hI.le
  have hp : (m : ℝ) ^ (-p * s - 1) * (m : ℝ) = (m : ℝ) ^ (-p * s) := by
    calc
      _ = (m : ℝ) ^ (-p * s - 1) * (m : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = (m : ℝ) ^ (-p * s - 1 + 1) := (Real.rpow_add hmR _ _).symm
      _ = _ := by congr 1; ring
  calc
    _ = (ε ^ s / 8) * ((m : ℝ) ^ (-p * s - 1) * m) * ∫ x : ℝ, |correctedBump x| ^ s := by rw [hp]; ring
    _ = ε ^ s * (m : ℝ) ^ (-p * s - 1) * ((m : ℝ) / 8) * ∫ x : ℝ, |correctedBump x| ^ s := by ring
    _ ≤ _ := he

/-- Concrete smooth functions in the fixed original Holder class, with exponential code size and Ls separation. -/
theorem hurst_function_packing (p M s : ℝ) (hp : 1 ≤ p) (hM : 0 < M) (hs : 0 < s) :
    ∃ ε₀ > 0, ∃ c > 0, ∃ d > 0, ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ m : ℕ, 0 < m →
      ∃ S : Finset (Fin m → Bool), S.Nonempty ∧ c * (m : ℝ) ≤ Real.log (S.card : ℝ) ∧
        (∀ θ ∈ S, bumpAlternative m p ε (booleanBumpWeights θ) ∈ hurstHolderClass p M) ∧
        ∀ θ ∈ S, ∀ η ∈ S, θ ≠ η →
          d * ε ^ s * (m : ℝ) ^ (-p * s) ≤
            ∫ x in Ioo (0 : ℝ) 1, |bumpAlternative m p ε (booleanBumpWeights θ) x -
              bumpAlternative m p ε (booleanBumpWeights η) x| ^ s := by
  obtain ⟨ε₀, hε₀, hclass⟩ := bumpAlternative_mem_hurstHolderClass p M hp hM
  obtain ⟨c, hc, hcode⟩ := binary_code_packing
  have hI := correctedBump_power_integral_pos s hs
  refine ⟨ε₀, hε₀, c, hc, (∫ x : ℝ, |correctedBump x| ^ s) / 8, by positivity, ?_⟩
  intro ε hε hεsmall m hm
  obtain ⟨S, hS, hcard, hsep⟩ := hcode m hm
  refine ⟨S, hS, hcard, ?_, ?_⟩
  · intro θ hθ
    exact hclass ε hε.le hεsmall m hm (booleanBumpWeights θ) (booleanBumpWeights_bound θ)
  · intro θ hθ η hη hneq
    exact bumpAlternative_boolean_loss_separation m hm p ε s hε.le hs θ η (hsep θ hθ η hη hneq).le

/-- One pair of constants controls the actual amplitude and derivative of every bump alternative. -/
theorem bumpAlternative_uniform_model_bounds :
    ∃ A > 0, ∃ D > 0, ∀ m : ℕ, 0 < m → ∀ p ε : ℝ, 0 ≤ ε → ∀ θ : Fin m → ℝ,
      (∀ i, |θ i| ≤ 1) → ∀ x : ℝ,
        |bumpAlternative m p ε θ x - 1 / 2| ≤ A * ε * (m : ℝ) ^ (-p) ∧
        |deriv (bumpAlternative m p ε θ) x| ≤ D * ε * (m : ℝ) ^ (1 - p) := by
  obtain ⟨A, hA, ha⟩ := bumpAlternative_amplitude_bound
  obtain ⟨D, hD, hd⟩ := bumpAlternative_derivative_bound 1 (by omega)
  refine ⟨A + 1, by positivity, D + 1, by positivity, ?_⟩
  intro m hm p ε hε θ hθ x
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  constructor
  · exact (ha m p ε hε θ hθ x).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : A ≤ A + 1) hε) (Real.rpow_nonneg hmR.le _))
  · have he := hd m hm p ε hε θ hθ x
    simp only [iteratedDeriv_one, Nat.cast_one] at he
    exact he.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : D ≤ D + 1) hε) (Real.rpow_nonneg hmR.le _))

/-- The actual KL estimate for the constructed alternatives, with no unproved covariance premise. -/
theorem bumpAlternative_klDiv_rate :
    ∃ A > 0, ∃ D > 0, ∃ c₀ > 0, ∃ b₀ > 0, ∃ C > 0,
      ∀ n : ℕ, 0 < n → ∀ m : ℕ, 0 < m → ∀ p ε : ℝ, 0 ≤ ε →
      ∀ θ : Fin m → ℝ, (∀ i, |θ i| ≤ 1) →
      ∀ hH : MapsTo (bumpAlternative m p ε θ) (Ioo (0 : ℝ) 1) (Ioo (0 : ℝ) 1),
      ∀ σ : ℝ, σ ≠ 0 →
      (A * ε * (m : ℝ) ^ (-p)) * Real.log (2 * (n : ℝ)) ≤ c₀ →
      D * ε * (m : ℝ) ^ (1 - p) ≤ b₀ →
      klDiv (scaledHarmonizableGaussian σ (midpointSampleHurst (bumpAlternative m p ε θ) hH n)
          (fun i => grid n i.val))
        (scaledHarmonizableGaussian σ (fun _ => brownianHurst) (fun i => grid n i.val)) ≤
        ENNReal.ofReal (C * ε ^ 2 * ((n : ℝ) * (m : ℝ) ^ (-2 * p) + (m : ℝ) ^ (2 - 2 * p)) *
          Real.log (2 * (n : ℝ)) ^ 2) := by
  obtain ⟨A, hA, D, hD, hbounds⟩ := bumpAlternative_uniform_model_bounds
  obtain ⟨c₀, hc₀, b₀, hb₀, K, hK, hk⟩ := scaledHarmonizableGaussian_function_klDiv_rate
  refine ⟨A, hA, D, hD, c₀, hc₀, b₀, hb₀, K * (A ^ 2 + D ^ 2), by positivity, ?_⟩
  intro n hn m hm p ε hε θ hθ hH σ hσ hsmall hBsmall
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (bumpAlternative m p ε θ) (deriv (bumpAlternative m p ε θ) t) t := by
    intro t ht
    exact ((bumpAlternative_smooth m p ε θ).differentiable
      (by simp) t).hasDerivAt
  have he := hk n hn (bumpAlternative m p ε θ) (deriv (bumpAlternative m p ε θ)) hH σ
    (A * ε * (m : ℝ) ^ (-p)) (D * ε * (m : ℝ) ^ (1 - p)) hσ (by positivity) (by positivity)
    (fun t ht => (hbounds m hm p ε hε θ hθ t).1) hderiv
    (fun t ht => (hbounds m hm p ε hε θ hθ t).2) hsmall hBsmall
  apply he.trans
  apply ENNReal.ofReal_le_ofReal
  have hpA : ((m : ℝ) ^ (-p)) ^ 2 = (m : ℝ) ^ (-2 * p) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hmR.le]
    congr 1
    ring
  have hpD : ((m : ℝ) ^ (1 - p)) ^ 2 = (m : ℝ) ^ (2 - 2 * p) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hmR.le]
    congr 1
    ring
  have hw : (n : ℝ) * (A * ε * (m : ℝ) ^ (-p)) ^ 2 + (D * ε * (m : ℝ) ^ (1 - p)) ^ 2 ≤
      (A ^ 2 + D ^ 2) * ε ^ 2 * ((n : ℝ) * (m : ℝ) ^ (-2 * p) + (m : ℝ) ^ (2 - 2 * p)) := by
    simp only [mul_pow, hpA, hpD]
    have h1 : 0 ≤ A ^ 2 * ε ^ 2 * (m : ℝ) ^ (2 - 2 * p) := by positivity
    have h2 : 0 ≤ D ^ 2 * ε ^ 2 * (n : ℝ) * (m : ℝ) ^ (-2 * p) := by positivity
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw hK.le)
    (sq_nonneg (Real.log (2 * (n : ℝ))))
  exact hmul.trans_eq (by ring)

end Hurst
