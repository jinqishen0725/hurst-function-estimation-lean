import Hurst.LinearPatternMoment

noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace Hurst

def patternResidualCoefficient {m : ℕ} {ι : Type*} (a : ι → ℝ)
    (q : MomentPattern m) (g : Fin q.1.val ↪ ι) : ℝ :=
  ∏ j : Fin q.1.val, a (g j) ^ (momentMultiplicity q j - 1)

theorem momentMultiplicity_sub_one_sum {m : ℕ} (q : MomentPattern m) :
    (∑ j : Fin q.1.val, (momentMultiplicity q j - 1)) = m - q.1.val := by
  have hp := momentMultiplicity_pos q
  have he : ∀ j : Fin q.1.val,
      momentMultiplicity q j - 1 + 1 = momentMultiplicity q j := by
    intro j
    have hj := hp j
    omega
  apply Nat.eq_sub_of_add_eq
  calc
    (∑ j : Fin q.1.val, (momentMultiplicity q j - 1)) + q.1.val =
        (∑ j : Fin q.1.val, (momentMultiplicity q j - 1)) +
          ∑ _j : Fin q.1.val, 1 := by simp
    _ = ∑ j : Fin q.1.val, ((momentMultiplicity q j - 1) + 1) := by
      rw [Finset.sum_add_distrib]
    _ = ∑ j : Fin q.1.val, momentMultiplicity q j := by
      apply Finset.sum_congr rfl
      intro j _
      exact he j
    _ = m := momentMultiplicity_sum q

theorem patternResidualCoefficient_abs_le {m : ℕ} {ι : Type*}
    (a : ι → ℝ) (W : ℝ) (hW0 : 0 ≤ W) (ha : ∀ i, |a i| ≤ W)
    (q : MomentPattern m) (g : Fin q.1.val ↪ ι) :
    |patternResidualCoefficient a q g| ≤ W ^ (m - q.1.val) := by
  unfold patternResidualCoefficient
  rw [Finset.abs_prod]
  calc
    (∏ j : Fin q.1.val, |a (g j) ^ (momentMultiplicity q j - 1)|) ≤
        ∏ j : Fin q.1.val, W ^ (momentMultiplicity q j - 1) := by
      apply Finset.prod_le_prod
      · intro j _
        exact abs_nonneg _
      · intro j _
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (ha (g j)) _
    _ = W ^ (∑ j : Fin q.1.val, (momentMultiplicity q j - 1)) :=
      Finset.prod_pow_eq_pow_sum _ _ _
    _ = W ^ (m - q.1.val) := by rw [momentMultiplicity_sub_one_sum]

theorem pattern_product_weight_extraction {m : ℕ} {ι : Type*}
    (a : ι → ℝ) (q : MomentPattern m) (g : Fin q.1.val ↪ ι)
    (z : ι → ℝ) :
    (∏ j : Fin q.1.val, (a (g j) * z (g j)) ^ momentMultiplicity q j) =
      patternResidualCoefficient a q g *
        ∏ j : Fin q.1.val, a (g j) * z (g j) ^ momentMultiplicity q j := by
  unfold patternResidualCoefficient
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  have hp := momentMultiplicity_pos q j
  rw [mul_pow]
  nth_rewrite 1 [show momentMultiplicity q j =
      (momentMultiplicity q j - 1) + 1 by omega]
  rw [pow_add, pow_one]
  ring

/-- Deterministic extraction of the repeated copies of each coefficient from one
equality pattern. -/
theorem pattern_sum_le_residual_times_linear {m : ℕ} {ι Ω : Type*}
    [Fintype ι] [MeasurableSpace Ω] (P : Measure Ω)
    (X : ι → Ω → ℝ) (a : ι → ℝ) (W : ℝ) (hW0 : 0 ≤ W)
    (ha : ∀ i, |a i| ≤ W) (q : MomentPattern m) :
    (∑ g : Fin q.1.val ↪ ι,
      |∫ ω, ∏ j : Fin q.1.val,
        (a (g j) * X (g j) ω) ^ momentMultiplicity q j ∂P|) ≤
      W ^ (m - q.1.val) *
        ∑ g : Fin q.1.val ↪ ι,
          |∫ ω, ∏ j : Fin q.1.val,
            a (g j) * X (g j) ω ^ momentMultiplicity q j ∂P| := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro g _
  rw [show (fun ω => ∏ j : Fin q.1.val,
      (a (g j) * X (g j) ω) ^ momentMultiplicity q j) =
      fun ω => patternResidualCoefficient a q g *
        ∏ j : Fin q.1.val, a (g j) * X (g j) ω ^ momentMultiplicity q j by
    funext ω
    exact pattern_product_weight_extraction a q g (fun i => X i ω)]
  rw [integral_const_mul, abs_mul]
  exact mul_le_mul_of_nonneg_right (patternResidualCoefficient_abs_le a W hW0 ha q g)
    (abs_nonneg _)

end Hurst
