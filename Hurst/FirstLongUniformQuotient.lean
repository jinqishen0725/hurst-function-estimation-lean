import Hurst.FirstLongCrossKernel
import Hurst.FrozenEstimates
import Mathlib.Analysis.Calculus.Taylor

noncomputable section
open Set
namespace Hurst

private theorem rpow_taylor_one_quantitative (α u : ℝ)
    (hu : 0 < u) (hu1 : u < 1) :
    ∃ ξ ∈ Ioo 1 (1 + u),
      (1 + u) ^ α - (1 + α * u) =
        (α * (α - 1) * ξ ^ (α - 2)) * u ^ 2 / 2 := by
  have hpos : ∀ z ∈ uIcc (1 : ℝ) (1 + u), z ≠ 0 := by
    intro z hz
    rw [uIcc_of_le (by linarith)] at hz
    exact (zero_lt_one.trans_le hz.1).ne'
  have hcd : ContDiffOn ℝ 2 (fun z : ℝ => z ^ α)
      (uIcc (1 : ℝ) (1 + u)) :=
    contDiffOn_id.rpow_const_of_ne hpos
  obtain ⟨ξ, hξ, hrem⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv
      (show (1 : ℝ) ≠ 1 + u by linarith) hcd
  refine ⟨ξ, ?_, ?_⟩
  · simpa [uIoo, min_eq_left (by linarith : (1 : ℝ) ≤ 1 + u),
      max_eq_right (by linarith : (1 : ℝ) ≤ 1 + u)] using hξ
  have htaylor : taylorWithinEval (fun z : ℝ => z ^ α) 1
      (uIcc (1 : ℝ) (1 + u)) 1 (1 + u) = 1 + α * u := by
    rw [show (1 : ℕ) = 0 + 1 by omega, taylorWithinEval_succ,
      taylor_within_zero_eval, iteratedDerivWithin_one]
    have hunique : UniqueDiffWithinAt ℝ (uIcc (1 : ℝ) (1 + u)) 1 :=
      (uniqueDiffOn_Icc (by
        change min (1 : ℝ) (1 + u) < max 1 (1 + u)
        rw [min_eq_left (by linarith), max_eq_right (by linarith)]
        linarith)).uniqueDiffWithinAt (by
          constructor <;>
            simp [min_eq_left (by linarith : (1 : ℝ) ≤ 1 + u),
              max_eq_right (by linarith : (1 : ℝ) ≤ 1 + u), hu.le])
    rw [(Real.hasDerivAt_rpow_const (p := α)
      (Or.inl one_ne_zero)).hasDerivWithinAt.derivWithin hunique]
    norm_num
    ring
  rw [htaylor] at hrem
  rw [hrem]
  have hsecond : deriv (deriv (fun z : ℝ => z ^ α)) ξ =
      α * (α - 1) * ξ ^ (α - 2) := by
    rw [Real.deriv_rpow_const']
    rw [deriv_const_mul_field, Real.deriv_rpow_const]
    ring
  rw [show (2 : ℕ) = 1 + 1 by omega, iteratedDeriv_succ,
    iteratedDeriv_one, hsecond]
  norm_num

private theorem rpow_taylor_one_sub_quantitative (α u : ℝ)
    (hu : 0 < u) (hu1 : u < 1) :
    ∃ ξ ∈ Ioo (1 - u) 1,
      (1 - u) ^ α - (1 - α * u) =
        (α * (α - 1) * ξ ^ (α - 2)) * u ^ 2 / 2 := by
  have hpos : ∀ z ∈ uIcc (1 : ℝ) (1 - u), z ≠ 0 := by
    intro z hz
    rw [uIcc_of_ge (by linarith)] at hz
    exact (by linarith [hz.1] : 0 < z).ne'
  have hcd : ContDiffOn ℝ 2 (fun z : ℝ => z ^ α)
      (uIcc (1 : ℝ) (1 - u)) :=
    contDiffOn_id.rpow_const_of_ne hpos
  obtain ⟨ξ, hξ, hrem⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv
      (show (1 : ℝ) ≠ 1 - u by linarith) hcd
  refine ⟨ξ, ?_, ?_⟩
  · simpa [uIoo, min_eq_right (by linarith : 1 - u ≤ (1 : ℝ)),
      max_eq_left (by linarith : 1 - u ≤ (1 : ℝ))] using hξ
  have htaylor : taylorWithinEval (fun z : ℝ => z ^ α) 1
      (uIcc (1 : ℝ) (1 - u)) 1 (1 - u) = 1 - α * u := by
    rw [show (1 : ℕ) = 0 + 1 by omega, taylorWithinEval_succ,
      taylor_within_zero_eval, iteratedDerivWithin_one]
    have hunique : UniqueDiffWithinAt ℝ (uIcc (1 : ℝ) (1 - u)) 1 :=
      (uniqueDiffOn_Icc (by
        change min (1 : ℝ) (1 - u) < max 1 (1 - u)
        rw [min_eq_right (by linarith), max_eq_left (by linarith)]
        linarith)).uniqueDiffWithinAt (by
          constructor <;>
            simp [min_eq_right (by linarith : 1 - u ≤ (1 : ℝ)),
              max_eq_left (by linarith : 1 - u ≤ (1 : ℝ)), hu.le])
    rw [(Real.hasDerivAt_rpow_const (p := α)
      (Or.inl one_ne_zero)).hasDerivWithinAt.derivWithin hunique]
    norm_num
    ring
  rw [htaylor] at hrem
  rw [hrem]
  have hsecond : deriv (deriv (fun z : ℝ => z ^ α)) ξ =
      α * (α - 1) * ξ ^ (α - 2) := by
    rw [Real.deriv_rpow_const']
    rw [deriv_const_mul_field, Real.deriv_rpow_const]
    ring
  rw [show (2 : ℕ) = 1 + 1 by omega, iteratedDeriv_succ,
    iteratedDeriv_one, hsecond]
  norm_num

private theorem compact_rpow_factor_le (α : ℝ) (hα0 : 0 ≤ α) :
    (1 / 2 : ℝ) ^ (α - 3) ≤ 8 := by
  calc
    _ ≤ (1 / 2 : ℝ) ^ (-3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith)
    _ = 8 := by
      norm_num [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 1 / 2)]

private theorem rpow_at_taylor_point_sub_one_le
    (α u ξ : ℝ) (hα0 : 0 ≤ α) (hα2 : α ≤ 2)
    (hu0 : 0 ≤ u) (hu2 : u ≤ 1 / 2)
    (hξlo : 1 / 2 ≤ ξ) (hξdist : |ξ - 1| ≤ u) :
    |ξ ^ (α - 2) - 1| ≤ 16 * u := by
  have hraw := rpow_difference_bound_of_lower (α - 2) (1 / 2) ξ 1
    (by linarith) (by norm_num) hξlo (by norm_num)
  rw [Real.one_rpow] at hraw
  have habs : |α - 2| ≤ 2 := by
    rw [abs_le]
    constructor <;> linarith
  have hpow : (1 / 2 : ℝ) ^ (α - 2 - 1) ≤ 8 := by
    convert compact_rpow_factor_le α hα0 using 1 <;> ring
  have hfactor : |α - 2| * (1 / 2 : ℝ) ^ (α - 2 - 1) ≤ 16 := by
    nlinarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (α - 2 - 1),
      abs_nonneg (α - 2)]
  calc
    _ ≤ (|α - 2| * (1 / 2 : ℝ) ^ (α - 2 - 1)) * |ξ - 1| := hraw
    _ ≤ 16 * u :=
      mul_le_mul hfactor hξdist (abs_nonneg _) (by positivity)

/-- Uniform quantitative version of the symmetric second-difference limit.
The explicit bound is valid over the whole Hurst exponent range needed for
cross-correlations and upgrades pointwise kernel convergence to growing-matrix
uniform convergence away from a diverging diagonal cutoff. -/
theorem centeredCrossRpowQuotient_uniform_error
    (α u : ℝ) (hα0 : 0 ≤ α) (hα2 : α ≤ 2)
    (hu : 0 < u) (hu2 : u ≤ 1 / 2) :
    |centeredCrossRpowQuotient α u - α * (α - 1)| ≤ 32 * u := by
  have hu1 : u < 1 := hu2.trans_lt (by norm_num)
  obtain ⟨ξp, hξp, hp⟩ := rpow_taylor_one_quantitative α u hu hu1
  obtain ⟨ξm, hξm, hm⟩ := rpow_taylor_one_sub_quantitative α u hu hu1
  have hξplo : 1 / 2 ≤ ξp := by linarith [hξp.1]
  have hξmlo : 1 / 2 ≤ ξm := by linarith [hξm.1]
  have hξpdist : |ξp - 1| ≤ u := by
    rw [abs_of_nonneg (by linarith [hξp.1])]
    linarith [hξp.2]
  have hξmdist : |ξm - 1| ≤ u := by
    rw [abs_of_nonpos (by linarith [hξm.2])]
    linarith [hξm.1]
  have hpdiff := rpow_at_taylor_point_sub_one_le
    α u ξp hα0 hα2 hu.le hu2 hξplo hξpdist
  have hmdiff := rpow_at_taylor_point_sub_one_le
    α u ξm hα0 hα2 hu.le hu2 hξmlo hξmdist
  have hquot : centeredCrossRpowQuotient α u =
      (α * (α - 1) * ξp ^ (α - 2) +
        α * (α - 1) * ξm ^ (α - 2)) / 2 := by
    unfold centeredCrossRpowQuotient
    rw [show
      (1 + u) ^ α + (1 - u) ^ α - 2 =
        ((1 + u) ^ α - (1 + α * u)) +
          ((1 - u) ^ α - (1 - α * u)) by ring,
      hp, hm]
    field_simp [hu.ne']
    <;> ring
  have hsum :
      |(ξp ^ (α - 2) - 1) + (ξm ^ (α - 2) - 1)| ≤ 32 * u := by
    calc
      _ ≤ |ξp ^ (α - 2) - 1| + |ξm ^ (α - 2) - 1| := abs_add_le _ _
      _ ≤ 16 * u + 16 * u := add_le_add hpdiff hmdiff
      _ = 32 * u := by ring
  have hαabs : |α| ≤ 2 := by
    rw [abs_of_nonneg hα0]
    exact hα2
  have hαone : |α - 1| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hcoef : |α * (α - 1) / 2| ≤ 1 := by
    rw [abs_div, abs_mul]
    norm_num
    nlinarith [mul_le_mul hαabs hαone (abs_nonneg (α - 1))
      (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hquot]
  have halgebra :
      (α * (α - 1) * ξp ^ (α - 2) +
          α * (α - 1) * ξm ^ (α - 2)) / 2 - α * (α - 1) =
        (α * (α - 1) / 2) *
          ((ξp ^ (α - 2) - 1) + (ξm ^ (α - 2) - 1)) := by ring
  rw [halgebra, abs_mul]
  calc
    |α * (α - 1) / 2| *
        |(ξp ^ (α - 2) - 1) + (ξm ^ (α - 2) - 1)| ≤
      1 * (32 * u) :=
        mul_le_mul hcoef hsum (abs_nonneg _) (by positivity)
    _ = 32 * u := one_mul _

end Hurst
