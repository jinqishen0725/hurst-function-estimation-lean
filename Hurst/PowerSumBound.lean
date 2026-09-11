import Mathlib

/-!
# Power-sum bounds for fractional power tails

For `0 < β < 1` we bound the power sum `∑_{j ∈ range n} (j + 1 : ℝ) ^ (-β)`
by `n ^ (1 - β) / (1 - β)` (hence by `n ^ (1 - β) / (1 - β) + 1`), together with
finite-tail versions and the decay `(R + 1) ^ (2 * β - 1) → 0` for `β < 1/2`.

The engine is the step inequality
`(j + 1) ^ (1 - β) - j ^ (1 - β) ≥ (1 - β) * (j + 1) ^ (-β)`,
proved from weighted AM-GM, which then telescopes.
-/

open Filter Real

namespace Hurst

/-! ### Elementary step inequality -/

/-- Weighted AM-GM gives the tangent-line bound for the concave power map:
for `0 < a < 1` and `u ≤ 1`, `(1 - u) ^ a ≤ 1 - a * u`. -/
private lemma one_sub_rpow_le_one_sub_mul {a u : ℝ} (ha1 : 0 < a) (ha2 : a < 1) (hu : u ≤ 1) :
    (1 - u) ^ a ≤ 1 - a * u := by
  have hge := Real.geom_mean_le_arith_mean2_weighted (le_of_lt ha1)
    (le_of_lt (by linarith : (0 : ℝ) < 1 - a)) (by linarith : 0 ≤ 1 - u)
    (by norm_num : (0 : ℝ) ≤ 1) (by ring : a + (1 - a) = 1)
  rw [Real.one_rpow, mul_one, one_mul] at hge
  calc (1 - u) ^ a ≤ a * (1 - u) + (1 - a) := hge
    _ = 1 - a * u := by ring

/-- Step inequality: for `0 < β < 1`,
`(j + 1) ^ (1 - β) - j ^ (1 - β) ≥ (1 - β) * (j + 1) ^ (-β)`. -/
private lemma rpow_step_ge {β : ℝ} (hβ1 : 0 < β) (hβ2 : β < 1) (j : ℕ) :
    ((j : ℝ) + 1) ^ (1 - β) - (j : ℝ) ^ (1 - β) ≥ (1 - β) * ((j : ℝ) + 1) ^ (-β) := by
  have ha1 : 0 < 1 - β := by linarith
  set X : ℝ := (j : ℝ) + 1 with hX
  have hXpos : 0 < X := by rw [hX]; positivity
  have hu : 1 / X ≤ 1 := (div_le_one hXpos.le).2 hXpos.le
  have hub : (1 - 1 / X) ^ (1 - β) ≤ 1 - (1 - β) * (1 / X) :=
    one_sub_rpow_le_one_sub_mul ha1 hβ2 hu
  have hmul : X * (1 - 1 / X) = (j : ℝ) := by
    rw [hX]; field_simp
  have hexpr : (j : ℝ) ^ (1 - β) = X ^ (1 - β) * (1 - 1 / X) ^ (1 - β) := by
    conv_lhs => rw [← hmul]
    exact Real.rpow_mul hXpos.le _ _
  calc X ^ (1 - β) - (j : ℝ) ^ (1 - β)
      = X ^ (1 - β) * (1 - (1 - 1 / X) ^ (1 - β)) := by rw [hexpr]; ring
    _ ≥ X ^ (1 - β) * ((1 - β) * (1 / X)) :=
        mul_le_mul_of_nonneg_left (by linarith) hXpos.le
    _ = (1 - β) * X ^ (-β) := by
        rw [show (-β : ℝ) = (1 - β) - 1 by ring, Real.rpow_sub hXpos.le, Real.rpow_one]
        ring

/-- Pointwise division form of the step inequality, ready for summing:
`(j + 1) ^ (-β) ≤ (((j + 1) ^ (1 - β) - j ^ (1 - β)) / (1 - β))`. -/
private lemma rpow_step_div_le {β : ℝ} (hβ1 : 0 < β) (hβ2 : β < 1) (j : ℕ) :
    ((j : ℝ) + 1) ^ (-β)
      ≤ (((j : ℝ) + 1) ^ (1 - β) - (j : ℝ) ^ (1 - β)) / (1 - β) := by
  have hpos : (0 : ℝ) < 1 - β := by linarith
  have hstep := rpow_step_ge hβ1 hβ2 j
  calc ((j : ℝ) + 1) ^ (-β)
      ≤ (((j : ℝ) + 1) ^ (1 - β) - (j : ℝ) ^ (1 - β)) * (1 - β)⁻¹ := by
        have h1 : ((j : ℝ) + 1) ^ (-β) * (1 - β)
            ≤ ((j : ℝ) + 1) ^ (1 - β) - (j : ℝ) ^ (1 - β) := by
          rw [mul_comm ((j : ℝ) + 1) ^ (-β) (1 - β)]; exact hstep
        calc ((j : ℝ) + 1) ^ (-β)
            = ((j : ℝ) + 1) ^ (-β) * ((1 - β) * (1 - β)⁻¹) := by
              rw [mul_inv_cancel₀ hpos.ne', mul_one]
          _ ≤ (((j : ℝ) + 1) ^ (1 - β) - (j : ℝ) ^ (1 - β)) * (1 - β)⁻¹ :=
              mul_le_mul_of_nonneg_right h1 (inv_nonneg.2 hpos.le)
    _ = (((j : ℝ) + 1) ^ (1 - β) - (j : ℝ) ^ (1 - β)) / (1 - β) := by
        rw [div_eq_mul_inv]

/-! ### Telescoping -/

/-- Discrete fundamental theorem of calculus. -/
private lemma sum_telescope (g : ℕ → ℝ) (n : ℕ) :
    ∑ j ∈ Finset.range n, (g (j + 1) - g j) = g n - g 0 := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; ring

/-! ### Power-sum bounds -/

/-- **Power-sum bound**: for `0 < β < 1` and `n : ℕ`,
`∑_{j ∈ range n} (j + 1 : ℝ) ^ (-β) ≤ n ^ (1 - β) / (1 - β) + 1`. -/
theorem sum_range_rpow_neg_le {β : ℝ} (hβ1 : 0 < β) (hβ2 : β < 1) (n : ℕ) :
    ∑ j ∈ Finset.range n, ((j + 1 : ℕ) : ℝ) ^ (-β) ≤ ((n : ℝ) ^ (1 - β)) / (1 - β) + 1 := by
  have hpos : (0 : ℝ) < 1 - β := by linarith
  have hterm : ∀ j ∈ Finset.range n, ((j + 1 : ℕ) : ℝ) ^ (-β)
      ≤ (((j + 1 : ℕ) : ℝ) ^ (1 - β) - (j : ℝ) ^ (1 - β)) / (1 - β) := by
    intro j _
    push_cast
    exact rpow_step_div_le hβ1 hβ2 j
  refine le_trans (Finset.sum_le_sum hterm) ?_
  have hs := sum_telescope (fun k : ℕ => (k : ℝ) ^ (1 - β)) n
  have hs' : ∑ j ∈ Finset.range n, (((j : ℝ) + 1) ^ (1 - β) - (j : ℝ) ^ (1 - β))
      = (n : ℝ) ^ (1 - β) - (0 : ℝ) ^ (1 - β) := hs
  rw [Real.zero_rpow (by linarith : (1 : ℝ) - β ≠ 0), sub_zero] at hs'
  rw [Finset.sum_div, hs']
  linarith

/-- Sharper form without the `+ 1`: for `0 < β < 1`,
`∑_{j ∈ range n} (j + 1 : ℝ) ^ (-β) ≤ n ^ (1 - β) / (1 - β)`. -/
theorem sum_range_rpow_neg_le' {β : ℝ} (hβ1 : 0 < β) (hβ2 : β < 1) (n : ℕ) :
    ∑ j ∈ Finset.range n, ((j + 1 : ℕ) : ℝ) ^ (-β) ≤ ((n : ℝ) ^ (1 - β)) / (1 - β) := by
  have h := sum_range_rpow_neg_le hβ1 hβ2 n
  linarith

/-- **Finite tail bound**: for `0 < β < 1` and `R ≤ M`,
`∑_{R ≤ j < M} (j + 1 : ℝ) ^ (-β) ≤ (M ^ (1 - β) - R ^ (1 - β)) / (1 - β)`. -/
theorem sum_Ico_rpow_neg_le {β : ℝ} (hβ1 : 0 < β) (hβ2 : β < 1) (R M : ℕ) (hRM : R ≤ M) :
    ∑ j ∈ Finset.Ico R M, ((j + 1 : ℕ) : ℝ) ^ (-β)
      ≤ (((M : ℝ) ^ (1 - β) - (R : ℝ) ^ (1 - β))) / (1 - β) := by
  have hterm : ∀ j ∈ Finset.Ico R M, ((j + 1 : ℕ) : ℝ) ^ (-β)
      ≤ (((j + 1 : ℕ) : ℝ) ^ (1 - β) - (j : ℝ) ^ (1 - β)) / (1 - β) := by
    intro j _
    push_cast
    exact rpow_step_div_le hβ1 hβ2 j
  have hs := sum_telescope (fun k : ℕ => (k : ℝ) ^ (1 - β)) M
  have hs2 := sum_telescope (fun k : ℕ => (k : ℝ) ^ (1 - β)) R
  have hs' : ∑ j ∈ Finset.range M, (((j : ℝ) + 1) ^ (1 - β) - (j : ℝ) ^ (1 - β))
      = (M : ℝ) ^ (1 - β) - (0 : ℝ) ^ (1 - β) := hs
  have hs2' : ∑ j ∈ Finset.range R, (((j : ℝ) + 1) ^ (1 - β) - (j : ℝ) ^ (1 - β))
      = (R : ℝ) ^ (1 - β) - (0 : ℝ) ^ (1 - β) := hs2
  rw [Real.zero_rpow (by linarith : (1 : ℝ) - β ≠ 0), sub_zero] at hs' hs2'
  have htele : ∑ j ∈ Finset.Ico R M, (((j : ℝ) + 1) ^ (1 - β) - (j : ℝ) ^ (1 - β))
      = (M : ℝ) ^ (1 - β) - (R : ℝ) ^ (1 - β) := by
    rw [Finset.sum_Ico_eq_sub (fun j : ℕ => ((j : ℝ) + 1) ^ (1 - β) - (j : ℝ) ^ (1 - β)) hRM,
      hs', hs2']
    ring
  calc ∑ j ∈ Finset.Ico R M, ((j + 1 : ℕ) : ℝ) ^ (-β)
      ≤ ∑ j ∈ Finset.Ico R M,
          (((j : ℝ) + 1) ^ (1 - β) - (j : ℝ) ^ (1 - β)) / (1 - β) :=
        Finset.sum_le_sum (fun j _ => by push_cast; exact rpow_step_div_le hβ1 hβ2 j)
    _ = (∑ j ∈ Finset.Ico R M, (((j : ℝ) + 1) ^ (1 - β) - (j : ℝ) ^ (1 - β))) / (1 - β) :=
        (Finset.sum_div _ _ _).symm
    _ = ((M : ℝ) ^ (1 - β) - (R : ℝ) ^ (1 - β)) / (1 - β) := by rw [htele]

/-- For `β < 1/2`, the normalizing factor `(R + 1) ^ (2 * β - 1)` tends to `0`. -/
theorem tendsto_rpow_two_beta_sub_one {β : ℝ} (hβ : β < 1 / 2) :
    Tendsto (fun R : ℕ => ((R : ℝ) + 1) ^ (2 * β - 1)) atTop (𝓝 0) := by
  have hy : 0 < 1 - 2 * β := by linarith
  have key : Tendsto (fun x : ℝ => x ^ (-(1 - 2 * β))) atTop (𝓝 0) :=
    Real.tendsto_rpow_neg_atTop hy
  have hbase : Tendsto (fun R : ℕ => (R : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.add_const 1
  refine Tendsto.congr' ?_ (key.comp hbase)
  filter_upwards with R
  congr 1
  ring

end Hurst
