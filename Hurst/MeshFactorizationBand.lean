import Hurst.PowerSumBound

/-!
# Band difference bounds and the far-band square tail for mesh distances

Companion bounds for `Hurst.MeshFactorizationLimit`, shaped for the truncated
Riesz cycle kernel `c * (max ((R + 1 : ℕ) : ℝ)⁻¹ |x - y|) ^ (-psi)` away from
the diagonal cap, where entries reduce to `c * |x - y| ^ (-psi)`.

Two algebraic identities drive the band splitting (`psi > 0`, `0 < |x|`):

* `|x| ^ (-psi) = |x| ^ psi * |x| ^ (-2 * psi)`; and
* `|x| ^ (-2 * psi) = |x| ^ (-psi) * |x| ^ (-psi)`.

Consequences:

* **Near band** (`|x| ≤ R + 1`): `|x| ^ (-psi) ≤ (R + 1) ^ psi * |x| ^ (-2 * psi)`
  (the power `|x| ^ psi` is bounded by the band radius).
* **Far band** (`R + 1 ≤ |x|`): `|x| ^ (-2 * psi) ≤ (R + 1) ^ (-psi) * |x| ^ (-psi)`
  (on the far band the square `d ^ (-2 psi)` is dominated by the single power
  `d ^ (-psi)` times the decaying factor `(R + 1) ^ (-psi)`).

Note the direction: for `|x| ≥ R + 1` the reverse of the near-band inequality
holds, since `(|x| / (R + 1)) ^ psi ≥ 1`.  We land both true directional
variants.

Finally, via `Hurst.sum_Ico_rpow_neg_le`, the far band
`∑_{R ≤ j < M} (j + 1) ^ (-2 * psi)` is bounded by the power-sum tail
`(M ^ (1 - 2 * psi) - R ^ (1 - 2 * psi)) / (1 - 2 * psi)` for `2 * psi < 1`,
and in the square-summable regime `1 / 2 < psi` the normalizing factor
`((R : ℝ) + 1) ^ (1 - 2 * psi)` tends to `0`.
-/

open Filter Real

namespace Hurst

/-! ### Single-edge band difference bounds -/

/-- Algebraic identity splitting the single power into a square term:
`|x| ^ (-psi) = |x| ^ psi * |x| ^ (-2 * psi)`. -/
theorem abs_rpow_neg_eq_mul {x psi : ℝ} (hx : 0 < |x|) :
    |x| ^ (-psi) = |x| ^ psi * |x| ^ (-2 * psi) := by
  have h := Real.rpow_add hx psi (-2 * psi)
  rwa [show (psi : ℝ) + -2 * psi = -psi by ring] at h

/-- **Near-band bound**: for `|x| ≤ (R + 1 : ℝ)` the single power `|x| ^ (-psi)`
is dominated by the square term with the band-radius factor:
`|x| ^ (-psi) ≤ (R + 1) ^ psi * |x| ^ (-2 * psi)`. -/
theorem abs_rpow_neg_le_mul_of_le_succ {x : ℝ} (hx : 0 < |x|) {R : ℕ} {psi : ℝ}
    (hpsi : 0 < psi) (hbound : |x| ≤ ((R + 1 : ℕ) : ℝ)) :
    |x| ^ (-psi) ≤ ((R + 1 : ℕ) : ℝ) ^ psi * |x| ^ (-2 * psi) := by
  rw [abs_rpow_neg_eq_mul hx]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (abs_nonneg x) hbound hpsi.le)
    (Real.rpow_nonneg (abs_nonneg x) (-2 * psi))

/-- **Far-band bound**: for `(R + 1 : ℝ) ≤ |x|` the square term is dominated by
the single power with a decaying factor:
`|x| ^ (-2 * psi) ≤ (R + 1) ^ (-psi) * |x| ^ (-psi)`. -/
theorem abs_rpow_neg_two_le_mul_of_lt_succ {x : ℝ} (hx : 0 < |x|) {R : ℕ} {psi : ℝ}
    (hpsi : 0 < psi) (hfar : ((R + 1 : ℕ) : ℝ) ≤ |x|) :
    |x| ^ (-2 * psi) ≤ ((R + 1 : ℕ) : ℝ) ^ (-psi) * |x| ^ (-psi) := by
  have hsplit : |x| ^ (-2 * psi) = |x| ^ (-psi) * |x| ^ (-psi) := by
    have h := Real.rpow_add hx (-psi) (-psi)
    rwa [show (-psi : ℝ) + -psi = -2 * psi by ring] at h
  have hpow : |x| ^ (-psi) ≤ ((R + 1 : ℕ) : ℝ) ^ (-psi) := by
    rw [Real.rpow_neg (abs_nonneg x) psi, Real.rpow_neg (by positivity) psi,
      inv_eq_one_div, inv_eq_one_div]
    exact one_div_le_one_div_of_le
      (Real.rpow_pos_of_pos (by positivity) psi)
      (Real.rpow_le_rpow (by positivity) hfar hpsi.le)
  rw [hsplit]
  exact mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg (abs_nonneg x) (-psi))

/-! ### Far-band square tail -/

/-- **Far-band square tail**: for `0 < psi` with `2 * psi < 1` and `R ≤ M`,
`∑_{R ≤ j < M} (j + 1) ^ (-2 * psi) ≤ (M ^ (1 - 2 * psi) - R ^ (1 - 2 * psi)) / (1 - 2 * psi)`. -/
theorem sum_Ico_rpow_neg_two_le {psi : ℝ} (hpsi : 0 < psi) (hcrit : 2 * psi < 1) (R M : ℕ)
    (hRM : R ≤ M) :
    ∑ j ∈ Finset.Ico R M, ((j + 1 : ℕ) : ℝ) ^ (-2 * psi)
      ≤ (((M : ℝ) ^ (1 - 2 * psi) - (R : ℝ) ^ (1 - 2 * psi))) / (1 - 2 * psi) := by
  simpa using sum_Ico_rpow_neg_le (show (0 : ℝ) < 2 * psi by linarith) hcrit R M hRM

/-- Simplified far-band square tail: `∑_{R ≤ j < M} (j + 1) ^ (-2 * psi) ≤
M ^ (1 - 2 * psi) / (1 - 2 * psi)` for `0 < 2 * psi < 1`. -/
theorem sum_Ico_rpow_neg_two_le' {psi : ℝ} (hpsi : 0 < psi) (hcrit : 2 * psi < 1) (R M : ℕ)
    (hRM : R ≤ M) :
    ∑ j ∈ Finset.Ico R M, ((j + 1 : ℕ) : ℝ) ^ (-2 * psi)
      ≤ ((M : ℝ) ^ (1 - 2 * psi)) / (1 - 2 * psi) := by
  have h := sum_Ico_rpow_neg_two_le hpsi hcrit R M hRM
  have h0 : 0 ≤ (R : ℝ) ^ (1 - 2 * psi) := Real.rpow_nonneg (Nat.cast_nonneg R) _
  have hg : (0 : ℝ) < 1 - 2 * psi := by linarith
  calc ∑ j ∈ Finset.Ico R M, ((j + 1 : ℕ) : ℝ) ^ (-2 * psi)
      ≤ (((M : ℝ) ^ (1 - 2 * psi) - (R : ℝ) ^ (1 - 2 * psi))) / (1 - 2 * psi) := h
    _ ≤ ((M : ℝ) ^ (1 - 2 * psi)) / (1 - 2 * psi) := by
        have hd0 : (1 : ℝ) - 2 * psi ≠ 0 := ne_of_gt hg
        field_simp
        linarith

/-- In the square-summable regime `1 / 2 < psi` (i.e. `2 * psi > 1`), the
normalizing factor `((R : ℝ) + 1) ^ (1 - 2 * psi)` tends to `0`. -/
theorem tendsto_rpow_one_sub_two_psi {psi : ℝ} (hcrit : 1 / 2 < psi) :
    Tendsto (fun R : ℕ => ((R : ℝ) + 1) ^ (1 - 2 * psi)) atTop (nhds 0) := by
  have hy : (0 : ℝ) < 2 * psi - 1 := by linarith
  have key : Tendsto (fun R : ℕ => (((R + 1 : ℕ) : ℝ) ^ (2 * psi - 1))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp ((tendsto_rpow_atTop hy).comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)))
  refine Tendsto.congr' (Eventually.of_forall fun R => ?_) key
  have hbase : ((R : ℝ) + 1) = ((R + 1 : ℕ) : ℝ) := by push_cast; ring
  show (((R + 1 : ℕ) : ℝ) ^ (2 * psi - 1))⁻¹ = ((R : ℝ) + 1) ^ (1 - 2 * psi)
  rw [hbase, show (1 : ℝ) - 2 * psi = -(2 * psi - 1) by ring,
    Real.rpow_neg (by positivity) (2 * psi - 1)]

end Hurst
