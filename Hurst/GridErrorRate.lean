import Hurst.FirstScaleLongRates

/-!
# Cardinality-weighted grid covariance error rates

Rate lemmas discharging `card * gridCovarianceError`-shaped error terms for the
actual-kernel trace transfer: an active-set cardinality prefactor (eventually
`≤ 3 * (n:ℝ) * δ n`, with `δ n ≤ 1`) multiplied by the explicit grid covariance
error `gridCovarianceError b C₀ n = C₀ * (1 + log (2 * n)) * (n⁻¹ + n^{2*b-2})`
or by its square tends to zero.

## Main statements

* `card_gridError_sq_tendsto_zero` — `3 * (n:ℝ) * δ n * gridCovarianceError²  → 0`
  under `b < 3 / 4` (see the deviation note below).
* `natCard_gridError_sq_tendsto_zero` — same for an abstract cardinality `card n`
  with `(card n : ℝ) ≤ 3 * (n:ℝ) * δ n` eventually; the "card ≤ 3n" variant is
  the special case `δ n ≡ 1`.
* `card_gridError_S_psi_tendsto_zero` — linear form
  `3 * (n:ℝ) * δ n * gridCovarianceError * ((n:ℝ) * δ n)^(ψ-1) → 0` under
  `0 < ψ < 1` and `2 * b + ψ < 2`; this is the
  `card * S^{ψ-1} * gridCovarianceError` shape consumed by
  `Hurst/ActualQuadratureFinal`, and it is valid for every `b < 1`, in
  particular `b ∈ [3/4, 1)`.
* `four_card_gridError_sq_tendsto_zero`, `four_card_gridError_S_psi_tendsto_zero`
  — the ×4-constant variants.
* `natCard_gridError_S_psi_tendsto_zero` — the ψ-form with abstract cardinality.

## Deviation from the requested statement

The requested conclusion
`Tendsto (fun n => (3 * (n:ℝ) * δ n) * (gridCovarianceError b C₀ n) ^ 2) atTop (𝓝 0)`
is FALSE under the sole hypothesis `b < 1`: since
`(gridCovarianceError b C₀ n)² = C₀² * (1 + log (2n))² * (n⁻¹ + n^{2*b-2})²`,
multiplying by `3 * (n:ℝ) * δ n` with `δ n ≡ 1` (which satisfies the eventual
bounds `0 < δ n ≤ 1`) produces the summand
`3 * C₀² * (1 + log (2n))² * n^{4*b-3}`, whose exponent is negative iff
`b < 3 / 4`; for `b ∈ [3/4, 1)` the sequence diverges.  (The route sketch
`card * gridErr² ≤ 3n · C₀² (1+log 2n)² · 2(n^{-2} + n^{4b-4})` drops the factor
`n` from the second term: after multiplication it is `n^{4*b-3}`, not `n^{4*b-4}`.)
We therefore require `hb : b < 3 / 4`, matching the existing
`gridCovarianceError_square_row_tendsto`.  The `b < 1` case is rescued by the
linear `S^{ψ-1}`-form `card_gridError_S_psi_tendsto_zero`, whose dominant
exponent is `2 * b + ψ - 2 < 0` under the bandwidth condition `2 * b + ψ < 2`.
-/

noncomputable section
open Set Filter
open scoped Topology
namespace Hurst

set_option maxHeartbeats 1000000

/-- The active-set cardinality times the squared grid covariance error tends to
zero: `3 * (n:ℝ) * δ n * (gridCovarianceError b C₀ n)² → 0` for `b < 3 / 4`
whenever `δ n` is eventually in `(0, 1]`. -/
theorem card_gridError_sq_tendsto_zero
    (C₀ b : ℝ) (hb : b < 3 / 4) (δ : ℕ → ℝ)
    (hδpos : ∀ᶠ n : ℕ in atTop, 0 < δ n) (hδle : ∀ᶠ n : ℕ in atTop, δ n ≤ 1) :
    Tendsto (fun n : ℕ => (3 * (n : ℝ) * δ n) * (gridCovarianceError b C₀ n) ^ 2)
      atTop (𝓝 0) := by
  have h := (gridCovarianceError_square_row_tendsto b C₀ hb).const_mul 3
  simp only [mul_zero] at h
  apply squeeze_zero' _ _ h
  · filter_upwards [eventually_gt_atTop 0, hδpos] with n hn hδpos
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (le_of_lt hδpos))
      (sq_nonneg _)
  · filter_upwards [hδle] with n hδ
    have h3n : 0 ≤ (3 : ℝ) * (n : ℝ) := by positivity
    calc (3 * (n : ℝ) * δ n) * gridCovarianceError b C₀ n ^ 2
        ≤ (3 * (n : ℝ)) * 1 * gridCovarianceError b C₀ n ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hδ h3n) (sq_nonneg _)
      _ = 3 * ((n : ℝ) * gridCovarianceError b C₀ n ^ 2) := by ring

/-- Cardinality-uniform form: for any cardinality function `card` eventually
bounded by `3 * (n:ℝ) * δ n`, `card n * (gridCovarianceError b C₀ n)² → 0`
for `b < 3 / 4`.  The "card ≤ 3n" variant is the case `δ n ≡ 1`. -/
theorem natCard_gridError_sq_tendsto_zero
    (C₀ b : ℝ) (hb : b < 3 / 4) (δ : ℕ → ℝ) (card : ℕ → ℕ)
    (hcard : ∀ᶠ n : ℕ in atTop, (card n : ℝ) ≤ 3 * (n : ℝ) * δ n)
    (hδle : ∀ᶠ n : ℕ in atTop, δ n ≤ 1) :
    Tendsto (fun n : ℕ => (card n : ℝ) * (gridCovarianceError b C₀ n) ^ 2)
      atTop (𝓝 0) := by
  have h := (gridCovarianceError_square_row_tendsto b C₀ hb).const_mul 3
  simp only [mul_zero] at h
  apply squeeze_zero' _ _ h
  · filter_upwards [] with n
    exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  · filter_upwards [hcard, hδle] with n hcard hδ
    have h3n : 0 ≤ (3 : ℝ) * (n : ℝ) := by positivity
    calc (card n : ℝ) * gridCovarianceError b C₀ n ^ 2
        ≤ (3 * (n : ℝ) * δ n) * gridCovarianceError b C₀ n ^ 2 :=
          mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
      _ ≤ (3 * (n : ℝ)) * 1 * gridCovarianceError b C₀ n ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hδ h3n) (sq_nonneg _)
      _ = 3 * ((n : ℝ) * gridCovarianceError b C₀ n ^ 2) := by ring

/-- The linear `S^{ψ-1}`-form consumed by the quadrature-kernel transfer
(`card * S^{ψ-1} * gridCovarianceError`): with `S n = (n:ℝ) * δ n ≤ n` and
`0 < ψ < 1`,
`3 * (n:ℝ) * δ n * gridCovarianceError b C₀ n * (S n)^(ψ-1) → 0`
whenever `2 * b + ψ < 2`.  Unlike the squared form this needs no `b < 3 / 4`
hypothesis, so it covers the whole long-memory range `b < 1`. -/
theorem card_gridError_S_psi_tendsto_zero
    (C₀ b ψ : ℝ) (hC₀ : 0 ≤ C₀) (hψpos : 0 < ψ) (hψlt : ψ < 1) (hb2 : 2 * b + ψ < 2)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n : ℕ in atTop, 0 < δ n) (hδle : ∀ᶠ n : ℕ in atTop, δ n ≤ 1) :
    Tendsto (fun n : ℕ => (3 * (n : ℝ) * δ n) * gridCovarianceError b C₀ n *
      (((n : ℝ) * δ n) ^ (ψ - 1))) atTop (𝓝 0) := by
  have h1 := mesh_log_power_rpow_tendsto (ψ - 1) (by linarith) 1
  have h2 := mesh_log_power_rpow_tendsto (2 * b + ψ - 2) (by linarith) 1
  simp only [pow_one] at h1 h2
  have h := (h1.const_mul (3 * C₀)).add (h2.const_mul (3 * C₀))
  simp only [mul_zero, add_zero] at h
  apply squeeze_zero' _ _ h
  · filter_upwards [eventually_ge_atTop 1, hδpos] with n hn hδpos
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hδ0 : 0 ≤ δ n := le_of_lt hδpos
    have hge : 0 ≤ gridCovarianceError b C₀ n := by
      unfold gridCovarianceError
      have hln := Real.log_nonneg (show (1 : ℝ) ≤ 2 * (n : ℝ) by linarith)
      exact mul_nonneg (mul_nonneg hC₀ (by linarith))
        (add_nonneg (Real.rpow_nonneg hn0.le _) (Real.rpow_nonneg hn0.le _))
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hδ0) hge)
      (Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg _) hδ0) _)
  · filter_upwards [eventually_ge_atTop 1, hδle, hδpos] with n hn hδ hδpos
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hδ0 : 0 ≤ δ n := le_of_lt hδpos
    have hSn0 : 0 ≤ (n : ℝ) * δ n := mul_nonneg (Nat.cast_nonneg n) hδ0
    have hSnpos : (0 : ℝ) < (n : ℝ) * δ n := mul_pos hn0 hδpos
    have hL0 : (0 : ℝ) ≤ 1 + Real.log (2 * (n : ℝ)) := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * (n : ℝ) by linarith)
      linarith
    have e0 : (1 : ℝ) + (ψ - 1) = ψ := by ring
    have e1 : (n : ℝ) * δ n * ((n : ℝ) * δ n) ^ (ψ - 1) = ((n : ℝ) * δ n) ^ ψ := by
      calc (n : ℝ) * δ n * ((n : ℝ) * δ n) ^ (ψ - 1)
          = ((n : ℝ) * δ n) ^ (1 : ℝ) * ((n : ℝ) * δ n) ^ (ψ - 1) := by
            rw [Real.rpow_one]
        _ = ((n : ℝ) * δ n) ^ ((1 : ℝ) + (ψ - 1)) :=
          (Real.rpow_add hSnpos 1 (ψ - 1)).symm
        _ = ((n : ℝ) * δ n) ^ ψ := by rw [e0]
    have hn1 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hSn1 : (n : ℝ) * δ n ≤ (n : ℝ) := by
      have hp := mul_le_mul_of_nonneg_left hδ hn1
      linarith [show (n : ℝ) * 1 = (n : ℝ) from by ring]
    have hSψle : ((n : ℝ) * δ n) ^ ψ ≤ (n : ℝ) ^ ψ :=
      Real.rpow_le_rpow hSn0 hSn1 hψpos.le
    have hK : (0 : ℝ) ≤ C₀ * (1 + Real.log (2 * (n : ℝ))) *
        ((n : ℝ) ^ (-1 : ℝ) + (n : ℝ) ^ (2 * b - 2)) :=
      mul_nonneg (mul_nonneg hC₀ hL0)
        (add_nonneg (Real.rpow_nonneg hn0.le _) (Real.rpow_nonneg hn0.le _))
    have e2 : ψ + (-1 : ℝ) = ψ - 1 := by ring
    have e3 : ψ + (2 * b - 2) = 2 * b + ψ - 2 := by ring
    calc (3 * (n : ℝ) * δ n) * gridCovarianceError b C₀ n *
            ((n : ℝ) * δ n) ^ (ψ - 1)
        = 3 * ((n : ℝ) * δ n) * (C₀ * (1 + Real.log (2 * (n : ℝ))) *
            ((n : ℝ) ^ (-1 : ℝ) + (n : ℝ) ^ (2 * b - 2))) *
            ((n : ℝ) * δ n) ^ (ψ - 1) := by
          unfold gridCovarianceError; ring
      _ = 3 * (((n : ℝ) * δ n) ^ ψ * (C₀ * (1 + Real.log (2 * (n : ℝ))) *
            ((n : ℝ) ^ (-1 : ℝ) + (n : ℝ) ^ (2 * b - 2)))) := by
          rw [← e1]; ring
      _ ≤ 3 * ((n : ℝ) ^ ψ * (C₀ * (1 + Real.log (2 * (n : ℝ))) *
            ((n : ℝ) ^ (-1 : ℝ) + (n : ℝ) ^ (2 * b - 2)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hSψle hK) (by norm_num)
      _ = 3 * C₀ * (1 + Real.log (2 * (n : ℝ))) *
            ((n : ℝ) ^ ψ * ((n : ℝ) ^ (-1 : ℝ) + (n : ℝ) ^ (2 * b - 2))) := by ring
      _ = 3 * C₀ * (1 + Real.log (2 * (n : ℝ))) *
            ((n : ℝ) ^ (ψ - 1) + (n : ℝ) ^ (2 * b + ψ - 2)) := by
          rw [mul_add ((n : ℝ) ^ ψ) ((n : ℝ) ^ (-1 : ℝ)) ((n : ℝ) ^ (2 * b - 2)),
            ← Real.rpow_add hn0, ← Real.rpow_add hn0, e2, e3]
      _ = 3 * C₀ * ((1 + Real.log (2 * (n : ℝ))) * (n : ℝ) ^ (ψ - 1)) +
          3 * C₀ * ((1 + Real.log (2 * (n : ℝ))) * (n : ℝ) ^ (2 * b + ψ - 2)) := by
          ring

/-- The ×4-constant squared variant
`3 * (n:ℝ) * δ n * (4 * gridCovarianceError b C₀ n)² → 0` (`b < 3 / 4`). -/
theorem four_card_gridError_sq_tendsto_zero
    (C₀ b : ℝ) (hb : b < 3 / 4) (δ : ℕ → ℝ)
    (hδpos : ∀ᶠ n : ℕ in atTop, 0 < δ n) (hδle : ∀ᶠ n : ℕ in atTop, δ n ≤ 1) :
    Tendsto (fun n : ℕ => (3 * (n : ℝ) * δ n) * (4 * gridCovarianceError b C₀ n) ^ 2)
      atTop (𝓝 0) := by
  have h := (card_gridError_sq_tendsto_zero C₀ b hb δ hδpos hδle).const_mul 16
  simp only [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [] with n
  ring

/-- The ×4-constant linear `S^{ψ-1}` variant
`3 * (n:ℝ) * δ n * (4 * gridCovarianceError b C₀ n) * ((n:ℝ) * δ n)^(ψ-1) → 0`
(`0 < ψ < 1`, `2 * b + ψ < 2`). -/
theorem four_card_gridError_S_psi_tendsto_zero
    (C₀ b ψ : ℝ) (hC₀ : 0 ≤ C₀) (hψpos : 0 < ψ) (hψlt : ψ < 1) (hb2 : 2 * b + ψ < 2)
    (δ : ℕ → ℝ) (hδpos : ∀ᶠ n : ℕ in atTop, 0 < δ n) (hδle : ∀ᶠ n : ℕ in atTop, δ n ≤ 1) :
    Tendsto (fun n : ℕ => (3 * (n : ℝ) * δ n) * (4 * gridCovarianceError b C₀ n) *
      (((n : ℝ) * δ n) ^ (ψ - 1))) atTop (𝓝 0) := by
  have h := (card_gridError_S_psi_tendsto_zero C₀ b ψ hC₀ hψpos hψlt hb2 δ hδpos hδle).const_mul 4
  simp only [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [] with n
  ring

/-- Cardinality-uniform ψ-form: for any cardinality function `card` eventually
bounded by `3 * (n:ℝ) * δ n`,
`card n * gridCovarianceError b C₀ n * ((n:ℝ) * δ n)^(ψ-1) → 0`
(`0 < ψ < 1`, `2 * b + ψ < 2`). -/
theorem natCard_gridError_S_psi_tendsto_zero
    (C₀ b ψ : ℝ) (hC₀ : 0 ≤ C₀) (hψpos : 0 < ψ) (hψlt : ψ < 1) (hb2 : 2 * b + ψ < 2)
    (δ : ℕ → ℝ) (card : ℕ → ℕ)
    (hcard : ∀ᶠ n : ℕ in atTop, (card n : ℝ) ≤ 3 * (n : ℝ) * δ n)
    (hδpos : ∀ᶠ n : ℕ in atTop, 0 < δ n) (hδle : ∀ᶠ n : ℕ in atTop, δ n ≤ 1) :
    Tendsto (fun n : ℕ => (card n : ℝ) * gridCovarianceError b C₀ n *
      (((n : ℝ) * δ n) ^ (ψ - 1))) atTop (𝓝 0) := by
  have h := card_gridError_S_psi_tendsto_zero C₀ b ψ hC₀ hψpos hψlt hb2 δ hδpos hδle
  apply squeeze_zero' _ _ h
  · filter_upwards [eventually_ge_atTop 1, hδpos] with n hn hδpos
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hδ0 : 0 ≤ δ n := le_of_lt hδpos
    have hge : 0 ≤ gridCovarianceError b C₀ n := by
      unfold gridCovarianceError
      have hln := Real.log_nonneg (show (1 : ℝ) ≤ 2 * (n : ℝ) by linarith)
      exact mul_nonneg (mul_nonneg hC₀ (by linarith))
        (add_nonneg (Real.rpow_nonneg hn0.le _) (Real.rpow_nonneg hn0.le _))
    have hS0 : (0 : ℝ) ≤ (n : ℝ) * δ n := mul_nonneg (Nat.cast_nonneg n) hδ0
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg (card n)) hge)
      (Real.rpow_nonneg hS0 _)
  · filter_upwards [hcard, eventually_ge_atTop 1, hδpos] with n hcard hn hδpos
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hδ0 : 0 ≤ δ n := le_of_lt hδpos
    have hge : 0 ≤ gridCovarianceError b C₀ n := by
      unfold gridCovarianceError
      have hln := Real.log_nonneg (show (1 : ℝ) ≤ 2 * (n : ℝ) by linarith)
      exact mul_nonneg (mul_nonneg hC₀ (by linarith))
        (add_nonneg (Real.rpow_nonneg hn0.le _) (Real.rpow_nonneg hn0.le _))
    have hS0 : (0 : ℝ) ≤ (n : ℝ) * δ n := mul_nonneg (Nat.cast_nonneg n) hδ0
    have hX : (0 : ℝ) ≤ gridCovarianceError b C₀ n * ((n : ℝ) * δ n) ^ (ψ - 1) :=
      mul_nonneg hge (Real.rpow_nonneg hS0 _)
    calc (card n : ℝ) * gridCovarianceError b C₀ n * ((n : ℝ) * δ n) ^ (ψ - 1)
        ≤ (3 * (n : ℝ) * δ n) * gridCovarianceError b C₀ n *
            ((n : ℝ) * δ n) ^ (ψ - 1) := by
          rw [mul_assoc, mul_assoc]
          exact mul_le_mul_of_nonneg_right hcard hX

end Hurst
