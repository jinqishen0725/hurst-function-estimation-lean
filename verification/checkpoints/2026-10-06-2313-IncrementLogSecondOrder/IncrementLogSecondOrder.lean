import Hurst.FirstStrideGrid
import Hurst.MidpointKL

/-!
# Second-order increment-norm refinement (takeover9, task 2)

This file refines the per-row increment-norm deviation of the varying-Hurst
grid statistic from the first-order rate `ℓ^(1-b)` (VaryingIncrement.lean /
E5BiasExpansion) to the second-order rate `ℓ^(2-2*b)` on the band
`1/2 < a ≤ b < 1`.

## The exact expansion (hand derivation, verified below in Lean)

Write `v = ℓ^(-h) • (F_k(s+ℓ) - F_h(s))` for the varying increment,
`u' = F_h(s+ℓ) - F_h(s)` the frozen increment (`‖u'‖² = ℓ^(2h)` exactly) and
`w = F_k(s+ℓ) - F_h(s+ℓ)` the parameter mismatch.  Then

`‖v‖² = 1 + ℓ^(-2h) • (2⟨u', w⟩ + ‖w‖²)`,

and the EXACT kernel identities (`harmonizableFeature_inner_formula`,
`harmonizableFeature_norm_sq`, `harmonizableFeature_inner_same`) give, with
`Λ(h,k) := D((h+k)/2)² / (D(h)·D(k))` and
`Φ(q) := (s+ℓ)^(2q) - s^(2q) + ℓ^(2q)`:

* `2⟨u', w⟩ = Λ·Φ((h+k)/2) - Φ(h)`  (in particular `0` at `k = h`);
* `Λ(h,k) - 1 = -‖F_k(1) - F_h(1)‖² / 2`, so `|Λ - 1| ≤ (C_lip)²·|k-h|²/2`
  by the uniform parameter Lipschitz theorem — the normalization mismatch is
  QUADRATIC in `|k-h|` with no smoothness of `D` needed;
* `|Φ(h)| ≤ 3ℓ` (power Lipschitz for exponent `2q ∈ [1, 2)` plus
  `ℓ^(2q) ≤ ℓ`);
* `|Φ((h+k)/2) - Φ(h)| ≤ C·|k-h|·ℓ` (the function `g(x) = x^(h+k) - x^(2h)`
  is `C·|k-h|`-Lipschitz on `[0,1]` because `2h > 1` absorbs the logarithmic
  sensitivity of the power mismatch).

Assembling, with `|k-h| ≤ K·ℓ` and `h ≤ b`:

`|‖v‖² - 1| ≤ C·(1 + K + K² + K³)·ℓ^(2-2b)`.

## Honest-rate registration (deviation from the task-book sketch)

The task book targeted `n^(-(2-b))` (exponent `2-b > 1`).  That rate is NOT
achievable by this route: the normalization `ℓ^(-2h)` eats two powers of the
increment scale, and the surviving terms are `|k-h|·ℓ^(1-2h)` (cross term,
after the exact cancellation) and `(k-h)²·ℓ^(-2h)` (mismatch square), both of
order `ℓ^(2-2h) ≤ ℓ^(2-2b)` at `|k-h| = O(ℓ)`.  Since `2-2b < 1` whenever
`b > 1/2`, the honest rate is NOT of the form `n^(-(1+ε))` with `ε > 0` on
the long-memory band.  Consequence for the endpoint (registered in
Hurst.HBiasSecondOrder and the takeover9 report): the improved bias window is
`γ ≤ 2-2b` (strictly better than the first-order `γ ≤ 1-b` because
`2-2b > 1-b ⟺ b < 1`), but the endpoint rate `γ = f t > 3/4` remains out of
reach of the per-row log route (`2-2b < 1/2 < 3/4 < f t ≤ b`).

No log factor survives: the `ℓ·|log ℓ|` shape of a crude bound on
`ℓ^(h+k) - ℓ^(2h)` is avoided by the same Lipschitz argument (evaluate
`|g(ℓ) - g(0)| ≤ C|k-h|·ℓ`), so the final rate is the clean `ℓ^(2-2b)`.
-/

set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace Hurst

/-! ## Part 0: elementary power-logarithm lemmas -/

/-- `t · e^(-σt) ≤ 1/σ` for `σ > 0`, `t ≥ 0` (the exponential beats the
monomial, via `u ≤ e^u`). -/
theorem mul_exp_neg_le (σ t : ℝ) (hσ : 0 < σ) (ht : 0 ≤ t) :
    t * Real.exp (-σ * t) ≤ 1 / σ := by
  have hu : σ * t ≤ Real.exp (σ * t) := by
    have h1 := Real.add_one_le_exp (σ * t)
    linarith
  have hpos : 0 < Real.exp (-σ * t) := Real.exp_pos _
  have hz : Real.exp (σ * t) * Real.exp (-σ * t) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have h3 : σ * t * Real.exp (-σ * t) ≤ 1 := by
    have h4 : (σ * t) * Real.exp (-σ * t)
        ≤ Real.exp (σ * t) * Real.exp (-σ * t) :=
      mul_le_mul_of_nonneg_right hu hpos.le
    rw [hz] at h4
    exact h4
  calc t * Real.exp (-σ * t)
      = (σ * t * Real.exp (-σ * t)) / σ := by field_simp
    _ ≤ 1 / σ := div_le_div_of_nonneg_right h3 hσ.le

/-- `e^X - 1 ≤ X · e^X` (the exponential form of `1 - e^(-X) ≤ X`). -/
theorem exp_sub_one_le (X : ℝ) : Real.exp X - 1 ≤ X * Real.exp X := by
  have h1 := Real.add_one_le_exp (-X)
  have hm : Real.exp X * Real.exp (-X) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hpos : 0 < Real.exp X := Real.exp_pos _
  nlinarith [h1, hm, hpos]

/-- `z^σ · |log z| ≤ 1/σ` on `(0, 1]`: the power suppresses the logarithm. -/
theorem rpow_mul_abs_log_le (σ z : ℝ) (hσ : 0 < σ) (hz : z ∈ Ioc (0 : ℝ) 1) :
    z ^ σ * |Real.log z| ≤ 1 / σ := by
  have hz1 : 0 < z := hz.1
  have hlog : Real.log z ≤ 0 := Real.log_nonpos hz1.le hz.2
  have hzp : z ^ σ = Real.exp (-σ * |Real.log z|) := by
    have hexpe : Real.log z * σ = -σ * |Real.log z| := by
      rw [abs_of_nonpos hlog]; ring
    rw [Real.rpow_def_of_pos hz1, hexpe]
  rw [hzp, mul_comm]
  exact mul_exp_neg_le σ |Real.log z| hσ (abs_nonneg _)

/-- `1 - z^δ ≤ δ·|log z|` for `δ ≥ 0`, `z ∈ (0, 1]`. -/
theorem one_sub_rpow_le (δ z : ℝ) (hδ : 0 ≤ δ) (hz : z ∈ Ioc (0 : ℝ) 1) :
    1 - z ^ δ ≤ δ * |Real.log z| := by
  have hz1 : 0 < z := hz.1
  have hlog : Real.log z ≤ 0 := Real.log_nonpos hz1.le hz.2
  have hzp : z ^ δ = Real.exp (-δ * |Real.log z|) := by
    have hexpe : Real.log z * δ = -δ * |Real.log z| := by
      rw [abs_of_nonpos hlog]; ring
    rw [Real.rpow_def_of_pos hz1, hexpe]
  have h1 := Real.add_one_le_exp (-δ * |Real.log z|)
  rw [hzp]
  linarith

/-- `z^(-δ) - 1 ≤ δ·|log z|·z^(-δ)` for `δ ≥ 0`, `z ∈ (0, 1]`. -/
theorem rpow_neg_sub_one_le (δ z : ℝ) (hδ : 0 ≤ δ) (hz : z ∈ Ioc (0 : ℝ) 1) :
    z ^ (-δ) - 1 ≤ δ * |Real.log z| * z ^ (-δ) := by
  have hz1 : 0 < z := hz.1
  have hlog : Real.log z ≤ 0 := Real.log_nonpos hz1.le hz.2
  have hzp : z ^ (-δ) = Real.exp (δ * |Real.log z|) := by
    have hexpe : Real.log z * (-δ) = δ * |Real.log z| := by
      rw [abs_of_nonpos hlog]; ring
    rw [Real.rpow_def_of_pos hz1, hexpe]
  rw [hzp]
  exact exp_sub_one_le (δ * |Real.log z|)

/-- **The mismatch sensitivity lemma.**  On `0 ≤ z ≤ 1` and the parameter
window `1/2 < a ≤ h, k`, the power mismatch weighted by the freezing power
`z^(2h-1)` is linear in `|k-h|` uniformly.  This is where `2a > 1` absorbs
the logarithm: `z^(2h-1)·|log z| ≤ 1/(2h-1)` and
`z^(h+k-1)·|log z| ≤ 1/(h+k-1)`, both at most `1/(2a-1)`. -/
theorem rpow_mismatch_le (a h k z : ℝ) (ha : 1 / 2 < a) (hh : a ≤ h) (hkh : a ≤ k)
    (hz : z ∈ Icc (0 : ℝ) 1) :
    |z ^ (2 * h - 1) * (z ^ (k - h) - 1)| ≤ |k - h| / (2 * a - 1) := by
  have h2a : 0 < 2 * a - 1 := by linarith
  have h2h : 0 < 2 * h - 1 := by nlinarith
  have hhk : 0 < h + k - 1 := by nlinarith
  by_cases hz0 : z = 0
  · subst hz0
    have e0 : (0 : ℝ) ^ (2 * h - 1) = 0 := Real.zero_rpow (by linarith)
    rw [e0, zero_mul, abs_zero]
    exact div_nonneg (abs_nonneg _) h2a.le
  · have hz1 : 0 < z := lt_of_le_of_ne hz.1 (Ne.symm hz0)
    have hz11 : z ≤ 1 := hz.2
    have hIoc : z ∈ Ioc (0 : ℝ) 1 := ⟨hz1, hz11⟩
    have hpow : (0 : ℝ) ≤ z ^ (2 * h - 1) := Real.rpow_nonneg hz1.le _
    have hinv : (2 * h - 1)⁻¹ ≤ (2 * a - 1)⁻¹ := by
      rw [inv_le_inv₀ h2h h2a]
      linarith
    have hinv2 : (h + k - 1)⁻¹ ≤ (2 * a - 1)⁻¹ := by
      rw [inv_le_inv₀ hhk h2a]
      linarith
    rcases le_or_gt h k with hle | hlt
    · have hδ : 0 ≤ k - h := by linarith
      have hzle : z ^ (k - h) ≤ 1 := by
        have h5 := Real.rpow_le_rpow_of_exponent_ge hz1 hz11 (by linarith : (0 : ℝ) ≤ k - h)
        rwa [Real.rpow_zero] at h5
      have habs : |z ^ (k - h) - 1| = 1 - z ^ (k - h) := by
        rw [abs_of_nonpos (by nlinarith)]
        ring
      rw [abs_mul, abs_of_nonneg hpow, habs]
      have hone := one_sub_rpow_le (k - h) z hδ hIoc
      have hfin : (k - h) * (1 / (2 * h - 1)) ≤ |k - h| / (2 * a - 1) := by
        rw [abs_of_nonneg hδ, one_div, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left hinv hδ
      calc z ^ (2 * h - 1) * (1 - z ^ (k - h))
          ≤ z ^ (2 * h - 1) * ((k - h) * |Real.log z|) :=
            mul_le_mul_of_nonneg_left hone hpow
        _ = (k - h) * (z ^ (2 * h - 1) * |Real.log z|) := by ring
        _ ≤ (k - h) * (1 / (2 * h - 1)) :=
            mul_le_mul_of_nonneg_left (rpow_mul_abs_log_le (2 * h - 1) z h2h hIoc) hδ
        _ ≤ |k - h| / (2 * a - 1) := hfin
    · have hδ' : 0 ≤ h - k := by linarith
      have hge : (1 : ℝ) ≤ z ^ (k - h) := by
        have h5 := Real.rpow_le_rpow_of_exponent_ge hz1 hz11 (by linarith : k - h ≤ (0 : ℝ))
        rwa [Real.rpow_zero] at h5
      have habs : |z ^ (k - h) - 1| = z ^ (k - h) - 1 := by
        rw [abs_of_nonneg (by nlinarith)]
      have hneg : z ^ (k - h) = z ^ (-(h - k)) := by congr 1; ring
      rw [abs_mul, abs_of_nonneg hpow, habs, hneg]
      have hnegle := rpow_neg_sub_one_le (h - k) z hδ' hIoc
      have hcombine : z ^ (2 * h - 1) * z ^ (-(h - k)) = z ^ (h + k - 1) := by
        have hexpe : (2 * h - 1) + (-(h - k)) = h + k - 1 := by ring
        rw [← Real.rpow_add hz1, hexpe]
      have hfin : (h - k) * (1 / (h + k - 1)) ≤ |k - h| / (2 * a - 1) := by
        rw [abs_of_neg (by linarith : k - h < 0), neg_sub, one_div, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left hinv2 hδ'
      calc z ^ (2 * h - 1) * (z ^ (-(h - k)) - 1)
          ≤ z ^ (2 * h - 1) * ((h - k) * |Real.log z| * z ^ (-(h - k))) :=
            mul_le_mul_of_nonneg_left hnegle hpow
        _ = (h - k) * |Real.log z| * (z ^ (2 * h - 1) * z ^ (-(h - k))) := by ring
        _ = (h - k) * |Real.log z| * z ^ (h + k - 1) := by rw [hcombine]
        _ = (h - k) * (z ^ (h + k - 1) * |Real.log z|) := by ring
        _ ≤ (h - k) * (1 / (h + k - 1)) :=
            mul_le_mul_of_nonneg_left (rpow_mul_abs_log_le (h + k - 1) z hhk hIoc) hδ'
        _ ≤ |k - h| / (2 * a - 1) := hfin

/-! ## Part 1: Lipschitz lemmas on the unit interval -/

/-- A mean-value helper: a derivative bound on a closed interval with
positive left endpoint gives a Lipschitz bound. -/
theorem abs_sub_le_of_hasDerivAt_le {g g' : ℝ → ℝ} {x y C : ℝ} (hxy : x ≤ y)
    (hx : 0 < x) (hd : ∀ z ∈ Icc x y, HasDerivAt g (g' z) z)
    (hb : ∀ z ∈ Icc x y, |g' z| ≤ C) :
    |g y - g x| ≤ C * (y - x) := by
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z hz => (hd z hz).hasDerivWithinAt)
    (fun z hz => by rw [Real.norm_eq_abs]; exact hb z hz)
    (convex_Icc x y) (left_mem_Icc.mpr hxy) (right_mem_Icc.mpr hxy)
  rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hxy)] at hmvt

/-- Power functions with exponent at least `1` are Lipschitz on `[0, 1]`. -/
theorem abs_rpow_pow_sub_le {c x y : ℝ} (hc1 : 1 ≤ c) (hx0 : 0 ≤ x) (hxy : x ≤ y)
    (hy1 : y ≤ 1) :
    |y ^ c - x ^ c| ≤ c * (y - x) := by
  by_cases hx : x = 0
  · subst hx
    have hy0 : (0 : ℝ) ≤ y := hxy
    have hyc : y ^ c ≤ y := by
      have h5 := Real.rpow_le_rpow_of_exponent_ge' hy0 hy1
        (by norm_num : (0 : ℝ) ≤ 1) (by linarith : (1 : ℝ) ≤ c)
      simpa using h5
    have e0 : (0 : ℝ) ^ c = 0 := Real.zero_rpow (by linarith)
    rw [e0, sub_zero, abs_of_nonneg (Real.rpow_nonneg hy0 _)]
    nlinarith [hyc, mul_nonneg (by linarith : (0 : ℝ) ≤ c - 1) hy0]
  · have hx1 : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hx)
    have hxy1 : x ≤ 1 := hxy.trans hy1
    refine abs_sub_le_of_hasDerivAt_le (g := fun z => z ^ c) hxy hx1
      (g' := fun z => c * z ^ (c - 1)) ?_ ?_
    · intro z hz
      have hz1 : 0 < z := lt_of_lt_of_le hx1 hz.1
      exact Real.hasDerivAt_rpow_const (Or.inl hz1.ne')
    · intro z hz
      have hz11 : z ≤ 1 := hz.2.trans hy1
      have hz1 : 0 < z := lt_of_lt_of_le hx1 hz.1
      have hzp : z ^ (c - 1) ≤ 1 := by
        have h5 := Real.rpow_le_rpow_of_exponent_ge' hz1.le hz11
          (by norm_num : (0 : ℝ) ≤ 0) (by linarith : (0 : ℝ) ≤ c - 1)
        simpa using h5
      calc |c * z ^ (c - 1)| = c * z ^ (c - 1) := by
            rw [abs_of_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hz1.le _))]
        _ ≤ c * 1 := mul_le_mul_of_nonneg_left hzp (by linarith)
        _ = c := mul_one c

/-- The triangle inequality for real numbers (local copy of the E5BiasExpansion
lemma, kept so this core file does not depend on the E5 bias stack). -/
theorem abs_add_le' (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  have hrw : x + y = x - (-y) := by ring
  rw [hrw]
  have h2 := abs_sub x (-y)
  rw [abs_neg] at h2
  exact h2

/-- **The mixed-power Lipschitz lemma.**  For parameters in the band
`1/2 < a ≤ h, k ≤ b < 1`, the function `g(z) = z^(h+k) - z^(2h)` is
`(2b/(2a-1) + 1)·|k-h|`-Lipschitz on `[0, 1]`.  The window `2a > 1` absorbs
the logarithmic sensitivity of the power mismatch (lemma
`rpow_mismatch_le`); the endpoint `x = 0` is handled directly through the
factorization `g(y) - g(0) = y·(y^(2h-1)·(y^(k-h) - 1))`. -/
theorem abs_rpow_mixed_sub_le (a b h k x y : ℝ) (ha : 1 / 2 < a) (hb : b < 1)
    (hh : a ≤ h) (hkh : a ≤ k) (hhb : h ≤ b) (hkb : k ≤ b)
    (hx0 : 0 ≤ x) (hxy : x ≤ y) (hy1 : y ≤ 1) :
    |(y ^ (h + k) - y ^ (2 * h)) - (x ^ (h + k) - x ^ (2 * h))| ≤
      (2 * b / (2 * a - 1) + 1) * |k - h| * (y - x) := by
  have h2a : 0 < 2 * a - 1 := by linarith
  have hHK : (0 : ℝ) ≤ h + k := by linarith
  have hsc : (1 : ℝ) / (2 * a - 1) ≤ 2 * b / (2 * a - 1) + 1 := by
    have h1 := div_le_div_of_nonneg_right (show (1 : ℝ) ≤ 2 * b by linarith) h2a.le
    linarith [h1]
  by_cases hx : x = 0
  · subst hx
    have hy0 : (0 : ℝ) ≤ y := hxy
    have e0k : (0 : ℝ) ^ (h + k) = 0 := Real.zero_rpow (by nlinarith [hh, hkh, ha])
    have e0h : (0 : ℝ) ^ (2 * h) = 0 := Real.zero_rpow (by nlinarith [hh, ha])
    rw [e0k, e0h, sub_zero, sub_zero]
    by_cases hy0c : y = 0
    · subst hy0c
      have zz1 : (0 : ℝ) ^ (h + k) = 0 := Real.zero_rpow (by nlinarith [hh, hkh, ha])
      have zz2 : (0 : ℝ) ^ (2 * h) = 0 := Real.zero_rpow (by nlinarith [hh, ha])
      rw [zz1, zz2]
      simp
    · have hy1p : 0 < y := lt_of_le_of_ne hy0 (Ne.symm hy0c)
      have e1 : y ^ (h + k) = y ^ (2 * h) * y ^ (k - h) := by
        have hexpe : (2 * h) + (k - h) = h + k := by ring
        rw [← Real.rpow_add hy1p, hexpe]
      have e2 : y ^ (2 * h) = y * y ^ (2 * h - 1) := by
        have hprev : y ^ (2 * h) = y ^ (1 : ℝ) * y ^ (2 * h - 1) := by
          conv_lhs => rw [show (2 * h : ℝ) = 1 + (2 * h - 1) from by ring]
          rw [Real.rpow_add hy1p]
        rw [hprev, Real.rpow_one]
      have hsplit : y ^ (h + k) - y ^ (2 * h)
          = y * (y ^ (2 * h - 1) * (y ^ (k - h) - 1)) := by
        rw [e1, e2]; ring
      have hmis := rpow_mismatch_le a h k y ha hh hkh ⟨hy0, hy1⟩
      rw [hsplit, abs_mul, abs_of_nonneg hy0, sub_zero]
      have hkey : |k - h| ≤ (2 * b + (2 * a - 1)) * |k - h| := by
        have hbb : (1 : ℝ) ≤ 2 * b + (2 * a - 1) := by linarith
        nlinarith [mul_le_mul_of_nonneg_left hbb (abs_nonneg (k - h))]
      have hconv : (2 * b / (2 * a - 1) + 1) * |k - h| * (2 * a - 1)
          = (2 * b + (2 * a - 1)) * |k - h| := by
        field_simp [h2a.ne']
      calc y * |y ^ (2 * h - 1) * (y ^ (k - h) - 1)|
          ≤ y * (|k - h| / (2 * a - 1)) := mul_le_mul_of_nonneg_left hmis hy0
        _ ≤ y * ((2 * b / (2 * a - 1) + 1) * |k - h|) := by
            refine mul_le_mul_of_nonneg_left ?_ hy0
            rw [div_le_iff₀ h2a, hconv]
            exact hkey
        _ = (2 * b / (2 * a - 1) + 1) * |k - h| * y := by ring
  · have hx1 : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hx)
    refine abs_sub_le_of_hasDerivAt_le (g := fun z => z ^ (h + k) - z ^ (2 * h)) hxy hx1
      (g' := fun z => (h + k) * z ^ (h + k - 1) - 2 * h * z ^ (2 * h - 1)) ?_ ?_
    · intro z hz
      have hz1 : 0 < z := lt_of_lt_of_le hx1 hz.1
      exact (Real.hasDerivAt_rpow_const (Or.inl hz1.ne')).sub
        (Real.hasDerivAt_rpow_const (Or.inl hz1.ne'))
    · intro z hz
      have hz1 : 0 < z := lt_of_lt_of_le hx1 hz.1
      have hz11 : z ≤ 1 := hz.2.trans hy1
      have hpB : (0 : ℝ) ≤ z ^ (2 * h - 1) := Real.rpow_nonneg hz1.le _
      have hBle : z ^ (2 * h - 1) ≤ 1 := by
        have h5 := Real.rpow_le_rpow_of_exponent_ge' hz1.le hz11
          (by linarith : (0 : ℝ) ≤ 0) (by nlinarith [hh, ha] : (0 : ℝ) ≤ 2 * h - 1)
        simpa using h5
      have e3 : z ^ (h + k - 1) = z ^ (2 * h - 1) * z ^ (k - h) := by
        have hexpe : (2 * h - 1) + (k - h) = h + k - 1 := by ring
        rw [← Real.rpow_add hz1, hexpe]
      have hmis := rpow_mismatch_le a h k z ha hh hkh ⟨hz1.le, hz11⟩
      have hsplit : (h + k) * z ^ (h + k - 1) - 2 * h * z ^ (2 * h - 1)
          = (h + k) * (z ^ (2 * h - 1) * (z ^ (k - h) - 1))
            + (k - h) * z ^ (2 * h - 1) := by
        rw [e3]
        ring
      have hAB : |(h + k) * (z ^ (2 * h - 1) * (z ^ (k - h) - 1))|
          = |h + k| * |z ^ (2 * h - 1) * (z ^ (k - h) - 1)| := abs_mul _ _
      have hCD : |(k - h) * z ^ (2 * h - 1)| = |k - h| * z ^ (2 * h - 1) := by
        rw [abs_mul, abs_of_nonneg hpB]
      rw [hsplit]
      calc |(h + k) * (z ^ (2 * h - 1) * (z ^ (k - h) - 1)) + (k - h) * z ^ (2 * h - 1)|
          ≤ |(h + k) * (z ^ (2 * h - 1) * (z ^ (k - h) - 1))|
              + |(k - h) * z ^ (2 * h - 1)| := abs_add_le' _ _
        _ = |h + k| * |z ^ (2 * h - 1) * (z ^ (k - h) - 1)|
              + |k - h| * z ^ (2 * h - 1) := by rw [hAB, hCD]
        _ ≤ (h + k) * |z ^ (2 * h - 1) * (z ^ (k - h) - 1)|
              + |k - h| * z ^ (2 * h - 1) := by rw [abs_of_nonneg hHK]
        _ ≤ (h + k) * (|k - h| / (2 * a - 1)) + |k - h| * z ^ (2 * h - 1) :=
            add_le_add (mul_le_mul_of_nonneg_left hmis hHK) le_rfl
        _ ≤ (h + k) * (|k - h| / (2 * a - 1)) + |k - h| * 1 :=
            add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hBle (abs_nonneg _))
        _ ≤ (2 * b) * (|k - h| / (2 * a - 1)) + |k - h| * 1 := by
            refine add_le_add (mul_le_mul_of_nonneg_right (by linarith) ?_) (le_refl _)
            exact div_nonneg (abs_nonneg _) h2a.le
        _ = (2 * b / (2 * a - 1) + 1) * |k - h| := by
            field_simp [h2a.ne']

/-- The Φ-difference bound: the mixed-exponent second difference of the
increment scale is `O(|k-h|·ℓ)` (the exact-cancellation step of the
second-order refinement). -/
theorem phi_difference_le (a b h k s ℓ : ℝ) (ha : 1 / 2 < a) (hb : b < 1)
    (hh : a ≤ h) (hkh : a ≤ k) (hhb : h ≤ b) (hkb : k ≤ b)
    (hs : 0 ≤ s) (hℓ : 0 < ℓ) (hsℓ : s + ℓ ≤ 1) :
    |((s + ℓ) ^ (h + k) - s ^ (h + k) + ℓ ^ (h + k))
        - ((s + ℓ) ^ (2 * h) - s ^ (2 * h) + ℓ ^ (2 * h))| ≤
      2 * (2 * b / (2 * a - 1) + 1) * |k - h| * ℓ := by
  have hA := abs_rpow_mixed_sub_le a b h k s (s + ℓ) ha hb hh hkh hhb hkb hs
    (by linarith) hsℓ
  have hB0 := abs_rpow_mixed_sub_le a b h k 0 ℓ ha hb hh hkh hhb hkb
    (by norm_num) (by linarith : (0 : ℝ) ≤ ℓ) (by linarith : ℓ ≤ 1)
  rw [Real.zero_rpow (by nlinarith [hh, hkh, ha]),
    Real.zero_rpow (by nlinarith [hh, ha]), sub_zero, sub_zero,
    sub_zero] at hB0
  rw [add_sub_cancel_left] at hA
  have hsplit : ((s + ℓ) ^ (h + k) - s ^ (h + k) + ℓ ^ (h + k))
        - ((s + ℓ) ^ (2 * h) - s ^ (2 * h) + ℓ ^ (2 * h))
      = ((s + ℓ) ^ (h + k) - (s + ℓ) ^ (2 * h)) - (s ^ (h + k) - s ^ (2 * h))
        + (ℓ ^ (h + k) - ℓ ^ (2 * h)) := by ring
  rw [hsplit]
  have htri := abs_add_le'
    (((s + ℓ) ^ (h + k) - (s + ℓ) ^ (2 * h)) - (s ^ (h + k) - s ^ (2 * h)))
    (ℓ ^ (h + k) - ℓ ^ (2 * h))
  calc |(((s + ℓ) ^ (h + k) - (s + ℓ) ^ (2 * h)) - (s ^ (h + k) - s ^ (2 * h)))
        + (ℓ ^ (h + k) - ℓ ^ (2 * h))|
      ≤ |((s + ℓ) ^ (h + k) - (s + ℓ) ^ (2 * h)) - (s ^ (h + k) - s ^ (2 * h))|
          + |ℓ ^ (h + k) - ℓ ^ (2 * h)| := htri
    _ ≤ (2 * b / (2 * a - 1) + 1) * |k - h| * ℓ
        + (2 * b / (2 * a - 1) + 1) * |k - h| * ℓ :=
          add_le_add hA hB0
    _ = 2 * (2 * b / (2 * a - 1) + 1) * |k - h| * ℓ := by ring

/-- The pure-Φ bound: `|Φ(h)| ≤ 3ℓ` (power Lipschitz plus `ℓ^(2h) ≤ ℓ`). -/
theorem phi_self_le (a b h s ℓ : ℝ) (ha : 1 / 2 < a) (hb : b < 1) (hh : a ≤ h)
    (hhb : h ≤ b) (hs : 0 ≤ s) (hℓ : 0 < ℓ) (hsℓ : s + ℓ ≤ 1) :
    |(s + ℓ) ^ (2 * h) - s ^ (2 * h) + ℓ ^ (2 * h)| ≤ 3 * ℓ := by
  have h2h : (1 : ℝ) ≤ 2 * h := by nlinarith [hh, ha]
  have hP := abs_rpow_pow_sub_le (c := 2 * h) h2h hs (by linarith) hsℓ
  rw [add_sub_cancel_left] at hP
  have hℓb : ℓ ^ (2 * h) ≤ ℓ := by
    have h5 := Real.rpow_le_rpow_of_exponent_ge' hℓ.le (by linarith : ℓ ≤ 1)
      (by norm_num : (0 : ℝ) ≤ 1) h2h
    simpa using h5
  have htri := abs_add_le' ((s + ℓ) ^ (2 * h) - s ^ (2 * h)) (ℓ ^ (2 * h))
  calc |((s + ℓ) ^ (2 * h) - s ^ (2 * h)) + ℓ ^ (2 * h)|
      ≤ |(s + ℓ) ^ (2 * h) - s ^ (2 * h)| + |ℓ ^ (2 * h)| := htri
    _ ≤ 2 * h * ℓ + ℓ ^ (2 * h) := by
        rw [abs_of_nonneg (Real.rpow_nonneg hℓ.le _)]
        exact add_le_add hP (le_refl _)
    _ ≤ 2 * h * ℓ + ℓ := add_le_add (le_refl _) hℓb
    _ ≤ 3 * ℓ := by
        nlinarith [mul_nonneg hℓ.le (by linarith : (0 : ℝ) ≤ 1 - h)]

/-! ## Part 3: the spectral cross identities and the main theorem -/

/-- **The cross-parameter norm identity at the reference point `1`.**  The
normalization mismatch `Λ(h,k) = D((h+k)/2)²/(D(h)·D(k))` deviates from `1`
by exactly half the squared parameter-mismatch norm — so the uniform
parameter Lipschitz theorem makes `|Λ - 1| = O(|k-h|²)` with NO smoothness
of `D` required. -/
theorem harmonizableFeature_cross_sub_norm_sq (h k : Ioo (0 : ℝ) 1) :
    ‖harmonizableFeature k 1 - harmonizableFeature h 1‖ ^ 2
      = 2 - 2 * (harmonizableD (((h : ℝ) + k) / 2) ^ 2
          / (harmonizableD h * harmonizableD k)) := by
  rw [norm_sub_sq_real, harmonizableFeature_norm_sq k 1,
    harmonizableFeature_norm_sq h 1, harmonizableFeature_inner_formula k h 1 1,
    show ((k : ℝ) + h) / 2 = ((h : ℝ) + k) / 2 from by ring,
    sub_self, abs_zero, Real.zero_rpow (by nlinarith [k.2.1, h.2.1])]
  simp only [abs_one, Real.one_rpow]
  ring

/-- **The second-order assembly (abstract, small context).**  Given the
exact drift identity `E = ℓ^(-2h)·(R·Φ1 - Φ2 + W)` and the four bounds
(quadratic normalization mismatch `|R - 1|`, `|Φ1|`, `|Φ1 - Φ2|`, `W`) plus
the stride window `X ≤ K·ℓ`, the deviation `|E|` is bounded by
`C·(1+K+K²+K³)·ℓ^(2-2b)`.  Extracted as a standalone lemma to keep the
main theorem's context small (the composite defeq-expansion timeout
landmine of the takeover9 task book). -/
theorem secondOrder_assembly (Clip Cg R Φ1 Φ2 W X K ℓ h b : ℝ)
    (hClip0 : 0 ≤ Clip) (hCg0 : 0 ≤ Cg) (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (hK : 0 ≤ K)
    (hW0 : 0 ≤ W) (hX0 : 0 ≤ X) (hXℓ : X ≤ K * ℓ) (hhb : h ≤ b)
    (hR1 : |R - 1| ≤ (Clip * X) ^ 2 / 2)
    (hΦ1 : |Φ1| ≤ Cg * X * ℓ + 3 * ℓ) (hΦ1diff : |Φ1 - Φ2| ≤ Cg * X * ℓ)
    (hw2 : W ≤ (Clip * X) ^ 2)
    (E : ℝ) (hv3 : E = ℓ ^ (-(2 * h)) * (R * Φ1 - Φ2 + W)) :
    |E| ≤ (Clip ^ 2 * (Cg + 3) + Cg + Clip ^ 2 + 1) * (1 + K + K ^ 2 + K ^ 3)
      * ℓ ^ (2 - 2 * b) := by
  have hKℓ : (0 : ℝ) ≤ K * ℓ := mul_nonneg hK hℓ.le
  have hClip2 : (0 : ℝ) ≤ Clip ^ 2 := by positivity
  have hX2 : X * X ≤ (K * ℓ) * (K * ℓ) := mul_le_mul hXℓ hXℓ hX0 hKℓ
  have hX3 : X * X * X ≤ (K * ℓ) * (K * ℓ) * (K * ℓ) :=
    mul_le_mul hX2 hXℓ hX0 (mul_nonneg hKℓ hKℓ)
  have hℓ2 : ℓ * ℓ ≤ 1 := by nlinarith
  have hR1' : |R - 1| ≤ Clip ^ 2 * (X * X) := by
    have h2 : (Clip * X) ^ 2 / 2 ≤ Clip ^ 2 * (X * X) := by
      have hp : (0 : ℝ) ≤ Clip ^ 2 * (X * X) := by positivity
      nlinarith [hp]
    exact hR1.trans h2
  have hsum1 : (0 : ℝ) ≤ 1 + K + K ^ 2 + K ^ 3 := by
    nlinarith [sq_nonneg K, mul_nonneg (mul_nonneg hK hK) hK]
  have hKKK : K * K * K ≤ 1 + K + K ^ 2 + K ^ 3 := by
    nlinarith [sq_nonneg K, mul_nonneg (mul_nonneg hK hK) hK]
  have hKK : K * K ≤ 1 + K + K ^ 2 + K ^ 3 := by nlinarith [sq_nonneg K]
  have hK1 : K ≤ 1 + K + K ^ 2 + K ^ 3 := by
    nlinarith [sq_nonneg K, mul_nonneg (mul_nonneg hK hK) hK]
  have hinner : |R * Φ1 - Φ2 + W|
      ≤ (Clip ^ 2 * (Cg + 3) + Cg + Clip ^ 2 + 1) * (1 + K + K ^ 2 + K ^ 3) * (ℓ * ℓ) := by
    have hsplit : R * Φ1 - Φ2 + W = (R - 1) * Φ1 + (Φ1 - Φ2) + W := by ring
    have hstep1 : |R * Φ1 - Φ2 + W| ≤ |(R - 1) * Φ1| + |Φ1 - Φ2| + W := by
      rw [hsplit]
      have ht1 := abs_add_le' ((R - 1) * Φ1 + (Φ1 - Φ2)) W
      rw [abs_of_nonneg hW0] at ht1
      exact ht1.trans (add_le_add (abs_add_le' ((R - 1) * Φ1) (Φ1 - Φ2)) (le_refl _))
    have hA1 : |(R - 1) * Φ1| ≤ Clip ^ 2 * (X * X) * (Cg * X * ℓ + 3 * ℓ) := by
      rw [abs_mul]
      exact mul_le_mul hR1' hΦ1 (abs_nonneg Φ1) (by positivity)
    have hA3 : W ≤ Clip ^ 2 * (X * X) := by
      rw [show (Clip * X) ^ 2 = Clip ^ 2 * (X * X) from by ring] at hw2
      exact hw2
    have hmid : |R * Φ1 - Φ2 + W|
        ≤ Clip ^ 2 * (X * X) * (Cg * X * ℓ + 3 * ℓ) + Cg * X * ℓ + Clip ^ 2 * (X * X) :=
      hstep1.trans (add_le_add (add_le_add hA1 hΦ1diff) hA3)
    have hM1 : Cg * Clip ^ 2 * (X * X * X * ℓ) ≤ Cg * Clip ^ 2 * (K * K * K * (ℓ * ℓ)) := by
      have h1 : X * X * X * ℓ ≤ (K * ℓ) * (K * ℓ) * (K * ℓ) * ℓ :=
        mul_le_mul hX3 (le_refl ℓ) hℓ.le (mul_nonneg (mul_nonneg hKℓ hKℓ) hKℓ)
      have hℓ4 : ℓ * ℓ * ℓ * ℓ ≤ ℓ * ℓ := by
        nlinarith [hℓ2, mul_nonneg (mul_nonneg hℓ.le hℓ.le) (mul_nonneg hℓ.le hℓ.le)]
      have h2 : (K * ℓ) * (K * ℓ) * (K * ℓ) * ℓ ≤ (K * K * K) * (ℓ * ℓ) := by
        have hrw : (K * ℓ) * (K * ℓ) * (K * ℓ) * ℓ = (K * K * K) * (ℓ * ℓ * ℓ * ℓ) := by
          ring
        rw [hrw]
        exact mul_le_mul_of_nonneg_left hℓ4 (by positivity)
      exact mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
    have hM2 : 3 * Clip ^ 2 * (X * X * ℓ) ≤ 3 * Clip ^ 2 * (K * K * (ℓ * ℓ)) := by
      have h1 : X * X * ℓ ≤ K * ℓ * (K * ℓ) * ℓ :=
        mul_le_mul hX2 (le_refl ℓ) hℓ.le (mul_nonneg hKℓ hKℓ)
      have hℓ3 : ℓ * ℓ * ℓ ≤ ℓ * ℓ := by
        nlinarith [hℓ2, mul_nonneg (mul_nonneg hℓ.le hℓ.le) hℓ.le]
      have h2 : K * ℓ * (K * ℓ) * ℓ ≤ (K * K) * (ℓ * ℓ) := by
        have hrw : K * ℓ * (K * ℓ) * ℓ = (K * K) * (ℓ * ℓ * ℓ) := by ring
        rw [hrw]
        exact mul_le_mul_of_nonneg_left hℓ3 (by positivity)
      exact mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
    have hM3 : Cg * (X * ℓ) ≤ Cg * (K * (ℓ * ℓ)) := by
      have h1 : X * ℓ ≤ K * (ℓ * ℓ) := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right hXℓ hℓ.le
      exact mul_le_mul_of_nonneg_left h1 hCg0
    have hM4 : Clip ^ 2 * (X * X) ≤ Clip ^ 2 * (K * K * (ℓ * ℓ)) := by
      have h1 : X * X ≤ (K * K) * (ℓ * ℓ) := by
        nlinarith [hX2, mul_nonneg (mul_nonneg hK hK) (mul_nonneg hℓ.le hℓ.le)]
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    have hN1 : Cg * Clip ^ 2 * (K * K * K * (ℓ * ℓ))
        ≤ Cg * Clip ^ 2 * ((1 + K + K ^ 2 + K ^ 3) * (ℓ * ℓ)) := by
      calc Cg * Clip ^ 2 * (K * K * K * (ℓ * ℓ))
          = (Cg * Clip ^ 2 * (K * K * K)) * (ℓ * ℓ) := by ring
        _ ≤ (Cg * Clip ^ 2 * (1 + K + K ^ 2 + K ^ 3)) * (ℓ * ℓ) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hKKK (by positivity : (0 : ℝ) ≤ Cg * Clip ^ 2))
              (by positivity : (0 : ℝ) ≤ ℓ * ℓ)
        _ = Cg * Clip ^ 2 * ((1 + K + K ^ 2 + K ^ 3) * (ℓ * ℓ)) := by ring
    have hN2 : 3 * Clip ^ 2 * (K * K * (ℓ * ℓ))
        ≤ 3 * Clip ^ 2 * ((1 + K + K ^ 2 + K ^ 3) * (ℓ * ℓ)) := by
      calc 3 * Clip ^ 2 * (K * K * (ℓ * ℓ))
          = (3 * Clip ^ 2 * (K * K)) * (ℓ * ℓ) := by ring
        _ ≤ (3 * Clip ^ 2 * (1 + K + K ^ 2 + K ^ 3)) * (ℓ * ℓ) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hKK (by positivity : (0 : ℝ) ≤ 3 * Clip ^ 2))
              (by positivity : (0 : ℝ) ≤ ℓ * ℓ)
        _ = 3 * Clip ^ 2 * ((1 + K + K ^ 2 + K ^ 3) * (ℓ * ℓ)) := by ring
    have hN3 : Cg * (K * (ℓ * ℓ))
        ≤ Cg * ((1 + K + K ^ 2 + K ^ 3) * (ℓ * ℓ)) := by
      calc Cg * (K * (ℓ * ℓ))
          = (Cg * K) * (ℓ * ℓ) := by ring
        _ ≤ (Cg * (1 + K + K ^ 2 + K ^ 3)) * (ℓ * ℓ) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hK1 hCg0)
              (by positivity : (0 : ℝ) ≤ ℓ * ℓ)
        _ = Cg * ((1 + K + K ^ 2 + K ^ 3) * (ℓ * ℓ)) := by ring
    have hN4 : Clip ^ 2 * (K * K * (ℓ * ℓ))
        ≤ Clip ^ 2 * ((1 + K + K ^ 2 + K ^ 3) * (ℓ * ℓ)) := by
      calc Clip ^ 2 * (K * K * (ℓ * ℓ))
          = (Clip ^ 2 * (K * K)) * (ℓ * ℓ) := by ring
        _ ≤ (Clip ^ 2 * (1 + K + K ^ 2 + K ^ 3)) * (ℓ * ℓ) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hKK hClip2)
              (by positivity : (0 : ℝ) ≤ ℓ * ℓ)
        _ = Clip ^ 2 * ((1 + K + K ^ 2 + K ^ 3) * (ℓ * ℓ)) := by ring
    have hT : (0 : ℝ) ≤ (1 + K + K ^ 2 + K ^ 3) * (ℓ * ℓ) := by positivity
    have hcoeffsum : Cg * Clip ^ 2 + 3 * Clip ^ 2 + Cg + Clip ^ 2
        ≤ Clip ^ 2 * (Cg + 3) + Cg + Clip ^ 2 + 1 := by
      nlinarith [mul_nonneg hCg0 hClip2]
    calc |R * Φ1 - Φ2 + W| ≤ Cg * Clip ^ 2 * (X * X * X * ℓ) + 3 * Clip ^ 2 * (X * X * ℓ)
          + (Cg * (X * ℓ) + Clip ^ 2 * (X * X)) := hmid.trans_eq (by ring)
      _ ≤ Cg * Clip ^ 2 * (K * K * K * (ℓ * ℓ)) + 3 * Clip ^ 2 * (K * K * (ℓ * ℓ))
          + (Cg * (K * (ℓ * ℓ)) + Clip ^ 2 * (K * K * (ℓ * ℓ))) :=
            add_le_add (add_le_add hM1 hM2) (add_le_add hM3 hM4)
      _ ≤ (Cg * Clip ^ 2 + 3 * Clip ^ 2 + Cg + Clip ^ 2)
            * ((1 + K + K ^ 2 + K ^ 3) * (ℓ * ℓ)) := by
            linarith [hN1, hN2, hN3, hN4]
      _ ≤ (Clip ^ 2 * (Cg + 3) + Cg + Clip ^ 2 + 1) * (1 + K + K ^ 2 + K ^ 3) * (ℓ * ℓ) := by
            have hdiff : (0 : ℝ) ≤ (Clip ^ 2 * (Cg + 3) + Cg + Clip ^ 2 + 1)
                - (Cg * Clip ^ 2 + 3 * Clip ^ 2 + Cg + Clip ^ 2) := by
              linarith [hcoeffsum]
            nlinarith [hcoeffsum, hT, mul_nonneg hdiff hT]
  rw [hv3, abs_mul, abs_of_nonneg (Real.rpow_nonneg hℓ.le _)]
  have hscale : ℓ ^ (-(2 * h)) ≤ ℓ ^ (2 - 2 * b - 2) :=
    Real.rpow_le_rpow_of_exponent_ge hℓ hℓ1 (by linarith)
  have hmarg : ℓ ^ (2 - 2 * b - 2) * (ℓ * ℓ) = ℓ ^ (2 - 2 * b) := by
    have h2 : ℓ ^ ((2 : ℕ) : ℝ) = ℓ * ℓ := by rw [Real.rpow_natCast, pow_two]
    rw [← h2, ← Real.rpow_add hℓ,
      show (2 - 2 * b - 2) + ((2 : ℕ) : ℝ) = 2 - 2 * b from by push_cast; ring]
  calc ℓ ^ (-(2 * h)) * |R * Φ1 - Φ2 + W|
      ≤ ℓ ^ (2 - 2 * b - 2) * |R * Φ1 - Φ2 + W| :=
        mul_le_mul_of_nonneg_right hscale (abs_nonneg _)
    _ ≤ ℓ ^ (2 - 2 * b - 2)
          * ((Clip ^ 2 * (Cg + 3) + Cg + Clip ^ 2 + 1) * (1 + K + K ^ 2 + K ^ 3) * (ℓ * ℓ)) :=
        mul_le_mul_of_nonneg_left hinner (Real.rpow_nonneg hℓ.le _)
    _ = (Clip ^ 2 * (Cg + 3) + Cg + Clip ^ 2 + 1) * (1 + K + K ^ 2 + K ^ 3) * ℓ ^ (2 - 2 * b) := by
        linear_combination
          ((Clip ^ 2 * (Cg + 3) + Cg + Clip ^ 2 + 1) * (1 + K + K ^ 2 + K ^ 3)) * hmarg

/-- **The second-order increment-norm refinement (main theorem).**  On the
band `1/2 < a ≤ b < 1`, for frozen-varying parameter pairs within one stride
(`|k - h| ≤ K·ℓ`) and interval data `0 ≤ s`, `s + ℓ ≤ 1`, the squared norm of
the normalized varying increment deviates from `1` at the SECOND-ORDER rate
`ℓ^(2-2b)`:

`|‖normalizedVaryingIncrement h k s ℓ‖² - 1| ≤ C·(1+K+K²+K³)·ℓ^(2-2b)`.

Honest-rate note (see the module docstring): the exponent `2-2b < 1` on the
long-memory band, so this is NOT of the form `n^(-(1+ε))`; the task-book
target `2-b` is unattainable by the per-row route. -/
theorem varyingIncrement_norm_sq_secondOrder (a b : ℝ) (ha : 1 / 2 < a)
    (hb : b < 1) (hab : a ≤ b) :
    ∃ C ≥ 0, ∀ h k : Ioo (0 : ℝ) 1, (h : ℝ) ∈ Icc a b → (k : ℝ) ∈ Icc a b →
      ∀ s ℓ K : ℝ, 0 ≤ s → s + ℓ ≤ 1 → 0 < ℓ → 0 ≤ K → |(k : ℝ) - h| ≤ K * ℓ →
        |‖normalizedVaryingIncrement h k s ℓ‖ ^ 2 - 1|
          ≤ C * (1 + K + K ^ 2 + K ^ 3) * ℓ ^ (2 - 2 * b) := by
  have ha' : 0 < a := by linarith
  obtain ⟨Clip, hClip0, hClip⟩ :=
    harmonizableFeature_uniform_parameter_lipschitz a b ha' hb hab
  set Cg := 2 * (2 * b / (2 * a - 1) + 1) with hCgdef
  have hCg0 : 0 ≤ Cg := by
    have h2a : 0 < 2 * a - 1 := by linarith
    have h1 : 0 ≤ 2 * b / (2 * a - 1) := div_nonneg (by linarith) h2a.le
    positivity
  refine ⟨Clip ^ 2 * (Cg + 3) + Cg + Clip ^ 2 + 1, by positivity, ?_⟩
  intro h k hh hk s ℓ K hs hsℓ hℓ hK hkh
  have hℓ1 : ℓ ≤ 1 := by linarith
  have hbb : (h : ℝ) ≤ b := hh.2
  have hkk : (k : ℝ) ≤ b := hk.2
  have hsℓpos : 0 ≤ s + ℓ := add_nonneg hs hℓ.le
  -- the two kernel identities, in raw form first, then abbreviations
  have hL : ‖harmonizableFeature k (s + ℓ) - harmonizableFeature h s‖ ^ 2
      = (s + ℓ) ^ (2 * (k : ℝ)) + s ^ (2 * (h : ℝ))
        - (harmonizableD (((h : ℝ) + k) / 2) ^ 2
            / (harmonizableD h * harmonizableD k))
          * ((s + ℓ) ^ ((h : ℝ) + k) + s ^ ((h : ℝ) + k) - ℓ ^ ((h : ℝ) + k)) := by
    rw [norm_sub_sq_real, harmonizableFeature_norm_sq k (s + ℓ),
      harmonizableFeature_norm_sq h s, harmonizableFeature_inner_formula k h (s + ℓ) s]
    rw [abs_of_nonneg hsℓpos, abs_of_nonneg hs, add_sub_cancel_left,
      abs_of_nonneg hℓ.le,
      show ((k : ℝ) + h) / 2 = ((h : ℝ) + k) / 2 from by ring]
    ring
  have hw : ‖harmonizableFeature k (s + ℓ) - harmonizableFeature h (s + ℓ)‖ ^ 2
      = (s + ℓ) ^ (2 * (k : ℝ)) + (s + ℓ) ^ (2 * (h : ℝ))
        - 2 * (harmonizableD (((h : ℝ) + k) / 2) ^ 2
            / (harmonizableD h * harmonizableD k)) * (s + ℓ) ^ ((h : ℝ) + k) := by
    rw [norm_sub_sq_real, harmonizableFeature_norm_sq k (s + ℓ),
      harmonizableFeature_norm_sq h (s + ℓ),
      harmonizableFeature_inner_formula k h (s + ℓ) (s + ℓ),
      show ((k : ℝ) + h) / 2 = ((h : ℝ) + k) / 2 from by ring,
      abs_of_nonneg hsℓpos, sub_self, abs_zero,
      Real.zero_rpow (by nlinarith [k.2.1, h.2.1])]
    ring
  set R := harmonizableD (((h : ℝ) + k) / 2) ^ 2
    / (harmonizableD h * harmonizableD k) with hRdef
  set Φ1 := (s + ℓ) ^ ((h : ℝ) + k) - s ^ ((h : ℝ) + k) + ℓ ^ ((h : ℝ) + k) with hΦ1def
  set Φ2 := (s + ℓ) ^ (2 * (h : ℝ)) - s ^ (2 * (h : ℝ)) + ℓ ^ (2 * (h : ℝ)) with hΦ2def
  set W := ‖harmonizableFeature k (s + ℓ) - harmonizableFeature h (s + ℓ)‖ ^ 2 with hWdef
  have hW0 : (0 : ℝ) ≤ W := by rw [hWdef]; exact sq_nonneg _
  have hex2 : ‖harmonizableFeature k (s + ℓ) - harmonizableFeature h s‖ ^ 2
      = ℓ ^ (2 * (h : ℝ)) + R * Φ1 - Φ2 + W := by
    rw [hL, hw]
    ring
  have hΦ1diff : |Φ1 - Φ2| ≤ Cg * |(k : ℝ) - h| * ℓ :=
    phi_difference_le a b h k s ℓ ha hb hh.1 hk.1 hbb hkk hs hℓ hsℓ
  have hΦ2 : |Φ2| ≤ 3 * ℓ :=
    phi_self_le a b h s ℓ ha hb hh.1 hbb hs hℓ hsℓ
  have hΦ1 : |Φ1| ≤ Cg * |(k : ℝ) - h| * ℓ + 3 * ℓ := by
    have hsub : Φ1 = (Φ1 - Φ2) + Φ2 := by ring
    rw [hsub]
    exact (abs_add_le' _ _).trans (add_le_add hΦ1diff hΦ2)
  have hR1 : |R - 1| ≤ (Clip * |(k : ℝ) - h|) ^ 2 / 2 := by
    have hnorm := hClip h k hh hk 1 (by norm_num : |(1 : ℝ)| ≤ 1)
    rw [abs_sub_comm] at hnorm
    have hrev : ‖harmonizableFeature k 1 - harmonizableFeature h 1‖
        = ‖harmonizableFeature h 1 - harmonizableFeature k 1‖ := by
      rw [← norm_neg, neg_sub]
    have hsquared : ‖harmonizableFeature h 1 - harmonizableFeature k 1‖ ^ 2
        ≤ (Clip * |(k : ℝ) - h|) ^ 2 := by
      rw [pow_two, pow_two]
      exact mul_le_mul hnorm hnorm (norm_nonneg _) (mul_nonneg hClip0 (abs_nonneg _))
    have habs2 : |2 - 2 * R| = 2 * |R - 1| := by
      calc |2 - 2 * R| = |2 * (1 - R)| := by congr 1; ring
        _ = 2 * |1 - R| := by rw [abs_mul, abs_of_pos two_pos]
        _ = 2 * |R - 1| := by rw [abs_sub_comm]
    have hkey : |2 - 2 * R| ≤ (Clip * |(k : ℝ) - h|) ^ 2 := by
      rw [hRdef, ← harmonizableFeature_cross_sub_norm_sq h k, hrev,
        abs_of_nonneg (sq_nonneg _)]
      exact hsquared
    rw [habs2] at hkey
    linarith [hkey]
  have hw2 : W ≤ (Clip * |(k : ℝ) - h|) ^ 2 := by
    have hnorm := hClip k h hk hh (s + ℓ)
      (show |s + ℓ| ≤ 1 by rw [abs_of_nonneg hsℓpos]; exact hsℓ)
    rw [hWdef, pow_two, pow_two]
    exact mul_le_mul hnorm hnorm (norm_nonneg _) (mul_nonneg hClip0 (abs_nonneg _))
  have hv2 : ‖normalizedVaryingIncrement h k s ℓ‖ ^ 2
      = ℓ ^ (-(2 * (h : ℝ)))
          * ‖harmonizableFeature k (s + ℓ) - harmonizableFeature h s‖ ^ 2 := by
    rw [normalizedVaryingIncrement, norm_smul, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hℓ _), mul_pow,
      ← Real.rpow_natCast, ← Real.rpow_mul hℓ.le]
    congr 2
    ring
  have hc1 : ℓ ^ (-(2 * (h : ℝ))) * ℓ ^ (2 * (h : ℝ)) = 1 := by
    rw [← Real.rpow_add hℓ, neg_add_cancel, Real.rpow_zero]
  have hv3 : ‖normalizedVaryingIncrement h k s ℓ‖ ^ 2 - 1
      = ℓ ^ (-(2 * (h : ℝ))) * (R * Φ1 - Φ2 + W) := by
    rw [hv2, hex2]
    linear_combination hc1
  exact secondOrder_assembly Clip Cg R Φ1 Φ2 W |(k : ℝ) - h| K ℓ (h : ℝ) b
    hClip0 hCg0 hℓ hℓ1 hK hW0 (abs_nonneg _) hkh hbb hR1 hΦ1 hΦ1diff hw2 _ hv3

/-- **The per-row second-order deviation of the actual first-stride
statistic.**  For a Hölder Hurst profile sampled at the grid points, the
squared norm of every first-stride varying increment deviates from `1` at
the second-order rate `n^-(2-2b)` (the grid form of
`varyingIncrement_norm_sq_secondOrder` with the stride window
`K = D·(1+M)` of the uniform Hölder-Lipschitz package). -/
theorem gridStrideFirstActual_norm_sq_secondOrder (p a b M : ℝ) (hp : 1 ≤ p)
    (ha : 1 / 2 < a) (hb : b < 1) (hab : a ≤ b) (hM : 0 ≤ M) :
    ∃ C' ≥ 0, ∀ n : ℕ, 1 < n → ∀ (f : ℝ → ℝ) (hfM : f ∈ hurstHolderClass p M),
      MapsTo f (Ioo (0 : ℝ) 1) (Icc a b) → ∀ i : Fin (n - 1),
        |‖gridStrideFirstActual n 1 (midpointSampleHurst f hfM.1 n) i‖ ^ 2 - 1|
          ≤ C' * (n : ℝ) ^ (-(2 - 2 * b)) := by
  obtain ⟨C, hC, hmain⟩ := varyingIncrement_norm_sq_secondOrder a b ha hb hab
  obtain ⟨D, hD, hLip⟩ := hurstHolder_uniform_lower_derivative_lipschitz p hp
  refine ⟨C * (1 + D * (1 + M) + (D * (1 + M)) ^ 2 + (D * (1 + M)) ^ 3),
    by positivity, ?_⟩
  intro n hn f hfclass hF i
  have hstride : gridStrideFirstActual n 1 (midpointSampleHurst f hfclass.1 n) i
      = normalizedVaryingIncrement
          (midpointSampleHurst f hfclass.1 n (strideFirstLeft n 1 i))
          (midpointSampleHurst f hfclass.1 n (strideFirstRight n 1 i))
          (grid n i.val) (1 / n) := by
    simp only [gridStrideFirstActual, Nat.cast_one]
  have hmemL : grid n (strideFirstLeft n 1 i).val ∈ Ioo (0 : ℝ) 1 :=
    grid_mem n (strideFirstLeft n 1 i).val (by have := hn; omega) (strideFirstLeft n 1 i).isLt
  have hmemR : grid n (strideFirstRight n 1 i).val ∈ Ioo (0 : ℝ) 1 :=
    grid_mem n (strideFirstRight n 1 i).val (by have := hn; omega) (strideFirstRight n 1 i).isLt
  have hstep : grid n (strideFirstRight n 1 i).val
      = grid n i.val + (1 : ℝ) / n := by
    rw [grid_stride_first_step n 1 i, Nat.cast_one]
  have hL : grid n (strideFirstLeft n 1 i).val = grid n i.val := rfl
  have hℓpos : (0 : ℝ) < 1 / n := by positivity
  have hdiffParam : |(midpointSampleHurst f hfclass.1 n (strideFirstRight n 1 i) : ℝ)
        - (midpointSampleHurst f hfclass.1 n (strideFirstLeft n 1 i) : ℝ)|
      ≤ (D * (1 + M)) * (1 / n) := by
    have hfloorpos : (0 : ℕ) < Nat.floor p := by
      have hmono := Nat.floor_mono (a := (1 : ℝ)) hp
      have h1le : (1 : ℕ) ≤ Nat.floor p := by simpa using hmono
      omega
    have hlip := hLip M hM f hfclass 0 hfloorpos
      (grid n (strideFirstLeft n 1 i).val) hmemL
      (grid n (strideFirstRight n 1 i).val) hmemR
    have hdist : |grid n (strideFirstRight n 1 i).val
        - grid n (strideFirstLeft n 1 i).val| = (1 : ℝ) / n := by
      rw [hstep, hL, add_sub_cancel_left, abs_of_pos hℓpos]
    rw [hdist] at hlip
    have hrw : (midpointSampleHurst f hfclass.1 n (strideFirstRight n 1 i) : ℝ)
        - (midpointSampleHurst f hfclass.1 n (strideFirstLeft n 1 i) : ℝ)
        = f (grid n (strideFirstRight n 1 i).val)
          - f (grid n (strideFirstLeft n 1 i).val) := rfl
    rw [hrw]
    simpa only [iteratedDeriv_zero] using hlip
  have hℓ1 : (1 : ℝ) / n ≤ 1 := by
    have hR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    exact (div_le_one hR).mpr (by exact_mod_cast hn.le)
  have hs : (0 : ℝ) ≤ grid n i.val := hmemL.1.le
  have hs1 : (0 : ℝ) ≤ grid n i.val + 1 / n := by positivity
  have hsℓ : grid n i.val + 1 / n ≤ 1 := by
    rw [← hstep]
    exact le_of_lt hmemR.2
  have hbandL : (midpointSampleHurst f hfclass.1 n (strideFirstLeft n 1 i) : ℝ) ∈ Icc a b :=
    hF hmemL
  have hbandR : (midpointSampleHurst f hfclass.1 n (strideFirstRight n 1 i) : ℝ) ∈ Icc a b :=
    hF hmemR
  have hK0 : (0 : ℝ) ≤ D * (1 + M) := by positivity
  have hrpow : (1 / n : ℝ) ^ (2 - 2 * b) = (n : ℝ) ^ (-(2 - 2 * b)) := by
    rw [one_div, ← Real.rpow_neg_one, ← Real.rpow_mul
      (show (0 : ℝ) ≤ (n : ℝ) by exact_mod_cast (by omega : (0 : ℕ) ≤ n))]
    congr 1
    ring
  have herr := hmain
    (midpointSampleHurst f hfclass.1 n (strideFirstLeft n 1 i))
    (midpointSampleHurst f hfclass.1 n (strideFirstRight n 1 i))
    hbandL hbandR (grid n i.val) (1 / n) (D * (1 + M)) hs hsℓ hℓpos hK0 hdiffParam
  rw [hrpow] at herr
  rw [hstride]
  exact herr

end Hurst

#print axioms Hurst.mul_exp_neg_le
#print axioms Hurst.exp_sub_one_le
#print axioms Hurst.rpow_mul_abs_log_le
#print axioms Hurst.one_sub_rpow_le
#print axioms Hurst.rpow_neg_sub_one_le
#print axioms Hurst.rpow_mismatch_le
#print axioms Hurst.abs_sub_le_of_hasDerivAt_le
#print axioms Hurst.abs_rpow_pow_sub_le
#print axioms Hurst.abs_add_le'
#print axioms Hurst.abs_rpow_mixed_sub_le
#print axioms Hurst.phi_difference_le
#print axioms Hurst.phi_self_le
#print axioms Hurst.harmonizableFeature_cross_sub_norm_sq
#print axioms Hurst.secondOrder_assembly
#print axioms Hurst.varyingIncrement_norm_sq_secondOrder
#print axioms Hurst.gridStrideFirstActual_norm_sq_secondOrder
