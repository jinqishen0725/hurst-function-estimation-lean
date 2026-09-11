import Mathlib

/-!
# Uniform bound for two-factor shifted singular integrals

For `0 < β < 1` we produce an explicit uniform constant `ν` (namely
`ν = 2 * 2 ^ (1 - 2 * β) / (1 - 2 * β)`) such that for all `a b : ℝ`

`∫ x in Icc (-1:ℝ) 1, |x - a| ^ (-β) * |x - b| ^ (-β) ≤ ν`.

The proof reduces the two-factor bound to a single-factor uniform bound via the
pointwise AM-GM inequality `u * v ≤ (u ^ 2 + v ^ 2) / 2`, and the single-factor
bound follows from the translation formulas for interval integrals, monotonicity
of the integral over supersets, and the explicit computation
`∫ x in 0..2, x ^ (-c) = 2 ^ (1 - c) / (1 - c)` for `0 < c < 1`
(`Real.integral_rpow`).
-/

open MeasureTheory Real Set

noncomputable section

namespace Hurst

/-! ### Integrability of shifted power singularities -/

/-- `x ↦ (x - a) ^ (-p)` is interval-integrable on every compact interval
when `p < 1`. -/
theorem intervalIntegrable_comp_sub_rpow {p : ℝ} (hp1 : p < 1) (a u v : ℝ) :
    IntervalIntegrable (fun x : ℝ => (x - a) ^ (-p)) volume u v := by
  have hf : IntervalIntegrable (fun z : ℝ => z ^ (-p)) volume (u - a) (v - a) :=
    intervalIntegral.intervalIntegrable_rpow' (show (-1 : ℝ) < -p by linarith)
  simpa using hf.comp_sub_right a

/-- `x ↦ (a - x) ^ (-p)` is interval-integrable on every compact interval
when `p < 1`. -/
theorem intervalIntegrable_comp_neg_sub_rpow {p : ℝ} (hp1 : p < 1) (a u v : ℝ) :
    IntervalIntegrable (fun x : ℝ => (a - x) ^ (-p)) volume u v := by
  have h0 : IntervalIntegrable (fun z : ℝ => z ^ (-p)) volume (a - v) (a - u) :=
    intervalIntegral.intervalIntegrable_rpow' (show (-1 : ℝ) < -p by linarith)
  have h1 : IntervalIntegrable (fun z : ℝ => (-z) ^ (-p)) volume (u - a) (v - a) := by
    simpa using ((IntervalIntegrable.iff_comp_neg (f := fun z : ℝ => z ^ (-p))).mp h0).symm
  have h3 := h1.comp_sub_right a
  simpa using h3.congr (by
    intro x _
    show (-(x - a)) ^ (-p) = (a - x) ^ (-p)
    rw [neg_sub])

/-- Auxiliary: `x ↦ |x - a| ^ (-p)` is interval-integrable on `[u, v]` for `u ≤ v`
when `p < 1`. -/
private theorem intervalIntegrable_abs_sub_rpow_aux {p : ℝ} (hp1 : p < 1) (a u v : ℝ)
    (huv : u ≤ v) : IntervalIntegrable (fun x : ℝ => |x - a| ^ (-p)) volume u v := by
  by_cases hva : v ≤ a
  · -- the interval lies to the left of `a`: `|x - a| = a - x`
    refine (intervalIntegrable_comp_neg_sub_rpow hp1 a u v).congr ?_
    intro x hx
    have hx2 : x ≤ max u v := hx.2
    rw [max_eq_right huv] at hx2
    show (a - x) ^ (-p) = |x - a| ^ (-p)
    rw [abs_of_nonpos (show x - a ≤ 0 by linarith), neg_sub]
  · by_cases hau : a ≤ u
    · -- the interval lies to the right of `a`: `|x - a| = x - a`
      refine (intervalIntegrable_comp_sub_rpow hp1 a u v).congr ?_
      intro x hx
      have hx1 : min u v < x := hx.1
      rw [min_eq_left huv] at hx1
      show (x - a) ^ (-p) = |x - a| ^ (-p)
      rw [abs_of_nonneg (show 0 ≤ x - a by linarith)]
    · -- `u < a < v`: split at the singularity
      have hlt1 : u < a := lt_of_not_ge hau
      have hlt2 : a < v := lt_of_not_ge hva
      have h1 : IntervalIntegrable (fun x : ℝ => |x - a| ^ (-p)) volume u a :=
        (intervalIntegrable_comp_neg_sub_rpow hp1 a u a).congr (by
          intro x hx
          have hx2 : x ≤ max u a := hx.2
          rw [max_eq_right hlt1.le] at hx2
          show (a - x) ^ (-p) = |x - a| ^ (-p)
          rw [abs_of_nonpos (show x - a ≤ 0 by linarith), neg_sub])
      have h2 : IntervalIntegrable (fun x : ℝ => |x - a| ^ (-p)) volume a v :=
        (intervalIntegrable_comp_sub_rpow hp1 a a v).congr (by
          intro x hx
          have hx1 : min a v < x := hx.1
          rw [min_eq_left hlt2.le] at hx1
          show (x - a) ^ (-p) = |x - a| ^ (-p)
          rw [abs_of_nonneg (show 0 ≤ x - a by linarith)])
      exact h1.trans h2

/-- `x ↦ |x - a| ^ (-p)` is interval-integrable on every compact interval
when `p < 1`. -/
theorem intervalIntegrable_abs_sub_rpow {p : ℝ} (hp1 : p < 1) (a u v : ℝ) :
    IntervalIntegrable (fun x : ℝ => |x - a| ^ (-p)) volume u v := by
  by_cases huv : u ≤ v
  · exact intervalIntegrable_abs_sub_rpow_aux hp1 a u v huv
  · exact (intervalIntegrable_abs_sub_rpow_aux hp1 a v u (lt_of_not_ge huv).le).symm

/-! ### The reference integral and superset monotonicity -/

/-- For `0 < c < 1`, `∫ x in 0..2, x ^ (-c) = 2 ^ (1 - c) / (1 - c)`. -/
theorem integral_rpow_two (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    (∫ x in (0 : ℝ)..2, x ^ (-c)) = 2 ^ (1 - c) / (1 - c) := by
  have h : (∫ x in (0 : ℝ)..2, x ^ (-c))
      = (2 ^ ((-c) + 1) - 0 ^ ((-c) + 1)) / ((-c) + 1) :=
    integral_rpow (Or.inl (show (-1 : ℝ) < -c by linarith))
  rw [h, show (-c) + 1 = 1 - c from by ring,
    Real.zero_rpow (show (1 : ℝ) - c ≠ 0 by linarith)]
  ring

/-- For `0 < c < 1` and `0 ≤ u ≤ v ≤ 2`, the integral of `x ^ (-c)` over `[u, v]`
is at most its integral over `[0, 2]`. -/
theorem integral_rpow_le_two (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 2) :
    (∫ x in u..v, x ^ (-c)) ≤ (∫ x in (0 : ℝ)..2, x ^ (-c)) := by
  have hint1 : IntervalIntegrable (fun x : ℝ => x ^ (-c)) volume 0 u :=
    intervalIntegral.intervalIntegrable_rpow' (show (-1 : ℝ) < -c by linarith)
  have hint2 : IntervalIntegrable (fun x : ℝ => x ^ (-c)) volume u v :=
    intervalIntegral.intervalIntegrable_rpow' (show (-1 : ℝ) < -c by linarith)
  have hint3 : IntervalIntegrable (fun x : ℝ => x ^ (-c)) volume v 2 :=
    intervalIntegral.intervalIntegrable_rpow' (show (-1 : ℝ) < -c by linarith)
  have hint4 : IntervalIntegrable (fun x : ℝ => x ^ (-c)) volume 0 v :=
    intervalIntegral.intervalIntegrable_rpow' (show (-1 : ℝ) < -c by linarith)
  have e : (∫ x in (0 : ℝ)..2, x ^ (-c))
      = (∫ x in (0 : ℝ)..u, x ^ (-c)) + (∫ x in u..v, x ^ (-c))
        + (∫ x in v..2, x ^ (-c)) := by
    conv_lhs => rw [← intervalIntegral.integral_add_adjacent_intervals hint4 hint3]
    rw [intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
  have n1 : 0 ≤ (∫ x in (0 : ℝ)..u, x ^ (-c)) := by
    apply intervalIntegral.integral_nonneg hu
    intro x hx
    exact Real.rpow_nonneg hx.1 _
  have n2 : 0 ≤ (∫ x in u..v, x ^ (-c)) := by
    apply intervalIntegral.integral_nonneg huv
    intro x hx
    exact Real.rpow_nonneg (hu.trans hx.1) _
  have n3 : 0 ≤ (∫ x in v..2, x ^ (-c)) := by
    apply intervalIntegral.integral_nonneg hv
    intro x hx
    exact Real.rpow_nonneg (hu.trans (huv.trans hx.1)) _
  rw [e]
  linarith

/-! ### The single-factor uniform bound -/

/-- Core: for `-1 ≤ a ≤ 1` and `0 < c < 1`,
`∫ x in -1..1, |x - a| ^ (-c) ≤ 2 * 2 ^ (1 - c) / (1 - c)`, by translating the
singularity to the origin and comparing with the reference interval `[0, 2]`. -/
theorem single_factor_interval_core (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (a : ℝ)
    (ham : -1 ≤ a) (ha1 : a ≤ 1) :
    (∫ x in (-1 : ℝ)..1, |x - a| ^ (-c)) ≤ 2 * 2 ^ (1 - c) / (1 - c) := by
  have href := integral_rpow_two c hc0 hc1
  have hsplit : (∫ x in (-1 : ℝ)..1, |x - a| ^ (-c))
      = (∫ x in (-1 : ℝ)..a, |x - a| ^ (-c)) + (∫ x in a..1, |x - a| ^ (-c)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_abs_sub_rpow hc1 a (-1) a)
      (intervalIntegrable_abs_sub_rpow hc1 a a 1)).symm
  have p1 : (∫ x in (-1 : ℝ)..a, |x - a| ^ (-c)) = (∫ x in (0 : ℝ)..(1 + a), x ^ (-c)) := by
    calc ∫ x in (-1 : ℝ)..a, |x - a| ^ (-c)
        = ∫ x in (-1 : ℝ)..a, (a - x) ^ (-c) :=
          intervalIntegral.integral_congr (by
            intro x hx
            have hx2 : x ≤ max (-1) a := hx.2
            rw [max_eq_right (by linarith)] at hx2
            show |x - a| ^ (-c) = (a - x) ^ (-c)
            rw [abs_of_nonpos (show x - a ≤ 0 by linarith), neg_sub])
      _ = ∫ x in (-1 : ℝ)..a, (fun z : ℝ => z ^ (-c)) (a - x) := rfl
      _ = ∫ x in a - a..a - (-1), (fun z : ℝ => z ^ (-c)) x :=
          intervalIntegral.integral_comp_sub_left (fun z : ℝ => z ^ (-c)) a
      _ = ∫ x in (0 : ℝ)..(1 + a), x ^ (-c) := by
          rw [sub_self, sub_neg_eq_add, add_comm a 1]
  have p2 : (∫ x in a..1, |x - a| ^ (-c)) = (∫ x in (0 : ℝ)..(1 - a), x ^ (-c)) := by
    calc ∫ x in a..1, |x - a| ^ (-c)
        = ∫ x in a..1, (x - a) ^ (-c) :=
          intervalIntegral.integral_congr (by
            intro x hx
            have hx1 : min a 1 ≤ x := hx.1
            rw [min_eq_left (by linarith)] at hx1
            show |x - a| ^ (-c) = (x - a) ^ (-c)
            rw [abs_of_nonneg (show 0 ≤ x - a by linarith)])
      _ = ∫ x in a..1, (fun z : ℝ => z ^ (-c)) (x - a) := rfl
      _ = ∫ x in a - a..1 - a, (fun z : ℝ => z ^ (-c)) x :=
          intervalIntegral.integral_comp_sub_right (fun z : ℝ => z ^ (-c)) a
      _ = ∫ x in (0 : ℝ)..(1 - a), x ^ (-c) := by rw [sub_self]
  rw [hsplit, p1, p2]
  have b1 := integral_rpow_le_two c hc0 hc1 (u := 0) (v := 1 + a)
      (by linarith) (by linarith) (by linarith)
  have b2 := integral_rpow_le_two c hc0 hc1 (u := 0) (v := 1 - a)
      (by linarith) (by linarith) (by linarith)
  calc (∫ x in (0 : ℝ)..(1 + a), x ^ (-c)) + (∫ x in (0 : ℝ)..(1 - a), x ^ (-c))
      ≤ (∫ x in (0 : ℝ)..2, x ^ (-c)) + (∫ x in (0 : ℝ)..2, x ^ (-c)) := by linarith
    _ = 2 * 2 ^ (1 - c) / (1 - c) := by rw [href]; ring

/-- Uniform single-factor bound (interval-integral form): for `0 < c < 1` and every
`a : ℝ`, `∫ x in -1..1, |x - a| ^ (-c) ≤ 2 * 2 ^ (1 - c) / (1 - c)`. -/
theorem single_factor_interval (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (a : ℝ) :
    (∫ x in (-1 : ℝ)..1, |x - a| ^ (-c)) ≤ 2 * 2 ^ (1 - c) / (1 - c) := by
  have core := single_factor_interval_core c hc0 hc1
  by_cases ha1 : a ≤ 1
  · by_cases ham : -1 ≤ a
    · exact core a ham ha1
    · -- a < -1: compare pointwise with `a = -1` away from the endpoint `x = -1`
      have hlt : a < -1 := lt_of_not_ge ham
      have hpt : ∀ x ∈ Ioo (-1 : ℝ) 1, |x - a| ^ (-c) ≤ |x - (-1)| ^ (-c) := by
        intro x hx
        have hx1 : -1 < x := hx.1
        rw [abs_of_nonneg (show 0 ≤ x - a by linarith),
          abs_of_nonneg (show 0 ≤ x - (-1) by linarith)]
        exact Real.rpow_le_rpow_of_nonpos (show 0 < x - -1 by linarith)
          (show x - -1 ≤ x - a by linarith) (show (-c) ≤ 0 by linarith)
      have hmono := intervalIntegral.integral_mono_on_of_le_Ioo
        (show (-1 : ℝ) ≤ 1 by linarith)
        (intervalIntegrable_abs_sub_rpow hc1 a (-1) 1)
        (intervalIntegrable_abs_sub_rpow hc1 (-1) (-1) 1)
        hpt
      exact le_trans hmono (core (-1) (by linarith) (by linarith))
  · -- 1 < a: compare pointwise with `a = 1` away from the endpoint `x = 1`
    have hlt : 1 < a := lt_of_not_ge ha1
    have hpt : ∀ x ∈ Ioo (-1 : ℝ) 1, |x - a| ^ (-c) ≤ |x - 1| ^ (-c) := by
      intro x hx
      have hx2 : x < 1 := hx.2
      rw [abs_of_nonpos (show x - a ≤ 0 by linarith), neg_sub,
        abs_of_nonpos (show x - 1 ≤ 0 by linarith), neg_sub]
      exact Real.rpow_le_rpow_of_nonpos (show 0 < 1 - x by linarith)
        (show 1 - x ≤ a - x by linarith) (show (-c) ≤ 0 by linarith)
    have hmono := intervalIntegral.integral_mono_on_of_le_Ioo
      (show (-1 : ℝ) ≤ 1 by linarith)
      (intervalIntegrable_abs_sub_rpow hc1 a (-1) 1)
      (intervalIntegrable_abs_sub_rpow hc1 1 (-1) 1)
      hpt
    exact le_trans hmono (core 1 (by linarith) (by linarith))

/-! ### Bridge to set integrals -/

/-- Set integrals over a closed interval agree with interval integrals. -/
theorem setIntegral_Icc_eq_interval (f : ℝ → ℝ) {u v : ℝ} (huv : u ≤ v) :
    (∫ x in Icc u v, f x) = (∫ x in u..v, f x) := by
  rw [intervalIntegral.integral_of_le huv]
  exact MeasureTheory.setIntegral_congr_set MeasureTheory.Ioc_ae_eq_Icc.symm

/-- **Single-factor uniform bound.** For `0 < c < 1` there is an explicit
`ν = 2 * 2 ^ (1 - c) / (1 - c) > 0` with
`∫ x in Icc (-1:ℝ) 1, |x - a| ^ (-c) ≤ ν` for all `a : ℝ`. -/
theorem single_factor_bound (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    ∃ ν : ℝ, 0 < ν ∧ ∀ a : ℝ, (∫ x in Icc (-1 : ℝ) 1, |x - a| ^ (-c)) ≤ ν := by
  refine ⟨2 * 2 ^ (1 - c) / (1 - c),
    div_pos (mul_pos two_pos (Real.rpow_pos_of_pos two_pos _)) (by linarith), fun a => ?_⟩
  rw [setIntegral_Icc_eq_interval _ (by norm_num)]
  exact single_factor_interval c hc0 hc1 a

/-! ### The two-factor uniform bound -/

/-- **Main result: two-factor shifted singular integral bound.** For `0 < β` with
`2 * β < 1` there is an explicit `ν = 2 * 2 ^ (1 - 2 * β) / (1 - 2 * β) > 0` such
that for all `a b : ℝ`,

`∫ x in Icc (-1:ℝ) 1, |x - a| ^ (-β) * |x - b| ^ (-β) ≤ ν`.

The proof applies the pointwise AM-GM inequality to reduce to the
single-factor bound at exponent `2 * β < 1`. (The finiteness of the bound
requires `2 * β < 1`; this is the hypothesis under which the constant is finite.) -/
theorem two_factor_shift_bound (β : ℝ) (hβ0 : 0 < β) (hβ1 : 2 * β < 1) :
    ∃ ν : ℝ, 0 < ν ∧ ∀ a b : ℝ,
      (∫ x in Icc (-1 : ℝ) 1, |x - a| ^ (-β) * |x - b| ^ (-β)) ≤ ν := by
  refine ⟨2 * 2 ^ (1 - 2 * β) / (1 - 2 * β),
    div_pos (mul_pos two_pos (Real.rpow_pos_of_pos two_pos _)) (by linarith), ?_⟩
  intro a b
  rw [setIntegral_Icc_eq_interval _ (by norm_num)]
  have hF := intervalIntegrable_abs_sub_rpow hβ1 a (-1) 1
  have hG := intervalIntegrable_abs_sub_rpow hβ1 b (-1) 1
  have hsum := hF.add hG
  have hcm := hsum.const_mul (1 / 2 : ℝ)
  have ptw : ∀ x ∈ Icc (-1 : ℝ) 1,
      |x - a| ^ (-β) * |x - b| ^ (-β)
        ≤ (|x - a| ^ (-(2 * β)) + |x - b| ^ (-(2 * β))) / 2 := by
    intro x _
    have h1 : (|x - a| ^ (-β)) ^ 2 = |x - a| ^ (-(2 * β)) := by
      have hrw : (-(2 * β) : ℝ) = (-β) * 2 := by ring
      rw [(Real.rpow_two (|x - a| ^ (-β))).symm, hrw]
      exact (Real.rpow_mul (abs_nonneg (x - a)) (-β) 2).symm
    have h2 : (|x - b| ^ (-β)) ^ 2 = |x - b| ^ (-(2 * β)) := by
      have hrw : (-(2 * β) : ℝ) = (-β) * 2 := by ring
      rw [(Real.rpow_two (|x - b| ^ (-β))).symm, hrw]
      exact (Real.rpow_mul (abs_nonneg (x - b)) (-β) 2).symm
    have am : 2 * (|x - a| ^ (-β)) * (|x - b| ^ (-β))
        ≤ (|x - a| ^ (-β)) ^ 2 + (|x - b| ^ (-β)) ^ 2 := by
      nlinarith [sq_nonneg (|x - a| ^ (-β) - |x - b| ^ (-β))]
    calc |x - a| ^ (-β) * |x - b| ^ (-β)
        ≤ ((|x - a| ^ (-β)) ^ 2 + (|x - b| ^ (-β)) ^ 2) / 2 := by linarith
      _ = (|x - a| ^ (-(2 * β)) + |x - b| ^ (-(2 * β))) / 2 := by rw [h1, h2]
  -- integrability of the product, by domination through AM-GM
  have hprodII : IntervalIntegrable (fun x : ℝ => |x - a| ^ (-β) * |x - b| ^ (-β))
      volume (-1) 1 := by
    have hM : Measurable (fun x : ℝ => |x - a| ^ (-β) * |x - b| ^ (-β)) :=
      (((measurable_id.sub measurable_const).abs).pow measurable_const).mul
        (((measurable_id.sub measurable_const).abs).pow measurable_const)
    have hnorm : ∀ x ∈ Icc (-1 : ℝ) 1,
        ‖(|x - a| ^ (-β) * |x - b| ^ (-β) : ℝ)‖
          ≤ 1 / 2 * (|x - a| ^ (-(2 * β)) + |x - b| ^ (-(2 * β))) := by
      intro x hx
      have h := ptw x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (abs_nonneg (x - a)) _)
        (Real.rpow_nonneg (abs_nonneg (x - b)) _))]
      linarith
    constructor
    · refine hcm.1.mono' hM.aestronglyMeasurable ?_
      exact (MeasureTheory.ae_restrict_mem measurableSet_Ioc).mono fun x hx => by
        have hx1 : -1 < x := hx.1
        have hx2 : x ≤ 1 := hx.2
        exact hnorm x ⟨le_of_lt hx1, hx2⟩
    · refine hcm.2.mono' hM.aestronglyMeasurable ?_
      exact (MeasureTheory.ae_restrict_mem measurableSet_Ioc).mono fun x hx => by
        exact absurd hx.2 (by linarith [hx.1])
  have hmono : (∫ x in (-1 : ℝ)..1, |x - a| ^ (-β) * |x - b| ^ (-β))
      ≤ (∫ x in (-1 : ℝ)..1, 1 / 2 * (|x - a| ^ (-(2 * β)) + |x - b| ^ (-(2 * β)))) := by
    refine intervalIntegral.integral_mono_on (show (-1 : ℝ) ≤ 1 by norm_num) hprodII hcm ?_
    intro x hx
    exact le_trans (ptw x hx) (by linarith)
  have lin : (∫ x in (-1 : ℝ)..1, 1 / 2 * (|x - a| ^ (-(2 * β)) + |x - b| ^ (-(2 * β))))
      = 1 / 2 * ((∫ x in (-1 : ℝ)..1, |x - a| ^ (-(2 * β)))
          + (∫ x in (-1 : ℝ)..1, |x - b| ^ (-(2 * β)))) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add
        (intervalIntegrable_abs_sub_rpow (hp1 := hβ1) a (-1) 1)
        (intervalIntegrable_abs_sub_rpow (hp1 := hβ1) b (-1) 1)]
  have s1 := single_factor_interval (2 * β) (by linarith) hβ1 a
  have s2 := single_factor_interval (2 * β) (by linarith) hβ1 b
  have hle : (∫ x in (-1 : ℝ)..1, |x - a| ^ (-(2 * β)))
      + (∫ x in (-1 : ℝ)..1, |x - b| ^ (-(2 * β)))
      ≤ 2 * 2 ^ (1 - 2 * β) / (1 - 2 * β) + 2 * 2 ^ (1 - 2 * β) / (1 - 2 * β) := by
    linarith [s1, s2]
  refine le_trans hmono ?_
  rw [lin]
  calc (1:ℝ) / 2 * ((∫ x in (-1 : ℝ)..1, |x - a| ^ (-(2 * β)))
          + (∫ x in (-1 : ℝ)..1, |x - b| ^ (-(2 * β))))
      ≤ (1:ℝ) / 2 * (2 * 2 ^ (1 - 2 * β) / (1 - 2 * β)
          + 2 * 2 ^ (1 - 2 * β) / (1 - 2 * β)) :=
        mul_le_mul_of_nonneg_left hle (by norm_num)
    _ ≤ 2 * 2 ^ (1 - 2 * β) / (1 - 2 * β) := by linarith

end Hurst

end
