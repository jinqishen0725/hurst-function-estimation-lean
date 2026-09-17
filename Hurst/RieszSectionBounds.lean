import Mathlib
import Hurst.HSOperatorLayer2
import Hurst.TwoFactorShiftBound

/-!
# Uniform section bounds for the Riesz kernel (§1–§2 of the general-k gate spec)

This file delivers the elementary real-analysis bounds consumed by the general-k
spectral bridge:

* `fract_section_bound` — the singular section integral of the distance power
  `|a - y| ^ (-s)` against the carrier measure `HS.vol` is uniformly bounded by
  `2 + 2 / (1 - s)` for `0 ≤ s < 1` (the carrier interval `HS.I = Icc (-1 : ℝ) 1`
  has length `2`, and the additive slack absorbs the resulting factor
  `2 ^ (1 - s)` via the chord bound `2 ^ (1 - s) ≤ 2 - s`, i.e. weighted AM–GM);
* `rieszKernel_section_sq` / `rieszKernel_section_sq_symm` — uniform `L²` bounds
  `∫ a, |rieszKernel psi c omega (a, y)| ^ 2 ∂vol ≤ c ^ 2 * MR ^ 2 * (2 + 2 / (1 - 2 * psi))`
  (and the transposed section) under the capstone data hypotheses;
* `rieszKernel_section_l1` / `rieszKernel_section_l1_symm` — the analogous `L¹`
  bounds with constant `|c| * MR * (2 + 2 / (1 - psi))`.

NOTE on an amendment of the frozen §5 interface: the four kernel theorems carry
one extra hypothesis `hpsi0 : 0 ≤ psi`.  It is mathematically necessary (Lemma 1
is invoked at `s := psi`, resp. `s := 2 * psi`, and the squared claim is false
for `psi < 0`, e.g. `omega ≡ 1`, `c = MR = 1`, `psi = -1.1`, `y = 1`), and it is
available in the capstone window `0 < psi < 1`.  Everything else matches the
frozen signatures verbatim.
-/

open MeasureTheory Real Set

noncomputable section

namespace HS

/-! ### The chord bound `2 ^ (1 - s) ≤ 2 - s` on `[0, 1]` -/

/-- Weighted AM–GM on `2` and `1`: convexity of `t ↦ 2 ^ t` on `[0, 1]`. -/
private theorem two_rpow_le_two_sub {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (2 : ℝ) ^ (1 - s) ≤ 2 - s := by
  have h := Real.geom_mean_le_arith_mean2_weighted (w₁ := 1 - s) (w₂ := s) (p₁ := 2) (p₂ := 1)
    (by linarith) hs0 (by norm_num) (by norm_num) (by linarith)
  have h2 : (1 - s) * 2 + s * 1 = 2 - s := by ring
  rw [Real.one_rpow, mul_one, h2] at h
  exact h

private theorem sq_le_sq_of_nonneg {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : x ^ 2 ≤ y ^ 2 := by
  have hy : 0 ≤ y := le_trans hx hxy
  have e1 : x ^ 2 = x * x := pow_two x
  have e2 : y ^ 2 = y * y := pow_two y
  have h1 : x * x ≤ x * y := mul_le_mul_of_nonneg_left hxy hx
  have h2 : x * y ≤ y * y := mul_le_mul_of_nonneg_right hxy hy
  rw [e1, e2]
  linarith

/-! ### Transport between the `HS.vol`-indicator integral and the interval integral -/

/-- The section integral of an indicator over the carrier measure equals the
interval integral over `[-1, 1]` (the endpoint is `volume`-null). -/
private theorem indicator_vol_eq_interval (y s : ℝ) :
    (∫ a : ℝ, (I : Set ℝ).indicator (fun a : ℝ => |a - y| ^ (-s)) a ∂vol)
      = (∫ x in (-1 : ℝ)..1, |x - y| ^ (-s) ∂volume) := by
  have hae : Set.Icc (-1 : ℝ) 1 =ᵐ[MeasureTheory.volume] Set.Ioc (-1 : ℝ) 1 :=
    (MeasureTheory.Ioc_ae_eq_Icc' (Real.volume_singleton (a := (-1 : ℝ)))).symm
  rw [MeasureTheory.integral_indicator measurableSet_Icc,
    intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  have hmeas : ((vol : MeasureTheory.Measure ℝ).restrict (I : Set ℝ))
      = MeasureTheory.volume.restrict (Set.Ioc (-1 : ℝ) 1) := by
    have h1 : ((vol : MeasureTheory.Measure ℝ).restrict (I : Set ℝ))
        = (MeasureTheory.volume.restrict (Set.Icc (-1 : ℝ) 1)).restrict (I : Set ℝ) := rfl
    rw [h1, MeasureTheory.Measure.restrict_restrict_of_subset
      (Subset.rfl : (I : Set ℝ) ⊆ (I : Set ℝ)), Measure.restrict_congr_set hae]
  rw [hmeas]

/-! ### §1: the singular section integral -/

/-- Core of Lemma 1: for `0 ≤ s < 1` and every `y`, the integral of `|x - y| ^ (-s)`
over `[-1, 1]` is at most `2 + 2 / (1 - s)`. -/
private theorem section_bound_interval {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (y : ℝ) :
    (∫ x in (-1 : ℝ)..1, |x - y| ^ (-s) ∂volume) ≤ 2 + 2 / (1 - s) := by
  rcases eq_or_lt_of_le hs0 with hs | hs
  · -- `s = 0`: the integrand is `1`, the interval has length `2`
    subst hs
    have hex : -(0 : ℝ) = (0 : ℝ) := by norm_num
    have hnorm : ∀ x : ℝ, |x - y| ^ (-(0:ℝ)) = 1 := fun x => by rw [hex, Real.rpow_zero]
    have hEq : (∫ x in (-1 : ℝ)..1, |x - y| ^ (-(0:ℝ)) ∂volume)
        = ∫ x in (-1 : ℝ)..1, (1 : ℝ) ∂volume :=
      intervalIntegral.integral_congr (f := fun x : ℝ => |x - y| ^ (-(0:ℝ)))
        (g := fun _ => (1 : ℝ)) (fun x _ => hnorm x)
    rw [hEq, intervalIntegral.integral_const (1 : ℝ)]
    norm_num
  · -- `0 < s`: two half-intervals, each bounded via the reference integral on `[0, 2]`
    have hsf := Hurst.single_factor_interval s hs hs1 y
    have hchord := two_rpow_le_two_sub (le_of_lt hs) hs1.le
    have hpos : (0 : ℝ) < 1 - s := by linarith
    calc (∫ x in (-1 : ℝ)..1, |x - y| ^ (-s) ∂volume)
        ≤ 2 * 2 ^ (1 - s) / (1 - s) := hsf
      _ ≤ 2 * (2 - s) / (1 - s) :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hchord (by norm_num)) (by linarith)
      _ = 2 + 2 / (1 - s) := by field_simp [hpos.ne]; ring

/-- **Lemma 1** (with the deliberate additive slack): for `0 ≤ s < 1` and every `y`,
the `HS.vol`-integral of the `I`-indicator of `a ↦ |a - y| ^ (-s)` is at most
`2 + 2 / (1 - s)`. -/
theorem fract_section_bound {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (y : ℝ) :
    ∫ a : ℝ, (I : Set ℝ).indicator (fun a : ℝ => |a - y| ^ (-s)) a ∂vol
      ≤ 2 + 2 / (1 - s) := by
  rw [indicator_vol_eq_interval y]
  exact section_bound_interval hs0 hs1 y

/-! ### §2 helpers -/

/-- Off `I` the carrier measure gives no mass, so the plain distance power and its
`I`-indicator are a.e.-equal against `HS.vol`. -/
private theorem indicator_ae_abs_sub {p : ℝ} (y : ℝ) :
    ((I : Set ℝ).indicator (fun b : ℝ => |b - y| ^ (-p)))
      =ᵐ[vol] (fun a : ℝ => |a - y| ^ (-p)) := by
  filter_upwards [MeasureTheory.ae_restrict_mem
    (measurableSet_Icc : MeasurableSet (I : Set ℝ))] with a ha
  rw [Set.indicator_of_mem ha]

/-- Integrability of the indicator of the distance power against the carrier measure. -/
private theorem integrable_indicator_abs_sub {p : ℝ} (hp : p < 1) (y : ℝ) :
    MeasureTheory.Integrable ((I : Set ℝ).indicator (fun a : ℝ => |a - y| ^ (-p))) vol := by
  have hint := Hurst.intervalIntegrable_abs_sub_rpow hp y (-2 : ℝ) 2
  have h3 : MeasureTheory.IntegrableOn (fun a : ℝ => |a - y| ^ (-p))
      (Set.Ioc (-2 : ℝ) 2) MeasureTheory.volume := by
    have h4 := intervalIntegrable_iff.mp hint
    rwa [Set.uIoc_of_le (by norm_num)] at h4
  have h5 : MeasureTheory.IntegrableOn (fun a : ℝ => |a - y| ^ (-p)) (I : Set ℝ)
      MeasureTheory.volume := by
    refine h3.mono_set ?_
    intro x hx
    have h1x : (-1 : ℝ) ≤ x := hx.1
    have h2x : x ≤ 1 := hx.2
    exact ⟨by linarith, by linarith⟩
  have hmeas : ((vol : MeasureTheory.Measure ℝ).restrict (I : Set ℝ))
      = MeasureTheory.volume.restrict (I : Set ℝ) :=
    MeasureTheory.Measure.restrict_restrict_of_subset
      (Subset.rfl : (I : Set ℝ) ⊆ (I : Set ℝ))
  refine (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr ?_
  show MeasureTheory.Integrable (fun a : ℝ => |a - y| ^ (-p)) ((vol).restrict (I : Set ℝ))
  rw [hmeas]
  exact h5

/-- Integrability of the plain distance power against the carrier measure. -/
private theorem integrable_abs_sub_vol {p : ℝ} (hp : p < 1) (y : ℝ) :
    MeasureTheory.Integrable (fun a : ℝ => |a - y| ^ (-p)) vol :=
  MeasureTheory.Integrable.congr (integrable_indicator_abs_sub hp y) (indicator_ae_abs_sub y)

/-- On the carrier measure, the plain distance-power integral equals the
indicator-form integral of Lemma 1. -/
private theorem integral_abs_sub_vol_eq {p : ℝ} (_hp : p < 1) (y : ℝ) :
    (∫ a : ℝ, |a - y| ^ (-p) ∂vol)
      = (∫ a : ℝ, (I : Set ℝ).indicator (fun b : ℝ => |b - y| ^ (-p)) a ∂vol) :=
  MeasureTheory.integral_congr_ae (indicator_ae_abs_sub y).symm

/-- The indicator of `omega` agrees, as a function, with the indicator of the
constant `omega 0` (constant on `I` by `hconst`, zero off `I`). -/
private theorem indicator_const_of_const {omega : ℝ → ℝ}
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y) :
    ∀ a : ℝ, (I : Set ℝ).indicator omega a = (I : Set ℝ).indicator (fun _ => omega 0) a := by
  have h0mem : (0 : ℝ) ∈ (I : Set ℝ) := ⟨by norm_num, by norm_num⟩
  have hconst0 : ∀ a ∈ (I : Set ℝ), omega a = omega 0 := by
    intro a ha
    have h := hconst a 0
    rwa [Set.indicator_of_mem ha, Set.indicator_of_mem h0mem] at h
  intro a
  by_cases ha : a ∈ (I : Set ℝ)
  · rw [Set.indicator_of_mem ha, Set.indicator_of_mem ha]
    exact hconst0 a ha
  · rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem ha]

/-- The indicator of the constant `omega 0` is `0`/`omega 0`-valued, hence bounded
by `MR` whenever `|omega 0| ≤ MR`. -/
private theorem abs_indicator_const_le {omega : ℝ → ℝ} {MR : ℝ}
    (hbdd : ∀ x : ℝ, |omega x| ≤ MR) :
    ∀ a : ℝ, |(I : Set ℝ).indicator (fun _ => omega 0) a| ≤ MR := by
  have hMR : (0 : ℝ) ≤ MR := le_trans (abs_nonneg (omega 0)) (hbdd 0)
  intro a
  by_cases ha : a ∈ (I : Set ℝ)
  · rw [Set.indicator_of_mem ha]; exact hbdd 0
  · rw [Set.indicator_of_notMem ha, abs_zero]; exact hMR

private theorem abs_sub_rpow_sq {a y psi : ℝ} :
    (|a - y| ^ (-psi)) ^ 2 = |a - y| ^ (-(2 * psi)) := by
  rw [← Real.rpow_natCast (|a - y| ^ (-psi)) 2, ← Real.rpow_mul (abs_nonneg (a - y)),
    show (2:ℝ) * psi = psi * 2 from by ring, ← neg_mul]
  norm_num

/-! ### §2a: the squared section bound -/

/-- **Claim 2a**: uniform `L²` section bound of the Riesz kernel.

NOTE: the hypothesis `hpsi0 : 0 ≤ psi` is an amendment of the frozen interface
(see the module docstring). -/
theorem rieszKernel_section_sq {psi c : ℝ} {omega : ℝ → ℝ} {MR : ℝ}
    (hbdd : ∀ x : ℝ, |omega x| ≤ MR)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y)
    (hpsi : 2 * psi < 1) (hpsi0 : 0 ≤ psi)
    (y : ℝ) :
    ∫ a : ℝ, |rieszKernel psi c omega (a, y)| ^ 2 ∂vol
      ≤ c ^ 2 * MR ^ 2 * (2 + 2 / (1 - 2 * psi)) := by
  have hInd := indicator_const_of_const hconst
  have hbind := abs_indicator_const_le hbdd
  have hk : ∀ a : ℝ, rieszKernel psi c omega (a, y)
      = (I : Set ℝ).indicator (fun _ => omega 0) a * c * |a - y| ^ (-psi) := by
    intro a
    rw [rieszKernel_apply, hInd a]
  have h1 : ∀ a : ℝ, |rieszKernel psi c omega (a, y)|
      = |(I : Set ℝ).indicator (fun _ => omega 0) a| * |c| * (|a - y| ^ (-psi)) := by
    intro a
    rw [hk a, abs_mul, abs_mul, abs_rpow_of_nonneg (abs_nonneg (a - y)), abs_abs]
  have expand : ∀ a : ℝ, |rieszKernel psi c omega (a, y)| ^ 2
      = (|(I : Set ℝ).indicator (fun _ => omega 0) a| * |c| * (|a - y| ^ (-psi))) ^ 2 := by
    intro a
    rw [h1 a]
  have ptw : ∀ a : ℝ, |rieszKernel psi c omega (a, y)| ^ 2
      ≤ c ^ 2 * MR ^ 2 * |a - y| ^ (-(2 * psi)) := by
    intro a
    rw [expand a, ← abs_sub_rpow_sq]
    have hz : (0 : ℝ) ≤ |a - y| ^ (-psi) := Real.rpow_nonneg (abs_nonneg (a - y)) _
    have hx0 : (0 : ℝ) ≤ |(I : Set ℝ).indicator (fun _ => omega 0) a| * |c| * (|a - y| ^ (-psi)) :=
      mul_nonneg (mul_nonneg (abs_nonneg _ ) (abs_nonneg c)) hz
    have h2 : (|(I : Set ℝ).indicator (fun _ => omega 0) a| * |c| * (|a - y| ^ (-psi))) ^ 2
        ≤ (MR * |c| * (|a - y| ^ (-psi))) ^ 2 :=
      sq_le_sq_of_nonneg hx0 (by
        refine mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hbind a) (abs_nonneg c)) hz)
    calc (|(I : Set ℝ).indicator (fun _ => omega 0) a| * |c| * (|a - y| ^ (-psi))) ^ 2
        ≤ (MR * |c| * (|a - y| ^ (-psi))) ^ 2 := h2
      _ = MR ^ 2 * |c| ^ 2 * (|a - y| ^ (-psi)) ^ 2 := by rw [mul_pow, mul_pow]
      _ = c ^ 2 * MR ^ 2 * (|a - y| ^ (-psi)) ^ 2 := by rw [sq_abs c]; ring
  have hintBig : MeasureTheory.Integrable
      (fun a : ℝ => c ^ 2 * MR ^ 2 * |a - y| ^ (-(2 * psi))) vol :=
    MeasureTheory.Integrable.const_mul (integrable_abs_sub_vol (by linarith) y)
      (c ^ 2 * MR ^ 2)
  calc ∫ a : ℝ, |rieszKernel psi c omega (a, y)| ^ 2 ∂vol
      ≤ ∫ a : ℝ, c ^ 2 * MR ^ 2 * |a - y| ^ (-(2 * psi)) ∂vol :=
        MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun a => sq_nonneg _) hintBig
          (Filter.Eventually.of_forall fun a => ptw a)
    _ = c ^ 2 * MR ^ 2 * ∫ a : ℝ, |a - y| ^ (-(2 * psi)) ∂vol := by
        rw [MeasureTheory.integral_const_mul]
    _ = c ^ 2 * MR ^ 2 * ∫ a : ℝ, (I : Set ℝ).indicator
          (fun b : ℝ => |b - y| ^ (-(2 * psi))) a ∂vol := by
        rw [integral_abs_sub_vol_eq (by linarith) y]
    _ ≤ c ^ 2 * MR ^ 2 * (2 + 2 / (1 - 2 * psi)) :=
        mul_le_mul_of_nonneg_left (fract_section_bound (s := 2 * psi) (by linarith) hpsi y)
          (by positivity)

/-! ### §2b: the squared section bound, transposed section -/

/-- **Claim 2b**: uniform `L²` section bound for the transposed section.  The
weight indicator is constant in the integrated variable, so only `hbdd` is needed.

NOTE: the hypothesis `hpsi0 : 0 ≤ psi` is an amendment of the frozen interface
(see the module docstring). -/
theorem rieszKernel_section_sq_symm {psi c : ℝ} {omega : ℝ → ℝ} {MR : ℝ}
    (hbdd : ∀ x : ℝ, |omega x| ≤ MR)
    (hpsi : 2 * psi < 1) (hpsi0 : 0 ≤ psi)
    (y : ℝ) :
    ∫ a : ℝ, |rieszKernel psi c omega (y, a)| ^ 2 ∂vol
      ≤ c ^ 2 * MR ^ 2 * (2 + 2 / (1 - 2 * psi)) := by
  have hbindy : |(I : Set ℝ).indicator omega y| ≤ MR := by
    by_cases ha : y ∈ (I : Set ℝ)
    · rw [Set.indicator_of_mem ha]; exact hbdd y
    · rw [Set.indicator_of_notMem ha, abs_zero]; exact le_trans (abs_nonneg (omega 0)) (hbdd 0)
  have h1 : ∀ a : ℝ, |rieszKernel psi c omega (y, a)|
      = |(I : Set ℝ).indicator omega y| * |c| * (|a - y| ^ (-psi)) := by
    intro a
    rw [rieszKernel_apply, abs_mul, abs_mul, abs_rpow_of_nonneg (abs_nonneg (y - a)), abs_abs,
      abs_sub_comm y a]
  have expand : ∀ a : ℝ, |rieszKernel psi c omega (y, a)| ^ 2
      = (|(I : Set ℝ).indicator omega y| * |c| * (|a - y| ^ (-psi))) ^ 2 := by
    intro a
    rw [h1 a]
  have ptw : ∀ a : ℝ, |rieszKernel psi c omega (y, a)| ^ 2
      ≤ c ^ 2 * MR ^ 2 * |a - y| ^ (-(2 * psi)) := by
    intro a
    rw [expand a, ← abs_sub_rpow_sq]
    have hz : (0 : ℝ) ≤ |a - y| ^ (-psi) := Real.rpow_nonneg (abs_nonneg (a - y)) _
    have hx0 : (0 : ℝ) ≤ |(I : Set ℝ).indicator omega y| * |c| * (|a - y| ^ (-psi)) :=
      mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg c)) hz
    have h2 : (|(I : Set ℝ).indicator omega y| * |c| * (|a - y| ^ (-psi))) ^ 2
        ≤ (MR * |c| * (|a - y| ^ (-psi))) ^ 2 :=
      sq_le_sq_of_nonneg hx0 (by
        refine mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hbindy (abs_nonneg c)) hz)
    calc (|(I : Set ℝ).indicator omega y| * |c| * (|a - y| ^ (-psi))) ^ 2
        ≤ (MR * |c| * (|a - y| ^ (-psi))) ^ 2 := h2
      _ = MR ^ 2 * |c| ^ 2 * (|a - y| ^ (-psi)) ^ 2 := by rw [mul_pow, mul_pow]
      _ = c ^ 2 * MR ^ 2 * (|a - y| ^ (-psi)) ^ 2 := by rw [sq_abs c]; ring
  have hintBig : MeasureTheory.Integrable
      (fun a : ℝ => c ^ 2 * MR ^ 2 * |a - y| ^ (-(2 * psi))) vol :=
    MeasureTheory.Integrable.const_mul (integrable_abs_sub_vol (by linarith) y)
      (c ^ 2 * MR ^ 2)
  calc ∫ a : ℝ, |rieszKernel psi c omega (y, a)| ^ 2 ∂vol
      ≤ ∫ a : ℝ, c ^ 2 * MR ^ 2 * |a - y| ^ (-(2 * psi)) ∂vol :=
        MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun a => sq_nonneg _) hintBig
          (Filter.Eventually.of_forall fun a => ptw a)
    _ = c ^ 2 * MR ^ 2 * ∫ a : ℝ, |a - y| ^ (-(2 * psi)) ∂vol := by
        rw [MeasureTheory.integral_const_mul]
    _ = c ^ 2 * MR ^ 2 * ∫ a : ℝ, (I : Set ℝ).indicator
          (fun b : ℝ => |b - y| ^ (-(2 * psi))) a ∂vol := by
        rw [integral_abs_sub_vol_eq (by linarith) y]
    _ ≤ c ^ 2 * MR ^ 2 * (2 + 2 / (1 - 2 * psi)) :=
        mul_le_mul_of_nonneg_left (fract_section_bound (s := 2 * psi) (by linarith) hpsi y)
          (by positivity)

/-! ### §2c: the `L¹` section bound -/

/-- **Claim 2c**: uniform `L¹` section bound of the Riesz kernel.

NOTE: the hypothesis `hpsi0 : 0 ≤ psi` is an amendment of the frozen interface
(see the module docstring). -/
theorem rieszKernel_section_l1 {psi c : ℝ} {omega : ℝ → ℝ} {MR : ℝ}
    (hbdd : ∀ x : ℝ, |omega x| ≤ MR)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y)
    (hpsi : psi < 1) (hpsi0 : 0 ≤ psi)
    (y : ℝ) :
    ∫ a : ℝ, |rieszKernel psi c omega (a, y)| ∂vol
      ≤ |c| * MR * (2 + 2 / (1 - psi)) := by
  have hMR : (0 : ℝ) ≤ MR := le_trans (abs_nonneg (omega 0)) (hbdd 0)
  have hInd := indicator_const_of_const hconst
  have hbind := abs_indicator_const_le hbdd
  have hk : ∀ a : ℝ, rieszKernel psi c omega (a, y)
      = (I : Set ℝ).indicator (fun _ => omega 0) a * c * |a - y| ^ (-psi) := by
    intro a
    rw [rieszKernel_apply, hInd a]
  have expand : ∀ a : ℝ, |rieszKernel psi c omega (a, y)|
      = |(I : Set ℝ).indicator (fun _ => omega 0) a| * |c| * (|a - y| ^ (-psi)) := by
    intro a
    rw [hk a, abs_mul, abs_mul, abs_rpow_of_nonneg (abs_nonneg (a - y)), abs_abs]
  have ptw : ∀ a : ℝ, |rieszKernel psi c omega (a, y)|
      ≤ |c| * MR * |a - y| ^ (-psi) := by
    intro a
    rw [expand a]
    have hz : (0 : ℝ) ≤ |a - y| ^ (-psi) := Real.rpow_nonneg (abs_nonneg (a - y)) _
    have h1 : |(I : Set ℝ).indicator (fun _ => omega 0) a| * |c| ≤ MR * |c| :=
      mul_le_mul_of_nonneg_right (hbind a) (abs_nonneg c)
    have h2 : |c| * MR = MR * |c| := mul_comm _ _
    rw [h2]
    exact mul_le_mul_of_nonneg_right h1 hz
  have hintBig : MeasureTheory.Integrable
      (fun a : ℝ => |c| * MR * |a - y| ^ (-psi)) vol :=
    MeasureTheory.Integrable.const_mul (integrable_abs_sub_vol hpsi y) (|c| * MR)
  calc ∫ a : ℝ, |rieszKernel psi c omega (a, y)| ∂vol
      ≤ ∫ a : ℝ, |c| * MR * |a - y| ^ (-psi) ∂vol :=
        MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun a => abs_nonneg _) hintBig
          (Filter.Eventually.of_forall fun a => ptw a)
    _ = |c| * MR * ∫ a : ℝ, |a - y| ^ (-psi) ∂vol := by
        rw [MeasureTheory.integral_const_mul]
    _ = |c| * MR * ∫ a : ℝ, (I : Set ℝ).indicator
          (fun b : ℝ => |b - y| ^ (-psi)) a ∂vol := by
        rw [integral_abs_sub_vol_eq hpsi y]
    _ ≤ |c| * MR * (2 + 2 / (1 - psi)) :=
        mul_le_mul_of_nonneg_left (fract_section_bound (s := psi) hpsi0 hpsi y)
          (mul_nonneg (abs_nonneg c) hMR)

/-! ### §2d: the `L¹` section bound, transposed section -/

/-- **Claim 2d**: uniform `L¹` section bound for the transposed section.

NOTE: the hypothesis `hpsi0 : 0 ≤ psi` is an amendment of the frozen interface
(see the module docstring). -/
theorem rieszKernel_section_l1_symm {psi c : ℝ} {omega : ℝ → ℝ} {MR : ℝ}
    (hbdd : ∀ x : ℝ, |omega x| ≤ MR)
    (hpsi : psi < 1) (hpsi0 : 0 ≤ psi)
    (y : ℝ) :
    ∫ a : ℝ, |rieszKernel psi c omega (y, a)| ∂vol
      ≤ |c| * MR * (2 + 2 / (1 - psi)) := by
  have hMR : (0 : ℝ) ≤ MR := le_trans (abs_nonneg (omega 0)) (hbdd 0)
  have hbindy : |(I : Set ℝ).indicator omega y| ≤ MR := by
    by_cases ha : y ∈ (I : Set ℝ)
    · rw [Set.indicator_of_mem ha]; exact hbdd y
    · rw [Set.indicator_of_notMem ha, abs_zero]; exact le_trans (abs_nonneg (omega 0)) (hbdd 0)
  have expand : ∀ a : ℝ, |rieszKernel psi c omega (y, a)|
      = |(I : Set ℝ).indicator omega y| * |c| * (|a - y| ^ (-psi)) := by
    intro a
    rw [rieszKernel_apply, abs_mul, abs_mul, abs_rpow_of_nonneg (abs_nonneg (y - a)), abs_abs,
      abs_sub_comm y a]
  have ptw : ∀ a : ℝ, |rieszKernel psi c omega (y, a)|
      ≤ |c| * MR * |a - y| ^ (-psi) := by
    intro a
    rw [expand a]
    have hz : (0 : ℝ) ≤ |a - y| ^ (-psi) := Real.rpow_nonneg (abs_nonneg (a - y)) _
    have h1 : |(I : Set ℝ).indicator omega y| * |c| ≤ MR * |c| :=
      mul_le_mul_of_nonneg_right hbindy (abs_nonneg c)
    have h2 : |c| * MR = MR * |c| := mul_comm _ _
    rw [h2]
    exact mul_le_mul_of_nonneg_right h1 hz
  have hintBig : MeasureTheory.Integrable
      (fun a : ℝ => |c| * MR * |a - y| ^ (-psi)) vol :=
    MeasureTheory.Integrable.const_mul (integrable_abs_sub_vol hpsi y) (|c| * MR)
  calc ∫ a : ℝ, |rieszKernel psi c omega (y, a)| ∂vol
      ≤ ∫ a : ℝ, |c| * MR * |a - y| ^ (-psi) ∂vol :=
        MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun a => abs_nonneg _) hintBig
          (Filter.Eventually.of_forall fun a => ptw a)
    _ = |c| * MR * ∫ a : ℝ, |a - y| ^ (-psi) ∂vol := by
        rw [MeasureTheory.integral_const_mul]
    _ = |c| * MR * ∫ a : ℝ, (I : Set ℝ).indicator
          (fun b : ℝ => |b - y| ^ (-psi)) a ∂vol := by
        rw [integral_abs_sub_vol_eq hpsi y]
    _ ≤ |c| * MR * (2 + 2 / (1 - psi)) :=
        mul_le_mul_of_nonneg_left (fract_section_bound (s := psi) hpsi0 hpsi y)
          (mul_nonneg (abs_nonneg c) hMR)

end HS

end
