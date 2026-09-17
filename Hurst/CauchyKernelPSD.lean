import Mathlib
import Hurst.RieszOperatorPositivity

/-!
# The Cauchy-kernel PSD certificate: `exp(-u|x-y|)` is positive-definite

Lands the open certificate (a) of `Hurst.RieszOperatorPositivity`:
`kernelPSD_exp_dist : ∀ u > 0, KernelPSD (fun p => exp (-(u * |p.1 - p.2|)))`,
where `KernelPSD K := ∀ f : L2, 0 ≤ ∫∫ K(x,y) f(y) f(x)` over the unit square
(`kpair`, `HSOperatorFoundation`).

## Route (elementary, no Fourier transform)

*One-sided-exponential autocorrelation.*  For `u > 0` and the parameter
`v ∈ (0, exp (4*u)]` (finite measure `dmu u := volume.restrict (Ioc 0 (exp (4*u)))`)
define the bracket

`cbr u v x := 1_{x ≤ 1} * exp (u*(x-1)) * 1_{v < exp (2*u*(1-x))}`.

For `x, y ∈ [-1, 1]` the cutoffs lie in `[1, exp (4*u)]`, and

`∫ v, cbr u v x * cbr u v y = exp (u*(x-1) + u*(y-1)) * exp (2*u*(1 - max x y))
 = exp (u*(x+y) - 2*u*max x y) = exp (-u*|x-y|)`,

the classical tail integral `∫_{max(x,y)}^∞ 2u e^{-2u(t-(x+y)/2)} dt` under the
fixed change of variables `v = exp (2u(1 + 1 - t))`... more precisely
`v = exp (2*u*(1 - (t - 1)))`; the point is that `v` ranges over a
**finite-measure** space, so the triple Fubini needs only the crude bound
`|cbr u v x| ≤ exp u` (valid since the bracket vanishes off `x ≤ 1`, where
`u*(x-1) ≤ u`).

The quadratic form completes to a square:

`∫∫ exp (-u|x-y|) f(x) f(y) = ∫_v (∫ cbr u v x f(x) dx) (∫ cbr u v y f(y) dy)
 = ∫_v (∫ cbr u v x f(x) dx)^2 ≥ 0`,

by three Fubini/congruence steps (`integral_prod`, `integral_prod_swap`,
`integral_prod_mul`) plus `integral_nonneg`.  The kernel identity is used a.e.
on the square (`vol2` is supported on `I × I`).

## Main results

* `abs_cbr_le` — the bracket bound `|cbr u v x| ≤ exp u * 1_{x ≤ 1}`.
* `cbr_pair` — the bracket autocorrelation identity on the square.
* `kernelPSD_exp_dist` — **the certificate**: `KernelPSD` of `exp (-u|x-y|)` for `u > 0`.

This discharges hypothesis `hpoisson` of `kernelPSD_rpow_dist_of_poisson`
(the remaining open certificate there is the Schur-test integrability `hint`).
-/

open MeasureTheory Measure Real Set
open scoped Real

noncomputable section

namespace HS

/-! ### The one-sided exponential bracket and the parameter measure -/

/-- The one-sided exponential bracket: for `x ≤ 1`,
`cbr u v x = exp (u * (x - 1))` if `v < exp (2 * u * (1 - x))`, and `0` otherwise;
it vanishes identically for `x > 1`. -/
def cbr (u v x : ℝ) : ℝ :=
  (Iic (1 : ℝ)).indicator
    (fun w => exp (u * (w - 1)) *
      (Iio (exp (2 * u * (1 - w)))).indicator (fun _ => (1 : ℝ)) v) x

/-- The finite parameter measure `(0, exp (4 * u)]` (Lebesgue). -/
abbrev dmu (u : ℝ) : Measure ℝ := volume.restrict (Ioc 0 (exp (2 * u * 2)))

instance dmuIsFin (u : ℝ) : IsFiniteMeasure (dmu u) := by
  constructor
  simp only [dmu]
  rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  rw [Real.volume_Ioc]
  simp

/-- A positivity helper: `u * z ≤ u` for `0 < u`, `z ≤ 1`. -/
theorem mul_le_mul_one {u z : ℝ} (hu : 0 < u) (hz : z ≤ 1) : u * z ≤ u := by
  have h2 : 0 ≤ u * (1 - z) := mul_nonneg hu.le (by linarith)
  have h3 : u * (1 - z) = u * 1 - u * z := by ring
  rw [h3] at h2
  linarith

/-- `2 * u * (1 - x) ≤ 4 * u` for `0 < u`, `-1 ≤ x`. -/
theorem two_mul_sub_le {u x : ℝ} (hu : 0 < u) (hx : -1 ≤ x) :
    2 * u * (1 - x) ≤ 2 * u * 2 := by
  have h1 : 0 ≤ u * (1 + x) := mul_nonneg hu.le (by linarith)
  have h2 : 2 * u * (1 - x) + 2 * (u * (1 + x)) = 2 * u * 2 := by ring
  linarith

/-- The bracket bound: `|cbr u v x| ≤ exp u` on the half-line `x ≤ 1`. -/
theorem abs_cbr_le (u : ℝ) (hu : 0 < u) (x v : ℝ) :
    |cbr u v x| ≤ exp u * (Iic (1 : ℝ)).indicator (fun _ => (1 : ℝ)) x := by
  unfold cbr
  by_cases hx : x ≤ 1
  · rw [Set.indicator_of_mem (Set.mem_Iic.mpr hx)]
    show |exp (u * (x - 1)) * (Iio (exp (2 * u * (1 - x)))).indicator (fun _ => (1 : ℝ)) v|
        ≤ exp u * (Iic (1 : ℝ)).indicator (fun _ => (1 : ℝ)) x
    rw [Set.indicator_of_mem (Set.mem_Iic.mpr hx), mul_one, abs_mul,
      abs_of_nonneg (exp_pos _).le, abs_of_nonneg
        (Set.indicator_nonneg (fun w _ => zero_le_one) v)]
    by_cases hv : v ∈ Iio (exp (2 * u * (1 - x)))
    · rw [Set.indicator_of_mem hv, mul_one]
      exact exp_le_exp.mpr (mul_le_mul_one hu (by linarith))
    · rw [Set.indicator_of_notMem hv, mul_zero]
      exact (exp_pos u).le
  · rw [Set.indicator_of_notMem (fun h => by linarith [Set.mem_Iic.mp h]), abs_zero]
    exact mul_nonneg (exp_pos _).le
      (Set.indicator_nonneg (fun w _ => zero_le_one) x)

/-- The bracket `cbr u · ·` is measurable as a function of the pair
`(v, x)`: it is the single indicator of the measurable set
`{p | p.2 ≤ 1 ∧ p.1 < exp (2 * u * (1 - p.2))}` times a measurable function. -/
theorem measurable_cbr_uv (u : ℝ) :
    Measurable (fun p : ℝ × ℝ => cbr u p.1 p.2) := by
  have hS : MeasurableSet {p : ℝ × ℝ | p.2 ≤ 1 ∧ p.1 < exp (2 * u * (1 - p.2))} := by
    have h1 : MeasurableSet ((fun p : ℝ × ℝ => p.2) ⁻¹' (Iic (1 : ℝ))) :=
      measurableSet_Iic.preimage measurable_snd
    have h2 : MeasurableSet
        ((fun p : ℝ × ℝ => exp (2 * u * (1 - p.2)) - p.1) ⁻¹' (Ioi (0 : ℝ))) :=
      measurableSet_Ioi.preimage
        (((measurable_const.sub measurable_snd).const_mul _).exp.sub measurable_fst)
    have he : {p : ℝ × ℝ | p.2 ≤ 1 ∧ p.1 < exp (2 * u * (1 - p.2))}
        = ((fun p : ℝ × ℝ => p.2) ⁻¹' (Iic (1 : ℝ))) ∩
            ((fun p : ℝ × ℝ => exp (2 * u * (1 - p.2)) - p.1) ⁻¹' (Ioi (0 : ℝ))) := by
      ext p
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨Set.mem_Iic.mpr h1,
          Set.mem_preimage.mpr (Set.mem_Ioi.mpr (by linarith))⟩
      · rintro ⟨h1, h2⟩
        have h3 : 0 < exp (2 * u * (1 - p.2)) - p.1 :=
          Set.mem_Ioi.mp (Set.mem_preimage.mp h2)
        exact ⟨Set.mem_Iic.mp h1, by linarith⟩
    rw [he]
    exact h1.inter h2
  have hf : Measurable (fun p : ℝ × ℝ => exp (u * (p.2 - 1))) :=
    (measurable_const.mul (measurable_snd.sub measurable_const)).exp
  have hpt : ∀ p : ℝ × ℝ, cbr u p.1 p.2
      = {p : ℝ × ℝ | p.2 ≤ 1 ∧ p.1 < exp (2 * u * (1 - p.2))}.indicator
          (fun p => exp (u * (p.2 - 1))) p := by
    intro p
    unfold cbr
    by_cases h1 : p.2 ≤ 1
    · rw [Set.indicator_of_mem (Set.mem_Iic.mpr h1)]
      by_cases h2 : p.1 < exp (2 * u * (1 - p.2))
      · rw [Set.indicator_of_mem (Set.mem_Iio.mpr h2), mul_one,
          Set.indicator_of_mem (Set.mem_setOf.mpr ⟨h1, h2⟩)]
      · rw [Set.indicator_of_notMem (fun hmem => h2 (Set.mem_Iio.mp hmem)), mul_zero,
          Set.indicator_of_notMem (fun hmem => h2 hmem.2)]
    · rw [Set.indicator_of_notMem (fun hmem => h1 (Set.mem_Iic.mp hmem)),
        Set.indicator_of_notMem (fun hmem => h1 hmem.1)]
  simp only [hpt]
  exact hf.indicator hS

/-- **The bracket autocorrelation identity**: for `u > 0` and `x, y ∈ [-1, 1]`,
`∫ v, cbr u v x * cbr u v y ∂(dmu u) = exp (-u * |x - y|)`. -/
theorem cbr_pair (u : ℝ) (hu : 0 < u) {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I) :
    ∫ v : ℝ, cbr u v x * cbr u v y ∂(dmu u) = exp (-(u * |x - y|)) := by
  obtain ⟨hxlo, hx1⟩ : -1 ≤ x ∧ x ≤ 1 := hx
  obtain ⟨hylo, hy1⟩ : -1 ≤ y ∧ y ≤ 1 := hy
  have hpx : 0 ≤ u * (1 - x) := mul_nonneg hu.le (by linarith)
  have hpy : 0 ≤ u * (1 - y) := mul_nonneg hu.le (by linarith)
  have hcx1 : 1 ≤ exp (2 * u * (1 - x)) := by
    have h := exp_le_exp.mpr (show (0:ℝ) ≤ 2 * u * (1 - x) from by linarith)
    rwa [exp_zero] at h
  have hcy1 : 1 ≤ exp (2 * u * (1 - y)) := by
    have h := exp_le_exp.mpr (show (0:ℝ) ≤ 2 * u * (1 - y) from by linarith)
    rwa [exp_zero] at h
  have hcxE : exp (2 * u * (1 - x)) ≤ exp (2 * u * 2) := exp_le_exp.mpr (two_mul_sub_le hu hxlo)
  have hcyE : exp (2 * u * (1 - y)) ≤ exp (2 * u * 2) := exp_le_exp.mpr (two_mul_sub_le hu hylo)
  have hpts : ∀ v : ℝ, cbr u v x * cbr u v y
      = exp (u * ((x - 1) + (y - 1))) *
          (Iio (min (exp (2 * u * (1 - x))) (exp (2 * u * (1 - y))))).indicator
            (fun _ => (1 : ℝ)) v := by
    intro v
    unfold cbr
    rw [Set.indicator_of_mem (Set.mem_Iic.mpr hx1), Set.indicator_of_mem
      (Set.mem_Iic.mpr hy1)]
    by_cases hv : v < min (exp (2 * u * (1 - x))) (exp (2 * u * (1 - y)))
    · have hx' : v ∈ Iio (exp (2 * u * (1 - x))) :=
        Set.mem_Iio.mpr (lt_of_lt_of_le hv (min_le_left _ _))
      have hy' : v ∈ Iio (exp (2 * u * (1 - y))) :=
        Set.mem_Iio.mpr (lt_of_lt_of_le hv (min_le_right _ _))
      rw [Set.indicator_of_mem hx', Set.indicator_of_mem hy', Set.indicator_of_mem
        (Set.mem_Iio.mpr hv), mul_one, mul_one, ← exp_add, mul_one]
      congr 1
      ring
    · rcases min_le_iff.mp (le_of_not_gt hv) with hc | hc
      · have hncx : v ∉ Iio (exp (2 * u * (1 - x))) :=
          fun h => absurd (Set.mem_Iio.mp h) (by linarith)
        have hnm : v ∉ Iio (min (exp (2 * u * (1 - x))) (exp (2 * u * (1 - y)))) :=
          fun h => hv h
        rw [Set.indicator_of_notMem hncx, Set.indicator_of_notMem hnm]
        simp only [mul_zero, zero_mul]
      · have hncy : v ∉ Iio (exp (2 * u * (1 - y))) :=
          fun h => absurd (Set.mem_Iio.mp h) (by linarith)
        have hnm : v ∉ Iio (min (exp (2 * u * (1 - x))) (exp (2 * u * (1 - y)))) :=
          fun h => hv h
        rw [Set.indicator_of_notMem hncy, Set.indicator_of_notMem hnm]
        simp only [mul_zero]
  have hm1 : min (exp (2 * u * (1 - x))) (exp (2 * u * (1 - y))) ≤ exp (2 * u * 2) := by
    rcases le_total x y with h | h
    · rw [min_eq_right (exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (by linarith) (by linarith)))]
      exact hcyE
    · rw [min_eq_left (exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (by linarith) (by linarith)))]
      exact hcxE
  have hmpos : 0 < min (exp (2 * u * (1 - x))) (exp (2 * u * (1 - y))) :=
    lt_min (exp_pos _) (exp_pos _)
  rw [integral_congr_ae (Filter.Eventually.of_forall hpts), integral_const_mul,
    integral_indicator measurableSet_Iio]
  show exp (u * ((x - 1) + (y - 1))) * ∫ v : ℝ in Iio _, (1 : ℝ) ∂(dmu u) = _
  have hreal : (dmu u).real (Iio (min (exp (2 * u * (1 - x))) (exp (2 * u * (1 - y)))))
      = min (exp (2 * u * (1 - x))) (exp (2 * u * (1 - y))) := by
    rw [measureReal_def, Measure.restrict_apply measurableSet_Iio]
    have hI : Iio (min (exp (2 * u * (1 - x))) (exp (2 * u * (1 - y)))) ∩
        Ioc 0 (exp (2 * u * 2))
        = Ioo 0 (min (exp (2 * u * (1 - x))) (exp (2 * u * (1 - y)))) := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iio, Set.mem_Ioo]
      constructor
      · rintro ⟨h2, h1, h3⟩
        exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h2, h1, h2.le.trans hm1⟩
    rw [hI, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith), sub_zero]
  rw [MeasureTheory.setIntegral_const, hreal, smul_eq_mul, mul_one]
  have hexpm : min (exp (2 * u * (1 - x))) (exp (2 * u * (1 - y)))
      = exp (2 * u * (1 - max x y)) := by
    rcases le_total x y with h | h
    · rw [max_eq_right h, min_eq_right
        (exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) (by linarith)))]
    · rw [max_eq_left h, min_eq_left
        (exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) (by linarith)))]
  rw [hexpm, ← exp_add]
  have hring : u * ((x - 1) + (y - 1)) + (2 * u * (1 - max x y)) = -(u * |x - y|) := by
    rcases le_total x y with h | h
    · rw [max_eq_right h, abs_of_nonpos (by linarith : x - y ≤ 0)]
      ring
    · rw [max_eq_left h, abs_of_nonneg (by linarith : 0 ≤ x - y)]
      ring
  rw [hring]

/-! ### The PSD certificate -/

set_option maxHeartbeats 1000000 in
/-- **The Cauchy-kernel PSD certificate**: for `u > 0` the kernel
`exp (-(u * |x - y|))` is positive semidefinite on `L²` of the square. -/
theorem kernelPSD_exp_dist (u : ℝ) (hu : 0 < u) :
    KernelPSD (fun p : ℝ × ℝ => exp (-(u * |p.1 - p.2|))) := by
  intro f
  -- L¹ material for the coe of `f`
  have hf2 : MemLp (⇑f) 2 vol := Lp.memLp f
  have hf1 : MemLp (⇑f) 1 vol := hf2.mono_exponent one_le_two
  have hfi : Integrable (⇑f) vol := memLp_one_iff_integrable.mp hf1
  have hfF1 : Integrable (fun q : (ℝ × ℝ) × ℝ => (⇑f) q.1.1) (vol2.prod (dmu u)) :=
    (hfi.comp_fst vol).comp_fst (dmu u)
  have hfF2 : Integrable (fun q : (ℝ × ℝ) × ℝ => (⇑f) q.1.2) (vol2.prod (dmu u)) :=
    (hfi.comp_snd vol).comp_fst (dmu u)
  -- the triple integrand
  set Φ : (ℝ × ℝ) × ℝ → ℝ := fun q =>
    (cbr u q.2 q.1.1 * (⇑f) q.1.1) * (cbr u q.2 q.1.2 * (⇑f) q.1.2) with hΦdef
  have hΦpt : ∀ (p : ℝ × ℝ) (v : ℝ), Φ (p, v)
      = (cbr u v p.1 * (⇑f) p.1) * (cbr u v p.2 * (⇑f) p.2) := fun p v => rfl
  -- integrability of the coe-product via L² ⊗ L² → L¹ on the finite measure
  have hL2a : MemLp (fun q : (ℝ × ℝ) × ℝ => (⇑f) q.1.1) 2 (vol2.prod (dmu u)) :=
    hf2.comp_fst vol |>.comp_fst (dmu u)
  have hL2b : MemLp (fun q : (ℝ × ℝ) × ℝ => (⇑f) q.1.2) 2 (vol2.prod (dmu u)) :=
    hf2.comp_snd vol |>.comp_fst (dmu u)
  have hintF : Integrable (fun q : (ℝ × ℝ) × ℝ => (⇑f) q.1.1 * (⇑f) q.1.2)
      (vol2.prod (dmu u)) := by
    have h := memLp_one_iff_integrable.mp (hL2b.mul hL2a)
    exact h.congr (Filter.Eventually.of_forall fun q => rfl)
  -- measurability of the bracket part and a.e.-strong measurability of Φ
  have hmeas1 : Measurable (fun q : (ℝ × ℝ) × ℝ => cbr u q.2 q.1.1) :=
    (measurable_cbr_uv u).comp (measurable_snd.prodMk (measurable_fst.comp measurable_fst))
  have hmeas2 : Measurable (fun q : (ℝ × ℝ) × ℝ => cbr u q.2 q.1.2) :=
    (measurable_cbr_uv u).comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
  have hA : AEStronglyMeasurable (fun q : (ℝ × ℝ) × ℝ => cbr u q.2 q.1.1 * (⇑f) q.1.1)
      (vol2.prod (dmu u)) := hmeas1.aestronglyMeasurable.mul hfF1.aestronglyMeasurable
  have hB : AEStronglyMeasurable (fun q : (ℝ × ℝ) × ℝ => cbr u q.2 q.1.2 * (⇑f) q.1.2)
      (vol2.prod (dmu u)) := hmeas2.aestronglyMeasurable.mul hfF2.aestronglyMeasurable
  have hASM : AEStronglyMeasurable Φ (vol2.prod (dmu u)) := by
    show AEStronglyMeasurable
      (fun q => (cbr u q.2 q.1.1 * (⇑f) q.1.1) * (cbr u q.2 q.1.2 * (⇑f) q.1.2))
      (vol2.prod (dmu u))
    exact hA.mul hB
  -- a.e. nullity of the two rays `{q | q.1.i > 1}` (where the bracket is unbounded)
  have hvolgt : vol (Ioi (1 : ℝ)) = 0 := by
    simp only [vol]
    rw [Measure.restrict_apply measurableSet_Ioi]
    have hE : (Ioi (1 : ℝ)) ∩ (Icc (-1 : ℝ) 1) = ∅ := by
      ext z
      constructor
      · rintro ⟨h3, h1, h2⟩
        exact absurd (Set.mem_Ioi.mp h3) (by linarith)
      · rintro h
        exact absurd h (Set.notMem_empty z)
    rw [hE]
    simp
  have hae1 : ∀ᵐ q : (ℝ × ℝ) × ℝ ∂(vol2.prod (dmu u)), q.1.1 ≤ 1 := by
    rw [ae_iff]
    have hset : {q : (ℝ × ℝ) × ℝ | ¬q.1.1 ≤ 1}
        = ((Ioi (1 : ℝ)) ×ˢ (univ : Set ℝ)) ×ˢ (univ : Set ℝ) := by
      ext q
      simp
    rw [hset, Measure.prod_prod, Measure.prod_prod, hvolgt]
    simp [dmu]
  have hae2 : ∀ᵐ q : (ℝ × ℝ) × ℝ ∂(vol2.prod (dmu u)), q.1.2 ≤ 1 := by
    rw [ae_iff]
    have hset : {q : (ℝ × ℝ) × ℝ | ¬q.1.2 ≤ 1}
        = (((univ : Set ℝ)) ×ˢ (Ioi (1 : ℝ))) ×ˢ (univ : Set ℝ) := by
      ext q
      simp
    rw [hset, Measure.prod_prod, Measure.prod_prod, hvolgt]
    simp
  -- integrability of Φ by a.e. domination
  have hGint : Integrable
      (fun q : (ℝ × ℝ) × ℝ => exp u * exp u * ((⇑f) q.1.1 * (⇑f) q.1.2))
      (vol2.prod (dmu u)) :=
    hintF.const_mul _
  have hWint : Integrable Φ (vol2.prod (dmu u)) := by
    refine Integrable.mono hGint hASM ?_
    filter_upwards [hae1, hae2] with q hq1 hq2
    have hb1 := abs_cbr_le u hu q.1.1 q.2
    have hb2 := abs_cbr_le u hu q.1.2 q.2
    rw [Set.indicator_of_mem (Set.mem_Iic.mpr hq1), mul_one] at hb1
    rw [Set.indicator_of_mem (Set.mem_Iic.mpr hq2), mul_one] at hb2
    show |(cbr u q.2 q.1.1 * (⇑f) q.1.1) * (cbr u q.2 q.1.2 * (⇑f) q.1.2)| ≤
      |exp u * exp u * ((⇑f) q.1.1 * (⇑f) q.1.2)|
    have hstep : |(cbr u q.2 q.1.1 * (⇑f) q.1.1) * (cbr u q.2 q.1.2 * (⇑f) q.1.2)|
        ≤ exp u * exp u * (|(⇑f) q.1.1| * |(⇑f) q.1.2|) := by
      rw [abs_mul, abs_mul, abs_mul]
      calc |cbr u q.2 q.1.1| * |(⇑f) q.1.1| * (|cbr u q.2 q.1.2| * |(⇑f) q.1.2|)
          ≤ exp u * |(⇑f) q.1.1| * (exp u * |(⇑f) q.1.2|) :=
            mul_le_mul (mul_le_mul_of_nonneg_right hb1 (abs_nonneg _))
              (mul_le_mul_of_nonneg_right hb2 (abs_nonneg _)) (by positivity) (by positivity)
        _ = exp u * exp u * (|(⇑f) q.1.1| * |(⇑f) q.1.2|) := by ring
    have habsexp : |exp u * exp u * ((⇑f) q.1.1 * (⇑f) q.1.2)|
        = exp u * exp u * (|(⇑f) q.1.1| * |(⇑f) q.1.2|) := by
      rw [abs_mul (exp u * exp u) ((⇑f) q.1.1 * (⇑f) q.1.2),
        abs_of_pos (mul_pos (exp_pos u) (exp_pos u)), abs_mul]
    exact hstep.trans habsexp.symm.le
  -- the Fubini assembly; the kernel identity holds a.e. on the square
  have hvolIc : vol (Iᶜ) = 0 := by
    simp only [vol]
    rw [Measure.restrict_apply (isClosed_Icc.measurableSet.compl)]
    simp
  have haeP : ∀ᵐ p : ℝ × ℝ ∂vol2, p.1 ∈ I ∧ p.2 ∈ I := by
    rw [ae_iff]
    have hnull1 : vol2 {p : ℝ × ℝ | ¬(p.1 ∈ I)} = 0 := by
      have hset : {p : ℝ × ℝ | ¬(p.1 ∈ I)} = (Iᶜ) ×ˢ (univ : Set ℝ) := by
        ext p
        simp
      rw [hset, Measure.prod_prod, hvolIc, zero_mul]
    have hnull2 : vol2 {p : ℝ × ℝ | ¬(p.2 ∈ I)} = 0 := by
      have hset : {p : ℝ × ℝ | ¬(p.2 ∈ I)} = (univ : Set ℝ) ×ˢ (Iᶜ) := by
        ext p
        simp
      rw [hset, Measure.prod_prod, hvolIc, mul_zero]
    refine le_antisymm ?_ (by simp)
    have hsub : {p : ℝ × ℝ | ¬(p.1 ∈ I ∧ p.2 ∈ I)}
        ⊆ {p : ℝ × ℝ | ¬(p.1 ∈ I)} ∪ {p : ℝ × ℝ | ¬(p.2 ∈ I)} := by
      intro p hp
      by_cases h1 : p.1 ∈ I
      · exact Or.inr (fun h2 => hp ⟨h1, h2⟩)
      · exact Or.inl h1
    calc vol2 {p : ℝ × ℝ | ¬(p.1 ∈ I ∧ p.2 ∈ I)}
        ≤ vol2 ({p : ℝ × ℝ | ¬(p.1 ∈ I)} ∪ {p : ℝ × ℝ | ¬(p.2 ∈ I)}) :=
          measure_mono hsub
      _ ≤ vol2 {p : ℝ × ℝ | ¬(p.1 ∈ I)} + vol2 {p : ℝ × ℝ | ¬(p.2 ∈ I)} :=
          measure_union_le _ _
      _ = 0 := by rw [hnull1, hnull2]; simp
  have hcongr : ∀ (p : ℝ × ℝ), p.1 ∈ I → p.2 ∈ I →
      exp (-(u * |p.1 - p.2|)) * (⇑f) p.2 * (⇑f) p.1
      = ∫ v : ℝ, Φ (p, v) ∂(dmu u) := by
    intro p hp1 hp2
    rw [← cbr_pair u hu hp1 hp2, mul_assoc, ← integral_mul_const]
    have hc2 : ∀ v : ℝ,
        cbr u v p.1 * cbr u v p.2 * ((⇑f) p.2 * (⇑f) p.1) = Φ (p, v) := by
      intro v
      rw [hΦpt p v]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hc2)]
  have hca : (fun p : ℝ × ℝ => exp (-(u * |p.1 - p.2|)) * (⇑f) p.2 * (⇑f) p.1)
      =ᵐ[vol2] (fun p : ℝ × ℝ => ∫ v : ℝ, Φ (p, v) ∂(dmu u)) := by
    filter_upwards [haeP] with p hp
    exact hcongr p hp.1 hp.2
  show 0 ≤ ∫ p : ℝ × ℝ, exp (-(u * |p.1 - p.2|)) * (⇑f) p.2 * (⇑f) p.1 ∂vol2
  rw [integral_congr_ae hca]
  rw [← integral_prod Φ hWint]
  rw [← integral_prod_swap Φ]
  have hswap : Integrable (fun z : ℝ × (ℝ × ℝ) => Φ z.swap) ((dmu u).prod vol2) :=
    MeasurePreserving.integrable_comp_of_integrable
      (measurePreserving_swap (μ := dmu u) (ν := vol2)) hWint
  rw [integral_prod (fun z : ℝ × (ℝ × ℝ) => Φ z.swap) hswap]
  show 0 ≤ ∫ v : ℝ, ∫ y : ℝ × ℝ, Φ (y, v) ∂vol2 ∂(dmu u)
  refine integral_nonneg fun v => ?_
  show (0 : ℝ) ≤ ∫ y : ℝ × ℝ, Φ (y, v) ∂vol2
  have hc3 : ∀ p : ℝ × ℝ, Φ (p, v)
      = (cbr u v p.1 * (⇑f) p.1) * (cbr u v p.2 * (⇑f) p.2) := fun p => hΦpt p v
  rw [integral_congr_ae (Filter.Eventually.of_forall hc3),
    integral_prod_mul (fun x => cbr u v x * (⇑f) x) (fun y => cbr u v y * (⇑f) y)]
  exact mul_self_nonneg _

end HS

end
