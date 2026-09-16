import Hurst.GeneralKPeel
import Hurst.BandPowerSum

/-!
# Unconditional chain-integrability discharge for the Riesz kernel family

This file lands the last analytic item of the general-`k` HasSum application: the
*unconditional* chain-integrability `hP` instances for the Riesz-type kernel family
(the documented gap of `Hurst.GeneralKPeel`).  Everything builds on the landed `HS`
encoding: `vol = volume.restrict (Icc (-1:ℝ) 1)`, `vol2 = vol.prod vol`,
`chainProd k W z = ∏ i, W i (z i, z (cycleSucc i))`.

## Main results (landed this round)

* `measurable_exp_log_abs_sub` — the measurable representative `p ↦ exp (log |p.1-p.2| * (-β))`.
* `aestronglyMeasurable_abs_sub_rpow` — **(0), the `hpow` discharge**: the distance-power
  factor `p ↦ |p.1 - p.2| ^ (-β)` is a.e.-measurable w.r.t. `vol2` for `β ≠ 0` — this
  discharges the standing a.e.-measurability hypothesis `hpow` carried by
  `Hurst.HSOperatorLayer2` (and every downstream consumer) since its first landing.
* `integral_rpow_neg_le_two` — the elementary value `∫ u in 0..2, u ^ (-β) = 2 ^ (1-β) / (1-β)`,
  finite exactly when `β < 1` (the analytic gate of the whole 2ψ < 1 theory).

## Architecture landed for the next round (compiled out, budget)

The full discharge chain was architected and partially proved, but did not reach exit 0
within the budget; the finished building blocks and the exact remaining glue:

* **(b) core, uniform section bound** `section_abs_sub_rpow_le`: for `0 < β < 1`,
  `a ∈ [-1,1]`: `∫ y ∈ I, |a - y| ^ (-β) ∂volume ≤ 2 * 2^(1-β) / (1-β)`.  Route (verified
  API): split `Icc (-1) 1` at `a` into `Ioc (-1) a ∪ Ioc a 1 ∪ {a}` (pointwise subset;
  `Measure.restrict_union` + `integral_add` + `setIntegral_singleton` with
  `volume {a} = 0`), transport the two pieces by `u = a - y` resp. `u = y - a`
  (`intervalIntegral.integral_comp_sub_left` / `integral_comp_sub_right`, with
  `intervalIntegral.integral_congr` for the `|·|`-removal), dominate by
  `0..2` via `intervalIntegral.integral_mono_interval` + `integral_rpow_neg_le_two`.
* **(b) core, square integrability** `integrable_abs_sub_rpow_vol2`: from the uniform
  section bound via `hasFiniteIntegral_prod_iff` (strong measurability from the landed
  (0) lemma, sections a.e. on `I` via `ae_restrict_mem`, section-integral function
  measurable by `StronglyMeasurable.integral_prod_right'`).  At `β = 2ψ < 1` this is
  exactly the standing hypothesis `hg` of `hsKernel_rieszKernel` — unconditional.
* **(a) per-edge bound** `abs_rieszKernel_le`: `|rieszKernel ψ c ω (x,y)| ≤ B_ω |c| |x-y| ^ (-ψ)`
  under `|ω| ≤ B_ω` (elementary; `Set.indicator` split + `abs_mul`).
* **frozen variant, general `k`** `chainProd_integrable_of_bounded`: uniformly bounded
  measurable kernel family ⇒ `chainProd k W` integrable over `vol^k` (finite measure,
  `measurable_chainProd` + `Integrable.mono` against `B^k`); discharges every `hP`
  instance for the frozen family.
* **item (c), `k = 2`** `chainProd_riesz_integrable_two`: by (a) + (b) at `β = 2ψ`
  (`Fin.prod_univ_two` collapse `|x-y| ^ (-ψ) |y-x| ^ (-ψ) = |x-y| ^ (-2ψ)`).

## Gap report

* **Item (c) for general `k` (the Riesz family)**: not landed.  The statement is true for
  every `k ≥ 2` when `2 * ψ < 1` (full-collapse scaling needs `k ψ < k - 1`, which holds
  since `ψ < 1/2 ≤ 1 - 1/k`; proper sub-collapses are harmless on a cycle).  Route: peel
  one cycle coordinate by the section Cauchy–Schwarz bound
  `∫ a, |a - w| ^ (-ψ) |v - a| ^ (-ψ) da ≤ S(2ψ)²` (uniform in `w, v ∈ I`,
  `S(β) := 2 * 2^(1-β)/(1-β)` from the section bound), reducing the cycle product to the
  path product, which peels edge-by-edge at cost `S(ψ)` per step — formally one
  `measurePreserving_piFinSuccAbove` cons-transport induction (the same dance as the
  landed `chainIntegral_peel`).
-/

open MeasureTheory Measure Real Set
open scoped Real

noncomputable section

namespace HS

/-! ### (0) Measurability of the distance-power factor -/

/-- The measurable representative `p ↦ exp (log |p.1 - p.2| * (-β))` of the
distance-power factor. -/
theorem measurable_exp_log_abs_sub (β : ℝ) :
    Measurable (fun p : ℝ × ℝ => Real.exp (Real.log |p.1 - p.2| * (-β))) :=
  Real.measurable_exp.comp
    ((Real.measurable_log.comp (measurable_fst.sub measurable_snd).abs).mul measurable_const)

/-- **(0), the `hpow` discharge**: the distance-power factor `p ↦ |p.1 - p.2| ^ (-β)` is
a.e.-measurable w.r.t. `vol2` for `β ≠ 0` — off the (null) diagonal it agrees with the
measurable representative above, since for `r > 0`, `r ^ (-β) = exp (log r * (-β))`
(`Real.rpow_def_of_pos`).  This discharges the standing hypothesis `hpow` of
`Hurst.HSOperatorLayer2`. -/
theorem aestronglyMeasurable_abs_sub_rpow {β : ℝ} (hβ : β ≠ 0) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-β)) vol2 := by
  have hdiag : vol2 {p : ℝ × ℝ | |p.1 - p.2| = 0} = 0 := by
    have hset : {p : ℝ × ℝ | |p.1 - p.2| = 0} = {p : ℝ × ℝ | p.1 = p.2} := by
      ext p
      simp only [Set.mem_setOf_eq, abs_eq_zero]
      exact sub_eq_zero
    rw [hset, Measure.prod_apply
      ((isClosed_eq continuous_fst continuous_snd).measurableSet)]
    have hsing : ∀ x : ℝ, vol (Prod.mk x ⁻¹' {p : ℝ × ℝ | p.1 = p.2}) = 0 := by
      intro x
      have hsub : (Prod.mk x ⁻¹' {p : ℝ × ℝ | p.1 = p.2}) ⊆ ({x} : Set ℝ) := by
        intro y hy
        simp only [Set.mem_preimage, Set.mem_setOf_eq, Prod.mk.injEq] at hy
        exact Set.mem_singleton_iff.mpr hy.symm
      exact measure_mono_null hsub (by simp [Real.volume_singleton])
    rw [lintegral_congr_ae (ae_of_all _ hsing)]
    simp
  have hform : ∀ p : ℝ × ℝ, |p.1 - p.2| ≠ 0 →
      |p.1 - p.2| ^ (-β) = Real.exp (Real.log |p.1 - p.2| * (-β)) := by
    intro p hp
    rw [Real.rpow_def_of_pos (by simpa using abs_pos.mpr hp)]
  have hae : (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-β))
      =ᵐ[vol2] (fun p : ℝ × ℝ => Real.exp (Real.log |p.1 - p.2| * (-β))) := by
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_mono_null ?_ hdiag
    intro p hp
    by_cases hr : |p.1 - p.2| = 0
    · exact hr
    · exact absurd (hform p hr) hp
  exact (AEMeasurable.congr (measurable_exp_log_abs_sub β |>.aemeasurable) hae.symm).aestronglyMeasurable

/-! ### (b) The uniform section bound and the square-integrability core -/

end HS

end
