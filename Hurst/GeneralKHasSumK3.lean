import Hurst.GeneralKHasSumComplete
import Hurst.ChainIntegrabilityDischarge
import Hurst.GeneralKPeelInduction

/-!
# General-`k` HasSum completion, `k = 3`: integrability discharges, the `w ↔ q` splice,
and the cubic `HasSum`

This file completes the three items of the `k = 3` layer of the general-`k` `HasSum`
boundary on the landed `HS` encoding (`HSKernel K = MemLp K 2 vol2`,
`hsNorm K = (∫∫ K² ∂vol2)^(1/2)`, `chainCycleTriple`, `cycleIntegral`):

* **Item (1), the `hA`/`hB` discharge** (the documented obstruction of
  `Hurst.HSCycleComposition`, unblocked by the strongly-measurable dialect fix of
  `Hurst.GeneralKPeelInduction`): `integrable_abs_mul_sqrtsecE` — the two-variable
  Cauchy–Schwarz sandwich `∫∫ |M(y,x)| √(secE2 K x) √(secE1 L y) ≤ hsNorm M hsNorm K
  hsNorm L` (a.e. section Cauchy–Schwarz in `x` against `√(secE2 K)`, then
  Cauchy–Schwarz in `y` between `√(secE1 L)` and `√(secE2 M)`; Fubini-free, via
  `integrable_prod_iff'`) — and its consequences `K3Integrable_chainCycleTriple` /
  `integrable_chainCycleTripleB`: the triple chain integrands of both parenthesizations
  are integrable over `vol × vol × vol` for measurable HS kernels (Fubini split by
  `integrable_prod_iff`, section integrability by `MemLp.mul'`, section-integral
  domination by the sandwich).
* **Item (2), the `w ↔ q` splice** (the documented transport of
  `Hurst.HSCycleComposition`): `K3CycleIntegral_three_eq_chainCycleTriple` — the kernel-side
  `k = 3` cycle functional `cycleIntegral 3 K` equals the triple chain integral
  `chainCycleTriple K K K`, by the landed `cycleIntegral_three_eq_tripleW` (`Fin 3`
  succAbove-peel transport) composed with the coordinate identification
  `(Fin 2 → ℝ) × ℝ ≅ (ℝ × ℝ) × ℝ` (`MeasurePreserving.prod` of the landed
  `measurePreserving_piFinTwo` with the identity).  Unconditional (no integrability
  needed; `MeasurePreserving.integral_comp'`).
* **Item (3), the `k = 3` `HasSum`**: `hasSum_cubic_chainCycleTriple` — the enumerated
  cubic series `val j ^ 3` `HasSum`s to the triple integral `chainCycleTriple K K K`,
  conditional on the documented operator-side spectral bridge
  `∑' j, val j ^ 3 = cycleIntegral 3 K` (the product-basis Parseval gap of
  `Hurst.CycleTraceIdentification`; the summability side
  `hasSum_general_k_pow` is landed in `Hurst.GeneralKHasSumComplete`).
* **Bonus, the `k = 3` chain-integrability instance** feeding the general-`k` peel
  induction (`Hurst.GeneralKPeelInduction`): `integrable_chainProd_three` — the
  `Fin 3`-form cycle product `z ↦ ∏ i, K (z i, z (cycleSucc i))` is integrable over
  `vol^3` for measurable HS kernels (the `hP` instance of the peel induction at
  `k = 3`), transported from item (1) through the landed measure-preserving
  `Fin 3`-peel equiv and the splice equiv.
-/

open MeasureTheory Measure Real Set
open scoped Real

noncomputable section

namespace HS

variable {K L M : ℝ × ℝ → ℝ}

/-! ### Small bridges (copies of the landed private patterns) -/

private theorem K3Integral_pow_two_vol (u : ℝ → ℝ) :
    ∫ t : ℝ, u t ^ (2 : ℝ) ∂vol = ∫ t : ℝ, u t ^ 2 ∂vol := by
  apply integral_congr_ae
  filter_upwards with t
  rw [Real.rpow_two, pow_two]

private theorem stronglyMeasurable_secE2' {K : ℝ × ℝ → ℝ} (hKm : Measurable K) :
    StronglyMeasurable (secE2 K) :=
  (hKm.pow_const 2).stronglyMeasurable.integral_prod_right'

private theorem stronglyMeasurable_secE1' {K : ℝ × ℝ → ℝ} (hKm : Measurable K) :
    StronglyMeasurable (secE1 K) :=
  stronglyMeasurable_secE2' (hKm.comp measurable_swap)

private theorem aestronglyMeasurable_sqrt_secE2 {K : ℝ × ℝ → ℝ} (hKm : Measurable K) :
    AEStronglyMeasurable (fun x => Real.sqrt (secE2 K x)) vol :=
  Real.continuous_sqrt.comp_aestronglyMeasurable
    (stronglyMeasurable_secE2' hKm).aestronglyMeasurable

private theorem aestronglyMeasurable_sqrt_secE1 {K : ℝ × ℝ → ℝ} (hKm : Measurable K) :
    AEStronglyMeasurable (fun y => Real.sqrt (secE1 K y)) vol :=
  aestronglyMeasurable_sqrt_secE2 (hKm.comp measurable_swap)

private theorem memLp_two_sqrt_secE2 {K : ℝ × ℝ → ℝ} (hKm : Measurable K) (hK : HSKernel K) :
    MemLp (fun x => Real.sqrt (secE2 K x)) 2 vol := by
  refine memLp_two_of_aemeasurable (aestronglyMeasurable_sqrt_secE2 hKm) ?_
  refine (integrable_secE2 hK).congr (Filter.Eventually.of_forall fun x => ?_)
  show secE2 K x = Real.sqrt (secE2 K x) ^ 2
  exact (Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)).symm

private theorem memLp_two_sqrt_secE1 {K : ℝ × ℝ → ℝ} (hKm : Measurable K) (hK : HSKernel K) :
    MemLp (fun y => Real.sqrt (secE1 K y)) 2 vol :=
  memLp_two_sqrt_secE2 (hKm.comp measurable_swap) (hsKernel_transpose hK)

/-- Section Cauchy–Schwarz (the core of the landed `abs_compKernel_le`): for a.e.-type
`MemLp` sections, `∫_t |K (x,t)| |L (t,y)| ≤ √(secE2 K x) √(secE1 L y)`. -/
private theorem integral_section_cs {K L : ℝ × ℝ → ℝ} (x y : ℝ)
    (hx : MemLp (fun t => K (x, t)) 2 vol) (hy : MemLp (fun t => L (t, y)) 2 vol) :
    ∫ t : ℝ, |K (x, t)| * |L (t, y)| ∂vol
      ≤ Real.sqrt (secE2 K x) * Real.sqrt (secE1 L y) := by
  have hx2 : MemLp (fun t => K (x, t)) (ENNReal.ofReal 2) vol := by
    rw [real_two_ofReal]; exact hx
  have hy2 : MemLp (fun t => L (t, y)) (ENNReal.ofReal 2) vol := by
    rw [real_two_ofReal]; exact hy
  have hcs := integral_mul_norm_le_Lp_mul_Lq holderTriple221 hx2 hy2
  simp only [Real.norm_eq_abs] at hcs
  rw [K3Integral_pow_two_vol (fun t => |K (x, t)|),
    K3Integral_pow_two_vol (fun t => |L (t, y)|)] at hcs
  have h1 : (∫ t : ℝ, |K (x, t)| ^ 2 ∂vol) ^ ((1 : ℝ) / 2) = Real.sqrt (secE2 K x) := by
    rw [← Real.sqrt_eq_rpow]
    refine congrArg Real.sqrt ?_
    exact integral_congr_ae (Filter.Eventually.of_forall fun t => by simp [sq_abs])
  have h2 : (∫ t : ℝ, |L (t, y)| ^ 2 ∂vol) ^ ((1 : ℝ) / 2) = Real.sqrt (secE1 L y) := by
    rw [← Real.sqrt_eq_rpow]
    refine congrArg Real.sqrt ?_
    exact integral_congr_ae (Filter.Eventually.of_forall fun t => by simp [sq_abs])
  rw [h1, h2] at hcs
  exact hcs

private theorem abs_sq_eq_sq (u : ℝ) : |u| ^ 2 = u ^ 2 := by
  rw [← abs_pow, abs_of_nonneg (sq_nonneg _)]

private theorem integral_secE2_nonneg {K : ℝ × ℝ → ℝ} :
    0 ≤ ∫ x : ℝ, secE2 K x ∂vol := by
  apply integral_nonneg
  intro x
  exact integral_nonneg fun _ => sq_nonneg _

/-! ### Item (1): the two-variable Cauchy–Schwarz sandwich and the `hA`/`hB` discharge -/

/-- **The two-variable Cauchy–Schwarz sandwich**: for measurable HS kernels `A B C`,
the mixed factor `p ↦ |A (p.2, p.1)| · √(secE2 B p.1) · √(secE1 C p.2)` is integrable
over `vol2`.  Route (Fubini-free): `integrable_prod_iff'` splits the `x`-sections
(a.e. `MemLp` by `ae_section_memLp_snd`, Cauchy–Schwarz against `√(secE2 B)` by
`MemLp.mul'`), and the section-integral function is dominated a.e. by the constant
`√(∫ secE2 B)` times `√(secE1 C y) · √(secE2 A y)` — itself integrable by one more
`MemLp.mul'` Cauchy–Schwarz.  Its integral is `≤ hsNorm A · hsNorm B · hsNorm C`. -/
theorem integrable_abs_mul_sqrtsecE {A B C : ℝ × ℝ → ℝ}
    (hAm : Measurable A) (hBm : Measurable B) (hCm : Measurable C)
    (hA : HSKernel A) (hB : HSKernel B) (hC : HSKernel C) :
    Integrable (fun p : ℝ × ℝ => |A (p.2, p.1)| * Real.sqrt (secE2 B p.1)
        * Real.sqrt (secE1 C p.2)) vol2 := by
  classical
  have hsqrtB : MemLp (fun x => Real.sqrt (secE2 B x)) 2 vol :=
    memLp_two_sqrt_secE2 hBm hB
  have hsqrtA : MemLp (fun y => Real.sqrt (secE2 A y)) 2 vol :=
    memLp_two_sqrt_secE2 hAm hA
  have hsqrtC : MemLp (fun y => Real.sqrt (secE1 C y)) 2 vol :=
    memLp_two_sqrt_secE1 hCm hC
  have hBmeas : Measurable (fun p : ℝ × ℝ => secE2 B p.1) :=
    (stronglyMeasurable_secE2' hBm).measurable.comp measurable_fst
  have hCmeas : Measurable (fun p : ℝ × ℝ => secE1 C p.2) :=
    (stronglyMeasurable_secE1' hCm).measurable.comp measurable_snd
  have hFm : Measurable (fun p : ℝ × ℝ => |A (p.2, p.1)| * Real.sqrt (secE2 B p.1)
      * Real.sqrt (secE1 C p.2)) := by
    refine ((hAm.comp (measurable_snd.prodMk measurable_fst)).abs.mul ?_).mul ?_
    · exact Real.continuous_sqrt.measurable.comp hBmeas
    · exact Real.continuous_sqrt.measurable.comp hCmeas
  refine (integrable_prod_iff' hFm.aestronglyMeasurable).mpr ⟨?_, ?_⟩
  · -- the `x`-sections are integrable for a.e. `y`
    filter_upwards [ae_section_memLp_fst hAm hA] with y hy
    haveI hpqr : Real.HolderTriple 2 2 1 := holderTriple221
    have hAbsh : MemLp (fun x => |A (y, x)|) 2 vol := by
      refine memLp_two_of_aemeasurable
        ((measurable_section_fst hAm y).abs.aestronglyMeasurable) ?_
      refine (MemLp.integrable_sq hy).congr (Filter.Eventually.of_forall fun x => ?_)
      exact (abs_sq_eq_sq _).symm
    have hprod : Integrable (fun x => |A (y, x)| * Real.sqrt (secE2 B x)) vol :=
      memLp_one_iff_integrable.mp (MemLp.mul' hsqrtB hAbsh)
    exact hprod.const_mul (Real.sqrt (secE1 C y)) |>.congr
      (Filter.Eventually.of_forall fun x => by ring)
  · -- the section-integral function is integrable (dominated a.e.)
    have hdom2 : Integrable (fun y : ℝ => Real.sqrt (secE1 C y) * Real.sqrt (secE2 A y)) vol :=
      memLp_one_iff_integrable.mp (MemLp.mul' hsqrtA hsqrtC)
    refine (hdom2.const_mul ((∫ x : ℝ, secE2 B x ∂vol) ^ ((1 : ℝ) / 2))).mono ?_ ?_
    · exact (hFm.stronglyMeasurable.norm.comp_measurable measurable_swap).integral_prod_right'
        |>.aestronglyMeasurable
    · filter_upwards [ae_section_memLp_fst hAm hA] with y hy
      have hy2 : MemLp (fun x => A (y, x)) (ENNReal.ofReal 2) vol := by
        rw [real_two_ofReal]; exact hy
      have hsqB2 : MemLp (fun x => Real.sqrt (secE2 B x)) (ENNReal.ofReal 2) vol := by
        rw [real_two_ofReal]; exact hsqrtB
      have hnorm : ∀ x : ℝ, ‖(fun p : ℝ × ℝ => |A (p.2, p.1)| * Real.sqrt (secE2 B p.1)
            * Real.sqrt (secE1 C p.2)) (x, y)‖
          = |A (y, x)| * Real.sqrt (secE2 B x) * Real.sqrt (secE1 C y) := by
        intro x
        show ‖|A (y, x)| * Real.sqrt (secE2 B x) * Real.sqrt (secE1 C y)‖ = _
        rw [Real.norm_eq_abs]
        exact abs_of_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
          (Real.sqrt_nonneg _))
      have hcs := integral_mul_norm_le_Lp_mul_Lq holderTriple221 hy2 hsqB2
      simp only [Real.norm_eq_abs] at hcs
      have hcs0 : ∫ a : ℝ, |A (y, a)| * |Real.sqrt (secE2 B a)| ∂vol
          = ∫ a : ℝ, |A (y, a)| * Real.sqrt (secE2 B a) ∂vol := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
        show |A (y, a)| * |Real.sqrt (secE2 B a)| = |A (y, a)| * Real.sqrt (secE2 B a)
        rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      have hcs1 : ∫ a : ℝ, |Real.sqrt (secE2 B a)| ^ (2 : ℝ) ∂vol
          = ∫ a : ℝ, Real.sqrt (secE2 B a) ^ (2 : ℝ) ∂vol := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
        show |Real.sqrt (secE2 B a)| ^ (2 : ℝ) = Real.sqrt (secE2 B a) ^ (2 : ℝ)
        rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      rw [hcs0, hcs1, K3Integral_pow_two_vol (fun x => |A (y, x)|),
        K3Integral_pow_two_vol (fun x => Real.sqrt (secE2 B x))] at hcs
      have h1 : (∫ x : ℝ, |A (y, x)| ^ 2 ∂vol) ^ ((1 : ℝ) / 2) = Real.sqrt (secE2 A y) := by
        rw [← Real.sqrt_eq_rpow]
        refine congrArg Real.sqrt ?_
        exact integral_congr_ae (Filter.Eventually.of_forall fun x => abs_sq_eq_sq _)
      have h2 : (∫ x : ℝ, Real.sqrt (secE2 B x) ^ 2 ∂vol) ^ ((1 : ℝ) / 2)
          = (∫ x : ℝ, secE2 B x ∂vol) ^ ((1 : ℝ) / 2) := by
        refine congrArg (fun u : ℝ => u ^ ((1 : ℝ) / 2)) ?_
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        show Real.sqrt (secE2 B x) ^ 2 = secE2 B x
        exact Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)
      have hstep : ∫ x : ℝ, ‖(fun p : ℝ × ℝ => |A (p.2, p.1)| * Real.sqrt (secE2 B p.1)
            * Real.sqrt (secE1 C p.2)) (x, y)‖ ∂vol
          ≤ (∫ x : ℝ, secE2 B x ∂vol) ^ ((1 : ℝ) / 2)
            * (Real.sqrt (secE1 C y) * Real.sqrt (secE2 A y)) := by
        calc ∫ x : ℝ, ‖(fun p : ℝ × ℝ => |A (p.2, p.1)| * Real.sqrt (secE2 B p.1)
                * Real.sqrt (secE1 C p.2)) (x, y)‖ ∂vol
            = ∫ x : ℝ, |A (y, x)| * Real.sqrt (secE2 B x) * Real.sqrt (secE1 C y) ∂vol :=
              integral_congr_ae (Filter.Eventually.of_forall hnorm)
          _ = ∫ x : ℝ, Real.sqrt (secE1 C y) * (|A (y, x)| * Real.sqrt (secE2 B x)) ∂vol :=
              integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
          _ = Real.sqrt (secE1 C y) * ∫ x : ℝ, |A (y, x)| * Real.sqrt (secE2 B x) ∂vol :=
              integral_const_mul _ _
          _ ≤ Real.sqrt (secE1 C y)
                * ((∫ x : ℝ, |A (y, x)| ^ 2 ∂vol) ^ ((1 : ℝ) / 2)
                  * (∫ x : ℝ, Real.sqrt (secE2 B x) ^ 2 ∂vol) ^ ((1 : ℝ) / 2)) :=
              mul_le_mul_of_nonneg_left hcs (Real.sqrt_nonneg _)
          _ ≤ (∫ x : ℝ, secE2 B x ∂vol) ^ ((1 : ℝ) / 2)
                * (Real.sqrt (secE1 C y) * Real.sqrt (secE2 A y)) := by
              rw [h1, h2]
              refine le_of_eq ?_
              ring
      have hnormeq : ‖∫ x : ℝ, ‖(fun p : ℝ × ℝ => |A (p.2, p.1)| * Real.sqrt (secE2 B p.1)
            * Real.sqrt (secE1 C p.2)) (x, y)‖ ∂vol‖
          = ∫ x : ℝ, ‖(fun p : ℝ × ℝ => |A (p.2, p.1)| * Real.sqrt (secE2 B p.1)
              * Real.sqrt (secE1 C p.2)) (x, y)‖ ∂vol :=
        abs_of_nonneg (integral_nonneg fun x => norm_nonneg _)
      have hdoneq : ‖(∫ x : ℝ, secE2 B x ∂vol) ^ ((1 : ℝ) / 2)
            * (Real.sqrt (secE1 C y) * Real.sqrt (secE2 A y))‖
          = (∫ x : ℝ, secE2 B x ∂vol) ^ ((1 : ℝ) / 2)
            * (Real.sqrt (secE1 C y) * Real.sqrt (secE2 A y)) :=
        abs_of_nonneg (mul_nonneg
          (Real.rpow_nonneg integral_secE2_nonneg ((1 : ℝ) / 2))
          (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
      rw [hnormeq, hdoneq]
      exact hstep

set_option maxHeartbeats 1000000 in
/-- **Item (1), the `hA` discharge**: for measurable HS kernels the triple chain
integrand of `chainCycleTriple` is integrable over `vol × vol × vol` (the standing
hypothesis `hA` of `cycle2_compKernel_eq_triple` is automatic).  Route:
`integrable_prod_iff` splits the shared slot `t` — the `t`-sections are integrable by
`MemLp.mul'` (a.e. `MemLp` sections, landed in `Hurst.GeneralKPeelInduction`), and the
section-integral function is dominated a.e. by the sandwich of
`integrable_abs_mul_sqrtsecE` at `(A, B, C) = (M, K, L)`. -/
theorem K3Integrable_chainCycleTriple {K L M : ℝ × ℝ → ℝ}
    (hKm : Measurable K) (hLm : Measurable L) (hMm : Measurable M)
    (hK : HSKernel K) (hL : HSKernel L) (hM : HSKernel M) :
    Integrable (fun q : (ℝ × ℝ) × ℝ =>
        K (q.1.1, q.2) * L (q.2, q.1.2) * M (q.1.2, q.1.1))
      ((vol.prod vol).prod vol) := by
  classical
  have hKF : Measurable (fun q : (ℝ × ℝ) × ℝ => K (q.1.1, q.2)) :=
    hKm.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hLF : Measurable (fun q : (ℝ × ℝ) × ℝ => L (q.2, q.1.2)) :=
    hLm.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
  have hMF : Measurable (fun q : (ℝ × ℝ) × ℝ => M (q.1.2, q.1.1)) :=
    hMm.comp ((measurable_snd.comp measurable_fst).prodMk (measurable_fst.comp measurable_fst))
  have hFm : Measurable (fun q : (ℝ × ℝ) × ℝ =>
      K (q.1.1, q.2) * L (q.2, q.1.2) * M (q.1.2, q.1.1)) := hKF.mul hLF |>.mul hMF
  have hliftK : ∀ᵐ p : ℝ × ℝ ∂vol2, Integrable (fun t => K (p.1, t) ^ 2) vol := by
    have hind : ∀ᵐ x ∂vol,
        (if Integrable (fun t => K (x, t) ^ 2) vol then (1 : ℝ) else 0) = 1 := by
      filter_upwards [ae_section_integrable_fst hKm hK] with x hx
      rw [if_pos hx]
    filter_upwards [eventual_fst hind] with p hp
    by_cases hc : Integrable (fun t => K (p.1, t) ^ 2) vol
    · exact hc
    · rw [if_neg hc] at hp
      exact absurd hp (by norm_num)
  have hliftL : ∀ᵐ p : ℝ × ℝ ∂vol2, Integrable (fun t => L (t, p.2) ^ 2) vol := by
    have hind : ∀ᵐ y ∂vol,
        (if Integrable (fun t => L (t, y) ^ 2) vol then (1 : ℝ) else 0) = 1 := by
      filter_upwards [ae_section_integrable_snd hLm hL] with y hy
      rw [if_pos hy]
    filter_upwards [eventual_snd hind] with p hp
    by_cases hc : Integrable (fun t => L (t, p.2) ^ 2) vol
    · exact hc
    · rw [if_neg hc] at hp
      exact absurd hp (by norm_num)
  refine (integrable_prod_iff hFm.aestronglyMeasurable).mpr ⟨?_, ?_⟩
  · -- the `t`-sections are integrable for a.e. `(x, y)`
    filter_upwards [hliftK, hliftL] with p hpK hpL
    haveI hpqr : Real.HolderTriple 2 2 1 := holderTriple221
    have hKLm : MemLp (fun t => K (p.1, t) * L (t, p.2)) 1 vol :=
      MemLp.mul'
        (memLp_two_of_aemeasurable
          ((measurable_section_snd hLm p.2).aestronglyMeasurable) hpL)
        (memLp_two_of_aemeasurable
          ((measurable_section_fst hKm p.1).aestronglyMeasurable) hpK)
    exact (memLp_one_iff_integrable.mp hKLm).const_mul (M (p.2, p.1)) |>.congr
      (Filter.Eventually.of_forall fun t => by ring)
  · -- the section-integral function is dominated by the sandwich
    refine (integrable_abs_mul_sqrtsecE hMm hKm hLm hM hK hL).mono ?_ ?_
    · exact (hFm.stronglyMeasurable.norm).integral_prod_right' |>.aestronglyMeasurable
    · filter_upwards [hliftK, hliftL] with p hpK hpL
      have hKLp : MemLp (fun t => K (p.1, t)) 2 vol :=
        memLp_two_of_aemeasurable
          ((measurable_section_fst hKm p.1).aestronglyMeasurable) hpK
      have hLLp : MemLp (fun t => L (t, p.2)) 2 vol :=
        memLp_two_of_aemeasurable
          ((measurable_section_snd hLm p.2).aestronglyMeasurable) hpL
      have hnn : 0 ≤ |M (p.2, p.1)| * Real.sqrt (secE2 K p.1) * Real.sqrt (secE1 L p.2) :=
        mul_nonneg (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
      calc ‖∫ t : ℝ, ‖(fun q : (ℝ × ℝ) × ℝ =>
                K (q.1.1, q.2) * L (q.2, q.1.2) * M (q.1.2, q.1.1)) (p, t)‖ ∂vol‖
          = ∫ t : ℝ, ‖(fun q : (ℝ × ℝ) × ℝ =>
                K (q.1.1, q.2) * L (q.2, q.1.2) * M (q.1.2, q.1.1)) (p, t)‖ ∂vol :=
            abs_of_nonneg (integral_nonneg fun t => norm_nonneg _)
        _ = ∫ t : ℝ, |K (p.1, t)| * |L (t, p.2)| * |M (p.2, p.1)| ∂vol := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
            show ‖K (p.1, t) * L (t, p.2) * M (p.2, p.1)‖ = _
            rw [Real.norm_eq_abs, abs_mul, abs_mul]
        _ = ∫ t : ℝ, |M (p.2, p.1)| * (|K (p.1, t)| * |L (t, p.2)|) ∂vol := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
            ring
        _ = |M (p.2, p.1)| * ∫ t : ℝ, |K (p.1, t)| * |L (t, p.2)| ∂vol :=
            integral_const_mul _ _
        _ ≤ |M (p.2, p.1)| * (Real.sqrt (secE2 K p.1) * Real.sqrt (secE1 L p.2)) :=
            mul_le_mul_of_nonneg_left (integral_section_cs (p.1) (p.2) hKLp hLLp)
              (abs_nonneg _)
        _ = ‖|M (p.2, p.1)| * Real.sqrt (secE2 K p.1) * Real.sqrt (secE1 L p.2)‖ := by
            rw [Real.norm_eq_abs, abs_of_nonneg hnn]
            ring

set_option maxHeartbeats 1000000 in
/-- **Item (1), the `hB` discharge**: the triple chain integrand of the permuted
parenthesization `chainCycleTripleB` is integrable over `vol × vol × vol` (the standing
hypothesis `hB` of `cycle2_eq_compKernel_triple` is automatic); here the shared slot is
the middle coordinate, the section pairing is `(L (y, ·), M (·, x))`, and the dominating
sandwich is `integrable_abs_mul_sqrtsecE` at
`(A, B, C) = (ktranspose K, ktranspose M, ktranspose L)`. -/
theorem integrable_chainCycleTripleB {K L M : ℝ × ℝ → ℝ}
    (hKm : Measurable K) (hLm : Measurable L) (hMm : Measurable M)
    (hK : HSKernel K) (hL : HSKernel L) (hM : HSKernel M) :
    Integrable (fun q : (ℝ × ℝ) × ℝ =>
        K (q.1.1, q.1.2) * L (q.1.2, q.2) * M (q.2, q.1.1))
      ((vol.prod vol).prod vol) := by
  classical
  have hKtrm : Measurable (ktranspose K) := hKm.comp measurable_swap
  have hMtrm : Measurable (ktranspose M) := hMm.comp measurable_swap
  have hLtrm : Measurable (ktranspose L) := hLm.comp measurable_swap
  have hKF : Measurable (fun q : (ℝ × ℝ) × ℝ => K (q.1.1, q.1.2)) :=
    hKm.comp ((measurable_fst.comp measurable_fst).prodMk
      (measurable_snd.comp measurable_fst))
  have hLF : Measurable (fun q : (ℝ × ℝ) × ℝ => L (q.1.2, q.2)) :=
    hLm.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hMF : Measurable (fun q : (ℝ × ℝ) × ℝ => M (q.2, q.1.1)) :=
    hMm.comp (measurable_snd.prodMk (measurable_fst.comp measurable_fst))
  have hFm : Measurable (fun q : (ℝ × ℝ) × ℝ =>
      K (q.1.1, q.1.2) * L (q.1.2, q.2) * M (q.2, q.1.1)) := hKF.mul hLF |>.mul hMF
  have hliftL : ∀ᵐ p : ℝ × ℝ ∂vol2, Integrable (fun t => L (p.2, t) ^ 2) vol := by
    have hind : ∀ᵐ x ∂vol,
        (if Integrable (fun t => L (x, t) ^ 2) vol then (1 : ℝ) else 0) = 1 := by
      filter_upwards [ae_section_integrable_fst hLm hL] with x hx
      rw [if_pos hx]
    filter_upwards [eventual_snd hind] with p hp
    by_cases hc : Integrable (fun t => L (p.2, t) ^ 2) vol
    · exact hc
    · rw [if_neg hc] at hp
      exact absurd hp (by norm_num)
  have hliftM : ∀ᵐ p : ℝ × ℝ ∂vol2, Integrable (fun t => M (t, p.1) ^ 2) vol := by
    have hind : ∀ᵐ y ∂vol,
        (if Integrable (fun t => M (t, y) ^ 2) vol then (1 : ℝ) else 0) = 1 := by
      filter_upwards [ae_section_integrable_snd hMm hM] with y hy
      rw [if_pos hy]
    filter_upwards [eventual_fst hind] with p hp
    by_cases hc : Integrable (fun t => M (t, p.1) ^ 2) vol
    · exact hc
    · rw [if_neg hc] at hp
      exact absurd hp (by norm_num)
  refine (integrable_prod_iff hFm.aestronglyMeasurable).mpr ⟨?_, ?_⟩
  · -- the `t`-sections are integrable for a.e. `(x, y)`
    filter_upwards [hliftL, hliftM] with p hpL hpM
    haveI hpqr : Real.HolderTriple 2 2 1 := holderTriple221
    have hLMm : MemLp (fun t => L (p.2, t) * M (t, p.1)) 1 vol :=
      MemLp.mul'
        (memLp_two_of_aemeasurable
          ((measurable_section_snd hMm p.1).aestronglyMeasurable) hpM)
        (memLp_two_of_aemeasurable
          ((measurable_section_fst hLm p.2).aestronglyMeasurable) hpL)
    exact (memLp_one_iff_integrable.mp hLMm).const_mul (K (p.1, p.2)) |>.congr
      (Filter.Eventually.of_forall fun t => by ring)
  · -- the section-integral function is dominated by the transposed sandwich
    refine (integrable_abs_mul_sqrtsecE hKtrm hMtrm hLtrm (hsKernel_transpose hK)
      (hsKernel_transpose hM) (hsKernel_transpose hL)).mono ?_ ?_
    · exact (hFm.stronglyMeasurable.norm).integral_prod_right' |>.aestronglyMeasurable
    · filter_upwards [hliftL, hliftM] with p hpL hpM
      have hLp : MemLp (fun t => L (p.2, t)) 2 vol :=
        memLp_two_of_aemeasurable
          ((measurable_section_fst hLm p.2).aestronglyMeasurable) hpL
      have hMp : MemLp (fun t => M (t, p.1)) 2 vol :=
        memLp_two_of_aemeasurable
          ((measurable_section_snd hMm p.1).aestronglyMeasurable) hpM
      have hstep : ∫ t : ℝ, ‖(fun q : (ℝ × ℝ) × ℝ =>
            K (q.1.1, q.1.2) * L (q.1.2, q.2) * M (q.2, q.1.1)) (p, t)‖ ∂vol
          ≤ |K (p.1, p.2)| * (Real.sqrt (secE2 L p.2) * Real.sqrt (secE1 M p.1)) := by
        calc ∫ t : ℝ, ‖(fun q : (ℝ × ℝ) × ℝ =>
                  K (q.1.1, q.1.2) * L (q.1.2, q.2) * M (q.2, q.1.1)) (p, t)‖ ∂vol
            = ∫ t : ℝ, |K (p.1, p.2)| * |L (p.2, t)| * |M (t, p.1)| ∂vol := by
              refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
              show ‖K (p.1, p.2) * L (p.2, t) * M (t, p.1)‖ = _
              rw [Real.norm_eq_abs, abs_mul, abs_mul]
          _ = ∫ t : ℝ, |K (p.1, p.2)| * (|L (p.2, t)| * |M (t, p.1)|) ∂vol := by
              refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
              ring
          _ = |K (p.1, p.2)| * ∫ t : ℝ, |L (p.2, t)| * |M (t, p.1)| ∂vol :=
              integral_const_mul _ _
          _ ≤ |K (p.1, p.2)| * (Real.sqrt (secE2 L p.2) * Real.sqrt (secE1 M p.1)) :=
              mul_le_mul_of_nonneg_left (integral_section_cs (p.2) (p.1) hLp hMp)
                (abs_nonneg _)
      have hnn : 0 ≤ |ktranspose K (p.2, p.1)| * Real.sqrt (secE2 (ktranspose M) p.1)
          * Real.sqrt (secE1 (ktranspose L) p.2) :=
        mul_nonneg (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
      calc ‖∫ t : ℝ, ‖(fun q : (ℝ × ℝ) × ℝ =>
                K (q.1.1, q.1.2) * L (q.1.2, q.2) * M (q.2, q.1.1)) (p, t)‖ ∂vol‖
          = ∫ t : ℝ, ‖(fun q : (ℝ × ℝ) × ℝ =>
                K (q.1.1, q.1.2) * L (q.1.2, q.2) * M (q.2, q.1.1)) (p, t)‖ ∂vol :=
            abs_of_nonneg (integral_nonneg fun t => norm_nonneg _)
        _ ≤ |K (p.1, p.2)| * (Real.sqrt (secE2 L p.2) * Real.sqrt (secE1 M p.1)) := hstep
        _ = ‖|ktranspose K (p.2, p.1)| * Real.sqrt (secE2 (ktranspose M) p.1)
              * Real.sqrt (secE1 (ktranspose L) p.2)‖ := by
            rw [Real.norm_eq_abs, abs_of_nonneg hnn]
            show |K (p.1, p.2)| * (Real.sqrt (secE2 L p.2) * Real.sqrt (secE1 M p.1))
              = |ktranspose K (p.2, p.1)| * Real.sqrt (secE2 (ktranspose M) p.1)
                * Real.sqrt (secE1 (ktranspose L) p.2)
            rw [show ktranspose K (p.2, p.1) = K (p.1, p.2) from rfl,
              show secE2 (ktranspose M) p.1 = secE1 M p.1 from rfl,
              show secE1 (ktranspose L) p.2 = secE2 L p.2 from rfl]
            ring

/-! ### Item (2): the `w ↔ q` splice — `cycleIntegral 3 K = chainCycleTriple K K K` -/

/-- The `((x, y), t)`-coordinate of the peel coordinates `(w, t)` with
`w = (z 0, z 1)`: the splice equiv `(Fin 2 → ℝ) × ℝ ≃ (ℝ × ℝ) × ℝ`. -/
private def pi2PairE : (Fin 2 → ℝ) × ℝ ≃ᵐ (ℝ × ℝ) × ℝ :=
  (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)).prodCongr (MeasurableEquiv.refl ℝ)

private theorem mp_pi2Pair :
    MeasurePreserving (⇑pi2PairE)
      ((Measure.pi fun _ : Fin 2 => vol).prod vol) ((vol.prod vol).prod vol) :=
  (measurePreserving_piFinTwo (fun _ : Fin 2 => vol)).prod (MeasurePreserving.id vol)

set_option maxHeartbeats 1000000 in
/-- **Item (2), the `w ↔ q` splice**: the kernel-side `k = 3` cycle functional equals
the triple chain integral in the `((x, y), t)`-coordinate encoding:
`cycleIntegral 3 K = chainCycleTriple K K K`.  Unconditional: the landed
`cycleIntegral_three_eq_tripleW` (`Fin 3` succAbove-peel + coordinate swap) composed
with the coordinate identification `MeasurePreserving.prod` of the landed
`measurePreserving_piFinTwo` with the identity (`MeasurePreserving.integral_comp'`
needs no integrability). -/
theorem K3CycleIntegral_three_eq_chainCycleTriple (K : ℝ × ℝ → ℝ) :
    cycleIntegral 3 K = chainCycleTriple K K K := by
  have hpt : ∀ w : (Fin 2 → ℝ) × ℝ,
      (fun q : (ℝ × ℝ) × ℝ => K (q.1.1, q.2) * K (q.2, q.1.2) * K (q.1.2, q.1.1)) (⇑pi2PairE w)
      = (fun w : (Fin 2 → ℝ) × ℝ => K (w.1 0, w.2) * K (w.2, w.1 1) * K (w.1 1, w.1 0)) w := by
    intro w
    rfl
  have hsplice : (∫ w : (Fin 2 → ℝ) × ℝ,
      (fun q : (ℝ × ℝ) × ℝ => K (q.1.1, q.2) * K (q.2, q.1.2) * K (q.1.2, q.1.1)) (⇑pi2PairE w)
      ∂((Measure.pi fun _ : Fin 2 => vol).prod vol))
      = (∫ q : (ℝ × ℝ) × ℝ,
          (fun q : (ℝ × ℝ) × ℝ => K (q.1.1, q.2) * K (q.2, q.1.2) * K (q.1.2, q.1.1)) q
          ∂((vol.prod vol).prod vol)) :=
    MeasurePreserving.integral_comp' mp_pi2Pair
      (fun q : (ℝ × ℝ) × ℝ => K (q.1.1, q.2) * K (q.2, q.1.2) * K (q.1.2, q.1.1))
  calc cycleIntegral 3 K
      = ∫ w : (Fin 2 → ℝ) × ℝ,
          (fun w : (Fin 2 → ℝ) × ℝ => K (w.1 0, w.2) * K (w.2, w.1 1) * K (w.1 1, w.1 0)) w
          ∂((Measure.pi fun _ : Fin 2 => vol).prod vol) := cycleIntegral_three_eq_tripleW K
    _ = ∫ w : (Fin 2 → ℝ) × ℝ,
          (fun q : (ℝ × ℝ) × ℝ => K (q.1.1, q.2) * K (q.2, q.1.2) * K (q.1.2, q.1.1))
            (⇑pi2PairE w)
          ∂((Measure.pi fun _ : Fin 2 => vol).prod vol) :=
            integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ∫ q : (ℝ × ℝ) × ℝ,
          (fun q : (ℝ × ℝ) × ℝ => K (q.1.1, q.2) * K (q.2, q.1.2) * K (q.1.2, q.1.1)) q
          ∂((vol.prod vol).prod vol) := hsplice
    _ = chainCycleTriple K K K := rfl

/-! ### Item (3): the cubic `HasSum` over the enumeration, to the `C_3(K)`-form -/

set_option maxHeartbeats 1000000 in
/-- **Item (3), the `k = 3` `HasSum`**: for the multiplicity-exact enumeration of the
compact symmetric kernel operator (`HS.exists_multiplicity_enumeration`), the cubic
series `val j ^ 3` `HasSum`s to the triple chain integral `chainCycleTriple K K K`
(the `C_3(K)`-form), conditional on the documented operator-side spectral bridge
`∑' j, val j ^ 3 = cycleIntegral 3 K` — the product-basis Parseval gap of
`Hurst.CycleTraceIdentification` (not landed; the summability side
`hasSum_general_k_pow` is landed in `Hurst.GeneralKHasSumComplete`, and the kernel-side
transport `K3CycleIntegral_three_eq_chainCycleTriple` is landed here, unconditional). -/
theorem hasSum_cubic_chainCycleTriple {K : ℝ × ℝ → ℝ} {hK : HSKernel K}
    (hCompact : IsCompactOperator (TOp K hK))
    (hsym : (↑(TOp K hK) : L2 →ₗ[ℝ] L2).IsSymmetric)
    {val : ℕ → ℝ} {vec : ℕ → L2}
    (hval : ∀ j, val j = 0 ∨ Module.End.HasEigenvector (TOpEnd' K hK) (val j) (vec j))
    (hmult : ∀ μ : ℝ, Module.End.HasEigenvalue (TOpEnd' K hK) μ → μ ≠ 0 →
      Nat.card {j : ℕ // val j = μ}
        = Module.finrank ℝ (Module.End.eigenspace (TOpEnd' K hK) μ))
    (hspec : ∑' j, val j ^ 3 = cycleIntegral 3 K) :
    HasSum (fun j => val j ^ 3) (chainCycleTriple K K K) := by
  rw [← K3CycleIntegral_three_eq_chainCycleTriple K, ← hspec]
  exact hasSum_general_k_pow hCompact hsym hval hmult 3 (by norm_num)

/-! ### Bonus: the `k = 3` chain-integrability instance for the peel induction -/

private theorem mp_swap_pi2' :
    MeasurePreserving (Prod.swap : ℝ × (Fin 2 → ℝ) → (Fin 2 → ℝ) × ℝ)
      (vol.prod (Measure.pi fun _ : Fin 2 => vol))
      ((Measure.pi fun _ : Fin 2 => vol).prod vol) :=
  ⟨measurable_swap, prod_swap⟩

/-- The `Fin 3`-peel transport equiv of the landed `pi3Equiv` (private there), with its
measure-preservation. -/
private def pi3E' : (Fin 3 → ℝ) ≃ᵐ (Fin 2 → ℝ) × ℝ :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 1).trans MeasurableEquiv.prodComm

private theorem mp_pi3' :
    MeasurePreserving (⇑pi3E') (Measure.pi fun _ : Fin 3 => vol)
      ((Measure.pi fun _ : Fin 2 => vol).prod vol) :=
  (measurePreserving_piFinSuccAbove (fun _ : Fin 3 => vol) 1).trans mp_swap_pi2'

private theorem cycleSucc_three_zero' : cycleSucc (0 : Fin 3) = 1 := by simp [cycleSucc]

private theorem cycleSucc_three_one' : cycleSucc (1 : Fin 3) = 2 := by simp [cycleSucc]

private theorem cycleSucc_three_two' : cycleSucc (2 : Fin 3) = 0 := by simp [cycleSucc]

set_option maxHeartbeats 1000000 in
/-- **Bonus, the `k = 3` chain-integrability instance**: the `Fin 3`-form cycle product
`z ↦ ∏ i, K (z i, z (cycleSucc i))` is integrable over `vol^3` for measurable HS
kernels — the `hP` instance that the general-`k` peel induction
(`Hurst.GeneralKPeelInduction.chainIntegral_kchain_eq`,
`cycleIntegral_eq_cycle2_pow`) carries, at `k = 3` (where
`kchain 1 0 K = fun _ => K`).  Transported from `K3Integrable_chainCycleTriple` through
the `Fin 3`-peel equiv and the splice equiv. -/
theorem integrable_chainProd_three {K : ℝ × ℝ → ℝ} (hKm : Measurable K) (hK : HSKernel K) :
    Integrable (fun (z : Fin 3 → ℝ) => ∏ i : Fin 3, K (z i, z (cycleSucc i)))
      (Measure.pi fun _ : Fin 3 => vol) := by
  classical
  have hFq : Integrable (fun q : (ℝ × ℝ) × ℝ =>
      K (q.1.1, q.2) * K (q.2, q.1.2) * K (q.1.2, q.1.1))
      ((vol.prod vol).prod vol) :=
    K3Integrable_chainCycleTriple hKm hKm hKm hK hK hK
  have hw : Integrable
      (fun w : (Fin 2 → ℝ) × ℝ =>
        (fun q : (ℝ × ℝ) × ℝ => K (q.1.1, q.2) * K (q.2, q.1.2) * K (q.1.2, q.1.1))
          (Prod.map (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)) id w))
      ((Measure.pi fun _ : Fin 2 => vol).prod vol) :=
    (mp_pi2Pair.integrable_comp_of_integrable hFq).congr
      (Filter.Eventually.of_forall fun w => rfl)
  have hz : Integrable
      (fun (z : Fin 3 → ℝ) =>
        (fun w : (Fin 2 → ℝ) × ℝ =>
          (fun q : (ℝ × ℝ) × ℝ => K (q.1.1, q.2) * K (q.2, q.1.2) * K (q.1.2, q.1.1))
            (Prod.map (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)) id w)) (⇑pi3E' z))
      (Measure.pi fun _ : Fin 3 => vol) :=
    (mp_pi3'.integrable_comp_of_integrable hw).congr
      (Filter.Eventually.of_forall fun z => rfl)
  refine hz.congr (Filter.Eventually.of_forall fun z => ?_)
  have h0 : (pi3E' z).1 0 = z 0 := by
    simp only [pi3E', MeasurableEquiv.trans_apply]; rfl
  have h2' : (pi3E' z).1 1 = z 2 := by
    simp only [pi3E', MeasurableEquiv.trans_apply]; rfl
  have h1' : (pi3E' z).2 = z 1 := by
    simp only [pi3E', MeasurableEquiv.trans_apply]; rfl
  show (fun (z : Fin 3 → ℝ) =>
      (fun w : (Fin 2 → ℝ) × ℝ =>
        (fun q : (ℝ × ℝ) × ℝ => K (q.1.1, q.2) * K (q.2, q.1.2) * K (q.1.2, q.1.1))
          (Prod.map (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)) id w)) (⇑pi3E' z)) z
    = ∏ i : Fin 3, K (z i, z (cycleSucc i))
  rw [Fin.prod_univ_three, cycleSucc_three_zero', cycleSucc_three_one',
    cycleSucc_three_two']
  show K ((pi3E' z).1 0, (pi3E' z).2) * K ((pi3E' z).2, (pi3E' z).1 1)
      * K ((pi3E' z).1 1, (pi3E' z).1 0)
    = K (z 0, z 1) * K (z 1, z 2) * K (z 2, z 0)
  rw [h0, h1', h2']

end HS

end
