import Hurst.GeneralKHasSumComplete
import Hurst.GeneralKPeel

/-!
# The closed general-`k` HasSum: the `hA` discharge, the w↔q splice, the `k = 3` closure

This file assembles the landed pieces of the general-`k` HasSum program
(`Hurst.HSCycleComposition`, `Hurst.GeneralKPeel`, `Hurst.GeneralKHasSumComplete`,
`Hurst.FrozenSpectralCount`) into the closed kernel-side chain:

1. **The `hA` discharge** (`HS.integrable_chainCycleTriple`): for everywhere-measurable
   HS kernels `K L M` the triple chain integrand
   `q ↦ K (q.1.1, q.2) * L (q.2, q.1.2) * M (q.1.2, q.1.1)` is integrable over
   `((vol.prod vol).prod vol)` — the documented route: the a.e. section
   Cauchy–Schwarz bound `∫_t |K(x,t) L(t,y)| ≤ √(secE2 K x) √(secE1 L y)`
   (`HS.section_cs`, the engine of `abs_compKernel_le` extracted), the `vol2`-level
   domination of the section-integral function by
   `p ↦ |M p.swap| · √(secE2 K p.1) · √(secE1 L p.2)` (Cauchy–Schwarz against the
   `MemLp 2` function `HS.memLp_sqrt_secE2_mul_secE1`, bounded by
   `hsNorm M · hsNorm K · hsNorm L`), and one Fubini split (`integrable_prod_iff`)
   discharging the `t`-section integrability.  This makes the landed
   `cycle2_compKernel_eq_triple` anchor unconditional
   (`HS.cycle2_compKernel_eq_triple'`).

2. **The w↔q splice** (`HS.cycleIntegral_three_eq_chainCycleTriple`): the
   `(Fin 2 → ℝ) × ℝ`-encoding of the `k = 3` Fubini transport
   `cycleIntegral_three_eq_tripleW` is identified with the `(ℝ × ℝ) × ℝ`-encoding
   `chainCycleTriple K K K` by the measure-preserving equiv
   `w ↦ ((w.1 0, w.1 1), w.2)` (`HS.spliceEquiv`; measure preservation by the
   rectangles argument on top of the landed `measurePreserving_piFinTwo`).
   Pure bookkeeping, no integrability needed.

3. **The `k = 3` kernel closure** (`HS.cycleIntegral_three_eq_cycle2`):
   `cycleIntegral 3 K = cycle2 (compKernel K K) K = chainCycleTriple K K K`,
   unconditional for everywhere-measurable HS kernels — the `k = 3` base of the peel
   induction, now free of the `hA` hypothesis.

4. **The closed general-`k` HasSum** (`HS.hasSum_general_k_closed`): the
   multiplicity-exact enumeration's `k`-th power series `HasSum`s to its own tsum for
   every `k ≥ 3` (the landed summability layer `hasSum_general_k_pow`), the tsum
   carries the envelope `∑' val ^ k ≤ hsNorm K ^ k`, and the kernel side carries the
   unconditional `k = 3` chain closure of items 2–3.

## Documented residue (NOT landed here; the two remaining gates of the exact
`HasSum (fun j => val j ^ k) (cycleIntegral k K)` for `k ≥ 3`)

* **Operator-side Parseval** (`Hurst.CycleTraceIdentification` residue): the
  identification `∑' j, val j ^ k = cycleIntegral k K` needs the product-basis
  Parseval `Σ_j κ_j^k = Σ_j ⟪(TOp K)^k e_j, e_j⟫` over the eigenbasis — the
  completeness of the tensor-product system `ψ_{ij}(x,y) = (e i)(x) · (e j)(y)` in
  `L²(vol2)`; mathlib v4.31 has nothing for `L²` of a product measure.  This gates
  the exact tsum-to-cycle identification for every `k` (at `k = 2` only the one-sided
  Bessel bound `sum_val_sq_le_hsNorm_sq_of_multEnum` is landed).
* **The general-`k` chain-integrability discharge** (the `hP` hypothesis of the landed
  peel induction `chainIntegral_withLast_ind`/`cycleIntegral_comp`,
  `Hurst.GeneralKPeel`): the `k = 3` instance is discharged here (item 1).  The
  general-`k` discharge is the iterated section Cauchy–Schwarz peel
  `S(m) : ∫ u(z₀) · ∏_{j≤m} |K(z_j, z_{j+1})| · v(z_{m+1}) ≤ hsNorm K ^ m · ‖u‖₂ ‖v‖₂`
  (base `m = 0`: the two-factor Cauchy–Schwarz on `vol2`; step: the section CS
  `∫_t |K(a,t)| |v(t)| ≤ √(secE2 K a) ‖v‖₂` with `v := √secE2 K` and
  `‖√secE2 K‖₂ = hsNorm K`; Tonelli–Fubini throughout, the integrands being
  nonnegative), after which `cycleIntegral_comp` gives
  `cycleIntegral (n+2) K = cycle2 (compPowL n K) K` unconditionally.  (The
  `Measurable.stronglyMeasurable` route for standard Borel spaces — the documented
  dialect fix of the `Exists`-encoding obstruction — is what the measurability
  side of this discharge consumes; on `ℝ`, `Fin`-powers thereof, it is discharged by
  `Measurable.stronglyMeasurable` as used in `stronglyMeasurable_compKernel`.)
-/

open MeasureTheory Measure Real Set
open scoped Real

noncomputable section

namespace HS

/-! ### Helpers: prop-lifting along coordinates and the section Cauchy–Schwarz bound -/

/-- Lift an a.e. property of the first coordinate to the product measure. -/
private theorem eventual_prop_fst {P : ℝ → Prop} (h : ∀ᵐ x ∂vol, P x) :
    ∀ᵐ p : ℝ × ℝ ∂vol2, P p.1 := by
  rw [ae_iff] at h ⊢
  have hset : {p : ℝ × ℝ | ¬ P p.1}
      = {x : ℝ | ¬ P x} ×ˢ (univ : Set ℝ) := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_prod]
    exact ⟨fun hneg => ⟨hneg, Set.mem_univ _⟩, fun hpair => hpair.1⟩
  rw [hset, Measure.prod_prod, h]
  simp

/-- Lift an a.e. property of the second coordinate to the product measure. -/
private theorem eventual_prop_snd {P : ℝ → Prop} (h : ∀ᵐ y ∂vol, P y) :
    ∀ᵐ p : ℝ × ℝ ∂vol2, P p.2 := by
  rw [ae_iff] at h ⊢
  have hset : {p : ℝ × ℝ | ¬ P p.2} = (univ : Set ℝ) ×ˢ {y : ℝ | ¬ P y} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_prod]
    exact ⟨fun hneg => ⟨Set.mem_univ _, hneg⟩, fun hpair => hpair.2⟩
  rw [hset, Measure.prod_prod, h]
  simp

/-- Nat-pow vs real-pow bridge on sections (instance of the landed
`integral_pow_two` pattern on `vol`). -/
private theorem integral_pow_two_vol' (u : ℝ → ℝ) :
    ∫ t : ℝ, u t ^ (2 : ℝ) ∂vol = ∫ t : ℝ, u t ^ 2 ∂vol := by
  apply integral_congr_ae
  filter_upwards with t
  rw [Real.rpow_two, pow_two]

/-- **The section Cauchy–Schwarz bound** (the engine of `abs_compKernel_le`,
extracted): where the sections are `L²`,
`∫_t |K(x,t)| |L(t,y)| ≤ √(secE2 K x) √(secE1 L y)`. -/
private theorem section_cs {K L : ℝ × ℝ → ℝ} (x y : ℝ)
    (hx : MemLp (fun t => K (x, t)) 2 vol) (hy : MemLp (fun t => L (t, y)) 2 vol) :
    ∫ t : ℝ, |K (x, t)| * |L (t, y)| ∂vol
      ≤ Real.sqrt (secE2 K x) * Real.sqrt (secE1 L y) := by
  have hx2 : MemLp (fun t => K (x, t)) (ENNReal.ofReal 2) vol := by
    rw [real_two_ofReal]; exact hx
  have hy2 : MemLp (fun t => L (t, y)) (ENNReal.ofReal 2) vol := by
    rw [real_two_ofReal]; exact hy
  have hcs := integral_mul_norm_le_Lp_mul_Lq holderTriple221 hx2 hy2
  simp only [Real.norm_eq_abs] at hcs
  rw [integral_pow_two_vol' (fun t => |K (x, t)|),
    integral_pow_two_vol' (fun t => |L (t, y)|)] at hcs
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

/-! ### The `hA` discharge: integrability of the triple chain integrand -/

/-- The triple chain integrand of `chainCycleTriple K L M` (named for bookkeeping). -/
private def tripl (K L M : ℝ × ℝ → ℝ) (q : (ℝ × ℝ) × ℝ) : ℝ :=
  K (q.1.1, q.2) * L (q.2, q.1.2) * M (q.1.2, q.1.1)

/-- Strong measurability of the section-energy functions (the landed private
`stronglyMeasurable_secE2`/`secE1`, re-declared). -/
private theorem sm_secE2 {K : ℝ × ℝ → ℝ} (hKm : Measurable K) :
    StronglyMeasurable (secE2 K) :=
  (hKm.pow_const 2).stronglyMeasurable.integral_prod_right'

private theorem sm_secE1 {K : ℝ × ℝ → ℝ} (hKm : Measurable K) :
    StronglyMeasurable (secE1 K) :=
  sm_secE2 (hKm.comp measurable_swap)

/-- The `hsNorm_comp_le` domination function `p ↦ √(secE2 K p.1) · √(secE1 L p.2)`
is `MemLp 2 vol2`. -/
private theorem memLp_sqrt_secE2_mul_secE1 {K L : ℝ × ℝ → ℝ} (hKm : Measurable K)
    (hLm : Measurable L) (hIK : Integrable (secE2 K) vol) (hIL : Integrable (secE1 L) vol) :
    MemLp (fun p : ℝ × ℝ => Real.sqrt (secE2 K p.1) * Real.sqrt (secE1 L p.2)) 2 vol2 := by
  have hae : AEStronglyMeasurable
      (fun p : ℝ × ℝ => Real.sqrt (secE2 K p.1) * Real.sqrt (secE1 L p.2)) vol2 :=
    (((sm_secE2 hKm).measurable.sqrt.comp measurable_fst).mul
      ((sm_secE1 hLm).measurable.sqrt.comp measurable_snd)).aestronglyMeasurable
  have hsq : Integrable
      (fun p : ℝ × ℝ => (Real.sqrt (secE2 K p.1) * Real.sqrt (secE1 L p.2)) ^ 2) vol2 := by
    have hprod : Integrable (fun p : ℝ × ℝ => secE2 K p.1 * secE1 L p.2) vol2 :=
      Integrable.op_fst_snd (op := fun a b : ℝ => a * b) (by fun_prop)
        ⟨1, fun a b => by simp [Real.norm_eq_abs]⟩ hIK hIL
    refine hprod.congr (Filter.Eventually.of_forall fun p => ?_)
    have hn1 : 0 ≤ secE2 K p.1 := integral_nonneg fun _ => sq_nonneg _
    have hn2 : 0 ≤ secE1 L p.2 := integral_nonneg fun _ => sq_nonneg _
    show secE2 K p.1 * secE1 L p.2
        = (Real.sqrt (secE2 K p.1) * Real.sqrt (secE1 L p.2)) ^ 2
    rw [mul_pow, Real.sq_sqrt hn1, Real.sq_sqrt hn2]
  exact memLp_two_of_aemeasurable hae hsq

/-- **The `hA` discharge**: for everywhere-measurable HS kernels the triple chain
integrand of `chainCycleTriple K L M` is integrable over `((vol.prod vol).prod vol)`
(bounded in `L¹` by `hsNorm M · hsNorm K · hsNorm L`).  This discharges the standing
hypothesis `hA` of the landed `cycle2_compKernel_eq_triple` anchor. -/
theorem integrable_chainCycleTriple {K L M : ℝ × ℝ → ℝ}
    (hKm : Measurable K) (hLm : Measurable L) (hMm : Measurable M)
    (hK : HSKernel K) (hL : HSKernel L) (hM : HSKernel M) :
    Integrable (tripl K L M) ((vol.prod vol).prod vol) := by
  classical
  have hAm : Measurable (tripl K L M) := by
    refine ((hKm.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
      (hLm.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))).mul ?_
    exact hMm.comp ((measurable_snd.comp measurable_fst).prodMk
      (measurable_fst.comp measurable_fst))
  -- a.e. section square-integrability on `vol2`
  have hsections : ∀ᵐ p : ℝ × ℝ ∂vol2,
      MemLp (fun t => K (p.1, t)) 2 vol ∧ MemLp (fun t => L (t, p.2)) 2 vol := by
    filter_upwards [eventual_prop_fst (eventual_memLp_section_fst hKm hK),
      eventual_prop_snd (eventual_memLp_section_snd hLm hL)] with p hx hy
    exact ⟨hx, hy⟩
  -- the section-integral function is dominated by `|M p.swap| · √secE2 · √secE1`
  have hdom : ∀ᵐ p : ℝ × ℝ ∂vol2,
      ∫ t : ℝ, ‖tripl K L M (p, t)‖ ∂vol
        ≤ |M (p.swap)| * Real.sqrt (secE2 K p.1) * Real.sqrt (secE1 L p.2) := by
    filter_upwards [hsections] with p hp
    obtain ⟨hx, hy⟩ := hp
    have hsplit : ∀ t : ℝ, ‖tripl K L M (p, t)‖
        = |M (p.2, p.1)| * (|K (p.1, t)| * |L (t, p.2)|) := by
      intro t
      show ‖K (p.1, t) * L (t, p.2) * M (p.2, p.1)‖ = _
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hsplit), integral_const_mul]
    calc |M (p.2, p.1)| * ∫ t : ℝ, |K (p.1, t)| * |L (t, p.2)| ∂vol
        ≤ |M (p.2, p.1)| * (Real.sqrt (secE2 K p.1) * Real.sqrt (secE1 L p.2)) :=
          mul_le_mul_of_nonneg_left (section_cs p.1 p.2 hx hy) (abs_nonneg _)
      _ = |M (p.swap)| * Real.sqrt (secE2 K p.1) * Real.sqrt (secE1 L p.2) := by
          rw [show p.swap = (p.2, p.1) from rfl]; ring
  -- the dominator is integrable over `vol2` (Cauchy–Schwarz of `|ktranspose M|`
  -- against the `MemLp 2` section-energy factor)
  have hMemb : MemLp (fun p : ℝ × ℝ => Real.sqrt (secE2 K p.1) * Real.sqrt (secE1 L p.2))
      2 vol2 := memLp_sqrt_secE2_mul_secE1 hKm hLm (integrable_secE2 hK) (integrable_secE1 hL)
  have hDomInt : Integrable
      (fun p : ℝ × ℝ => |M (p.swap)| * Real.sqrt (secE2 K p.1) * Real.sqrt (secE1 L p.2))
      vol2 := by
    have hp := memLp_one_iff_integrable.mp (MemLp.mul' (hsKernel_transpose hM) hMemb)
    have hp1 := hp.abs
    refine hp1.congr (Filter.Eventually.of_forall fun p => ?_)
    show |Real.sqrt (secE2 K p.1) * Real.sqrt (secE1 L p.2) * ktranspose M p|
        = |M (p.swap)| * Real.sqrt (secE2 K p.1) * Real.sqrt (secE1 L p.2)
    have hkt : ktranspose M p = M (p.swap) := rfl
    calc |Real.sqrt (secE2 K p.1) * Real.sqrt (secE1 L p.2) * ktranspose M p|
        = |Real.sqrt (secE2 K p.1) * Real.sqrt (secE1 L p.2)| * |ktranspose M p| :=
          abs_mul _ _
      _ = (Real.sqrt (secE2 K p.1) * Real.sqrt (secE1 L p.2)) * |M (p.swap)| := by
          rw [abs_of_nonneg
            (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)), hkt]
      _ = |M (p.swap)| * Real.sqrt (secE2 K p.1) * Real.sqrt (secE1 L p.2) := by ring
  -- first Fubini split: integrable sections + integrable section-integral function
  have hBmeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => ∫ t : ℝ, ‖tripl K L M (p, t)‖ ∂vol) vol2 :=
    (hAm.norm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
  have hB : Integrable (fun p : ℝ × ℝ => ∫ t : ℝ, ‖tripl K L M (p, t)‖ ∂vol) vol2 := by
    refine hDomInt.mono hBmeas ?_
    filter_upwards [hdom] with p hp
    have hnB : 0 ≤ ∫ t : ℝ, ‖tripl K L M (p, t)‖ ∂vol :=
      integral_nonneg fun _ => norm_nonneg _
    have hnD : 0 ≤ |M (p.swap)| * Real.sqrt (secE2 K p.1) * Real.sqrt (secE1 L p.2) :=
      by positivity
    show ‖(fun p : ℝ × ℝ => ∫ t : ℝ, ‖tripl K L M (p, t)‖ ∂vol) p‖
        ≤ ‖(fun p : ℝ × ℝ => |M (p.swap)| * Real.sqrt (secE2 K p.1)
            * Real.sqrt (secE1 L p.2)) p‖
    rw [Real.norm_eq_abs, abs_of_nonneg hnB, Real.norm_eq_abs, abs_of_nonneg hnD]
    exact hp
  have hsec : ∀ᵐ p : ℝ × ℝ ∂vol2, Integrable (fun t => tripl K L M (p, t)) vol := by
    filter_upwards [hsections] with p hp
    obtain ⟨hx, hy⟩ := hp
    have h1 : Integrable (fun t => K (p.1, t) * L (t, p.2)) vol :=
      memLp_one_iff_integrable.mp (MemLp.mul' hy hx)
    have h2 : Integrable (fun t => |M (p.2, p.1)| * (K (p.1, t) * L (t, p.2))) vol :=
      h1.const_mul _
    have h3 : Integrable (fun t => |M (p.2, p.1)| * |K (p.1, t) * L (t, p.2)|) vol := by
      refine h2.abs.congr (Filter.Eventually.of_forall fun t => ?_)
      show |(|M (p.2, p.1)| * (K (p.1, t) * L (t, p.2)))|
          = |M (p.2, p.1)| * |K (p.1, t) * L (t, p.2)|
      rw [abs_mul, abs_of_nonneg (abs_nonneg _)]
    have h4 : Integrable (fun t => |tripl K L M (p, t)|) vol := by
      refine h3.congr (Filter.Eventually.of_forall fun t => ?_)
      show |M (p.2, p.1)| * |K (p.1, t) * L (t, p.2)|
          = |K (p.1, t) * L (t, p.2) * M (p.2, p.1)|
      rw [abs_mul (K (p.1, t) * L (t, p.2)) (M (p.2, p.1)),
        abs_mul (K (p.1, t)) (L (t, p.2))]
      ring
    have h5 : AEStronglyMeasurable (fun t => tripl K L M (p, t)) vol :=
      (hAm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    refine h4.mono h5 ?_
    filter_upwards with t
    show ‖tripl K L M (p, t)‖ ≤ ‖|tripl K L M (p, t)|‖
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact le_abs_self _
  exact (integrable_prod_iff hAm.aestronglyMeasurable).mpr ⟨hsec, hB⟩

/-- **The `hA` anchor, unconditional**: the composite-operator pairing
`cycle2 (compKernel K L) M` equals the triple chain integral `chainCycleTriple K L M`
for everywhere-measurable HS kernels (the landed `cycle2_compKernel_eq_triple` with
the discharge of this file). -/
theorem cycle2_compKernel_eq_triple' {K L M : ℝ × ℝ → ℝ}
    (hKm : Measurable K) (hLm : Measurable L) (hMm : Measurable M)
    (hK : HSKernel K) (hL : HSKernel L) (hM : HSKernel M) :
    cycle2 (compKernel K L) M = chainCycleTriple K L M :=
  cycle2_compKernel_eq_triple (integrable_chainCycleTriple hKm hLm hMm hK hL hM)

/-! ### The w↔q splice: the `Fin`-encoding integral equals the pair-encoding integral -/

/-- The splice equiv: `w ↦ ((w.1 0, w.1 1), w.2)` from the `(Fin 2 → ℝ) × ℝ`-encoding
of the triple space to the `(ℝ × ℝ) × ℝ`-encoding. -/
private def spliceEquiv : (Fin 2 → ℝ) × ℝ ≃ᵐ (ℝ × ℝ) × ℝ :=
  (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)).prodCongr (MeasurableEquiv.refl ℝ)

private theorem spliceEquiv_apply (w : (Fin 2 → ℝ) × ℝ) :
    spliceEquiv w = ((w.1 0, w.1 1), w.2) := by
  unfold spliceEquiv
  show ((MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)).prodCongr
      (MeasurableEquiv.refl ℝ)) w = _
  rfl

/-- The splice equiv preserves the iterated product measure (sections argument on
top of the landed `measurePreserving_piFinTwo`). -/
private theorem measurePreserving_splice :
    MeasurePreserving spliceEquiv
      ((Measure.pi fun _ : Fin 2 => vol).prod vol) ((vol.prod vol).prod vol) := by
  refine ⟨spliceEquiv.measurable, ?_⟩
  ext s hs
  have hp : MeasurableSet (spliceEquiv ⁻¹' s) := spliceEquiv.measurable hs
  have hsec2 : ∀ p : ℝ × ℝ, MeasurableSet (Prod.mk p ⁻¹' s) :=
    fun p => measurable_prodMk_left hs
  have hsetall : ∀ w : Fin 2 → ℝ,
      Prod.mk w ⁻¹' (spliceEquiv ⁻¹' s) = Prod.mk ((w 0, w 1) : ℝ × ℝ) ⁻¹' s := by
    intro w
    ext t
    simp only [Set.mem_preimage, spliceEquiv_apply]
  simp_rw [Measure.map_apply spliceEquiv.measurable hs, Measure.prod_apply hp,
    Measure.prod_apply hs]
  refine Eq.trans (lintegral_congr_ae (Filter.Eventually.of_forall fun w => ?_))
    ((measurePreserving_piFinTwo (fun _ : Fin 2 => vol)).lintegral_comp
      (measurable_measure_prodMk_left hs))
  show vol (Prod.mk w ⁻¹' (spliceEquiv ⁻¹' s)) = vol (Prod.mk ((w 0, w 1) : ℝ × ℝ) ⁻¹' s)
  exact congrArg vol (hsetall w)

/-- **The w↔q splice**: the `k = 3` Fubini transport's `(Fin 2 → ℝ) × ℝ`-encoding
(`cycleIntegral_three_eq_tripleW`) equals the `(ℝ × ℝ) × ℝ`-encoding
`chainCycleTriple K K K`.  Pure measure-theoretic bookkeeping (no integrability). -/
theorem cycleIntegral_three_eq_chainCycleTriple (K : ℝ × ℝ → ℝ) :
    cycleIntegral 3 K = chainCycleTriple K K K := by
  rw [cycleIntegral_three_eq_tripleW K]
  have hcomp : ∫ w : (Fin 2 → ℝ) × ℝ,
      K (w.1 0, w.2) * K (w.2, w.1 1) * K (w.1 1, w.1 0)
      ∂((Measure.pi fun _ : Fin 2 => vol).prod vol)
      = ∫ q : (ℝ × ℝ) × ℝ,
          K (q.1.1, q.2) * K (q.2, q.1.2) * K (q.1.2, q.1.1)
          ∂((vol.prod vol).prod vol) := by
    refine Eq.trans ?_ (measurePreserving_splice.integral_comp'
      (fun q : (ℝ × ℝ) × ℝ => K (q.1.1, q.2) * K (q.2, q.1.2) * K (q.1.2, q.1.1)))
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    show (fun q : (ℝ × ℝ) × ℝ =>
        K (q.1.1, q.2) * K (q.2, q.1.2) * K (q.1.2, q.1.1)) (spliceEquiv w)
        = K (w.1 0, w.2) * K (w.2, w.1 1) * K (w.1 1, w.1 0)
    rw [spliceEquiv_apply]
  rw [hcomp]
  rfl

/-! ### The `k = 3` kernel closure -/

/-- **The `k = 3` kernel closure (the peel-induction base, unconditional)**: for an
everywhere-measurable HS kernel, the `3`-cycle integral equals the composite-operator
trace form `cycle2 (compKernel K K) K`, and both equal the triple chain integral
`chainCycleTriple K K K` — the landed `k = 3` anchors with the `hA` discharge and the
w↔q splice of this file. -/
theorem cycleIntegral_three_eq_cycle2 (K : ℝ × ℝ → ℝ)
    (hKm : Measurable K) (hK : HSKernel K) :
    cycleIntegral 3 K = cycle2 (compKernel K K) K ∧
      cycleIntegral 3 K = chainCycleTriple K K K ∧
      cycle2 (compKernel K K) K = chainCycleTriple K K K := by
  refine ⟨?_, cycleIntegral_three_eq_chainCycleTriple K, ?_⟩
  · exact (cycleIntegral_three_eq_chainCycleTriple K).trans
      (cycle2_compKernel_eq_triple' hKm hKm hKm hK hK hK).symm
  · exact cycle2_compKernel_eq_triple' hKm hKm hKm hK hK hK

/-! ### The closed general-`k` HasSum -/

/-- **The closed general-`k` HasSum (`k ≥ 3`)**: for the multiplicity-exact
enumeration `val` of the compact symmetric kernel operator (with its eigenbasis
`vec`), the `k`-th power series `HasSum`s to its own tsum for every `k ≥ 3` (the
landed summability layer), the tsum carries the envelope
`∑' val ^ k ≤ hsNorm K ^ k` (via `val j ^ k ≤ |val j| ^ k` and the landed
interpolation bound), and the kernel side carries the unconditional `k = 3` chain
closure `cycleIntegral 3 K = cycle2 (compKernel K K) K = chainCycleTriple K K K`.
The exact upgrade of the tsum target to `cycleIntegral k K` for `k ≥ 3` is gated on
the operator-side product-basis Parseval step and the general-`k`
chain-integrability discharge — both documented residues (module docstring). -/
theorem hasSum_general_k_closed (K : ℝ × ℝ → ℝ) (hKm : Measurable K) (hK : HSKernel K)
    (hCompact : IsCompactOperator (TOp K hK))
    (hsym : (↑(TOp K hK) : L2 →ₗ[ℝ] L2).IsSymmetric)
    {val : ℕ → ℝ} {vec : ℕ → L2}
    (hval : ∀ j, val j = 0 ∨ Module.End.HasEigenvector (TOpEnd' K hK) (val j) (vec j))
    (hmult : ∀ μ : ℝ, Module.End.HasEigenvalue (TOpEnd' K hK) μ → μ ≠ 0 →
      Nat.card {j : ℕ // val j = μ}
        = Module.finrank ℝ (Module.End.eigenspace (TOpEnd' K hK) μ))
    (k : ℕ) (hk : 3 ≤ k) :
    HasSum (fun j => val j ^ k) (∑' j, val j ^ k)
      ∧ (∑' j, val j ^ k ≤ hsNorm K ^ k)
      ∧ (cycleIntegral 3 K = cycle2 (compKernel K K) K
          ∧ cycle2 (compKernel K K) K = chainCycleTriple K K K) := by
  refine ⟨hasSum_general_k_pow hCompact hsym hval hmult k (by omega), ?_, ?_⟩
  · have habs := summable_abs_pow_of_multEnum hCompact hsym hval hmult k (by omega)
    have hconv : Summable (fun j => val j ^ k) :=
      summable_abs_iff.mp (habs.congr fun j => by rw [abs_pow])
    have hpoint : ∀ j : ℕ, val j ^ k ≤ |val j| ^ k := by
      intro j
      rw [← abs_pow]
      exact le_abs_self _
    calc ∑' j, val j ^ k
        ≤ ∑' j, |val j| ^ k := hasSum_le hpoint hconv.hasSum habs.hasSum
      _ ≤ hsNorm K ^ k := tsum_abs_pow_le_multEnum hCompact hsym hval hmult k (by omega)
  · exact ⟨(cycleIntegral_three_eq_cycle2 K hKm hK).1,
      (cycleIntegral_three_eq_cycle2 K hKm hK).2.2⟩

end HS

end
