import Hurst.HSOperatorFoundation
import Hurst.HSOperatorLayer2
import Hurst.HSOperatorLayer3
import Hurst.HSCycleComposition
import Hurst.GeneralKPeelInduction
import Hurst.FrozenSpectralEnumeration

/-!
# hPair: the operator-power identification `T^k = TOp K ∘ TOp (compPowR (k-2) K)`

This file formalizes spec §6 (`general_k_gate_math_spec.md`): the a.e. section formula
of the Riesz representers, the general kernel-composition action of `TOp`, and the
tower induction identifying the kernel operator of the right-growing tower
`compPowR n K` with the `(n+1)`-st power of `TOp K`.

## Main results

* `HS.sectionInt K f` — the section-integral function `x ↦ ∫ K (x, y) · f y ∂vol`.
* `TOp_eq_sectionIntegral` — **Step 1 (the a.e. section formula)**: for an HS kernel
  `K` and `f : L2`, `TOp K hK f` equals (as an `L2` element, equivalently a.e.)
  `MemLp.toLp (sectionInt K f)`; `coe_TOp_eq_sectionIntegral` gives the a.e. form
  `⇑(TOp K hK f) =ᵐ[vol] sectionInt K f`.  Proof: the landed defining pairing
  (`inner_TOp`) + Fubini (`integrable_kintegrand`, `integral_prod`) + section
  Cauchy–Schwarz + the Riesz representer uniqueness (`eq_of_forall_inner_eq`).
* `kpair_compKernel_apply` — **Step 2 (composition of the pairings)**:
  `kpair A (TOpFun B hB x) g = kpair (compKernel A B) x g`, by two Fubini steps
  (the quadruple chain integrand is integrable by the section Cauchy–Schwarz chain,
  `integrable_chain4`) and the coordinate flip `tripleFlip` `(u, v, t) ↦ (u, t, v)`
  (measure preserving, `measurePreserving_tripleFlip`).
* `TOp_compKernel_apply` / `TOp_compKernel` — the composition action
  `TOp (compKernel A B) = TOp A ∘ TOp B` (Riesz representer uniqueness).
* `TOp_compPowR_apply` — **the tower induction**:
  `TOp (compPowR n K) x = (TOp K hK)^(n+1) x`.
* `TOpEnd'_pow_apply` — the CLM↔`Module.End` transport for powers.
* `hPair_pow_succ` / `hPair_uniform` / `hPair_contract` — **the downstream contract**
  consumed by `Hurst/GeneralKHasSumFinal.lean`:
  `(TOp K hK) ((TOp (compPowR (k - 2) K) hKL) x) = (TOpEnd' K hK ^ k) x`.

Deviations from the frozen shapes of `Hurst/GeneralKHasSumFinal.lean`: the theorems
additionally carry `hKm : Measurable K` (the landed tower constructor
`hsKernel_compPowR` requires it; every downstream consumer carries `hKmMeas`), and the
k-uniform variant is stated as `∀ k, 2 ≤ k → ∀ x, …` since the `2 ≤ k`-free packaging
`∀ k x, …` of the consumer is false at `k < 2` (`compPowR (k-2) K = K` there, so the
claim would read `T (T x) = x`).  The consumers only use `hPair` at `k ≥ 2`
(`gate_of_bridge` carries `hk : 2 ≤ k` in scope), so the one-line adaptation
`fun k hk x => hPair_uniform hKm hK k hk x` discharges their hypotheses.
-/

set_option maxHeartbeats 1000000

open MeasureTheory Measure Real Set
open scoped Real

noncomputable section

namespace HS

/-! ### Small a.e.-lifting helpers -/

/-- Lift an a.e. property of the first coordinate to the product. -/
theorem eventual_fst_prop {P : ℝ → Prop} (h : ∀ᵐ x ∂vol, P x) :
    ∀ᵐ p ∂vol2, P p.1 := by
  have h' : ∀ᵐ x : ℝ ∂vol, P x := h
  rw [ae_iff] at h'
  show ∀ᵐ p : ℝ × ℝ ∂vol2, P p.1
  rw [ae_iff]
  have hset : {p : ℝ × ℝ | ¬ P p.1} = {x : ℝ | ¬ P x} ×ˢ (univ : Set ℝ) := by
    ext p
    simp [Set.mem_prod]
  rw [hset, Measure.prod_prod, h']
  simp

/-- Lift an a.e. property of the second coordinate to the product. -/
theorem eventual_snd_prop {P : ℝ → Prop} (h : ∀ᵐ y ∂vol, P y) :
    ∀ᵐ p ∂vol2, P p.2 := by
  have h' : ∀ᵐ y : ℝ ∂vol, P y := h
  rw [ae_iff] at h'
  show ∀ᵐ p : ℝ × ℝ ∂vol2, P p.2
  rw [ae_iff]
  have hset : {p : ℝ × ℝ | ¬ P p.2} = (univ : Set ℝ) ×ˢ {y : ℝ | ¬ P y} := by
    ext p
    simp [Set.mem_prod]
  rw [hset, Measure.prod_prod, h']
  simp

/-- The square of an a.e. measurable real function is a.e. measurable. -/
private theorem aes_two {α : Type*} [MeasurableSpace α] {f : α → ℝ} {μ : Measure α}
    (h : AEStronglyMeasurable f μ) : AEStronglyMeasurable (fun p : α => f p ^ 2) μ := by
  obtain ⟨g, hgme, hgc⟩ := h
  refine ⟨g * g, hgme.mul hgme, ?_⟩
  filter_upwards [hgc] with p hp
  show f p ^ 2 = (g * g) p
  rw [hp, pow_two, Pi.mul_apply]

/-- The absolute value of an a.e. measurable real function is a.e. measurable. -/
private theorem aes_abs {α : Type*} [MeasurableSpace α] {f : α → ℝ} {μ : Measure α}
    (h : AEStronglyMeasurable f μ) : AEStronglyMeasurable (fun p : α => |f p|) μ := by
  refine h.norm.congr ?_
  exact Filter.Eventually.of_forall fun p => (Real.norm_eq_abs _).symm

/-- An a.e.-equality of one-dimensional functions lifts through the projection
`q ↦ q.1.2` to the triple space. -/
private theorem aes_lift_12 {f : ℝ → ℝ} {g : ℝ → ℝ}
    (hsm : StronglyMeasurable g) (h : f =ᵐ[vol] g) :
    AEStronglyMeasurable (fun q : (ℝ × ℝ) × ℝ => f q.1.2) ((vol.prod vol).prod vol) := by
  refine ⟨fun q => g q.1.2, hsm.comp_measurable (measurable_snd.comp measurable_fst), ?_⟩
  have hN : ((vol.prod vol).prod vol) {q : (ℝ × ℝ) × ℝ | ¬(f q.1.2 = g q.1.2)} = 0 := by
    have hset : {q : (ℝ × ℝ) × ℝ | ¬(f q.1.2 = g q.1.2)}
        = ((univ : Set ℝ) ×ˢ {r : ℝ | ¬(f r = g r)}) ×ˢ (univ : Set ℝ) := by
      ext q
      simp [Set.mem_prod]
    have hNvol : (vol) {r : ℝ | ¬(f r = g r)} = 0 := ae_iff.mp h
    rw [hset, Measure.prod_prod, Measure.prod_prod, hNvol]
    simp
  exact ae_iff.mpr hN

/-- An a.e.-equality of one-dimensional functions lifts through the projection
`q ↦ q.1.1` to the triple space. -/
private theorem aes_lift_11 {f : ℝ → ℝ} {g : ℝ → ℝ}
    (hsm : StronglyMeasurable g) (h : f =ᵐ[vol] g) :
    AEStronglyMeasurable (fun q : (ℝ × ℝ) × ℝ => f q.1.1) ((vol.prod vol).prod vol) := by
  refine ⟨fun q => g q.1.1, hsm.comp_measurable (measurable_fst.comp measurable_fst), ?_⟩
  have hN : ((vol.prod vol).prod vol) {q : (ℝ × ℝ) × ℝ | ¬(f q.1.1 = g q.1.1)} = 0 := by
    have hset : {q : (ℝ × ℝ) × ℝ | ¬(f q.1.1 = g q.1.1)}
        = ({r : ℝ | ¬(f r = g r)} ×ˢ (univ : Set ℝ)) ×ˢ (univ : Set ℝ) := by
      ext q
      simp [Set.mem_prod]
    have hNvol : (vol) {r : ℝ | ¬(f r = g r)} = 0 := ae_iff.mp h
    rw [hset, Measure.prod_prod, Measure.prod_prod, hNvol]
    simp
  exact ae_iff.mpr hN

/-- Nat-pow vs real-pow bridge on one-dimensional sections. -/
private theorem integral_abs_rpow_two (u : ℝ → ℝ) :
    ∫ t : ℝ, |u t| ^ (2 : ℝ) ∂vol = ∫ t : ℝ, |u t| ^ 2 ∂vol := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  show |u t| ^ (2 : ℝ) = |u t| ^ 2
  rw [Real.rpow_two, pow_two]

/-- `Integrable (secE2 K)` from the `integrable_prod_iff` machinery. -/
private theorem integrable_secE2_of {K : ℝ × ℝ → ℝ} (hK : HSKernel K) :
    Integrable (secE2 K) vol := by
  obtain ⟨-, hnorm⟩ := (integrable_prod_iff (aes_two (hK.1 : AEStronglyMeasurable K vol2))).mp
    (MemLp.integrable_sq hK)
  refine hnorm.congr (Filter.Eventually.of_forall fun u => ?_)
  show (∫ y : ℝ, ‖K (u, y) ^ 2‖ ∂vol) = (∫ y : ℝ, K (u, y) ^ 2 ∂vol)
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show ‖K (u, y) ^ 2‖ = K (u, y) ^ 2
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]

/-- `Integrable (secE1 K)` from the `integrable_prod_iff` machinery. -/
private theorem integrable_secE1_of {K : ℝ × ℝ → ℝ} (hK : HSKernel K) :
    Integrable (secE1 K) vol := by
  obtain ⟨-, hnorm⟩ := (integrable_prod_iff (aes_two
    (hK.1.prod_swap : AEStronglyMeasurable (fun z : ℝ × ℝ => K z.swap) vol2))).mp
    (MemLp.integrable_sq (hsKernel_transpose hK))
  refine hnorm.congr (Filter.Eventually.of_forall fun v => ?_)
  show (∫ t : ℝ, ‖ktranspose K (v, t) ^ 2‖ ∂vol) = (∫ t : ℝ, K (t, v) ^ 2 ∂vol)
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  show ‖ktranspose K (v, t) ^ 2‖ = K (t, v) ^ 2
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  rfl

/-! ### Step 1: the a.e. section formula -/

/-- The section-integral function `x ↦ ∫ K (x, y) · f y ∂vol` of a kernel against an
`L2` function. -/
def sectionInt (K : ℝ × ℝ → ℝ) (f : L2) : ℝ → ℝ :=
  fun x => ∫ y : ℝ, K (x, y) * ⇑f y ∂vol

/-- The section-integral function is square-integrable (section Cauchy–Schwarz +
Fubini): `MemLp (sectionInt K f) 2 vol`. -/
theorem memLp_sectionInt {K : ℝ × ℝ → ℝ} (hK : HSKernel K) (f : L2) :
    MemLp (sectionInt K f) 2 vol := by
  classical
  -- a.e. square-integrability of the sections of `K`
  obtain ⟨hsecSq, -⟩ := (integrable_prod_iff (aes_two (hK.1 : AEStronglyMeasurable K vol2))).mp
    (MemLp.integrable_sq hK)
  have hsecE2 : Integrable (secE2 K) vol := integrable_secE2_of hK
  -- a.e. `MemLp 2` of the sections
  have hsecAes : ∀ᵐ x ∂vol, AEStronglyMeasurable (fun y : ℝ => K (x, y)) vol :=
    (AEStronglyMeasurable.prodMk_left (μ := vol) (ν := vol)
      (hK.1 : AEStronglyMeasurable K vol2))
  have hsecMem : ∀ᵐ x ∂vol, MemLp (fun y : ℝ => K (x, y)) 2 vol := by
    filter_upwards [hsecSq, hsecAes] with x hx hae
    exact memLp_two_of_aemeasurable hae hx
  -- section Cauchy–Schwarz: |sectionInt| ≤ √secE2 · ‖f‖
  have hCS : ∀ᵐ x ∂vol, |sectionInt K f x| ≤ Real.sqrt (secE2 K x) * ‖f‖ := by
    filter_upwards [hsecMem] with x hx
    have hcs := integral_mul_norm_le_Lp_mul_Lq holderTriple221
      (by rw [real_two_ofReal]; exact hx) (by rw [real_two_ofReal]; exact Lp.memLp f)
    simp only [Real.norm_eq_abs] at hcs
    rw [integral_abs_rpow_two (fun t => K (x, t)),
      integral_abs_rpow_two (fun t : ℝ => ⇑f t)] at hcs
    have h1 : (∫ y : ℝ, |K (x, y)| ^ 2 ∂vol) ^ ((1 : ℝ) / 2) = Real.sqrt (secE2 K x) := by
      rw [← Real.sqrt_eq_rpow]
      refine congrArg Real.sqrt ?_
      exact integral_congr_ae (Filter.Eventually.of_forall fun y => by simp [sq_abs])
    have h2 : (∫ y : ℝ, |⇑f y| ^ 2 ∂vol) ^ ((1 : ℝ) / 2) = ‖f‖ := by
      rw [← L2sq_eq_norm f]
      refine congrArg (fun a : ℝ => a ^ ((1 : ℝ) / 2)) ?_
      exact integral_congr_ae (Filter.Eventually.of_forall fun y => by simp [sq_abs])
    rw [h1, h2] at hcs
    calc |sectionInt K f x|
        = |∫ y : ℝ, K (x, y) * ⇑f y ∂vol| := rfl
      _ ≤ ∫ y : ℝ, |K (x, y) * ⇑f y| ∂vol := abs_integral_le_integral_abs
      _ = ∫ y : ℝ, |K (x, y)| * |⇑f y| ∂vol := by
          exact integral_congr_ae (Filter.Eventually.of_forall fun y => abs_mul _ _)
      _ ≤ Real.sqrt (secE2 K x) * ‖f‖ := hcs
  -- the pointwise domination of the square
  have hsqDom : ∀ᵐ x ∂vol, sectionInt K f x ^ 2 ≤ ‖f‖ ^ 2 * secE2 K x := by
    filter_upwards [hCS] with x hcs
    have hn2 : 0 ≤ secE2 K x := integral_nonneg fun _ => sq_nonneg _
    calc sectionInt K f x ^ 2
        = |sectionInt K f x| ^ 2 := (sq_abs _).symm
      _ ≤ (Real.sqrt (secE2 K x) * ‖f‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hcs 2
      _ = ‖f‖ ^ 2 * secE2 K x := by rw [mul_pow, Real.sq_sqrt hn2]; ring
  -- a.e. measurability of the section-integral function
  have hae : AEStronglyMeasurable (sectionInt K f) vol :=
    (((hK.1 : AEStronglyMeasurable K vol2).mul
      ((Lp.aestronglyMeasurable f).comp_snd))).integral_prod_right'
  -- domination gives square-integrability, hence `MemLp 2`
  have hRHS : Integrable (fun x : ℝ => ‖f‖ ^ 2 * secE2 K x) vol := hsecE2.const_mul _
  refine memLp_two_of_aemeasurable hae (hRHS.mono (aes_two hae) ?_)
  filter_upwards [hsqDom] with x hp
  have hn : 0 ≤ ‖f‖ ^ 2 * secE2 K x :=
    mul_nonneg (pow_nonneg (norm_nonneg _) 2) (integral_nonneg fun _ => sq_nonneg _)
  calc ‖sectionInt K f x ^ 2‖
      = sectionInt K f x ^ 2 := by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    _ ≤ ‖f‖ ^ 2 * secE2 K x := hp
    _ = ‖(fun x : ℝ => ‖f‖ ^ 2 * secE2 K x) x‖ := by
          rw [Real.norm_eq_abs, abs_of_nonneg hn]

/-- The Fubini identity behind the section formula: the pairing of the
section-integral representer against `g` is the kernel pairing. -/
theorem inner_toLp_sectionInt {K : ℝ × ℝ → ℝ} (hK : HSKernel K) (f g : L2) :
    inner ℝ (MemLp.toLp (sectionInt K f) (memLp_sectionInt hK f)) g = kpair K f g := by
  rw [inner_toLp (memLp_sectionInt hK f) g]
  -- a.e. section-integrability of `K (·, y) · f y · g x`
  have hsec : ∀ᵐ x ∂vol, Integrable (fun y : ℝ => K (x, y) * ⇑f y * ⇑g x) vol := by
    exact (integrable_kintegrand hK f g).prod_right_ae
  have hstep : (∫ x : ℝ, sectionInt K f x * ⇑g x ∂vol)
      = (∫ x : ℝ, ∫ y : ℝ, K (x, y) * ⇑f y * ⇑g x ∂vol ∂vol) := by
    refine integral_congr_ae ?_
    filter_upwards [hsec] with x hx
    show sectionInt K f x * ⇑g x = (∫ y : ℝ, K (x, y) * ⇑f y * ⇑g x ∂vol)
    rw [integral_mul_const]
    rfl
  rw [hstep]
  show (∫ x : ℝ, ∫ y : ℝ, K (x, y) * ⇑f y * ⇑g x ∂vol ∂vol)
      = (∫ p : ℝ × ℝ, K p * ⇑f p.2 * ⇑g p.1 ∂vol2)
  exact (integral_prod (fun p : ℝ × ℝ => K p * ⇑f p.2 * ⇑g p.1)
    (integrable_kintegrand hK f g)).symm

/-- **The a.e. section formula (spec §6 Step 1)**: `TOp K hK f` equals, as an `L2`
element (equivalently: a.e.), the section-integral function
`x ↦ ∫ K (x, y) · f y ∂vol`. -/
theorem TOp_eq_sectionIntegral {K : ℝ × ℝ → ℝ} (hK : HSKernel K) (f : L2) :
    TOp K hK f = MemLp.toLp (sectionInt K f) (memLp_sectionInt hK f) :=
  eq_of_forall_inner_eq fun g => by
    rw [inner_toLp_sectionInt hK f g, inner_TOp]

/-- The a.e. form of the section formula: the coefficients of `TOp K hK f` are a.e.
given by the section integral `x ↦ ∫ K (x, y) · f y ∂vol`. -/
theorem coe_TOp_eq_sectionIntegral {K : ℝ × ℝ → ℝ} (hK : HSKernel K) (f : L2) :
    (⇑(TOp K hK f) : ℝ → ℝ) =ᵐ[vol] sectionInt K f := by
  rw [TOp_eq_sectionIntegral hK f]
  exact MemLp.coeFn_toLp (memLp_sectionInt hK f)

/-! ### Section-integrability helpers -/

/-- a.e. `MemLp 2` of the row sections `t ↦ B (v, t)` of a measurable HS kernel. -/
theorem memLp_row_sections {B : ℝ × ℝ → ℝ} (hBm : Measurable B) (hB : HSKernel B) :
    ∀ᵐ v ∂vol, MemLp (fun t : ℝ => B (v, t)) 2 vol := by
  obtain ⟨hsecB2, -⟩ := (integrable_prod_iff (aes_two (hBm.aestronglyMeasurable))).mp
    (MemLp.integrable_sq hB)
  filter_upwards [hsecB2] with v hv
  exact memLp_two_of_aemeasurable
    ((hBm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable) hv

/-- a.e. integrability of the row sections of `B` weighted by `x`. -/
theorem integrable_secBx {B : ℝ × ℝ → ℝ} (hBm : Measurable B) (hB : HSKernel B) (x : L2) :
    ∀ᵐ v ∂vol, Integrable (fun t : ℝ => B (v, t) * ⇑x t) vol := by
  filter_upwards [memLp_row_sections hBm hB] with v hv
  exact memLp_one_iff_integrable.mp (MemLp.mul' (Lp.memLp x) hv)

/-- a.e. integrability of the mixed sections `A (p.1, ·) · B (·, p.2)`. -/
theorem integrable_ABsec {A B : ℝ × ℝ → ℝ} (hAm : Measurable A) (hBm : Measurable B)
    (hA : HSKernel A) (hB : HSKernel B) :
    ∀ᵐ p ∂vol2, Integrable (fun t : ℝ => A (p.1, t) * B (t, p.2)) vol := by
  obtain ⟨hsecA2, -⟩ := (integrable_prod_iff (aes_two (hAm.aestronglyMeasurable))).mp
    (MemLp.integrable_sq hA)
  obtain ⟨hsecB2, -⟩ := (integrable_prod_iff (aes_two
    ((hBm.comp measurable_swap).aestronglyMeasurable))).mp
    (MemLp.integrable_sq (hsKernel_transpose hB))
  filter_upwards [eventual_fst_prop hsecA2, eventual_snd_prop hsecB2] with p hu hv
  have hmemA : MemLp (fun t : ℝ => A (p.1, t)) 2 vol :=
    memLp_two_of_aemeasurable
      ((hAm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable) hu
  have hmemB : MemLp (fun t : ℝ => B (t, p.2)) 2 vol :=
    memLp_two_of_aemeasurable
      ((hBm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable) hv
  exact memLp_one_iff_integrable.mp (MemLp.mul' hmemB hmemA)

/-! ### The coordinate flip on the triple space -/

/-- The flip `(u, v, t) ↦ (u, t, v)` of the last two coordinates as a measurable
equiv of the triple space. -/
def tripleFlip : (ℝ × ℝ) × ℝ ≃ᵐ (ℝ × ℝ) × ℝ where
  toFun := fun q : (ℝ × ℝ) × ℝ => ((q.1.1, q.2), q.1.2)
  invFun := fun r : (ℝ × ℝ) × ℝ => ((r.1.1, r.2), r.1.2)
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  measurable_toFun := Measurable.prodMk
    (Measurable.prodMk (measurable_fst.comp measurable_fst) measurable_snd)
    (measurable_snd.comp measurable_fst)
  measurable_invFun := Measurable.prodMk
    (Measurable.prodMk (measurable_fst.comp measurable_fst) measurable_snd)
    (measurable_snd.comp measurable_fst)

theorem tripleFlip_apply (q : (ℝ × ℝ) × ℝ) :
    tripleFlip q = ((q.1.1, q.2), q.1.2) := by
  simp only [tripleFlip, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk]

/-- The flip is measure preserving for the triple of `vol`-factors. -/
theorem measurePreserving_tripleFlip :
    MeasurePreserving tripleFlip ((vol.prod vol).prod vol) ((vol.prod vol).prod vol) := by
  have hassoc : MeasurePreserving
      (MeasurableEquiv.prodAssoc : (ℝ × ℝ) × ℝ ≃ᵐ ℝ × ℝ × ℝ)
      ((vol.prod vol).prod vol) (vol.prod (vol.prod vol)) :=
    measurePreserving_prodAssoc vol vol vol
  have hswap : MeasurePreserving
      (fun w : ℝ × (ℝ × ℝ) => (w.1, w.2.swap))
      (vol.prod (vol.prod vol)) (vol.prod (vol.prod vol)) :=
    MeasurePreserving.prod (MeasurePreserving.id vol) measurePreserving_swap
  have hcomp := (MeasurePreserving.symm _ hassoc).comp (hswap.comp hassoc)
  refine MeasurePreserving.congr hcomp tripleFlip.measurable
    (Filter.Eventually.of_forall fun q => ?_)
  rw [tripleFlip_apply]
  simp [MeasurableEquiv.prodAssoc, Equiv.prodAssoc, Function.comp_apply]


/-! ### Quadruple chain integrability -/

/-- **Quadruple chain integrability** (spec §6, the Fubini justification): the chain
integrand `A (u, v) · B (v, t) · x (t) · g (u)` is integrable over the triple space
(`((vol.prod vol).prod vol)`), by the section Cauchy–Schwarz chain. -/
theorem integrable_chain4 {A B : ℝ × ℝ → ℝ} (hAm : Measurable A) (hBm : Measurable B)
    (hA : HSKernel A) (hB : HSKernel B) (x g : L2) :
    Integrable
      (fun q : (ℝ × ℝ) × ℝ => A (q.1.1, q.1.2) * B (q.1.2, q.2) * ⇑x q.2 * ⇑g q.1.1)
      ((vol.prod vol).prod vol) := by
  classical
  obtain ⟨hsecA2, -⟩ := (integrable_prod_iff (aes_two (hAm.aestronglyMeasurable))).mp
    (MemLp.integrable_sq hA)
  have hsecE2B : Integrable (secE2 B) vol := integrable_secE2_of hB
  -- the weighted row energy `W v := ∫_t |B (v, t)| |⇑x t|` (row sections of B)
  set W : ℝ → ℝ := fun v => ∫ t : ℝ, |B (v, t)| * |⇑x t| ∂vol with hWdef
  have hWnonneg : ∀ v : ℝ, 0 ≤ W v := by
    intro v
    rw [hWdef]
    exact integral_nonneg fun t => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hWae : AEStronglyMeasurable W vol :=
    ((aes_abs (hBm.aestronglyMeasurable)).mul
      (aes_abs ((Lp.aestronglyMeasurable x).comp_snd))).integral_prod_right'
  have hWb : ∀ᵐ v ∂vol, W v ≤ Real.sqrt (secE2 B v) * ‖x‖ := by
    filter_upwards [memLp_row_sections hBm hB] with v hv
    have hcs := integral_mul_norm_le_Lp_mul_Lq holderTriple221
      (by rw [real_two_ofReal]; exact hv) (by rw [real_two_ofReal]; exact Lp.memLp x)
    simp only [Real.norm_eq_abs] at hcs
    rw [integral_abs_rpow_two (fun t => B (v, t)),
      integral_abs_rpow_two (fun t : ℝ => ⇑x t)] at hcs
    have h1 : (∫ t : ℝ, |B (v, t)| ^ 2 ∂vol) ^ ((1 : ℝ) / 2) = Real.sqrt (secE2 B v) := by
      rw [← Real.sqrt_eq_rpow]
      refine congrArg Real.sqrt ?_
      exact integral_congr_ae (Filter.Eventually.of_forall fun t => by simp [sq_abs])
    have h2 : (∫ t : ℝ, |⇑x t| ^ 2 ∂vol) ^ ((1 : ℝ) / 2) = ‖x‖ := by
      rw [← L2sq_eq_norm x]
      refine congrArg (fun a : ℝ => a ^ ((1 : ℝ) / 2)) ?_
      exact integral_congr_ae (Filter.Eventually.of_forall fun t => by simp [sq_abs])
    rw [h1, h2] at hcs
    show (∫ t : ℝ, |B (v, t)| * |⇑x t| ∂vol) ≤ Real.sqrt (secE2 B v) * ‖x‖
    exact hcs
  have hW2 : Integrable (fun v : ℝ => W v ^ 2) vol := by
    have hd : Integrable (fun v : ℝ => ‖x‖ ^ 2 * secE2 B v) vol := hsecE2B.const_mul _
    refine hd.mono (aes_two hWae) ?_
    filter_upwards [hWb] with v hv
    have hn1 : 0 ≤ secE2 B v := integral_nonneg fun _ => sq_nonneg _
    have hnW : 0 ≤ W v := hWnonneg v
    have hns : 0 ≤ ‖x‖ ^ 2 := pow_nonneg (norm_nonneg _) 2
    calc ‖W v ^ 2‖
        = W v ^ 2 := by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      _ ≤ (Real.sqrt (secE2 B v) * ‖x‖) ^ 2 := pow_le_pow_left₀ hnW hv 2
      _ = ‖x‖ ^ 2 * secE2 B v := by rw [mul_pow, Real.sq_sqrt hn1]; ring
      _ = ‖(fun v : ℝ => ‖x‖ ^ 2 * secE2 B v) v‖ := by
            rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hns hn1)]
  have hWmem : MemLp W 2 vol := memLp_two_of_aemeasurable hWae hW2
  have hW2e : ∀ᵐ u : ℝ ∂vol, Integrable (fun v : ℝ => W v ^ 2) vol :=
    Filter.Eventually.of_forall fun _ => hW2
  -- Level 2: the vol-integrability of `u ↦ |A u| * |⇑g u| * W u` over the square
  have hint2 : Integrable (fun p : ℝ × ℝ => |A p| * |⇑g p.1| * W p.2) vol2 := by
    have hFae : AEStronglyMeasurable
        (fun p : ℝ × ℝ => |A p| * |⇑g p.1| * W p.2) vol2 :=
      ((aes_abs (hAm.aestronglyMeasurable)).mul
        (aes_abs ((Lp.aestronglyMeasurable g).comp_fst))).mul (hWae.comp_snd)
    have hsec2 : ∀ᵐ u ∂vol, Integrable
        (fun v : ℝ => |A (u, v)| * |⇑g u| * W v) vol := by
      filter_upwards [hsecA2, hW2e] with u hu hW2u
      have hAint : Integrable (fun v : ℝ => A (u, v) ^ 2 + W v ^ 2) vol := hu.add hW2u
      have hdom : Integrable
          (fun v : ℝ => (|⇑g u| / 2) * (A (u, v) ^ 2 + W v ^ 2)) vol :=
        hAint.const_mul (|⇑g u| / 2)
      have hme : AEStronglyMeasurable (fun v : ℝ => |A (u, v)| * |⇑g u| * W v) vol :=
        ((aes_abs ((hAm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)).mul
          (aes_abs (aestronglyMeasurable_const : AEStronglyMeasurable
            (fun _ : ℝ => ⇑g u) vol))).mul hWae
      have hsmall : ∀ v : ℝ, ‖(fun v : ℝ => |A (u, v)| * |⇑g u| * W v) v‖
          = |A (u, v)| * |⇑g u| * W v := by
        intro v
        simp only [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg (hWnonneg v)]
      have hbig : ∀ v : ℝ, ‖(fun v : ℝ => (|⇑g u| / 2) * (A (u, v) ^ 2 + W v ^ 2)) v‖
          = (|⇑g u| / 2) * (A (u, v) ^ 2 + W v ^ 2) := by
        intro v
        simp only [Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (show (0:ℝ) ≤ |⇑g u| / 2 from by positivity),
          abs_of_nonneg (by positivity : (0:ℝ) ≤ A (u, v) ^ 2 + W v ^ 2)]
      refine hdom.mono hme ?_
      filter_upwards [Filter.Eventually.of_forall hsmall,
        Filter.Eventually.of_forall hbig] with v hs hb
      rw [hs, hb]
      have h1 : |A (u, v)| * |⇑g u| * W v
          ≤ (|⇑g u| / 2) * (A (u, v) ^ 2 + W v ^ 2) := by
        have h2 : |A (u, v)| * W v ≤ (A (u, v) ^ 2 + W v ^ 2) / 2 := by
          have h4 : 0 ≤ (|A (u, v)| - W v) ^ 2 := sq_nonneg _
          have hab2 : (|A (u, v)| - W v) ^ 2
              = |A (u, v)| ^ 2 - 2 * (|A (u, v)| * W v) + W v ^ 2 := by
            ring
          have e1 : |A (u, v)| ^ 2 = A (u, v) ^ 2 := by simp [sq_abs]
          rw [e1] at hab2
          linarith
        calc |A (u, v)| * |⇑g u| * W v
            = |⇑g u| * (|A (u, v)| * W v) := by ring
          _ ≤ |⇑g u| * ((A (u, v) ^ 2 + W v ^ 2) / 2) :=
            mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
          _ = (|⇑g u| / 2) * (A (u, v) ^ 2 + W v ^ 2) := by ring
      exact h1
    have hintaes : AEStronglyMeasurable
        (fun u : ℝ => ∫ v : ℝ, ‖|A (u, v)| * |⇑g u| * W v‖ ∂vol) vol := by
      refine (hFae.integral_prod_right').congr ?_
      filter_upwards [Filter.Eventually.of_forall hWnonneg] with u hu
      refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
      show |A (u, v)| * |⇑g u| * W v = ‖|A (u, v)| * |⇑g u| * W v‖
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_abs, abs_abs,
        abs_of_nonneg (hWnonneg v)]
    have hAsecMem : ∀ᵐ u ∂vol, MemLp (fun v : ℝ => A (u, v)) 2 vol := by
      filter_upwards [hsecA2] with u hu
      exact memLp_two_of_aemeasurable
        ((hAm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable) hu
    have hintfun : Integrable
        (fun u : ℝ => ∫ v : ℝ, ‖|A (u, v)| * |⇑g u| * W v‖ ∂vol) vol := by
      have hint2g : Integrable (fun u : ℝ => ⇑g u ^ 2) vol := (Lp.memLp g).integrable_sq
      have hintsecA : Integrable (secE2 A) vol := integrable_secE2_of hA
      have hCpos : 0 ≤ Real.sqrt (∫ v : ℝ, W v ^ 2 ∂vol) := Real.sqrt_nonneg _
      have hdom : Integrable (fun u : ℝ =>
          Real.sqrt (∫ v : ℝ, W v ^ 2 ∂vol) * ((⇑g u ^ 2 + secE2 A u) / 2)) vol := by
        have h1 := hint2g.const_mul (Real.sqrt (∫ v : ℝ, W v ^ 2 ∂vol) / 2)
        have h2 := hintsecA.const_mul (Real.sqrt (∫ v : ℝ, W v ^ 2 ∂vol) / 2)
        refine h1.add h2 |>.congr (Filter.Eventually.of_forall fun u => ?_)
        show (Real.sqrt (∫ v : ℝ, W v ^ 2 ∂vol) / 2) * ⇑g u ^ 2
            + (Real.sqrt (∫ v : ℝ, W v ^ 2 ∂vol) / 2) * secE2 A u
            = Real.sqrt (∫ v : ℝ, W v ^ 2 ∂vol) * ((⇑g u ^ 2 + secE2 A u) / 2)
        ring
      refine hdom.mono hintaes ?_
      filter_upwards [hAsecMem] with u huA
      have hge : 0 ≤ ∫ v : ℝ, ‖|A (u, v)| * |⇑g u| * W v‖ ∂vol :=
        integral_nonneg fun v => norm_nonneg _
      have hn2 : 0 ≤ Real.sqrt (∫ v : ℝ, W v ^ 2 ∂vol) * ((⇑g u ^ 2 + secE2 A u) / 2) :=
        mul_nonneg hCpos
          (div_nonneg (add_nonneg (sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _))
            (by norm_num))
      show ‖(∫ v : ℝ, ‖|A (u, v)| * |⇑g u| * W v‖ ∂vol)‖
          ≤ ‖Real.sqrt (∫ v : ℝ, W v ^ 2 ∂vol) * ((⇑g u ^ 2 + secE2 A u) / 2)‖
      rw [Real.norm_eq_abs, abs_of_nonneg hge, Real.norm_eq_abs, abs_of_nonneg hn2]
      have hsecC : (∫ v : ℝ, |A (u, v)| * W v ∂vol)
          ≤ Real.sqrt (secE2 A u) * Real.sqrt (∫ t : ℝ, W t ^ 2 ∂vol) := by
        have hcs := integral_mul_norm_le_Lp_mul_Lq holderTriple221
          (by rw [real_two_ofReal]; exact huA) (by rw [real_two_ofReal]; exact hWmem)
        simp only [Real.norm_eq_abs] at hcs
        rw [integral_abs_rpow_two (fun t => A (u, t)),
          integral_abs_rpow_two (fun t : ℝ => W t)] at hcs
        have h1 : (∫ t : ℝ, |A (u, t)| ^ 2 ∂vol) ^ ((1 : ℝ) / 2)
            = Real.sqrt (secE2 A u) := by
          rw [← Real.sqrt_eq_rpow]
          refine congrArg Real.sqrt ?_
          exact integral_congr_ae (Filter.Eventually.of_forall fun t => by simp [sq_abs])
        have h2 : (∫ t : ℝ, |W t| ^ 2 ∂vol) ^ ((1 : ℝ) / 2)
            = Real.sqrt (∫ t : ℝ, W t ^ 2 ∂vol) := by
          rw [← Real.sqrt_eq_rpow]
          refine congrArg Real.sqrt ?_
          exact integral_congr_ae (Filter.Eventually.of_forall fun t => by simp [sq_abs])
        rw [h1, h2] at hcs
        have hAW : ∀ v : ℝ, |A (u, v)| * W v = |A (u, v)| * |W v| := by
          intro v
          rw [abs_of_nonneg (hWnonneg v)]
        rw [integral_congr_ae (Filter.Eventually.of_forall hAW)]
        exact hcs
      have hkey : |⇑g u| * Real.sqrt (secE2 A u) ≤ (⇑g u ^ 2 + secE2 A u) / 2 := by
        have hnn : 0 ≤ (|⇑g u| - Real.sqrt (secE2 A u)) ^ 2 := sq_nonneg _
        have hab : (|⇑g u| - Real.sqrt (secE2 A u)) ^ 2
            = |⇑g u| ^ 2 - 2 * (|⇑g u| * Real.sqrt (secE2 A u))
              + (Real.sqrt (secE2 A u)) ^ 2 := by
          ring
        have h1 : |⇑g u| ^ 2 = ⇑g u ^ 2 := by simp
        have h2 : (Real.sqrt (secE2 A u)) ^ 2 = secE2 A u :=
          Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)
        rw [h1, h2] at hab
        linarith
      calc (∫ v : ℝ, ‖|A (u, v)| * |⇑g u| * W v‖ ∂vol)
          = |⇑g u| * (∫ v : ℝ, |A (u, v)| * W v ∂vol) := by
            refine Eq.trans (integral_congr_ae
              (Filter.Eventually.of_forall fun v => ?_)) (integral_const_mul _ _)
            show ‖|A (u, v)| * |⇑g u| * W v‖ = |⇑g u| * (|A (u, v)| * W v)
            simp only [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg (hWnonneg v)]
            ring
        _ ≤ |⇑g u| * (Real.sqrt (secE2 A u) * Real.sqrt (∫ t : ℝ, W t ^ 2 ∂vol)) :=
            mul_le_mul_of_nonneg_left hsecC (abs_nonneg _)
        _ = (|⇑g u| * Real.sqrt (secE2 A u)) * Real.sqrt (∫ t : ℝ, W t ^ 2 ∂vol) := by
            ring
        _ ≤ ((⇑g u ^ 2 + secE2 A u) / 2) * Real.sqrt (∫ t : ℝ, W t ^ 2 ∂vol) :=
            mul_le_mul_of_nonneg_right hkey hCpos
        _ = Real.sqrt (∫ v : ℝ, W v ^ 2 ∂vol) * ((⇑g u ^ 2 + secE2 A u) / 2) := by
            ring
    exact (integrable_prod_iff hFae).mpr ⟨hsec2, hintfun⟩
  -- Transport to the triple space: measurability of the chain integrand
  have hAq : Measurable (fun q : (ℝ × ℝ) × ℝ => A (q.1.1, q.1.2)) :=
    hAm.comp ((measurable_fst.prodMk measurable_snd).comp measurable_fst)
  have hBq : Measurable (fun q : (ℝ × ℝ) × ℝ => B (q.1.2, q.2)) :=
    hBm.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hG1 : AEStronglyMeasurable (fun p : ℝ × ℝ => ⇑g p.1) vol2 :=
    (Lp.aestronglyMeasurable g).comp_quasiMeasurePreserving quasiMeasurePreserving_fst
  have hGq : AEStronglyMeasurable (fun q : (ℝ × ℝ) × ℝ => ⇑g q.1.1)
      ((vol.prod vol).prod vol) :=
    hG1.comp_quasiMeasurePreserving quasiMeasurePreserving_fst
  have hXq : AEStronglyMeasurable (fun q : (ℝ × ℝ) × ℝ => ⇑x q.2)
      ((vol.prod vol).prod vol) :=
    (Lp.aestronglyMeasurable x).comp_quasiMeasurePreserving quasiMeasurePreserving_snd
  have hFae1 : AEStronglyMeasurable
      (fun q : (ℝ × ℝ) × ℝ => A (q.1.1, q.1.2) * B (q.1.2, q.2) * ⇑x q.2 * ⇑g q.1.1)
      ((vol.prod vol).prod vol) :=
    ((hAq.aestronglyMeasurable.mul hBq.aestronglyMeasurable).mul hXq).mul hGq
  -- the integrated sections are exactly `|A p| * |⇑g p.1| * W p.2`
  have hintmid : Integrable
      (fun p : ℝ × ℝ => ∫ t : ℝ,
        ‖A (p.1, p.2) * B (p.2, t) * ⇑x t * ⇑g p.1‖ ∂vol) vol2 := by
    refine hint2.congr (Filter.Eventually.of_forall fun p => ?_)
    show |A p| * |⇑g p.1| * W p.2
        = (∫ t : ℝ, ‖A (p.1, p.2) * B (p.2, t) * ⇑x t * ⇑g p.1‖ ∂vol)
    have hnorm : ∀ t : ℝ, |A p * ⇑g p.1| * |B (p.2, t) * ⇑x t|
        = ‖A (p.1, p.2) * B (p.2, t) * ⇑x t * ⇑g p.1‖ := by
      intro t
      show |A p * ⇑g p.1| * |B (p.2, t) * ⇑x t|
          = |A p * B (p.2, t) * ⇑x t * ⇑g p.1|
      simp only [abs_mul]
      ring
    calc |A p| * |⇑g p.1| * W p.2
        = |A p * ⇑g p.1| * W p.2 := by rw [abs_mul]
      _ = |A p * ⇑g p.1| * (∫ t : ℝ, |B (p.2, t)| * |⇑x t| ∂vol) := rfl
      _ = |A p * ⇑g p.1| * (∫ t : ℝ, |B (p.2, t) * ⇑x t| ∂vol) := by
            rw [integral_congr_ae
              (Filter.Eventually.of_forall fun t => abs_mul (B (p.2, t)) (⇑x t))]
      _ = ∫ t : ℝ, |A p * ⇑g p.1| * |B (p.2, t) * ⇑x t| ∂vol :=
            (integral_const_mul _ _).symm
      _ = ∫ t : ℝ, ‖A (p.1, p.2) * B (p.2, t) * ⇑x t * ⇑g p.1‖ ∂vol :=
            integral_congr_ae (Filter.Eventually.of_forall hnorm)
  have hsec1 : ∀ᵐ p : ℝ × ℝ ∂vol2,
      Integrable (fun t : ℝ => A (p.1, p.2) * B (p.2, t) * ⇑x t * ⇑g p.1) vol := by
    filter_upwards [eventual_snd_prop (memLp_row_sections hBm hB)] with p hv
    refine Integrable.congr
      ((memLp_one_iff_integrable.mp (MemLp.mul' (Lp.memLp x) hv)).const_mul
        (A (p.1, p.2) * ⇑g p.1))
      (Filter.Eventually.of_forall fun t => by ring)
  exact (integrable_prod_iff hFae1).mpr ⟨hsec1, hintmid⟩

/-- The flipped chain integrand is integrable: transport of `integrable_chain4`
along the measure-preserving flip `tripleFlip`. -/
theorem integrable_chain4_flip {A B : ℝ × ℝ → ℝ} (hAm : Measurable A) (hBm : Measurable B)
    (hA : HSKernel A) (hB : HSKernel B) (x g : L2) :
    Integrable
      (fun q : (ℝ × ℝ) × ℝ => A (q.1.1, q.2) * B (q.2, q.1.2) * ⇑x q.1.2 * ⇑g q.1.1)
      ((vol.prod vol).prod vol) := by
  have h1 := integrable_chain4 hAm hBm hA hB x g
  have hpt : (fun q : (ℝ × ℝ) × ℝ => A (q.1.1, q.2) * B (q.2, q.1.2) * ⇑x q.1.2 * ⇑g q.1.1)
      = (fun q : (ℝ × ℝ) × ℝ => A (q.1.1, q.1.2) * B (q.1.2, q.2) * ⇑x q.2 * ⇑g q.1.1)
        ∘ tripleFlip := by
    funext q
    show A (q.1.1, q.2) * B (q.2, q.1.2) * ⇑x q.1.2 * ⇑g q.1.1
      = A ((tripleFlip q).1.1, (tripleFlip q).1.2)
        * B ((tripleFlip q).1.2, (tripleFlip q).2)
        * ⇑x (tripleFlip q).2 * ⇑g (tripleFlip q).1.1
    rw [tripleFlip_apply]
  rw [hpt]
  exact measurePreserving_tripleFlip.integrable_comp_of_integrable h1

/-! ### Step 2: the composition action -/

/-- **The composition of the pairings (spec §6 Step 2)**: the kernel pairing of the
composed kernel equals the iterated pairing:
`kpair A (TOpFun B hB x) g = kpair (compKernel A B) x g`. -/
theorem kpair_compKernel_apply {A B : ℝ × ℝ → ℝ} (hAm : Measurable A) (hBm : Measurable B)
    (hA : HSKernel A) (hB : HSKernel B) (x g : L2) :
    kpair A (TOpFun B hB x) g = kpair (compKernel A B) x g := by
  classical
  have hBsec : ∀ᵐ y ∂vol, ⇑(TOpFun B hB x) y = sectionInt B x y := by
    filter_upwards [coe_TOp_eq_sectionIntegral hB x] with y hy
    exact hy
  have hRstep : ∀ᵐ p : ℝ × ℝ ∂vol2,
      A p * ⇑(TOpFun B hB x) p.2 * ⇑g p.1
        = A p * (⇑g p.1 * (∫ t : ℝ, B (p.2, t) * ⇑x t ∂vol)) := by
    filter_upwards [eventual_snd_prop hBsec] with p hp
    show A p * ⇑(TOpFun B hB x) p.2 * ⇑g p.1
      = A p * (⇑g p.1 * (∫ t : ℝ, B (p.2, t) * ⇑x t ∂vol))
    rw [hp]
    show A p * (∫ y : ℝ, B (p.2, y) * ⇑x y ∂vol) * ⇑g p.1
      = A p * (⇑g p.1 * (∫ t : ℝ, B (p.2, t) * ⇑x t ∂vol))
    ring
  have hRit : (∫ p : ℝ × ℝ, A p * (⇑g p.1 * (∫ t : ℝ, B (p.2, t) * ⇑x t ∂vol)) ∂vol2)
      = (∫ p : ℝ × ℝ, ∫ t : ℝ, A p * B (p.2, t) * ⇑x t * ⇑g p.1 ∂vol ∂vol2) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    calc A p * (⇑g p.1 * (∫ t : ℝ, B (p.2, t) * ⇑x t ∂vol))
        = (A p * ⇑g p.1) * (∫ t : ℝ, B (p.2, t) * ⇑x t ∂vol) := by ring
      _ = ∫ t : ℝ, (A p * ⇑g p.1) * (B (p.2, t) * ⇑x t) ∂vol :=
            (integral_const_mul _ _).symm
      _ = ∫ t : ℝ, A p * B (p.2, t) * ⇑x t * ⇑g p.1 ∂vol :=
            integral_congr_ae (Filter.Eventually.of_forall fun t => by ring)
  have hLit : (∫ p : ℝ × ℝ,
        (∫ t : ℝ, A (p.1, t) * B (t, p.2) ∂vol) * ⇑x p.2 * ⇑g p.1 ∂vol2)
      = (∫ p : ℝ × ℝ, ∫ t : ℝ, A (p.1, t) * B (t, p.2) * ⇑x p.2 * ⇑g p.1 ∂vol ∂vol2) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    calc (∫ t : ℝ, A (p.1, t) * B (t, p.2) ∂vol) * ⇑x p.2 * ⇑g p.1
        = (⇑x p.2 * ⇑g p.1) * (∫ t : ℝ, A (p.1, t) * B (t, p.2) ∂vol) := by ring
      _ = ∫ t : ℝ, (⇑x p.2 * ⇑g p.1) * (A (p.1, t) * B (t, p.2)) ∂vol :=
            (integral_const_mul _ _).symm
      _ = ∫ t : ℝ, A (p.1, t) * B (t, p.2) * ⇑x p.2 * ⇑g p.1 ∂vol :=
            integral_congr_ae (Filter.Eventually.of_forall fun t => by ring)
  -- the measure-preserving re-labeling `(u, v, t) ↦ (u, t, v)` of the triple space
  have hflip : (∫ q : (ℝ × ℝ) × ℝ,
        A (q.1.1, q.1.2) * B (q.1.2, q.2) * ⇑x q.2 * ⇑g q.1.1 ∂((vol.prod vol).prod vol))
      = (∫ q : (ℝ × ℝ) × ℝ,
        A (q.1.1, q.2) * B (q.2, q.1.2) * ⇑x q.1.2 * ⇑g q.1.1 ∂((vol.prod vol).prod vol)) := by
    rw [← MeasurePreserving.integral_comp' measurePreserving_tripleFlip
      (fun q : (ℝ × ℝ) × ℝ => A (q.1.1, q.2) * B (q.2, q.1.2) * ⇑x q.1.2 * ⇑g q.1.1)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun q => by
      show A (q.1.1, q.1.2) * B (q.1.2, q.2) * ⇑x q.2 * ⇑g q.1.1
        = A ((tripleFlip q).1.1, (tripleFlip q).2)
          * B ((tripleFlip q).2, (tripleFlip q).1.2)
          * ⇑x (tripleFlip q).1.2 * ⇑g (tripleFlip q).1.1
      rw [tripleFlip_apply])
  calc kpair A (TOpFun B hB x) g
      = ∫ p : ℝ × ℝ, A p * ⇑(TOpFun B hB x) p.2 * ⇑g p.1 ∂vol2 := rfl
    _ = ∫ p : ℝ × ℝ, A p * (⇑g p.1 * (∫ t : ℝ, B (p.2, t) * ⇑x t ∂vol)) ∂vol2 :=
          integral_congr_ae hRstep
    _ = ∫ p : ℝ × ℝ, ∫ t : ℝ,
          (fun q : (ℝ × ℝ) × ℝ =>
            A (q.1.1, q.1.2) * B (q.1.2, q.2) * ⇑x q.2 * ⇑g q.1.1) (p, t) ∂vol ∂vol2 := hRit
    _ = ∫ q : (ℝ × ℝ) × ℝ,
          A (q.1.1, q.1.2) * B (q.1.2, q.2) * ⇑x q.2 * ⇑g q.1.1
          ∂((vol.prod vol).prod vol) :=
          (integral_prod
            (fun q : (ℝ × ℝ) × ℝ =>
              A (q.1.1, q.1.2) * B (q.1.2, q.2) * ⇑x q.2 * ⇑g q.1.1)
            (integrable_chain4 hAm hBm hA hB x g)).symm
    _ = ∫ q : (ℝ × ℝ) × ℝ,
          A (q.1.1, q.2) * B (q.2, q.1.2) * ⇑x q.1.2 * ⇑g q.1.1
          ∂((vol.prod vol).prod vol) := hflip
    _ = ∫ p : ℝ × ℝ, ∫ t : ℝ,
          (fun q : (ℝ × ℝ) × ℝ =>
            A (q.1.1, q.2) * B (q.2, q.1.2) * ⇑x q.1.2 * ⇑g q.1.1) (p, t) ∂vol ∂vol2 :=
          integral_prod
            (fun q : (ℝ × ℝ) × ℝ =>
              A (q.1.1, q.2) * B (q.2, q.1.2) * ⇑x q.1.2 * ⇑g q.1.1)
            (integrable_chain4_flip hAm hBm hA hB x g)
    _ = ∫ p : ℝ × ℝ,
          (∫ t : ℝ, A (p.1, t) * B (t, p.2) ∂vol) * ⇑x p.2 * ⇑g p.1 ∂vol2 := hLit.symm
    _ = kpair (compKernel A B) x g := rfl

/-- **The composition action (spec §6 Step 2)**: the kernel operator of the composed
kernel is the composition of the kernel operators:
`TOp (compKernel A B) x = TOp A (TOp B x)` for all `x : L2`. -/
theorem TOp_compKernel_apply {A B : ℝ × ℝ → ℝ} (hAm : Measurable A) (hBm : Measurable B)
    (hA : HSKernel A) (hB : HSKernel B) (hAB : HSKernel (compKernel A B)) (x : L2) :
    TOp (compKernel A B) hAB x = TOp A hA (TOp B hB x) :=
  eq_of_forall_inner_eq fun g => by
    rw [inner_TOp hAB x g, inner_TOp hA (TOp B hB x) g]
    exact (kpair_compKernel_apply hAm hBm hA hB x g).symm

/-- The composition action as an identity of continuous linear maps:
`TOp (compKernel A B) = TOp A * TOp B`. -/
theorem TOp_compKernel {A B : ℝ × ℝ → ℝ} (hAm : Measurable A) (hBm : Measurable B)
    (hA : HSKernel A) (hB : HSKernel B) (hAB : HSKernel (compKernel A B)) :
    TOp (compKernel A B) hAB = TOp A hA * TOp B hB :=
  ContinuousLinearMap.ext fun x => TOp_compKernel_apply hAm hBm hA hB hAB x

/-! ### The tower induction -/

/-- **The tower induction (spec §6)**: the kernel operator of the right-growing tower
is the operator power: `TOp (compPowR n K) x = (TOp K hK)^(n+1) x`. -/
theorem TOp_compPowR_apply {K : ℝ × ℝ → ℝ} (hKm : Measurable K) (hK : HSKernel K)
    (n : ℕ) (x : L2) :
    TOp (compPowR n K) (hsKernel_compPowR n hKm hK) x = (TOp K hK ^ (n + 1)) x := by
  induction n generalizing x with
  | zero =>
      show TOp K hK x = (TOp K hK ^ 1) x
      rw [pow_one]
  | succ m ih =>
      have h1 : TOp (compPowR (m + 1) K) (hsKernel_compPowR (m + 1) hKm hK) x
          = TOp (compPowR m K) (hsKernel_compPowR m hKm hK) (TOp K hK x) :=
        TOp_compKernel_apply (measurable_compPowR m hKm) hKm (hsKernel_compPowR m hKm hK)
          hK (hsKernel_compPowR (m + 1) hKm hK) x
      rw [h1, ih (TOp K hK x), pow_succ]
      rfl

/-! ### The CLM↔End transport and the downstream hPair contract -/

/-- The CLM↔`Module.End` transport for powers: `(TOpEnd' K hK ^ n) x` agrees with the
`n`-th power of the continuous-linear-map operator applied to `x`. -/
theorem TOpEnd'_pow_apply {K : ℝ × ℝ → ℝ} (hK : HSKernel K) (n : ℕ) (x : L2) :
    (TOpEnd' K hK ^ n) x = ((TOp K hK : L2 →L[ℝ] L2) ^ n) x := by
  have h : TOpEnd' K hK = ((TOp K hK : L2 →L[ℝ] L2) : L2 →ₗ[ℝ] L2) := rfl
  rw [h, ← ContinuousLinearMap.coe_pow]
  rfl

/-- The composition step of the downstream contract at tower exponent `n`:
`T ∘ TOp (compPowR n K) = T^(n+2)`. -/
theorem hPair_pow_succ {K : ℝ × ℝ → ℝ} (hKm : Measurable K) (hK : HSKernel K)
    (n : ℕ) (x : L2) :
    (TOp K hK) ((TOp (compPowR n K) (hsKernel_compPowR n hKm hK)) x)
      = (TOpEnd' K hK ^ (n + 2)) x := by
  rw [TOp_compPowR_apply hKm hK n x, TOpEnd'_pow_apply hK (n + 2) x]
  have h2 : (n + 1) + 1 = n + 2 := rfl
  rw [← h2, pow_succ' (TOp K hK) (n + 1)]
  rfl

/-- **The k-uniform downstream contract (spec §6, `hPair`)**: for every `k ≥ 2`,
`TOp K hK ∘ TOp (compPowR (k-2) K) = (TOpEnd' K hK) ^ k` as operators. -/
theorem hPair_uniform {K : ℝ × ℝ → ℝ} (hKm : Measurable K) (hK : HSKernel K) :
    ∀ (k : ℕ), 2 ≤ k → ∀ x : L2,
      (TOp K hK) ((TOp (compPowR (k - 2) K) (hsKernel_compPowR (k - 2) hKm hK)) x)
        = (TOpEnd' K hK ^ k) x := by
  intro k _ x
  have h2 : k - 2 + 2 = k := by omega
  have h := hPair_pow_succ hKm hK (k - 2) x
  rwa [h2] at h

/-- **The downstream contract (verbatim shape of `gate_of_bridge` /
`hasSum_general_k_of_gate` in `Hurst/GeneralKHasSumFinal.lean`)**: for `k ≥ 2` with
an HS-kernel proof of the tower level `compPowR (k-2) K`,
`(TOp K hK) ((TOp (compPowR (k - 2) K) hKL) x) = (TOpEnd' K hK ^ k) x`. -/
theorem hPair_contract {K : ℝ × ℝ → ℝ} {k : ℕ} (hk : 2 ≤ k)
    (hKm : Measurable K) (hK : HSKernel K) (hKL : HSKernel (compPowR (k - 2) K))
    (x : L2) :
    (TOp K hK) ((TOp (compPowR (k - 2) K) hKL) x) = (TOpEnd' K hK ^ k) x :=
  hPair_uniform hKm hK k hk x

/-- **The Riesz-instantiated k-uniform contract** (the `hPair` hypothesis shape of
`rieszSpectrumVal_hGen_of_bridge` in `Hurst/GeneralKHasSumFinal.lean`, instantiated at
`K := rieszKernel psi c omega`; the HS-kernel proofs are interchangeable by proof
irrelevance): for every `k ≥ 2` and `x : L2`,
`TOp K (TOp (compPowR (k-2) K) x) = (TOpEnd' K ^ k) x`. -/
theorem hPair_riesz {psi c : ℝ} {omega : ℝ → ℝ}
    (hKmMeas : Measurable (rieszKernel psi c omega))
    (hKR : HSKernel (rieszKernel psi c omega)) :
    ∀ (k : ℕ), 2 ≤ k → ∀ x : L2,
      (TOp (rieszKernel psi c omega) hKR)
        ((TOp (compPowR (k - 2) (rieszKernel psi c omega))
          (hsKernel_compPowR (k - 2) hKmMeas hKR)) x)
        = (TOpEnd' (rieszKernel psi c omega) hKR ^ k) x :=
  hPair_uniform hKmMeas hKR

end HS

end
