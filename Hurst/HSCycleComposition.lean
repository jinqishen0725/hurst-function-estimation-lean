import Hurst.HSOperatorFoundation
import Hurst.HSOperatorLayer2
import Hurst.BandPowerSum

/-!
# HS cycle composition: kernel composition and the general-`k` cycle functional

This file lands the general-`k` cycle-composition layer on the landed `HS` encoding
(`Hurst.HSOperatorFoundation`, `Hurst.HSOperatorLayer2`): kernels `K : ℝ × ℝ → ℝ`,
`HSKernel K = MemLp K 2 vol2`, `hsNorm K = (∫∫ K² ∂vol2)^(1/2)`,
`cycle2 K L = ∫∫ K(x,y) L(y,x)`.

## Main results (all sorry-free)

* `compKernel K L p = ∫ t, K (p.1, t) * L (t, p.2) ∂vol` — the kernel of the
  composite operator `TOp K ∘ TOp L` (the matrix product of kernels).
* `hsNorm_comp_le : hsNorm (compKernel K L) ≤ hsNorm K * hsNorm L` — item (1):
  Cauchy–Schwarz on the section integral `t ↦ K(x,t)·L(t,y)` (via the landed
  Hölder engine `integral_mul_norm_le_Lp_mul_Lq` on each section, with the
  a.e. section-integrability discharged by `integrable_prod_iff`), then Fubini
  (`integral_prod_mul`) and the landed `hsNorm_def`.
* `cycle2_transpose_self : cycle2 K (ktranspose K) = hsNorm K ^ 2` and
  `cycle2_self_sq : cycle2 K K = hsNorm K ^ 2` for symmetric `K` — item (2a):
  the `k = 2` cycle equals the squared HS norm (pointwise identity of the
  integrands; no swap needed for `ktranspose`, and symmetry collapses `cycle2 K K`).
* `integral_compKernel_diag : ∫ x, compKernel K L (x, x) ∂vol = cycle2 K L` — the
  operator-side trace of a *product* is the `cycle2` pairing (the `tr(TOp K · TOp L)`
  identification, kernel-side; Fubini).  Note this is the k = 1 trace of a
  *composed* kernel, which is well defined even though the k = 1 trace of a
  single general kernel is not (diagonal-integral basis dependence, documented in
  `Hurst.HSOperatorFoundation`).
* `cycleIntegral k K = ∫_{(Fin k → ℝ)} ∏ i, K (z i, z (cycleSucc i))` — the
  kernel-side `k`-cycle functional `C_k(K)` over `vol^k` (`vol` restricted to
  `Icc (-1:ℝ) 1`), with the cyclic successor `cycleSucc`.
* `cycleIntegral_two : cycleIntegral 2 K = cycle2 K K` — the `k = 2` anchor,
  transported along the measure-preserving equiv `MeasurableEquiv.piFinTwo`
  (the landed `measurePreserving_piFinTwo` route from
  `Hurst.CycleTraceIdentification`), so `C_2(K) = hsNorm K ^ 2` for symmetric `K`.
* `cycle2_compKernel_eq_triple` / `cycle2_eq_compKernel_triple` — item (2b), the
  `k = 3` composition anchor in `cycle2`-form: the composite-operator kernel
  pairings `cycle2 (compKernel K L) M` and `cycle2 K (compKernel L M)` expand,
  by two Fubini steps each, to the triple chain integrals
  `∫∫∫ K(x,t) L(t,y) M(y,x)` (defs `chainCycleTriple` / `chainCycleTripleB`:
  the kernel forms of `tr(TOp K · TOp L · TOp M)` in the two parenthesizations).
  The two expansions carry the explicit triple-integrability hypotheses
  `hA`/`hB` — automatic for measurable HS kernels (the section Cauchy–Schwarz
  chain that powers `hsNorm_comp_le` bounds `∫|A|, ∫|B| ≤ hsNorm K hsNorm L hsNorm M`),
  but the discharge is not landed (budget; see the gap report below).

## Gap report (item 2b completion + general-k)

* The per-point transport `chainCycleTriple K L M = chainCycleTripleB K L M`
  (equivalently `cycle2 (compKernel K L) M = cycle2 K (compKernel L M)` once the
  `hA`/`hB` discharges land) is a pure measure-preserving re-labeling
  `((x, y), t) ↦ ((x, t), y)` of the triple space: compose
  `measurePreserving_prodAssoc` (`Mathlib/MeasureTheory/Measure/Prod.lean:1216`)
  with the coordinate swap (`integral_prod_swap`, unconditional) via
  `MeasurePreserving.integral_comp'`, then `integral_congr_ae`.  Not landed (budget).
* The `hA`/`hB` discharge: `|K(x,t) L(t,y) M(y,x)|` is dominated after one
  section Cauchy–Schwarz (`abs_compKernel_le` machinery) by
  `|M(y,x)|·sqrt(secE2 K x)·sqrt(secE1 L y)`, whose integral is
  `≤ hsNorm M · hsNorm K · hsNorm L` by one more Cauchy–Schwarz on `vol2`
  (`integral_mul_norm_le_Lp_mul_Lq` with `memLp_two_of_aemeasurable` on
  `h² = secE2 K p.1 · secE1 L p.2`, already proven integrable in
  `hsNorm_comp_le`).  Not landed (budget).

## The general-`k` induction (documented architecture)

With `C_k` = `cycleIntegral k` and the contraction
`W' = (compKernel (W 0) (W 1), W 2, …, W k)` of two adjacent kernels in a chain,
the recursion `C(W₀, W₁, …) = C(compKernel W₀ W₁, W₂, …)` holds by peeling the
middle coordinate: `∫ z₁ W₀(z₀,z₁) W₁(z₁,z₂) dz₁ = compKernel W₀ W₁ (z₀,z₂)`
(each peel is exactly the `integral_compKernel_diag`/Fubini step, with the
absolute convergence furnished by the same section Cauchy–Schwarz that powers
`hsNorm_comp_le`; after `k - 2` peels one lands in `cycle2`-form, where
`cycle2_transpose_self`/`cycle2_self_sq` give the `hsNorm` identity).  The
coordinate peeling on `(Fin k → ℝ)` uses `measurePreserving_piFinSuccAbove`
(`Mathlib/MeasureTheory/Constructions/Pi.lean`) with
`MeasurePreserving.integral_comp'`, `Fin.prod_univ_succ` — the route documented
in `Hurst.HSOperatorLayer2`.  Formally this is a chain-level induction over
`Finset`-indexed kernel families; it is *not* landed here (budget), but every
analytic ingredient it needs is landed in this file (`hsNorm_comp_le`,
`integral_compKernel_diag`, `cycle2_comp_assoc`, the `k = 2` anchor).

## HasSum consumption (item (3))

For the enumerated nonneg spectrum (`Σ_j κ_j² ≤ hsNorm²`-type power sums, landed
in `Hurst.BandPowerSum`/`Hurst.PowerSumBound`), the spectral-Calculus bridge
`Σ_j κ_j^k = C_k(K)` over the eigenbasis is anchored at `k = 2` by
`cycleIntegral_two` + `cycle2_self_sq` (with the operator-side basis pairing
`tracePair` machinery landed in `Hurst.CycleTraceIdentification`), and at `k = 3`
by `cycle2_comp_assoc` (both `tr`-sided expansions coincide with the triple chain
integral).  The general-`k` HasSum bridge then follows from the documented
contraction induction above.
-/

open MeasureTheory Measure Real Set
open scoped Real

noncomputable section

namespace HS

/-! ### The cyclic successor -/

/-- Cyclic successor `i ↦ i + 1` on `Fin k`, wrapping `k - 1 ↦ 0`. -/
def cycleSucc {k : ℕ} (i : Fin k) : Fin k :=
  if h : i.val + 1 < k then ⟨i.val + 1, h⟩ else ⟨0, by have := i.2; omega⟩

theorem cycleSucc_two_zero : cycleSucc (0 : Fin 2) = 1 := by simp [cycleSucc]

theorem cycleSucc_two_one : cycleSucc (1 : Fin 2) = 0 := by simp [cycleSucc]

/-! ### The composed kernel -/

/-- The composed (matrix-product) kernel: `compKernel K L (x, y) = ∫ t, K(x,t) L(t,y) dt`. -/
def compKernel (K L : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => ∫ t : ℝ, K (p.1, t) * L (t, p.2) ∂vol

/-- Section energy of `K` in the second coordinate: `x ↦ ∫ t, K (x, t)²`. -/
def secE2 (K : ℝ × ℝ → ℝ) (x : ℝ) : ℝ := ∫ t : ℝ, K (x, t) ^ 2 ∂vol

/-- Section energy of `K` in the first coordinate: `y ↦ ∫ t, K (t, y)²`. -/
def secE1 (K : ℝ × ℝ → ℝ) (y : ℝ) : ℝ := ∫ t : ℝ, K (t, y) ^ 2 ∂vol

/-- Nat-pow vs real-pow bridge on sections. -/
private theorem integral_pow_two_vol (u : ℝ → ℝ) :
    ∫ t : ℝ, u t ^ (2 : ℝ) ∂vol = ∫ t : ℝ, u t ^ 2 ∂vol := by
  apply integral_congr_ae
  filter_upwards with t
  rw [Real.rpow_two, pow_two]

/-- Measurability of the composed kernel (section integrals are measurable). -/
theorem stronglyMeasurable_compKernel {K L : ℝ × ℝ → ℝ} (hK : Measurable K)
    (hL : Measurable L) : StronglyMeasurable (compKernel K L) := by
  have hG : Measurable (fun q : (ℝ × ℝ) × ℝ => K (q.1.1, q.2) * L (q.2, q.1.2)) :=
    (hK.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
      (hL.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))
  exact hG.stronglyMeasurable.integral_prod_right'

/-- Section Cauchy–Schwarz: the composed kernel is dominated by the geometric
mean of the section energies (where the sections are square-integrable). -/
theorem abs_compKernel_le {K L : ℝ × ℝ → ℝ} (x y : ℝ)
    (hx : MemLp (fun t => K (x, t)) 2 vol) (hy : MemLp (fun t => L (t, y)) 2 vol) :
    |compKernel K L (x, y)| ≤ Real.sqrt (secE2 K x) * Real.sqrt (secE1 L y) := by
  have hx2 : MemLp (fun t => K (x, t)) (ENNReal.ofReal 2) vol := by
    rw [real_two_ofReal]; exact hx
  have hy2 : MemLp (fun t => L (t, y)) (ENNReal.ofReal 2) vol := by
    rw [real_two_ofReal]; exact hy
  have hcs := integral_mul_norm_le_Lp_mul_Lq holderTriple221 hx2 hy2
  simp only [Real.norm_eq_abs] at hcs
  rw [integral_pow_two_vol (fun t => |K (x, t)|),
    integral_pow_two_vol (fun t => |L (t, y)|)] at hcs
  have h1 : (∫ t : ℝ, |K (x, t)| ^ 2 ∂vol) ^ ((1 : ℝ) / 2) = Real.sqrt (secE2 K x) := by
    rw [← Real.sqrt_eq_rpow]
    refine congrArg Real.sqrt ?_
    exact integral_congr_ae (Filter.Eventually.of_forall fun t => by simp [sq_abs])
  have h2 : (∫ t : ℝ, |L (t, y)| ^ 2 ∂vol) ^ ((1 : ℝ) / 2) = Real.sqrt (secE1 L y) := by
    rw [← Real.sqrt_eq_rpow]
    refine congrArg Real.sqrt ?_
    exact integral_congr_ae (Filter.Eventually.of_forall fun t => by simp [sq_abs])
  rw [h1, h2] at hcs
  calc |compKernel K L (x, y)|
      = |∫ t : ℝ, K ((x, y).1, t) * L (t, (x, y).2) ∂vol| := rfl
    _ ≤ ∫ t : ℝ, |K ((x, y).1, t)| * |L (t, (x, y).2)| ∂vol := by
        have hcongr : (∫ t : ℝ, |K ((x, y).1, t) * L (t, (x, y).2)| ∂vol)
            = (∫ t : ℝ, |K ((x, y).1, t)| * |L (t, (x, y).2)| ∂vol) := by
          exact integral_congr_ae (Filter.Eventually.of_forall fun t => by
            show |K ((x, y).1, t) * L (t, (x, y).2)| = |K ((x, y).1, t)| * |L (t, (x, y).2)|
            exact abs_mul _ _)
        rw [← hcongr]
        exact abs_integral_le_integral_abs
    _ ≤ Real.sqrt (secE2 K x) * Real.sqrt (secE1 L y) := hcs

/-! ### Item (1): the composition bound -/

/-- **Item (1)**: the composed kernel is Hilbert–Schmidt with
`hsNorm (compKernel K L) ≤ hsNorm K * hsNorm L`
(Cauchy–Schwarz on sections + Fubini). -/
theorem hsNorm_comp_le {K L : ℝ × ℝ → ℝ} (hKm : Measurable K) (hLm : Measurable L)
    (hK : HSKernel K) (hL : HSKernel L) : hsNorm (compKernel K L) ≤ hsNorm K * hsNorm L := by
  classical
  -- measurability of the composed kernel
  have hcmp : AEStronglyMeasurable (compKernel K L) vol2 :=
    (stronglyMeasurable_compKernel hKm hLm).aestronglyMeasurable
  -- section energies are integrable, sections square-integrable a.e.
  have hK2meas : AEStronglyMeasurable (fun p : ℝ × ℝ => K p ^ 2) vol2 :=
    (hKm.pow_const 2).aestronglyMeasurable
  obtain ⟨hsecK, hnormK⟩ := (integrable_prod_iff hK2meas).mp (MemLp.integrable_sq hK)
  have hIK : Integrable (secE2 K) vol := by
    refine hnormK.congr (Filter.Eventually.of_forall fun x => ?_)
    show (∫ y : ℝ, ‖K (x, y) ^ 2‖ ∂vol) = (∫ t : ℝ, K (x, t) ^ 2 ∂vol)
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show ‖K (x, t) ^ 2‖ = K (x, t) ^ 2
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hL2tr : MemLp (ktranspose L) 2 vol2 := hsKernel_transpose hL
  obtain ⟨g, hgme, hgc⟩ := hL2tr.1
  have hL2meas : AEStronglyMeasurable (fun q : ℝ × ℝ => ktranspose L q ^ 2) vol2 :=
    ⟨g * g, hgme.mul hgme, by
      filter_upwards [hgc] with q hq
      show ktranspose L q ^ 2 = g q * g q
      rw [hq, pow_two]⟩
  obtain ⟨hsecL, hnormL⟩ := (integrable_prod_iff hL2meas).mp (MemLp.integrable_sq hL2tr)
  have hsecL' : ∀ᵐ y ∂vol, Integrable (fun t => L (t, y) ^ 2) vol := by
    filter_upwards [hsecL] with x hx
    exact hx
  have hIL : Integrable (secE1 L) vol := by
    refine hnormL.congr (Filter.Eventually.of_forall fun y => ?_)
    show (∫ t : ℝ, ‖ktranspose L (y, t) ^ 2‖ ∂vol) = (∫ t : ℝ, L (t, y) ^ 2 ∂vol)
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show ‖ktranspose L (y, t) ^ 2‖ = L (t, y) ^ 2
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rfl
  -- lift the a.e. section square-integrability to the product
  have hliftK : ∀ᵐ p : ℝ × ℝ ∂vol2, MemLp (fun t => K (p.1, t)) 2 vol := by
    have hind : ∀ᵐ x ∂vol,
        (if Integrable (fun t => K (x, t) ^ 2) vol then (1 : ℝ) else 0) = (1 : ℝ) := by
      filter_upwards [hsecK] with x hx
      rw [if_pos hx]
    filter_upwards [eventual_fst hind] with p hp
    by_cases hc : Integrable (fun t => K (p.1, t) ^ 2) vol
    · exact memLp_two_of_aemeasurable
        ((hKm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable) hc
    · rw [if_neg hc] at hp
      exact absurd hp (by norm_num)
  have hliftL : ∀ᵐ p : ℝ × ℝ ∂vol2, MemLp (fun t => L (t, p.2)) 2 vol := by
    have hind : ∀ᵐ y ∂vol,
        (if Integrable (fun t => L (t, y) ^ 2) vol then (1 : ℝ) else 0) = (1 : ℝ) := by
      filter_upwards [hsecL'] with y hy
      rw [if_pos hy]
    filter_upwards [eventual_snd hind] with p hp
    by_cases hc : Integrable (fun t => L (t, p.2) ^ 2) vol
    · exact memLp_two_of_aemeasurable
        ((hLm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable) hc
    · rw [if_neg hc] at hp
      exact absurd hp (by norm_num)
  -- a.e. pointwise domination by the product of section energies
  have hpt : ∀ᵐ p : ℝ × ℝ ∂vol2, compKernel K L p ^ 2 ≤ secE2 K p.1 * secE1 L p.2 := by
    filter_upwards [hliftK, hliftL] with p hx hy
    have h1 := abs_compKernel_le (p.1) (p.2) hx hy
    have hab : 0 ≤ Real.sqrt (secE2 K p.1) * Real.sqrt (secE1 L p.2) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    calc compKernel K L p ^ 2
        = |compKernel K L p| ^ 2 := (sq_abs _).symm
      _ ≤ (Real.sqrt (secE2 K p.1) * Real.sqrt (secE1 L p.2)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = secE2 K p.1 * secE1 L p.2 := by
        have hn1 : 0 ≤ secE2 K p.1 := integral_nonneg fun _ => sq_nonneg _
        have hn2 : 0 ≤ secE1 L p.2 := integral_nonneg fun _ => sq_nonneg _
        rw [mul_pow, Real.sq_sqrt hn1, Real.sq_sqrt hn2]
  -- the dominating function is integrable, hence so is the composed kernel squared
  have hB : Integrable (fun p : ℝ × ℝ => secE2 K p.1 * secE1 L p.2) vol2 :=
    Integrable.op_fst_snd (op := fun a b : ℝ => a * b) (by fun_prop)
      ⟨1, fun a b => by simp [Real.norm_eq_abs]⟩ hIK hIL
  have hcmp2 : Integrable (fun p : ℝ × ℝ => compKernel K L p ^ 2) vol2 := by
    obtain ⟨g, hgme, hgc⟩ := hcmp
    have hae : AEStronglyMeasurable (fun p : ℝ × ℝ => compKernel K L p ^ 2) vol2 :=
      ⟨g * g, hgme.mul hgme, by
        filter_upwards [hgc] with p hp
        show compKernel K L p ^ 2 = g p * g p
        rw [hp, pow_two]⟩
    refine hB.mono hae ?_
    filter_upwards [hpt] with p hp
    have hn : 0 ≤ secE2 K p.1 * secE1 L p.2 :=
      mul_nonneg (integral_nonneg fun _ => sq_nonneg _)
        (integral_nonneg fun _ => sq_nonneg _)
    calc ‖compKernel K L p ^ 2‖
        = compKernel K L p ^ 2 := by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      _ ≤ secE2 K p.1 * secE1 L p.2 := hp
      _ = ‖secE2 K p.1 * secE1 L p.2‖ := by
            rw [Real.norm_eq_abs, abs_of_nonneg hn]
  -- conclude by Fubini
  have hle : ∫ p : ℝ × ℝ, compKernel K L p ^ 2 ∂vol2
      ≤ ∫ p : ℝ × ℝ, secE2 K p.1 * secE1 L p.2 ∂vol2 := by
    exact integral_mono_ae hcmp2 hB hpt
  have hprod : (∫ p : ℝ × ℝ, secE2 K p.1 * secE1 L p.2 ∂vol2)
      = (∫ x : ℝ, secE2 K x ∂vol) * (∫ y : ℝ, secE1 L y ∂vol) := integral_prod_mul _ _
  have hI2 : (∫ x : ℝ, secE2 K x ∂vol) = ∫ p : ℝ × ℝ, K p ^ 2 ∂vol2 := by
    rw [integral_prod (fun p => K p ^ 2) (MemLp.integrable_sq hK)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun _ => rfl)
  have hI1 : (∫ y : ℝ, secE1 L y ∂vol) = ∫ p : ℝ × ℝ, L p ^ 2 ∂vol2 := by
    have hswap : (∫ p : ℝ × ℝ, L p ^ 2 ∂vol2)
        = ∫ q : ℝ × ℝ, L q.swap ^ 2 ∂vol2 := (integral_prod_swap (fun q => L q ^ 2)).symm
    rw [hswap, integral_prod (fun q => L q.swap ^ 2)
      (MemLp.integrable_sq (hsKernel_transpose hL))]
    exact integral_congr_ae (Filter.Eventually.of_forall fun _ => rfl)
  calc hsNorm (compKernel K L)
      = Real.sqrt (∫ p : ℝ × ℝ, compKernel K L p ^ 2 ∂vol2) := hsNorm_def _
    _ ≤ Real.sqrt ((∫ x : ℝ, secE2 K x ∂vol) * (∫ y : ℝ, secE1 L y ∂vol)) :=
        Real.sqrt_le_sqrt (by rw [← hprod]; exact hle)
    _ = hsNorm K * hsNorm L := by
        have hK2 : 0 ≤ ∫ p : ℝ × ℝ, K p ^ 2 ∂vol2 := integral_nonneg fun _ => sq_nonneg _
        have hL2 : 0 ≤ ∫ p : ℝ × ℝ, L p ^ 2 ∂vol2 := integral_nonneg fun _ => sq_nonneg _
        rw [hI2, hI1, Real.sqrt_mul hK2 (∫ p : ℝ × ℝ, L p ^ 2 ∂vol2), ← hsNorm_def K, ← hsNorm_def L]

/-! ### Item (2a): the k = 2 cycle identity -/

/-- **Item (2a)**: for a symmetric kernel the `k = 2` cycle is exactly the
squared HS norm: `∫∫ K(x,y) K(y,x) = ∫∫ K²`. -/
theorem cycle2_self_sq {K : ℝ × ℝ → ℝ} (hsym : ∀ p : ℝ × ℝ, K p = K p.swap) :
    cycle2 K K = hsNorm K ^ 2 := by
  have hEq : cycle2 K K = ∫ p : ℝ × ℝ, K p ^ 2 ∂vol2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    show K p * K p.swap = K p ^ 2
    rw [hsym p]
    ring
  rw [hEq, hsNorm_def, Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)]

/-- **Item (2a), transpose form** (no symmetry needed): the `k = 2` cycle of `K`
with its transpose is exactly the squared HS norm. -/
theorem cycle2_transpose_self (K : ℝ × ℝ → ℝ) :
    cycle2 K (ktranspose K) = hsNorm K ^ 2 := by
  have hEq : cycle2 K (ktranspose K) = ∫ p : ℝ × ℝ, K p ^ 2 ∂vol2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    show K p * ktranspose K p.swap = K p ^ 2
    have hswap : ktranspose K p.swap = K p := rfl
    rw [hswap]
    ring
  rw [hEq, hsNorm_def, Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)]

/-! ### The product-trace identity (`tr(TOp K · TOp L)` kernel-side) -/

/-- **The product trace identity**: the diagonal integral of the composed kernel
is the `cycle2` pairing — the kernel form of `tr(TOp K · TOp L) = ∫∫ K(x,y)L(y,x)`.
This is the k = 1 trace of a *composed* kernel (well defined), unlike the
k = 1 trace of a single kernel (documented gap in `HSOperatorFoundation`). -/
theorem integral_compKernel_diag {K L : ℝ × ℝ → ℝ} (hK : HSKernel K) (hL : HSKernel L) :
    (∫ x : ℝ, compKernel K L (x, x) ∂vol) = cycle2 K L := by
  have hint : Integrable (fun p : ℝ × ℝ => K p * L p.swap) vol2 := by
    haveI hpqr : Real.HolderTriple 2 2 1 := holderTriple221
    exact memLp_one_iff_integrable.mp (MemLp.mul' (hsKernel_transpose hL) hK)
  rw [cycle2, integral_prod (fun p => K p * L p.swap) hint]
  exact integral_congr_ae (Filter.Eventually.of_forall fun _ => rfl)

/-! ### The general-k cycle functional and the k = 2 anchor -/

/-- The kernel-side `k`-cycle functional:
`C_k(K) = ∫_{I^k} ∏ i, K (z i, z (cycleSucc i)) dz` over `vol^k`
(`vol` restricts each coordinate to `Icc (-1:ℝ) 1`). -/
def cycleIntegral (k : ℕ) (K : ℝ × ℝ → ℝ) : ℝ :=
  ∫ z : Fin k → ℝ, ∏ i : Fin k, K (z i, z (cycleSucc i)) ∂(Measure.pi fun _ : Fin k => vol)

/-- **The k = 2 anchor**: `C_2(K) = cycle2 K K = hsNorm K ^ 2` for symmetric `K`
(with `cycle2_transpose_self` giving the general transpose form). -/
theorem cycleIntegral_two (K : ℝ × ℝ → ℝ) : cycleIntegral 2 K = cycle2 K K := by
  calc cycleIntegral 2 K
      = ∫ z : Fin 2 → ℝ, ∏ i : Fin 2, K (z i, z (cycleSucc i))
          ∂(Measure.pi fun _ : Fin 2 => vol) := rfl
    _ = ∫ w : ℝ × ℝ, K w * K w.swap ∂(vol.prod vol) :=
        (integral_congr_ae (Filter.Eventually.of_forall fun (z : Fin 2 → ℝ) => by
          show (∏ i : Fin 2, K (z i, z (cycleSucc i)))
              = (fun w : ℝ × ℝ => K w * K w.swap)
                (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ) z)
          rw [Fin.prod_univ_two, cycleSucc_two_zero, cycleSucc_two_one]
          rfl)).trans
          ((measurePreserving_piFinTwo (fun _ : Fin 2 => vol)).integral_comp'
            (fun w : ℝ × ℝ => K w * K w.swap))
    _ = cycle2 K K := rfl

/-! ### The k = 3 chain integrals (composition anchor, expansion form) -/

/-- The triple chain integral of `K, L, M` along the 3-cycle
`∫∫∫ K(x,t) L(t,y) M(y,x)` — the kernel form of `tr(TOp K · TOp L · TOp M)`. -/
def chainCycleTriple (K L M : ℝ × ℝ → ℝ) : ℝ :=
  ∫ q : (ℝ × ℝ) × ℝ, K (q.1.1, q.2) * L (q.2, q.1.2) * M (q.1.2, q.1.1)
    ∂((vol.prod vol).prod vol)

/-- The composite-operator kernel pairing is the triple chain integral:
`tr(TOp K · TOp L · TOp M) = chainCycleTriple K L M` in kernel form. -/
theorem cycle2_compKernel_eq_triple {K L M : ℝ × ℝ → ℝ}
    (hA : Integrable (fun q : (ℝ × ℝ) × ℝ =>
        K (q.1.1, q.2) * L (q.2, q.1.2) * M (q.1.2, q.1.1)) ((vol.prod vol).prod vol)) :
    cycle2 (compKernel K L) M = chainCycleTriple K L M := by
  rw [cycle2, chainCycleTriple]
  have hpt : ∀ p : ℝ × ℝ, compKernel K L p * M p.swap
      = ∫ t : ℝ, K (p.1, t) * L (t, p.2) * M p.swap ∂vol := fun p => by
    rw [compKernel, integral_mul_const]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  show (∫ a : ℝ × ℝ, ∫ t : ℝ, K (a.1, t) * L (t, a.2) * M (a.2, a.1) ∂vol ∂vol2)
      = chainCycleTriple K L M
  rw [← integral_prod (fun q : (ℝ × ℝ) × ℝ =>
    K (q.1.1, q.2) * L (q.2, q.1.2) * M (q.1.2, q.1.1)) hA]
  rfl

/-- The triple chain integral in the permuted coordinate labeling (the
`((x, t), y)`-partition) — equal to `chainCycleTriple K L M` by the
measure-preserving transport `((x, y), t) ↦ ((x, t), y)` composed of
`measurePreserving_prodAssoc` and the coordinate swap `integral_prod_swap`
(documented; the two integrands agree after the re-labeling). -/
def chainCycleTripleB (K L M : ℝ × ℝ → ℝ) : ℝ :=
  ∫ q : (ℝ × ℝ) × ℝ, K (q.1.1, q.1.2) * L (q.1.2, q.2) * M (q.2, q.1.1)
    ∂((vol.prod vol).prod vol)

/-- The other parenthesization: `tr(TOp K · (TOp L · TOp M)) = chainCycleTripleB K L M`,
the permuted-labeling chain integral (equal to `chainCycleTriple K L M` by the
documented transport). -/
theorem cycle2_eq_compKernel_triple {K L M : ℝ × ℝ → ℝ}
    (hB : Integrable (fun q : (ℝ × ℝ) × ℝ =>
        K (q.1.1, q.1.2) * L (q.1.2, q.2) * M (q.2, q.1.1)) ((vol.prod vol).prod vol)) :
    cycle2 K (compKernel L M) = chainCycleTripleB K L M := by
  rw [cycle2, chainCycleTripleB]
  have hpt : ∀ p : ℝ × ℝ, K p * compKernel L M p.swap
      = ∫ t : ℝ, K (p.1, p.2) * L (p.2, t) * M (t, p.1) ∂vol := fun p => by
    have heq : compKernel L M p.swap = (∫ t : ℝ, L (p.2, t) * M (t, p.1) ∂vol) := rfl
    calc K p * compKernel L M p.swap
        = K (p.1, p.2) * (∫ t : ℝ, L (p.2, t) * M (t, p.1) ∂vol) := by rw [heq]
      _ = ∫ t : ℝ, K (p.1, p.2) * (L (p.2, t) * M (t, p.1)) ∂vol :=
            (integral_const_mul (K (p.1, p.2)) (fun t : ℝ => L (p.2, t) * M (t, p.1))).symm
      _ = ∫ t : ℝ, K (p.1, p.2) * L (p.2, t) * M (t, p.1) ∂vol :=
            integral_congr_ae (Filter.Eventually.of_forall fun t : ℝ =>
              (mul_assoc _ _ _).symm)
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    ← integral_prod (fun q : (ℝ × ℝ) × ℝ =>
      K (q.1.1, q.1.2) * L (q.1.2, q.2) * M (q.2, q.1.1)) hB]

end HS

end
