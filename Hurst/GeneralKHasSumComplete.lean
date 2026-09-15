import Hurst.HSCycleComposition
import Hurst.CycleTraceIdentification
import Hurst.FrozenSpectralCount
import Hurst.HSOperatorLayer3
import Hurst.P2SpectrumCloseout
import Hurst.GeneralKHasSum

/-!
# General-`k` HasSum completion: the `k = 3` Fubini anchor and the summability layer

This file completes parts of the DOCUMENTED RESIDUE of `Hurst.HSCycleComposition` on the
landed `HS` encoding and assembles the summability half of the general-`k` `HasSum` for
the multiplicity-exact enumeration of the compact symmetric kernel operator
(`HS.exists_multiplicity_enumeration`, `Hurst.FrozenSpectralCount`).

## What is landed here (all proofs complete, no placeholders)

* `HS.integrable_secE2` / `HS.integrable_secE1` — the section-energy functions
  `secE2 K x = ∫ t, K (x, t)^2`, `secE1 K y = ∫ t, K (t, y)^2` are integrable for every
  `HSKernel K` (the inline `hIK`/`hIL` steps of `hsNorm_comp_le`, extracted), together
  with the a.e. section square-integrability lemmas
  `HS.eventual_memLp_section_fst` / `HS.eventual_memLp_section_snd` (the raw material of
  the section Cauchy–Schwarz bound `abs_compKernel_le`).
* `HS.cycleIntegral_three_eq_tripleW` — **the `k = 3` Fubini transport**: the kernel-side
  `k = 3` cycle functional `cycleIntegral 3 K` equals the triple chain integral
  `∫∫∫ K(z₀,z₁) K(z₁,z₂) K(z₂,z₀)` in the `piFinSuccAbove`-peel coordinate form, via the
  measure-preserving equiv `pi3Equiv` (`measurePreserving_piFinSuccAbove` at `i = 1`
  composed with the coordinate swap — `prod_swap`), the `Fin.succAbove (1 : Fin 3)`
  point lemmas and `Fin.prod_univ_three`.
* `HS.summable_pow_of_multEnum` / `HS.hasSum_general_k_pow` — the summability half of the
  mission statement for **every `k ≥ 2`**: the enumerated power series `val j ^ k` is
  summable (the landed interpolation layer `summable_abs_pow_of_multEnum` gives absolute
  convergence; `summable_abs_iff` + `abs_pow` strip the absolute values) and `HasSum`s
  to its own tsum.

## The general-`k` induction skeleton (documented residue)

The exact mission statement `HasSum (fun j => val j ^ k) (cycleIntegral k K)` for
`k ≥ 3` is gated on two further pieces, both documented (NOT landed here):

1. **The operator-side diagonal-action step** (spectral-Calculus): `Σ_j κ_j^k =
   Σ_j ⟪(TOp K)^k e_j, e_j⟫` over the eigenbasis and the identification of that sum with
   `cycleIntegral k K` — the product-basis Parseval gap isolated in
   `Hurst.CycleTraceIdentification` (completeness of the tensor-product system
   `ψ_{ij}(x,y) = (e i)(x) · (e j)(y)` in `L²(vol2)`; mathlib v4.31 has nothing for `L²`
   of a product measure).  It gates `k = 3` as well; the `k = 2` anchor is landed
   (`cycleIntegral_two` + `cycle2_self_sq`).
2. **The `hA` discharge and the w↔q splice (kernel side, `k = 3` layer)**: the landed
   anchor `cycle2_compKernel_eq_triple` (`Hurst.HSCycleComposition`) identifies
   `cycle2 (compKernel K K) K` with the triple chain integral `chainCycleTriple K K K`
   over `((ℝ × ℝ) × ℝ)` under the integrability hypothesis `hA` (the discharge route:
   `hasFiniteIntegral_prod_iff` splits the shared slot `t`; a.e. section
   Cauchy–Schwarz bounds `∫_t |K(x,t)L(t,y)| ≤ √(secE2 K x) √(secE1 L y)`; the remaining
   `(x, y)`-bound `|M(y,x)| √(secE2 K x) √(secE1 L y)` is Hölder over `vol2` in `x`
   against the CS-in-`y`, giving `∫ |K L M| ≤ hsNorm K · hsNorm L · hsNorm M`; the
   `L²(vol)` factors `√secE2K`, `√secE2M` land exactly like the section-energy lemmas
   here).  The coordinate encoding produced by `cycleIntegral_three_eq_tripleW` (over
   `(Fin 2 → ℝ) × ℝ` with the `pi`-product measure) is identified with the
   `(ℝ × ℝ) × ℝ`-encoding of `chainCycleTriple` by the
   `prod_eq`/`measurePreserving_piFinTwo` extensionality technique — exactly Mathlib's
   own ad-hoc proof pattern for `measurePreserving_piFinTwo` (`Measure.prod_eq`,
   `Measure.pi_pi`, `Fin.prod_univ_two`); this splice is bookkeeping, not analysis.
3. **The chain-level peel induction** (kernel side): the recursion
   `C(W₀, W₁, W₂, …) = C(compKernel W₀ W₁, W₂, …)` peels the middle coordinate `z₁`:
   `∫_{z₁} W₀(z₀,z₁) W₁(z₁,z₂) dz₁ = compKernel W₀ W₁ (z₀,z₂)`.  Each peel is the
   `integral_compKernel_diag`/Fubini step with absolute convergence furnished by the
   section Cauchy–Schwarz machinery of item 2 iterated, and the `Fin.succAbove`
   reindexing transport landed in `cycleIntegral_three_eq_tripleW` is its `k = 3`
   instance.  After `k − 2` peels one reaches the `cycle2` form where
   `cycle2_transpose_self` / `cycle2_self_sq` give the `hsNorm` identity, integrability
   of the contracted kernels being maintained by `hsNorm_comp_le`.  The formal
   chain-level induction over `Fin`-indexed kernel families is not landed (budget).

With items 1–3 landed, `HasSum (fun j => val j ^ k) (cycleIntegral k K)` for `k ≥ 3`
closes by `HasSum` transport against `hasSum_general_k_pow` (the summability side is
complete).
-/

open MeasureTheory Measure Real Set
open scoped Real

noncomputable section

namespace HS

variable {K : ℝ × ℝ → ℝ} {hK : HSKernel K}

/-! ### Section-energy integrability (extracted from `hsNorm_comp_le`) -/

private theorem integral_pow_two_vol (u : ℝ → ℝ) :
    ∫ t : ℝ, u t ^ (2 : ℝ) ∂vol = ∫ t : ℝ, u t ^ 2 ∂vol := by
  apply integral_congr_ae
  filter_upwards with t
  rw [Real.rpow_two, pow_two]

private theorem stronglyMeasurable_secE2 {K : ℝ × ℝ → ℝ} (hKm : Measurable K) :
    StronglyMeasurable (secE2 K) :=
  (hKm.pow_const 2).stronglyMeasurable.integral_prod_right'

private theorem stronglyMeasurable_secE1 {K : ℝ × ℝ → ℝ} (hKm : Measurable K) :
    StronglyMeasurable (secE1 K) :=
  stronglyMeasurable_secE2 (hKm.comp measurable_swap)

/-- `secE2 K x = ∫ t, K (x, t)^2` is integrable for every `HSKernel K`. -/
theorem integrable_secE2 {K : ℝ × ℝ → ℝ} (hK : HSKernel K) : Integrable (secE2 K) vol := by
  obtain ⟨hsecK, hnormK⟩ :=
    (integrable_prod_iff (MemLp.integrable_sq hK).aestronglyMeasurable).mp
      (MemLp.integrable_sq hK)
  refine hnormK.congr (Filter.Eventually.of_forall fun x => ?_)
  show (∫ y : ℝ, ‖K (x, y) ^ 2‖ ∂vol) = (∫ t : ℝ, K (x, t) ^ 2 ∂vol)
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  show ‖K (x, t) ^ 2‖ = K (x, t) ^ 2
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]

/-- `secE1 K y = ∫ t, K (t, y)^2` is integrable for every `HSKernel K`. -/
theorem integrable_secE1 {K : ℝ × ℝ → ℝ} (hK : HSKernel K) : Integrable (secE1 K) vol := by
  have htr : secE2 (ktranspose K) = secE1 K := by
    funext y
    show (∫ t : ℝ, ktranspose K (y, t) ^ 2 ∂vol) = (∫ t : ℝ, K (t, y) ^ 2 ∂vol)
    rfl
  rw [← htr]
  exact integrable_secE2 (hsKernel_transpose hK)

/-! ### A.e. section square-integrability and the section Cauchy–Schwarz bound -/

/-- A.e. section square-integrability in the second slot: for a.e. `x`,
`t ↦ K (x, t)` is `L²(vol)`. -/
theorem eventual_memLp_section_fst {K : ℝ × ℝ → ℝ} (hKm : Measurable K)
    (hK : HSKernel K) : ∀ᵐ x ∂vol, MemLp (fun t => K (x, t)) 2 vol := by
  have hsecK : ∀ᵐ x ∂vol, Integrable (fun t => K (x, t) ^ 2) vol := by
    obtain ⟨h0, _⟩ :=
      (integrable_prod_iff (MemLp.integrable_sq hK).aestronglyMeasurable).mp
      (MemLp.integrable_sq hK)
    exact h0
  filter_upwards [hsecK] with x hx
  exact memLp_two_of_aemeasurable
    ((hKm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable) hx

/-- A.e. section square-integrability in the first slot: for a.e. `y`,
`t ↦ L (t, y)` is `L²(vol)`. -/
theorem eventual_memLp_section_snd {L : ℝ × ℝ → ℝ} (hLm : Measurable L)
    (hL : HSKernel L) : ∀ᵐ y ∂vol, MemLp (fun t => L (t, y)) 2 vol := by
  have hL2tr : MemLp (ktranspose L) 2 vol2 := hsKernel_transpose hL
  obtain ⟨hsecL, _⟩ :=
    (integrable_prod_iff (MemLp.integrable_sq hL2tr).aestronglyMeasurable).mp
      (MemLp.integrable_sq hL2tr)
  filter_upwards [hsecL] with y hy
  exact memLp_two_of_aemeasurable
    ((hLm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable) hy

/-! ### The `k = 3` Fubini anchor: `Fin 3` transport and composition -/

/-! ### The `k = 3` Fubini transport: the `Fin 3`-form cycle as a triple integral -/

/-- The coordinate swap on `ℝ × (Fin 2 → ℝ)` is measure preserving. -/
private theorem mp_swap_pi2 :
    MeasurePreserving (Prod.swap : ℝ × (Fin 2 → ℝ) → (Fin 2 → ℝ) × ℝ)
      (vol.prod (Measure.pi fun _ : Fin 2 => vol))
      ((Measure.pi fun _ : Fin 2 => vol).prod vol) :=
  ⟨measurable_swap, prod_swap⟩

/-- The `k = 3` transport equiv: `z ↦ ((z 0, z 2), z 1)` (succAbove-peel of coordinate 1,
composed with the coordinate swap). -/
private def pi3Equiv : (Fin 3 → ℝ) ≃ᵐ (Fin 2 → ℝ) × ℝ :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 1).trans MeasurableEquiv.prodComm

private theorem mp_pi3 :
    MeasurePreserving pi3Equiv (Measure.pi fun _ : Fin 3 => vol)
      ((Measure.pi fun _ : Fin 2 => vol).prod vol) :=
  (measurePreserving_piFinSuccAbove (fun _ : Fin 3 => vol) 1).trans mp_swap_pi2

private theorem pi3Equiv_fst_zero (z : Fin 3 → ℝ) : (pi3Equiv z).1 0 = z 0 := by
  simp only [pi3Equiv, MeasurableEquiv.trans_apply]
  rfl

private theorem pi3Equiv_fst_one (z : Fin 3 → ℝ) : (pi3Equiv z).1 1 = z 2 := by
  simp only [pi3Equiv, MeasurableEquiv.trans_apply]
  rfl

private theorem pi3Equiv_snd (z : Fin 3 → ℝ) : (pi3Equiv z).2 = z 1 := by
  simp only [pi3Equiv, MeasurableEquiv.trans_apply]
  rfl

private theorem cycleSucc_three_zero : cycleSucc (0 : Fin 3) = 1 := by
  simp [cycleSucc]

private theorem cycleSucc_three_one : cycleSucc (1 : Fin 3) = 2 := by
  simp [cycleSucc]

private theorem cycleSucc_three_two : cycleSucc (2 : Fin 3) = 0 := by
  simp [cycleSucc]

/-- **The `k = 3` Fubini transport**: the kernel-side `k = 3` cycle functional equals the
triple chain integral `∫∫∫ K(z₀,z₁) K(z₁,z₂) K(z₂,z₀)` (in the `piFinSuccAbove`-peel
coordinate form).  Together with the landed `cycle2_compKernel_eq_triple`
(`Hurst.HSCycleComposition`, whose triple chain integral `chainCycleTriple K K K` is the
same integral in the `(ℝ × ℝ) × ℝ`-coordinate encoding — the two measures
`(Measure.pi fun _ : Fin 2 => vol).prod vol` and `(vol.prod vol).prod vol` are identified
by the `prod_eq`/`measurePreserving_piFinTwo` extensionality technique, exactly as in
Mathlib's own proof of `measurePreserving_piFinTwo`) this gives the `k = 3` instance of
the peel composition `cycleIntegral 3 K = cycle2 (compKernel K K) K`. -/
theorem cycleIntegral_three_eq_tripleW (K : ℝ × ℝ → ℝ) :
    cycleIntegral 3 K = ∫ w : (Fin 2 → ℝ) × ℝ,
      K (w.1 0, w.2) * K (w.2, w.1 1) * K (w.1 1, w.1 0)
      ∂((Measure.pi fun _ : Fin 2 => vol).prod vol) := by
  have hterm : ∀ z : Fin 3 → ℝ,
      (∏ i : Fin 3, K (z i, z (cycleSucc i)))
        = (fun w : (Fin 2 → ℝ) × ℝ =>
            K (w.1 0, w.2) * K (w.2, w.1 1) * K (w.1 1, w.1 0)) (pi3Equiv z) := by
    intro z
    rw [Fin.prod_univ_three, cycleSucc_three_zero, cycleSucc_three_one, cycleSucc_three_two]
    show K (z 0, z 1) * K (z 1, z 2) * K (z 2, z 0)
      = (fun w : (Fin 2 → ℝ) × ℝ =>
          K (w.1 0, w.2) * K (w.2, w.1 1) * K (w.1 1, w.1 0)) (pi3Equiv z)
    simp only []
    rw [pi3Equiv_fst_zero, pi3Equiv_snd, pi3Equiv_fst_one]
  show (∫ z : Fin 3 → ℝ, ∏ i : Fin 3, K (z i, z (cycleSucc i))
      ∂(Measure.pi fun _ : Fin 3 => vol)) = _
  refine Eq.trans ?_ (mp_pi3.integral_comp' (fun w : (Fin 2 → ℝ) × ℝ =>
    K (w.1 0, w.2) * K (w.2, w.1 1) * K (w.1 1, w.1 0)))
  exact integral_congr_ae (Filter.Eventually.of_forall hterm)

/-! ### The general-`k` HasSum: the summability layer for the enumerated spectrum -/

/-- **Summability of the enumerated powers for every `k ≥ 2`**: the interpolation layer
`summable_abs_pow_of_multEnum` gives absolute convergence, hence convergence of
`val j ^ k` itself. -/
theorem summable_pow_of_multEnum
    (hCompact : IsCompactOperator (TOp K hK))
    (hsym : (↑(TOp K hK) : L2 →ₗ[ℝ] L2).IsSymmetric)
    {val : ℕ → ℝ} {vec : ℕ → L2}
    (hval : ∀ j, val j = 0 ∨ Module.End.HasEigenvector (TOpEnd' K hK) (val j) (vec j))
    (hmult : ∀ μ : ℝ, Module.End.HasEigenvalue (TOpEnd' K hK) μ → μ ≠ 0 →
      Nat.card {j : ℕ // val j = μ}
        = Module.finrank ℝ (Module.End.eigenspace (TOpEnd' K hK) μ))
    (k : ℕ) (hk : 2 ≤ k) :
    Summable (fun j => val j ^ k) := by
  have habs := summable_abs_pow_of_multEnum hCompact hsym hval hmult k hk
  exact summable_abs_iff.mp (habs.congr fun j => by rw [abs_pow])

/-- **The general-`k` `HasSum` (summability layer, `k ≥ 2`)**: the enumerated power
series `val j ^ k` `HasSum`s to its own tsum.  The exact target `cycleIntegral k K`
(`C_k(K)`) is gated on the operator-side Parseval gap
(`Hurst.CycleTraceIdentification`) and the chain-level peel induction (see the module
docstring); at `k = 3` the kernel-side transport
`cycleIntegral_three_eq_tripleW` is landed here. -/
theorem hasSum_general_k_pow
    (hCompact : IsCompactOperator (TOp K hK))
    (hsym : (↑(TOp K hK) : L2 →ₗ[ℝ] L2).IsSymmetric)
    {val : ℕ → ℝ} {vec : ℕ → L2}
    (hval : ∀ j, val j = 0 ∨ Module.End.HasEigenvector (TOpEnd' K hK) (val j) (vec j))
    (hmult : ∀ μ : ℝ, Module.End.HasEigenvalue (TOpEnd' K hK) μ → μ ≠ 0 →
      Nat.card {j : ℕ // val j = μ}
        = Module.finrank ℝ (Module.End.eigenspace (TOpEnd' K hK) μ))
    (k : ℕ) (hk : 2 ≤ k) :
    HasSum (fun j => val j ^ k) (∑' j, val j ^ k) :=
  (summable_pow_of_multEnum hCompact hsym hval hmult k hk).hasSum

end HS

end
