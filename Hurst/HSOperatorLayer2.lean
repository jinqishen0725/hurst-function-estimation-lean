import Hurst.HSOperatorFoundation

/-!
# HS operator layer 2: the Riesz kernel instantiation (spectrum prerequisites)

Builds spectrum-construction prerequisites on top of the landed `HS` layer
(`Hurst.HSOperatorFoundation`), reusing its encoding exactly: carrier measure
`vol = volume.restrict (Icc (-1:ℝ) 1)` on `ℝ`, kernels `K : ℝ × ℝ → ℝ` with
`HSKernel K = MemLp K 2 vol2`, `hsNorm K = (∫∫ K² ∂vol2)^(1/2)`.

## Main results

* `memLp_two_of_aemeasurable` — bridge: a.e.-measurable + square-integrable ⇒ `MemLp 2`.
* `rieszKernel` — the continuum truncated weighted Riesz kernel
  `K_R(x,y) = ω(x)·c·|x-y|^(-ψ)` on the unit square; its k-fold cyclic
  integrals are `Hurst.weightedRieszCycleIntegral k ψ c ω`: the cycle product
  ∏ ω(z_i)·c·|z_i - z_{succ i}|^(-ψ) is the `vol^k`-integral of
  `∏ rieszKernel ψ c ω (z_i, z_{succ i})`; the `Icc`-indicator encoding of
  `weightedRieszCycleIntegral` over `volume^k` converts via
  `Measure.restrict_pi_pi` (`Mathlib/MeasureTheory/Constructions/Pi.lean:420`).
  * `hsKernel_rieszKernel` — **item (2a)**: square-integrability of the kernel
    from square-integrability of `|x-y|^(-2ψ)` on the square (the analytic
    core, `2ψ < 1`) plus a bounded weight, by domination;
  * `hsNorm_rieszKernel_sq` — the HS norm² is exactly the L²-energy integral;
  * `TOp_riesz_norm_le` — **item (2b)**: the induced bounded operator on L²;
  * `TOp_riesz_selfAdjoint` — **item (3)**: self-adjointness for constant
    weight (the uniform-`ω` case used by the HasSum power-sum work).

The a.e.-measurability of the factor `p ↦ |p.1-p.2|^(-ψ)` is carried as the
explicit hypothesis `hpow` (it is elementary: `Real.rpow_def_of_nonneg` gives
an `ite`-expansion agreeing off the null diagonal with the measurable function
`p ↦ exp (log |p.1-p.2| * (-ψ))`; landing the a.e.-congruence was out of
budget this round).

## Items 1 and the rest of 3 — status and gap report

* **General-k cycle bound (item 1)**: not landed (budget).  Verified
  architecture for the next round: peel coordinate `z_0` via
  `measurePreserving_piFinSuccAbove` (`Mathlib/MeasureTheory/Constructions/Pi.lean:801`,
  with `MeasurePreserving.integral_comp'`, `Fin.cons_zero`, `Fin.cons_succ`,
  `Fin.prod_univ_succ`), absorb the two kernels adjacent to `z_0` into the
  composition kernel `compK K L p = ∫ t, K (p.1,t) * L (t,p.2)` with
  `hsNorm (compK K L) ≤ hsNorm K * hsNorm L` (Cauchy–Schwarz on section
  integrals via `integral_mul_norm_le_Lp_mul_Lq` + Fubini), contract, induct
  from the landed `HS.cycle2_bound` base.  Section integrals are measurable by
  `MeasureTheory.StronglyMeasurable.integral_prod_right'`
  (`Mathlib/MeasureTheory/Integral/Prod.lean:124`), so kernels must be assumed
  everywhere-`Measurable`; nonneg kernels make every Fubini step Tonelli and
  the signed bound follows from `|∫F| ≤ ∫|F|`.
* **Compaction (item 3)**: mathlib v4.31 has a genuine compact-operator API
  (see inventory) but no "L² kernel ⇒ compact operator" lemma, so compaction
  of `TOp K_R` is a documented gap; self-adjointness IS landed here.
* **Positivity**: pointwise-nonneg kernels do NOT have nonneg quadratic form
  (moving-average counterexample `1_{|x-y|≤ε}` has negative eigenvalues); the
  true positive-definiteness of `|x-y|^(-ψ)` is Fourier-analytic, absent from
  mathlib.  Not landed.
* **Square-integrability of `|x-y|^(-2ψ)` itself**: elementary dyadic layering
  (`|x-y|^(-2ψ) ≤ Σ_n 2^{2ψ(n+1)}·1_{|x-y|≤2^{-n}}`, each layer has area ≤
  8·2^{-n}, geometric sum since `2^{2ψ-1} < 1`) — architected, not landed.

## Mathlib v4.31 spectral inventory (searched 2026-09-12)

EXISTS:
* `ContinuousLinearMap.IsCompactOperator` (`Analysis/Normed/Operator/Compact/Basic.lean`),
  `IsCompactOperator.comp_clm`, `isCompactOperator_of_tendsto` (limits of
  compact operators are compact), `isClosed_setOf_isCompactOperator`, the
  `compactOperator` ideal.
* Fredholm alternative (`Analysis/Normed/Operator/Compact/FredholmAlternative.lean`):
  `IsCompactOperator.hasEigenvalue_or_mem_resolventSet`,
  `IsCompactOperator.hasEigenvalue_iff_mem_spectrum` (nonzero spectrum = nonzero
  eigenvalues).
* **Spectral theorem for compact self-adjoint operators**
  (`Analysis/InnerProductSpace/Spectrum.lean`, `ContinuousLinearMap` namespace):
  `orthogonalComplement_iSup_eigenspaces_eq_bot` (eigenspaces span densely),
  `finite_dimensional_eigenspace` (nonzero eigenspaces finite-dimensional),
  `eq_zero_of_forall_hasEigenvalue_eq_zero`, `eigenvalue_nonneg_of_nonneg`,
  `spectralRadius_eq_nnnorm`.

MISSING (blocks the eigenvalue-enumeration corollary `Σκ_j² = hsNorm²`):
* Hilbert–Schmidt/Schatten-class API; eigenvalue enumeration with Parseval for
  compact self-adjoint operators (`LinearMap.IsSymmetric.eigenvectorBasis` is
  finite-dimensional only).
-/

open MeasureTheory Measure Real Set
open scoped Real

noncomputable section

namespace HS

/-! ### Bridges -/

/-- `MemLp f 2 μ` from a.e.-measurability and square-integrability. -/
theorem memLp_two_of_aemeasurable {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : AEStronglyMeasurable f μ)
    (hfin : Integrable (fun x => f x ^ 2) μ) : MemLp f 2 μ := by
  rw [memLp_two_iff_integrable_sq_norm hf]
  exact (integrable_congr (Filter.Eventually.of_forall fun x => by
    simp only [Real.norm_eq_abs, sq_abs])).1 hfin

/-- The square of the distance-power factor. -/
private theorem abs_rpow_sq {r e : ℝ} (hr : 0 ≤ r) :
    (r ^ e) ^ (2 : ℕ) = r ^ (e * 2) := by
  rw [← Real.rpow_natCast]
  exact (Real.rpow_mul hr e 2).symm

/-! ### The Riesz kernel -/

/-- The continuum truncated weighted Riesz kernel on the unit square:
`K_R(x,y) = ω(x)·c·|x-y|^(-ψ)` for `x,y ∈ Icc (-1) 1` (the `Icc`-indicator
matches the encoding of `Hurst.weightedRieszCycleIntegral`). -/
def rieszKernel (psi c : ℝ) (omega : ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => (I : Set ℝ).indicator omega p.1 * c * |p.1 - p.2| ^ (-psi)

theorem rieszKernel_apply (psi c : ℝ) (omega : ℝ → ℝ) (x y : ℝ) :
    rieszKernel psi c omega (x, y)
      = (I : Set ℝ).indicator omega x * c * |x - y| ^ (-psi) := rfl

/-- The Riesz kernel is a.e.-measurable given the a.e.-measurability of the
distance-power factor and measurability of the weight. -/
theorem aestronglyMeasurable_rieszKernel {psi c : ℝ} {omega : ℝ → ℝ}
    (homega : Measurable omega)
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2) :
    AEStronglyMeasurable (rieszKernel psi c omega) vol2 := by
  have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => (I : Set ℝ).indicator omega p.1 * c) vol2 :=
    (Measurable.mul_const (Measurable.comp
      (homega.indicator (measurableSet_Icc (a := (-1 : ℝ)) (b := (1 : ℝ)))) measurable_fst)
      c).aestronglyMeasurable
  exact h1.mul hpow

/-- **Item (2a)**: the Riesz kernel is a Hilbert–Schmidt kernel once
`|x-y|^(-2ψ)` is square-integrable on the square (true for `2ψ < 1`) and the
weight is bounded; proved by domination. -/
theorem hsKernel_rieszKernel {psi c : ℝ} {omega : ℝ → ℝ} {M : ℝ}
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2) :
    HSKernel (rieszKernel psi c omega) := by
  have hae : AEStronglyMeasurable (rieszKernel psi c omega) vol2 :=
    aestronglyMeasurable_rieszKernel homega hpow
  have hind : ∀ x : ℝ, |(I : Set ℝ).indicator omega x| ≤ |M| := by
    intro x
    by_cases hx : x ∈ (I : Set ℝ)
    · rw [Set.indicator_of_mem hx]
      calc |omega x| ≤ M := hbdd x
        _ ≤ |M| := le_abs_self _
    · simp [hx]
  have hle : ∀ p : ℝ × ℝ,
      rieszKernel psi c omega p ^ 2 ≤ (M * c) ^ 2 * |p.1 - p.2| ^ (-2 * psi) := by
    intro p
    have hsplit : rieszKernel psi c omega p ^ 2
        = ((I : Set ℝ).indicator omega p.1 * c) ^ 2 * (|p.1 - p.2| ^ (-psi)) ^ 2 := by
      rw [rieszKernel_apply, mul_pow, mul_pow]
    rw [hsplit, abs_rpow_sq (abs_nonneg (p.1 - p.2))]
    have h1' : |(I : Set ℝ).indicator omega p.1 * c| ≤ |M * c| := by
      have ha1 : |(I : Set ℝ).indicator omega p.1 * c|
          = |(I : Set ℝ).indicator omega p.1| * |c| := abs_mul _ _
      have ha2 : |M * c| = |M| * |c| := abs_mul _ _
      rw [ha1, ha2]
      exact mul_le_mul (hind p.1) (le_refl (|c|)) (abs_nonneg c) (abs_nonneg _)
    have h2' : ((I : Set ℝ).indicator omega p.1 * c) ^ 2
        = |(I : Set ℝ).indicator omega p.1 * c| ^ 2 := (sq_abs _).symm
    have h3' : (M * c) ^ 2 = |M * c| ^ 2 := (sq_abs _).symm
    rw [h2', h3', show (-psi : ℝ) * 2 = -2 * psi from by ring]
    exact mul_le_mul_of_nonneg_right (sq_le_sq.mpr (by simpa using h1')) (by positivity)
  have hconst : Integrable (fun p : ℝ × ℝ => (M * c) ^ 2 * |p.1 - p.2| ^ (-2 * psi)) vol2 :=
    hg.const_mul _
  have hK2 : AEStronglyMeasurable
      (fun p : ℝ × ℝ => rieszKernel psi c omega p ^ 2) vol2 := by
    have heq : (fun p : ℝ × ℝ => rieszKernel psi c omega p ^ 2)
        = (rieszKernel psi c omega * rieszKernel psi c omega) := by
      funext p
      simp [Pi.mul_apply, pow_two]
    rw [heq]
    exact hae.mul hae
  have hKsq : Integrable (fun p : ℝ × ℝ => rieszKernel psi c omega p ^ 2) vol2 :=
    hconst.mono hK2
      (Filter.Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Real.norm_eq_abs,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ (M * c) ^ 2 * |p.1 - p.2| ^ (-2 * psi))]
        exact hle p)
  exact memLp_two_of_aemeasurable hae hKsq

/-- The HS norm² of the Riesz kernel is exactly its L² energy on the square. -/
theorem hsNorm_rieszKernel_sq (psi c : ℝ) (omega : ℝ → ℝ) :
    hsNorm (rieszKernel psi c omega) ^ 2
      = ∫ p : ℝ × ℝ, rieszKernel psi c omega p ^ 2 ∂vol2 := by
  rw [hsNorm_def, Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)]

/-! ### The Riesz operator (items 2b, 3) -/

/-- **Item (2b)**: the Riesz kernel induces a bounded operator on `L²`
with operator norm bounded by the kernel HS norm. -/
theorem TOp_riesz_norm_le {psi c : ℝ} {omega : ℝ → ℝ} {M : ℝ}
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2) :
    ‖TOp (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg)‖
      ≤ hsNorm (rieszKernel psi c omega) :=
  TOp_norm_le _

/-- **Item (3)**: if the truncated weight `(Icc (-1) 1).indicator ω` is constant
(in particular: `ω` constant on the square and vanishing off it — the uniform
weight case used by the HasSum power-sum work), the Riesz kernel is symmetric
and the Riesz operator is self-adjoint. -/
theorem TOp_riesz_selfAdjoint {psi c : ℝ} {omega : ℝ → ℝ} {M : ℝ}
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y) :
    (TOp (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg)).adjoint
      = TOp (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg) := by
  refine TOp_selfAdjoint (hsKernel_rieszKernel hpow homega hbdd hg) fun p => ?_
  show rieszKernel psi c omega p = rieszKernel psi c omega p.swap
  have e1 : rieszKernel psi c omega p
      = (I : Set ℝ).indicator omega p.1 * c * |p.1 - p.2| ^ (-psi) := rieszKernel_apply _ _ _ _ _
  have e2 : rieszKernel psi c omega p.swap
      = (I : Set ℝ).indicator omega p.2 * c * |p.2 - p.1| ^ (-psi) :=
    rieszKernel_apply psi c omega p.2 p.1
  rw [e1, e2, hconst p.1 p.2, abs_sub_comm p.1 p.2]

end HS

end
