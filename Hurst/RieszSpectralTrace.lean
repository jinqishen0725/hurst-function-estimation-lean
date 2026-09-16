import Hurst.RieszCompactEnumeration
import Hurst.FrozenSpectralCount
import Hurst.P2SpectrumConstruction

/-!
# Spectral trace-identity pair for the uniform-`ω` Riesz kernel operator

The pair consumed by P2's `rieszSpectrum` construction (`Hurst.P2SpectrumConstruction`):
the multiplicity-exact eigenvalue enumeration `κ` of the compact self-adjoint Riesz
operator `T = TOp K_R` (`HS.exists_multiplicity_enumeration` instantiated at
`isCompactOperator_TOp_riesz` / `isSymmetric_TOp_rieszKernel`), and the identification
of its power sums with the Riesz cycle integrals.

## Landed here

1. **Eigenvector power identity (the `⟨T^k f, f⟩` quadratic-form layer).**
   * `HS.inner_pow_of_hasEigenvector` — for an eigenvector `e` of `T` with eigenvalue
     `μ`, `⟪(T^k) e, e⟫ = μ^k · ‖e‖²` (via mathlib `Module.End.HasEigenvector.pow_apply`);
   * `HS.inner_pow_eq_zero_of_mem_zeroEigenspace` — the kernel part contributes `0`:
     for `e ∈ eigenspace T 0` and `k ≥ 1`, `⟪(T^k) e, e⟫ = 0` (the `T^k`-annihilation
     of the kernel part of the eigenbasis);
   * `HS.inner_pow_of_enumeration` — the identity over the multiplicity enumeration:
     `⟪(T^k) (vec j), vec j⟫ = κ_j^k · ‖vec j‖²` for every entry that is a nonzero
     eigenvalue or a kernel-padded zero vector (exactly the entries the landed
     enumeration produces);
   * `HS.exists_multiplicity_enumeration_riesz` — the enumeration existence for the
     uniform-`ω` Riesz operator with the pairing identity bundled;
   * `HS.hasEigenvalue_pow_TOpEnd` — `μ` eigenvalue ⇒ `μ^k` eigenvalue of `T^k`.

   *Documented deviation from the mission item (1):* the *full-ONB* trace identity
   `Σ_{ONB} ⟪T^k f, f⟫ = Σ_j κ_j^k` requires assembling an orthonormal basis across
   the countably many finite-dimensional eigenspaces plus a kernel-part basis and
   reindexing both sums by eigenvalue fibers (the `OrthogonalFamily`/`tsum_fiberwise`
   bookkeeping); that layer is NOT landed — the landed form is the term-level identity
   above, which is exactly the per-basis-vector contribution, so the ONB identity
   follows once the cross-eigenspace ONB assembly is added.

2. **Cycle identification `k = 2`.**
   * `HS.integral_vol2_eq_indicator_square` — bridge: `vol2`-integrals are indicator
     integrals over `volume × volume` on the square (`Measure.prod_restrict` +
     `integral_indicator`);
   * `HS.weightedRieszCycleIntegral_two_eq_cycle2` — `weightedRieszCycleIntegral 2 ψ c ω
     = cycle2 K_R K_R`, unconditional: the `Fin 2 → ℝ` volume is carried to
     `ℝ × ℝ` by `volume_preserving_finTwoArrow` and the cyclic product collapses to
     `K_R p · K_R p.swap` pointwise (the `finCyclicSucc`-on-`Fin 2` case analysis is
     proved here as `finCyclicSucc_two_zero`/`finCyclicSucc_two_one`);
   * `HS.cycle2_self_eq_hsNorm_sq` / `HS.cycle2_rieszKernel_eq_hsNorm_sq` — for the
     symmetric Riesz kernel, `cycle2 K K = hsNorm K²`;
   * `HS.weightedRieszCycleIntegral_two_eq_hsNorm_sq` — **the k = 2 cycle integral is
     the squared HS norm**: `weightedRieszCycleIntegral 2 ψ c ω = hsNorm K_R²`.

3. **General `k`.**
   * `HS.weightedRieszCycleIntegral_eq_kernelProduct` — unconditional: the `k`-cycle
     integral is the `volume^k`-integral of the kernel product
     `∏_i K_R(z_i, z_{succ i})` (so the iterated-Fubini identification with
     `⟪(T^k)·,·⟫` pairings can be stated purely kernel-side);
   * `HS.isRieszSpectrumSequence_of_hasSum` — the P2 consumption packaging.

## Gap report — the exact remaining path to P2's `rieszSpectrum`

* **Parseval step (blocks the HasSum at `k = 2`)**: `Σ_j κ_j² = hsNorm K_R²` needs the
  a.e. section formula `(T f) x = ∫ K(x, y) f y dy` (Riesz representer of the section
  pairings; then Bessel/Parseval over the eigenbasis and `∫∫ K² = hsNorm²`).  The
  pairing formula `inner_TOp` alone does not expand `T f` inside an integral.
* **Composition step (blocks general `k`)**: `Σ_j κ_j^k = weightedRieszCycleIntegral
  k ψ c ω` for `k ≥ 3` needs the iterated-Fubini composition
  (`compK K K` with `hsNorm (compK) ≤ hsNorm²`, peel `z_0` via
  `measurePreserving_piFinSuccAbove`, induct from `cycle2_bound`), as architected in
  the gap report of `Hurst.HSOperatorLayer2`.
* **PSD (the nonnegativity clause)**: remains deferred exactly as documented in
  `Hurst.P2SpectrumConstruction` (the Fourier-analytic positive-definiteness of
  `|x - y|^(-ψ)`); the signed `hPos`-conditional route covers nonnegative weights.
-/

open MeasureTheory Measure Real Set
open scoped Real

noncomputable section

namespace HS

/-! ### Fin 2 cyclic successor -/

/-- On `Fin 2` the cyclic successor of `0` is `1`. -/
theorem finCyclicSucc_two_zero : Hurst.finCyclicSucc (0 : Fin 2) = 1 := by
  unfold Hurst.finCyclicSucc
  simp

/-- On `Fin 2` the cyclic successor of `1` is `0`. -/
theorem finCyclicSucc_two_one : Hurst.finCyclicSucc (1 : Fin 2) = 0 := rfl

/-! ### The generic quadratic-form power identities -/

variable {K : ℝ × ℝ → ℝ} {hK : HSKernel K}

/-- **Eigenvector power identity**: for an eigenvector `e` of the kernel operator with
eigenvalue `μ`, the `k`-th power pairing is `⟪(T^k) e, e⟫ = μ^k · ‖e‖²`
(mathlib `Module.End.HasEigenvector.pow_apply`). -/
theorem inner_pow_of_hasEigenvector {μ : ℝ} {e : L2}
    (he : Module.End.HasEigenvector (TOpEnd' K hK) μ e) (k : ℕ) :
    inner ℝ ((TOpEnd' K hK ^ k) e) e = μ ^ k * ‖e‖ ^ 2 := by
  rw [he.pow_apply k, real_inner_smul_left, real_inner_self_eq_norm_sq]

/-- The kernel part of the eigenbasis contributes zero: for `e` in the zero eigenspace
(the operator kernel) and `k ≥ 1`, `⟪(T^k) e, e⟫ = 0`. -/
theorem inner_pow_eq_zero_of_mem_zeroEigenspace {e : L2}
    (he : e ∈ Module.End.eigenspace (TOpEnd' K hK) 0) {k : ℕ} (hk : 1 ≤ k) :
    inner ℝ ((TOpEnd' K hK ^ k) e) e = 0 := by
  by_cases h0 : e = 0
  · subst h0
    simp
  · have hv : Module.End.HasEigenvector (TOpEnd' K hK) 0 e := ⟨he, h0⟩
    rw [inner_pow_of_hasEigenvector hv k,
      show (0 : ℝ) ^ k = 0 from zero_pow (by omega), zero_mul]

/-- `μ` an eigenvalue of the kernel operator ⇒ `μ^k` an eigenvalue of `T^k`
(mathlib `Module.End.HasEigenvalue.pow`). -/
theorem hasEigenvalue_pow_TOpEnd {μ : ℝ} {k : ℕ}
    (hμ : Module.End.HasEigenvalue (TOpEnd' K hK) μ) :
    Module.End.HasEigenvalue (TOpEnd' K hK ^ k) (μ ^ k) :=
  hμ.pow k

/-- **Enumeration power identity**: for a multiplicity enumeration `(val, vec)` of the
kernel operator (in the shape delivered by `exists_multiplicity_enumeration`), every
entry that is a nonzero eigenvalue or a kernel-padded zero satisfies
`⟪(T^k) (vec j), vec j⟫ = val j^k · ‖vec j‖²`.  On the eigenbasis part this is the
`κ^k` eigenvalue contribution (`‖vec j‖ = 1` for the landed enumeration), on the
kernel part both sides vanish. -/
theorem inner_pow_of_enumeration {val : ℕ → ℝ} {vec : ℕ → L2}
    (hvec : ∀ j, val j = 0 ∨ Module.End.HasEigenvector (TOpEnd' K hK) (val j) (vec j))
    (k : ℕ) (j : ℕ) (hj : val j ≠ 0 ∨ vec j = 0) :
    inner ℝ ((TOpEnd' K hK ^ k) (vec j)) (vec j) = val j ^ k * ‖vec j‖ ^ 2 := by
  rcases hj with hj | hj
  · have hv : Module.End.HasEigenvector (TOpEnd' K hK) (val j) (vec j) := by
      rcases hvec j with h | h
      · exact absurd h hj
      · exact h
    exact inner_pow_of_hasEigenvector hv k
  · rw [hj]
    simp

/-- The `k = 2` pairing passes through the kernel: `⟪(T²) f, f⟫ = kpair K (T f) f`
(the landed master formula `inner_TOp` applied twice). -/
theorem inner_pow_two_pairing (f : L2) :
    inner ℝ ((TOpEnd' K hK ^ 2) f) f = kpair K (TOp K hK f) f := by
  have h : (TOpEnd' K hK ^ 2) f = TOpEnd' K hK (TOpEnd' K hK f) := rfl
  rw [h]
  exact inner_TOp hK (TOp K hK f) f

/-! ### The Riesz-instantiated enumeration with the pairing identity -/

/-- **Multiplicity-exact enumeration of the Riesz spectrum with the power pairing**:
instantiating `exists_multiplicity_enumeration` at the uniform-`ω` Riesz operator
(compactness `isCompactOperator_TOp_riesz`, symmetry `isSymmetric_TOp_rieszKernel`)
and bundling the eigenvector power identity. -/
theorem exists_multiplicity_enumeration_riesz {psi c : ℝ} {omega : ℝ → ℝ} {M : ℝ}
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y) :
    ∃ val : ℕ → ℝ, ∃ vec : ℕ → L2,
      (∀ j, val j = 0 ∨ Module.End.HasEigenvector
        (TOpEnd' (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg))
        (val j) (vec j)) ∧
      (∀ (k : ℕ) (j : ℕ), val j ≠ 0 ∨ vec j = 0 →
        inner ℝ ((TOpEnd' (rieszKernel psi c omega)
            (hsKernel_rieszKernel hpow homega hbdd hg) ^ k) (vec j)) (vec j)
          = val j ^ k * ‖vec j‖ ^ 2) := by
  obtain ⟨val, vec, h1, -⟩ :=
    exists_multiplicity_enumeration (isCompactOperator_TOp_riesz hpow homega hbdd hg hconst)
      (isSymmetric_TOp_rieszKernel hpow homega hbdd hg hconst)
  exact ⟨val, vec, h1, fun k j hj =>
    inner_pow_of_enumeration h1 k j hj⟩

/-! ### The `k = 2` cycle-integral identification -/

/-- Bridge: any `vol2`-integral over the unit square is the indicator integral over
`volume × volume` (`Measure.prod_restrict` + `integral_indicator`). -/
theorem integral_vol2_eq_indicator_square (F : ℝ × ℝ → ℝ) :
    ∫ p : ℝ × ℝ, F p ∂vol2
      = ∫ p : ℝ × ℝ, (I ×ˢ I).indicator F p ∂(volume.prod volume) := by
  have hS : MeasurableSet (I ×ˢ I) :=
    (measurableSet_Icc (a := (-1 : ℝ)) (b := (1 : ℝ))).prod
      (measurableSet_Icc (a := (-1 : ℝ)) (b := (1 : ℝ)))
  show ∫ p : ℝ × ℝ, F p ∂((volume.restrict I).prod (volume.restrict I)) = _
  rw [Measure.prod_restrict I I]
  exact (integral_indicator hS).symm

set_option maxHeartbeats 1000000 in
/-- **The `k = 2` cycle integral in the square-indicator form** (unconditional): the
cyclic integral of the `Fin 2` encoding is the indicator integral over
`volume × volume` on the unit square — the `Fin 2 → ℝ` volume is carried to `ℝ × ℝ`
by `volume_preserving_finTwoArrow`, and the cyclic product collapses pointwise to
`K_R p · K_R p.swap` (`|z 1 - z 0| = |z 0 - z 1|` inside the identical distance
factor). -/
theorem weightedRieszCycleIntegral_two_eq_indicator (psi c : ℝ) (omega : ℝ → ℝ) :
    Hurst.weightedRieszCycleIntegral 2 psi c omega
      = ∫ p : ℝ × ℝ, (I ×ˢ I).indicator
          (fun q : ℝ × ℝ => rieszKernel psi c omega q
            * rieszKernel psi c omega q.swap) p ∂(volume.prod volume) := by
  classical
  have hpt : ∀ p : ℝ × ℝ,
      (∏ i : Fin 2, (Icc (-1 : ℝ) 1).indicator omega (MeasurableEquiv.finTwoArrow.symm p i) * c *
        |MeasurableEquiv.finTwoArrow.symm p i
          - MeasurableEquiv.finTwoArrow.symm p (Hurst.finCyclicSucc i)| ^ (-psi))
        = (I ×ˢ I).indicator
          (fun q : ℝ × ℝ => rieszKernel psi c omega q
            * rieszKernel psi c omega q.swap) p := by
    intro p
    have hs0 : MeasurableEquiv.finTwoArrow.symm p 0 = p.1 := by
      simp [MeasurableEquiv.finTwoArrow_symm_apply]
    have hs1 : MeasurableEquiv.finTwoArrow.symm p 1 = p.2 := by
      simp [MeasurableEquiv.finTwoArrow_symm_apply]
    have eprod : (∏ i : Fin 2, (Icc (-1 : ℝ) 1).indicator omega
            (MeasurableEquiv.finTwoArrow.symm p i) * c *
          |MeasurableEquiv.finTwoArrow.symm p i
            - MeasurableEquiv.finTwoArrow.symm p (Hurst.finCyclicSucc i)| ^ (-psi))
        = (Icc (-1 : ℝ) 1).indicator omega p.1 * c * |p.1 - p.2| ^ (-psi)
          * ((Icc (-1 : ℝ) 1).indicator omega p.2 * c * |p.2 - p.1| ^ (-psi)) := by
      rw [Fin.prod_univ_two, finCyclicSucc_two_zero, finCyclicSucc_two_one, hs0, hs1]
    rw [eprod]
    by_cases hp1 : p.1 ∈ Icc (-1 : ℝ) 1 <;> by_cases hp2 : p.2 ∈ Icc (-1 : ℝ) 1
    · rw [Set.indicator_of_mem (Set.mem_prod.mpr ⟨hp1, hp2⟩)]
      rfl
    · have hnot : p ∉ Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 :=
        fun hmem => hp2 (Set.mem_prod.mp hmem).2
      rw [Set.indicator_of_notMem hnot, Set.indicator_of_notMem hp2]
      ring
    · have hnot : p ∉ Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 :=
        fun hmem => hp1 (Set.mem_prod.mp hmem).1
      rw [Set.indicator_of_notMem hnot, Set.indicator_of_notMem hp1]
      ring
    · have hnot : p ∉ Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 :=
        fun hmem => hp1 (Set.mem_prod.mp hmem).1
      rw [Set.indicator_of_notMem hnot, Set.indicator_of_notMem hp1]
      ring
  unfold Hurst.weightedRieszCycleIntegral
  rw [← (volume_preserving_finTwoArrow ℝ).symm.integral_comp'
    (fun z : Fin 2 → ℝ => ∏ i : Fin 2, (Icc (-1 : ℝ) 1).indicator omega (z i) * c *
      |z i - z (Hurst.finCyclicSucc i)| ^ (-psi))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  exact hpt p

/-- **The `k = 2` cycle-integral identification** (unconditional):
`weightedRieszCycleIntegral 2 ψ c ω = cycle2 K_R K_R`. -/
theorem weightedRieszCycleIntegral_two_eq_cycle2 (psi c : ℝ) (omega : ℝ → ℝ) :
    Hurst.weightedRieszCycleIntegral 2 psi c omega
      = cycle2 (rieszKernel psi c omega) (rieszKernel psi c omega) := by
  have hc : cycle2 (rieszKernel psi c omega) (rieszKernel psi c omega)
      = ∫ p : ℝ × ℝ, (I ×ˢ I).indicator
          (fun q : ℝ × ℝ => rieszKernel psi c omega q
            * rieszKernel psi c omega q.swap) p ∂(volume.prod volume) :=
    integral_vol2_eq_indicator_square
      (fun q : ℝ × ℝ => rieszKernel psi c omega q * rieszKernel psi c omega q.swap)
  rw [weightedRieszCycleIntegral_two_eq_indicator, hc]

/-- **Symmetric-kernel self-cycle is the squared HS norm**: for a symmetric kernel,
`cycle2 K K = ∫∫ K(x,y) K(y,x) = ∫∫ K² = hsNorm K²`. -/
theorem cycle2_self_eq_hsNorm_sq {K : ℝ × ℝ → ℝ}
    (hsym : ∀ p : ℝ × ℝ, K p = K p.swap) :
    cycle2 K K = hsNorm K ^ 2 := by
  have hpt : ∀ p : ℝ × ℝ, K p * K p.swap = K p ^ 2 := fun p => by
    rw [hsym p]
    ring
  have e : cycle2 K K = ∫ p : ℝ × ℝ, K p * K p.swap ∂vol2 := rfl
  rw [e, integral_congr_ae (Filter.Eventually.of_forall fun p => hpt p), hsNorm_def,
    Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)]

/-- The Riesz specialization: `cycle2 K_R K_R = hsNorm K_R²` (kernel symmetry from
`rieszKernel_symm_of_const`). -/
theorem cycle2_rieszKernel_eq_hsNorm_sq {psi c : ℝ} {omega : ℝ → ℝ}
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y) :
    cycle2 (rieszKernel psi c omega) (rieszKernel psi c omega)
      = hsNorm (rieszKernel psi c omega) ^ 2 :=
  cycle2_self_eq_hsNorm_sq (rieszKernel_symm_of_const hconst)

/-- **The `k = 2` cycle integral is the squared HS norm** of the uniform-`ω` Riesz
kernel: `weightedRieszCycleIntegral 2 ψ c ω = hsNorm K_R²`. -/
theorem weightedRieszCycleIntegral_two_eq_hsNorm_sq {psi c : ℝ} {omega : ℝ → ℝ}
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y) :
    Hurst.weightedRieszCycleIntegral 2 psi c omega
      = hsNorm (rieszKernel psi c omega) ^ 2 := by
  rw [weightedRieszCycleIntegral_two_eq_cycle2, cycle2_rieszKernel_eq_hsNorm_sq hconst]

/-! ### General `k`: the kernel-product form and the P2 packaging -/

/-- **Kernel-product form of the general `k`-cycle integral** (unconditional, `rfl`):
the `weightedRieszCycleIntegral` integrand is exactly the cyclic kernel product
`∏_i K_R(z_i, z_{succ i})` — the form the iterated-Fubini identification with the
`⟪(T^k)·,·⟫` trace pairings consumes. -/
theorem weightedRieszCycleIntegralEqKernelProduct (k : ℕ) (psi c : ℝ)
    (omega : ℝ → ℝ) :
    Hurst.weightedRieszCycleIntegral k psi c omega
      = ∫ z : Fin k → ℝ, ∏ i : Fin k,
          rieszKernel psi c omega (z i, z (Hurst.finCyclicSucc i)) ∂volume := rfl

/-- **P2 consumption packaging**: a sequence with the nonnegativity clause (the PSD
deferral, `Hurst.P2SpectrumConstruction`) that realizes the cycle integrals as its
power sums in the `HasSum` sense — with the square-summability from the `k = 2`
`HasSum` — satisfies the complete P2 contract. -/
theorem isRieszSpectrumSequence_of_hasSum {psi c : ℝ} {omega : ℝ → ℝ}
    {lambda : ℕ → ℝ} (hnn : ∀ j, 0 ≤ lambda j)
    (h2 : HasSum (fun j => lambda j ^ 2)
      (Hurst.weightedRieszCycleIntegral 2 psi c omega))
    (hgen : ∀ k : ℕ, 2 ≤ k → HasSum (fun j => lambda j ^ k)
      (Hurst.weightedRieszCycleIntegral k psi c omega)) :
    Hurst.IsRieszSpectrumSequence psi c omega lambda :=
  ⟨hnn, h2.summable, hgen⟩

end HS

end
