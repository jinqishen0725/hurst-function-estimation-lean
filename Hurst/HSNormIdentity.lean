import Hurst.HSOperatorLayer2
import Hurst.HSOperatorLayer3
import Hurst.SpectralEnumeration

/-!
# The kernel↔operator Hilbert–Schmidt norm identity (Bessel route, round 3.5)

On the landed L² encoding (`Hurst.HSOperatorFoundation`: `vol = volume.restrict (Icc (-1:ℝ) 1)`,
kernels `K : ℝ × ℝ → ℝ` with `HSKernel K = MemLp K 2 vol2`, `hsNorm K = (∫∫ K² ∂vol2)^(1/2)`,
`TOp K hK : L2 →L[ℝ] L2`), this file lands the kernel↔operator HS-norm identity via
**Bessel's inequality applied to sections of the kernel**, entirely Parseval-free.

## Main results

* `sum_norm_TOp_sq_le` — **the analytic core**: for ANY orthonormal family `v : ι → L2` and
  any finite `s : Finset ι`, `∑ i ∈ s, ‖TOp K hK (v i)‖² ≤ hsNorm K²`.
  No compactness, self-adjointness or eigenvector input is used.
  Proof: for each `i ∈ s` with `TOp K (v i) ≠ 0`, the section function
  `p ↦ (TOp K (v i)/‖TOp K (v i)‖)(x) · (v i)(y)` is a unit vector of `L²(vol2)`; these
  sections form an orthonormal family (their inner products factor through the
  orthonormality of `v` — `inner_prodKernel`), and Bessel's inequality in `L²(vol2)`
  (`Orthonormal.sum_inner_products_le`) applied at the kernel point `K` reads
  `∑ ‖⟪K, (T v i / ‖T v i‖) ⊗ v i⟫‖² ≤ ‖K‖²`, i.e. `∑ ‖T (v i)‖² ≤ ∫∫ K² = hsNorm K²`,
  since `⟪K, (T v i / ‖T v i‖) ⊗ v i⟫ = kpair K (v i) (T v i / ‖T v i‖) = ‖T (v i)‖`.
  Zero images `T (v i) = 0` contribute nothing and are dropped.
* `tsum_norm_TOp_sq_le` — the same bound for the full (possibly uncountable) family:
  `∑' i, ‖TOp K hK (v i)‖² ≤ hsNorm K²` (`Real.tsum_le_of_sum_le`).
* `summable_norm_TOp_sq` — for `v : ℕ → L2` orthonormal: `Summable (fun j => ‖TOp K (v j)‖²)`
  (`Real.summable_of_sum_le`: the partial sums are uniformly bounded by `hsNorm K²` —
  the "monotone partial sums" route of the round-3.5 spec).
* `summable_eigenvalues_sq` — **the Summable-λ² corollary**: any orthonormal eigen-sequence
  `v j` of the kernel operator with eigenvalues `κ j` (`TOp K hK (v j) = κ j • v j`) satisfies
  `Summable (fun j => κ j ^ 2)`.  Pure Bessel: no compactness or symmetry hypothesis needed.
* `hsNorm_sq_ge_sum_norm_sq_of_orthonormal`, `hsNorm_sq_ge_tsum_norm_sq_of_orthonormal` —
  the **upper half of the kernel↔operator HS-norm identity** `Σ_i ‖TOp K (e i)‖² ≤ hsNorm K²`.

## Status of the full identity and of the multiplicity enumeration

* **Equality** `Σ_i ‖TOp K (e i)‖² = hsNorm K²` over a complete ONB needs the reverse
  inequality, i.e. Parseval for the kernel space at the point `K` against the family
  `(T e_i / ‖T e_i‖) ⊗ e_i` — the documented-blocked general-k Parseval gap
  (`HSOperatorLayer3` tail).  This file deliberately lands only the `≤` direction.
* **Multiplicity-exact enumeration** (`HS.exists_multiplicity_enumeration`,
  `Hurst.FrozenSpectralCount`): its entries are unit eigenvectors that are orthonormal
  *across distinct eigenvalues* but not within one eigenspace, so `summable_eigenvalues_sq`
  does not apply to it verbatim.  The missing step is per-eigenspace Gram–Schmidt: an
  orthonormal basis of each nonzero eigenspace, spliced over the countable set of nonzero
  eigenvalues into ONE orthonormal family (indexed by `Σ a : nonzero eigenvalues,
  Fin (finrank (eigenspace a))`), after which the fiber-count identity
  `Nat.card {j // val j = μ} = finrank (eigenspace μ)` gives `∑_{j<N} (val j)² ≤ hsNorm K²`
  for every `N` and hence `Summable (fun j => val j ^ 2)`.  Pure finite-dimensional linear
  algebra bookkeeping; documented as the exact remaining step, not attempted this round.
-/

open MeasureTheory Measure Real Set
open scoped Real

noncomputable section

namespace HS

variable {K : ℝ × ℝ → ℝ} {hK : HSKernel K}

/-! ### Basic bridges -/

/-- `hsNorm K² = ∫∫ K²` (the square of the kernel HS norm is the plain L² energy). -/
theorem hsNorm_sq (K : ℝ × ℝ → ℝ) : hsNorm K ^ 2 = ∫ p : ℝ × ℝ, K p ^ 2 ∂vol2 := by
  rw [hsNorm_def, Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)]

/-- The inner product of two `Lp ℝ 2 μ` elements is the integral of the representative
product (real case, arbitrary carrier measure). -/
theorem inner_Lp_eq_coe {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
    (f g : MeasureTheory.Lp ℝ 2 μ) :
    inner ℝ f g = ∫ x, (⇑f) x * (⇑g) x ∂μ := by
  rw [L2.inner_def]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
    simp only [RCLike.inner_apply, RCLike.conj_to_real]
    ring)

/-- Inner product of two `MemLp.toLp` elements = integral of the pointwise product. -/
theorem inner_toLp_toLp {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
    {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (MemLp.toLp f hf) (MemLp.toLp g hg) = ∫ x, f x * g x ∂μ := by
  rw [inner_Lp_eq_coe]
  exact integral_congr_ae ((MemLp.coeFn_toLp hf).mul (MemLp.coeFn_toLp hg))

/-! ### The kernel section family -/

/-- The "section" kernel `p ↦ u(p.1) · v(p.2)` built from two `L²(vol)` elements,
as an element of the kernel space `L²(vol2)`. -/
def prodKernel (u v : L2) : MeasureTheory.Lp ℝ 2 vol2 :=
  MemLp.toLp (fun p : ℝ × ℝ => (⇑u) p.1 * (⇑v) p.2)
    (memLp2_prod_fst_snd (Lp_coe_memLp u) (Lp_coe_memLp v))

/-- The inner product of section kernels factors through the inner products of the factors:
`⟪u₁ ⊗ v₁, u₂ ⊗ v₂⟫_{L²(vol2)} = ⟪u₁, u₂⟫ · ⟪v₁, v₂⟫` — the master lemma that transfers
orthonormality from `L²(vol)` to the kernel space. -/
theorem inner_prodKernel (u₁ u₂ v₁ v₂ : L2) :
    inner ℝ (prodKernel u₁ v₁) (prodKernel u₂ v₂)
      = inner ℝ u₁ u₂ * inner ℝ v₁ v₂ := by
  have step : inner ℝ (prodKernel u₁ v₁) (prodKernel u₂ v₂)
      = ∫ p : ℝ × ℝ, ((⇑u₁) p.1 * (⇑v₁) p.2) * ((⇑u₂) p.1 * (⇑v₂) p.2) ∂vol2 :=
    inner_toLp_toLp (memLp2_prod_fst_snd (Lp_coe_memLp u₁) (Lp_coe_memLp v₁))
      (memLp2_prod_fst_snd (Lp_coe_memLp u₂) (Lp_coe_memLp v₂))
  rw [step, L2_inner_eq, L2_inner_eq,
    integral_congr_ae (Filter.Eventually.of_forall (fun p : ℝ × ℝ =>
      show ((⇑u₁) p.1 * (⇑v₁) p.2) * ((⇑u₂) p.1 * (⇑v₂) p.2)
        = (⇑u₁) p.1 * (⇑u₂) p.1 * ((⇑v₁) p.2 * (⇑v₂) p.2) by ring)),
    integral_prod_mul (μ := vol) (ν := vol)
      (f := fun x : ℝ => (⇑u₁) x * (⇑u₂) x) (g := fun y : ℝ => (⇑v₁) y * (⇑v₂) y)]

/-- The kernel pairing reads off the section family:
`⟪K, u ⊗ v⟫_{L²(vol2)} = kpair K v u = ⟪TOp K v, u⟫`. -/
theorem inner_prodKernel_kernel (u v : L2) :
    inner ℝ (prodKernel u v) (MemLp.toLp K hK) = kpair K v u := by
  have heq : prodKernel u v = MemLp.toLp (fun p : ℝ × ℝ => (⇑u) p.1 * (⇑v) p.2)
      (memLp2_prod_fst_snd (Lp_coe_memLp u) (Lp_coe_memLp v)) := rfl
  rw [heq, inner_toLp_toLp _ hK]
  show ∫ p : ℝ × ℝ, ((⇑u) p.1 * (⇑v) p.2) * K p ∂vol2
    = ∫ p : ℝ × ℝ, K p * (⇑v) p.2 * (⇑u) p.1 ∂vol2
  exact integral_congr_ae (Filter.Eventually.of_forall fun p => by ring)

/-! ### The HS-norm identity: the Bessel upper bound -/

/-- **The HS-norm identity, upper half (finite Bessel form)**: for any orthonormal family
`v` in `L²` and any finite subset, the operator-image norm squares sum to at most the
kernel HS norm squared.  No compactness or symmetry input. -/
theorem sum_norm_TOp_sq_le {ι : Type*} {v : ι → L2} (hv : Orthonormal ℝ v) (s : Finset ι) :
    ∑ i ∈ s, ‖TOp K hK (v i)‖ ^ 2 ≤ hsNorm K ^ 2 := by
  classical
  set T : L2 →L[ℝ] L2 := TOp K hK with hT
  set s' : Finset ι := s.filter (fun i => T (v i) ≠ 0) with hs'
  -- the family of normalized images (unit vectors, or zero off `s'`)
  have hunit : ∀ i : ↥s', ‖(‖T (v (i : ι))‖)⁻¹ • T (v (i : ι))‖ = 1 := by
    intro i
    have hne : T (v (i : ι)) ≠ 0 := by
      have h2 := i.2
      simp only [hs', Finset.mem_filter] at h2
      exact h2.2
    have hnpos : ‖T (v (i : ι))‖ ≠ 0 := norm_ne_zero_iff.mpr hne
    have hpos : (0 : ℝ) < ‖T (v (i : ι))‖ := norm_pos_iff.mpr hne
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos),
      inv_mul_cancel₀ hnpos]
  -- the section family is orthonormal in the kernel space
  have hWnorm : ∀ i : ↥s',
      ‖prodKernel ((‖T (v (i : ι))‖)⁻¹ • T (v (i : ι))) (v (i : ι))‖ = 1 := by
    intro i
    have h1 : inner ℝ (prodKernel ((‖T (v (i : ι))‖)⁻¹ • T (v (i : ι))) (v (i : ι)))
        (prodKernel ((‖T (v (i : ι))‖)⁻¹ • T (v (i : ι))) (v (i : ι))) = 1 := by
      rw [inner_prodKernel, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
        hunit i, hv.1 (i : ι)]
      norm_num
    have h2 : ‖prodKernel ((‖T (v (i : ι))‖)⁻¹ • T (v (i : ι))) (v (i : ι))‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq]
      exact h1
    rw [← Real.sqrt_sq (norm_nonneg _), h2, Real.sqrt_one]
  have hWpair : ∀ i j : ↥s', i ≠ j →
      inner ℝ (prodKernel ((‖T (v (i : ι))‖)⁻¹ • T (v (i : ι))) (v (i : ι)))
        (prodKernel ((‖T (v (j : ι))‖)⁻¹ • T (v (j : ι))) (v (j : ι))) = 0 := by
    intro i j hij
    rw [inner_prodKernel,
      hv.2 (show (i : ι) ≠ (j : ι) from fun h => hij (Subtype.ext h)), mul_zero]
  have hW : Orthonormal ℝ (fun i : ↥s' =>
      prodKernel ((‖T (v (i : ι))‖)⁻¹ • T (v (i : ι))) (v (i : ι))) :=
    ⟨hWnorm, fun i j hij => hWpair i j hij⟩
  -- Bessel in the kernel space, at the kernel point
  have hbessel := hW.sum_inner_products_le (s := s'.attach) (MemLp.toLp K hK)
  -- each Bessel term is exactly ‖T (v i)‖
  have hterm : ∀ i : ↥s',
      ‖inner ℝ (prodKernel ((‖T (v (i : ι))‖)⁻¹ • T (v (i : ι))) (v (i : ι)))
        (MemLp.toLp K hK)‖ = ‖T (v (i : ι))‖ := by
    intro i
    have hne : T (v (i : ι)) ≠ 0 := by
      have h2 := i.2
      simp only [hs', Finset.mem_filter] at h2
      exact h2.2
    have hnpos : ‖T (v (i : ι))‖ ≠ 0 := norm_ne_zero_iff.mpr hne
    have hpos : (0 : ℝ) < ‖T (v (i : ι))‖ := norm_pos_iff.mpr hne
    have hval : inner ℝ (prodKernel ((‖T (v (i : ι))‖)⁻¹ • T (v (i : ι))) (v (i : ι)))
        (MemLp.toLp K hK) = ‖T (v (i : ι))‖ := by
      rw [inner_prodKernel_kernel, ← inner_TOp hK, real_inner_smul_right,
        real_inner_self_eq_norm_sq, sq, ← mul_assoc, inv_mul_cancel₀ hnpos, one_mul]
    rw [hval, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  -- zero terms contribute nothing
  have hzero : ∀ i ∈ s, i ∉ s' → ‖T (v i)‖ ^ 2 = 0 := by
    intro i hi hne
    have h0 : T (v i) = 0 := by
      by_contra hc
      exact hne (Finset.mem_filter.mpr ⟨hi, hc⟩)
    rw [show ‖T (v i)‖ = 0 from norm_eq_zero.mpr h0]
    simp
  have hsum : ∑ i ∈ s', ‖T (v i)‖ ^ 2 = ∑ i ∈ s, ‖T (v i)‖ ^ 2 :=
    Finset.sum_subset (Finset.filter_subset _ s) hzero
  calc ∑ i ∈ s, ‖T (v i)‖ ^ 2
      = ∑ i ∈ s', ‖T (v i)‖ ^ 2 := hsum.symm
    _ = ∑ i ∈ s'.attach, ‖T (v (i : ι))‖ ^ 2 := (Finset.sum_attach s' _).symm
    _ = ∑ i ∈ s'.attach, ‖inner ℝ (prodKernel ((‖T (v (i : ι))‖)⁻¹ • T (v (i : ι)))
          (v (i : ι))) (MemLp.toLp K hK)‖ ^ 2 :=
        Finset.sum_congr rfl fun i _ => by rw [hterm i]
    _ ≤ ‖MemLp.toLp K hK‖ ^ 2 := hbessel
    _ = inner ℝ (MemLp.toLp K hK) (MemLp.toLp K hK) := (real_inner_self_eq_norm_sq _).symm
    _ = ∫ p : ℝ × ℝ, K p ^ 2 ∂vol2 := by
        rw [inner_toLp_toLp hK hK]
        exact integral_congr_ae (Filter.Eventually.of_forall fun p => by ring)
    _ = hsNorm K ^ 2 := (hsNorm_sq K).symm

/-- The HS-norm identity, upper half (tsum form): `∑' i, ‖TOp K (v i)‖² ≤ hsNorm K²` over
any orthonormal family (any index type). -/
theorem hsNorm_sq_ge_tsum_norm_sq_of_orthonormal {ι : Type*} {v : ι → L2}
    (hv : Orthonormal ℝ v) :
    ∑' i, ‖TOp K hK (v i)‖ ^ 2 ≤ hsNorm K ^ 2 :=
  Real.tsum_le_of_sum_le (fun i => sq_nonneg (‖TOp K hK (v i)‖))
    (fun u => sum_norm_TOp_sq_le hv u)

/-- Alias of `hsNorm_sq_ge_tsum_norm_sq_of_orthonormal` in the finite form
(`∑ i ∈ s, ‖TOp K (v i)‖² ≤ hsNorm K²` is `sum_norm_TOp_sq_le`). -/
theorem hsNorm_sq_ge_sum_norm_sq_of_orthonormal {ι : Type*} {v : ι → L2}
    (hv : Orthonormal ℝ v) (s : Finset ι) :
    ∑ i ∈ s, ‖TOp K hK (v i)‖ ^ 2 ≤ hsNorm K ^ 2 :=
  sum_norm_TOp_sq_le hv s

/-- **Summability of the image norms**: for an orthonormal sequence `v`, the series
`∑ ‖TOp K (v j)‖²` converges (its partial sums are uniformly bounded by `hsNorm K²`). -/
theorem summable_norm_TOp_sq {v : ℕ → L2} (hv : Orthonormal ℝ v) :
    Summable (fun j => ‖TOp K hK (v j)‖ ^ 2) :=
  summable_of_sum_le (fun j => sq_nonneg (‖TOp K hK (v j)‖))
    (fun u => sum_norm_TOp_sq_le hv u)

/-- **The Summable-λ² corollary**: for an orthonormal eigen-sequence `v j` of the kernel
operator with eigenvalues `κ j` (`TOp K hK (v j) = κ j • v j`), the squared-eigenvalue
series `∑ κ j²` converges.  Pure Bessel (finite-subset bound + bounded partial sums);
no compactness or self-adjointness hypothesis. -/
theorem summable_eigenvalues_sq {κ : ℕ → ℝ} {v : ℕ → L2} (hv : Orthonormal ℝ v)
    (hvk : ∀ j, TOp K hK (v j) = κ j • v j) :
    Summable (fun j => κ j ^ 2) := by
  have heq : (fun j => κ j ^ 2) = (fun j => ‖TOp K hK (v j)‖ ^ 2) := by
    funext j
    rw [hvk j, norm_smul, Real.norm_eq_abs, hv.1 j, mul_one, sq_abs]
  rw [heq]
  exact summable_norm_TOp_sq hv

end HS

end
