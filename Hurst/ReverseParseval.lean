import Hurst.HSOperatorLayer4
import Hurst.HSNormIdentity

/-!
# Reverse Parseval: the ≥-half of the kernel↔operator HS-norm identity

On the landed `HS` stack (`Hurst.HSOperatorFoundation`, `...Layer2/3/4`,
`Hurst.HSNormIdentity`) the **upper half** of the HS-norm identity is Bessel:
`∑' i, ‖TOp K (v i)‖² ≤ hsNorm K²` for ANY orthonormal family `v` of `L²`.
This file lands the **reverse (Parseval) half**, closing the `hTwo` Parseval boundary
documented in `HSNormIdentity`.

## Route

1. **Abstract reverse Parseval** (`norm_sq_eq_tsum_inner_sq_of_complete`): in a real
   Hilbert space, an orthonormal family whose span has trivial orthogonal complement is
   a `HilbertBasis` (mathlib `HilbertBasis.mkOfOrthogonalEqBot`), and mathlib's
   `HilbertBasis.tsum_inner_mul_inner` is Parseval: `‖f‖² = ∑' i, ⟪f, v i⟫²`.
2. **Kernel-space Parseval** (`hsNorm_sq_eq_tsum_inner_sq_of_complete`): the same in the
   kernel space `L²(vol2)` at the kernel point `K`, giving `hsNorm K² = ∑' ⟪K, W i⟫²`
   for any complete orthonormal family `W` of `L²(vol2)`.  Via
   `hsNorm_sq_eq_tsum_inner_sq_of_hilbertBasis` this holds **unconditionally** for a
   Hilbert basis of the kernel space (Zorn-supplied by mathlib).
3. **The reverse HS-norm identity** (`hsNorm_sq_eq_tsum_norm_sq_of_complete_sections`):
   for a complete orthonormal family `v` of `L²` whose **section family**
   `p ↦ prodKernel (v p.2) (v p.1)` is complete in `L²(vol2)` (the tensor-ONB clause),
   `hsNorm K² = ∑' j, ‖TOp K (v j)‖²`.  Proof: kernel-space Parseval at `K` against the
   section family, each pairing transferred by `inner_prodKernel_kernel` to
   `⟪TOp K (v p.2), v p.1⟫`, the double sum swapped by `Summable.tsum_prod'`, and each
   fiber summed by Parseval of `TOp K (v j)` against `v` (step 1).  For eigenvectors
   (`hsNorm_sq_eq_tsum_eigenvalue_sq_of_complete_sections`) the right side is `∑' κ²`.

## Honest scope

* The completeness clause `hsec` for the section family is carried as a hypothesis.
  Its general proof is the classical measurable-sections argument (an `L²(vol2)`
  function orthogonal to all `u ⊗ v` with `u, v` from complete families vanishes),
  which needs section-measurability/Fubini API for `Lp` elements that was not
  available in budget; it is the exact remaining gap between this file and the
  unconditional `hsNorm K² = ∑' ‖TOp K e_j‖²` over a complete eigenbasis.
* What IS unconditional here: Parseval for `K` against any Hilbert basis of `L²(vol2)`
  (`hsNorm_sq_eq_tsum_inner_sq_of_hilbertBasis`), the reverse Parseval ≥-half at the
  abstract level, Parseval of operator images against complete families of `L²`
  (`norm_TOp_sq_eq_tsum_kpair_of_complete`), and the bridge from the landed compact
  spectral decomposition `(⨆ μ, eigenspace μ)ᗮ = ⊥` to completeness of a spliced
  eigenfamily (`span_orthogonal_eq_bot_of_eigenspace_span`) — the assembly
  prerequisite for the multiplicity enumeration.
-/

open MeasureTheory Measure Real Set Submodule
open scoped Real

noncomputable section

namespace HS

variable {K : ℝ × ℝ → ℝ} {hK : HSKernel K}

/-! ### A. Completeness bridges and abstract reverse Parseval -/

/-- The whole space has trivial orthogonal complement (real case). -/
theorem top_orthogonal_eq_bot {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] :
    (⊤ : Submodule ℝ H)ᗮ = ⊥ := by
  refine Submodule.ext fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · rw [Submodule.mem_orthogonal'] at hx
    have hxx := hx x (Submodule.mem_top (x := x))
    have hn : ‖x‖ ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq]
      exact hxx
    rw [Submodule.mem_bot ℝ]
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
  · rw [Submodule.mem_orthogonal']
    intro u _
    have hx0 : x = 0 := (Submodule.mem_bot ℝ).mp hx
    rw [hx0]
    simp

/-- Dense span forces trivial orthogonal complement: if the topological closure of the
span of `v` is everything, then `(span (range v))ᗮ = ⊥`. -/
theorem orthogonalComplement_eq_bot_of_dense_span {ι : Type*} {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] {v : ι → H}
    (hdense : (span ℝ (Set.range v)).topologicalClosure = ⊤) :
    (span ℝ (Set.range v))ᗮ = ⊥ := by
  rw [← Submodule.orthogonal_closure (span ℝ (Set.range v)), hdense]
  exact top_orthogonal_eq_bot

/-- A subspace with trivial orthogonal complement stays trivial-complement after
enlargement: `Vᗮ = ⊥` and `V ≤ W` give `Wᗮ = ⊥`. -/
theorem orthogonalComplement_eq_bot_of_le {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {V W : Submodule ℝ H} (hV : Vᗮ = ⊥) (hle : V ≤ W) : Wᗮ = ⊥ := by
  refine Submodule.ext fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · rw [Submodule.mem_orthogonal'] at hx
    have hxV : x ∈ Vᗮ := by
      rw [Submodule.mem_orthogonal']
      intro u hu
      exact hx u (hle hu)
    rw [hV, Submodule.mem_bot ℝ] at hxV
    exact hxV
  · rw [Submodule.mem_bot ℝ] at hx
    rw [Submodule.mem_orthogonal']
    intro u _
    rw [hx]
    simp

/-- **Abstract reverse Parseval (the ≥-half)**: for a complete orthonormal family `v`
of a real Hilbert space (trivial orthogonal complement of the span), Parseval holds:
`‖f‖² = ∑' i, ⟪f, v i⟫²`.  This is the engine the Bessel-bound file lacked. -/
theorem norm_sq_eq_tsum_inner_sq_of_complete {ι : Type*} {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] {v : ι → H}
    (hv : Orthonormal ℝ v) (hcomp : (span ℝ (Set.range v))ᗮ = ⊥) (f : H) :
    ‖f‖ ^ 2 = ∑' i, inner ℝ f (v i) ^ 2 := by
  have hb := (HilbertBasis.mkOfOrthogonalEqBot hv hcomp).tsum_inner_mul_inner f f
  simp only [HilbertBasis.coe_mkOfOrthogonalEqBot] at hb
  have hterm : ∀ i : ι, inner ℝ f (v i) * inner ℝ (v i) f = inner ℝ f (v i) ^ 2 := by
    intro i
    rw [real_inner_comm (v i) f]
    ring
  rw [show (fun i : ι => inner ℝ f (v i) ^ 2)
        = (fun i : ι => inner ℝ f (v i) * inner ℝ (v i) f) from
      funext (fun i => (hterm i).symm),
    hb, real_inner_self_eq_norm_sq]

/-- The ≥-half in inequality form: `‖f‖² ≤ ∑' i, ⟪f, v i⟫²` for complete families. -/
theorem norm_sq_le_tsum_inner_sq_of_complete {ι : Type*} {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] {v : ι → H}
    (hv : Orthonormal ℝ v) (hcomp : (span ℝ (Set.range v))ᗮ = ⊥) (f : H) :
    ‖f‖ ^ 2 ≤ ∑' i, inner ℝ f (v i) ^ 2 :=
  (norm_sq_eq_tsum_inner_sq_of_complete hv hcomp f).le

/-! ### B. Parseval for the kernel space `L²(vol2)` at the kernel point -/

/-- **Kernel-space reverse Parseval**: for any complete orthonormal family `W` of the
kernel space `L²(vol2)`, the kernel L²-energy is the squared-coordinate sum:
`∑' i, ⟪K, W i⟫² = hsNorm K²`.  This is the `≥`-half of the Bessel bound of
`Hurst.HSNormIdentity`, with completeness supplying Parseval. -/
theorem hsNorm_sq_eq_tsum_inner_sq_of_complete {ι : Type*}
    {W : ι → MeasureTheory.Lp ℝ 2 vol2}
    (hW : Orthonormal ℝ W) (hcomp : (span ℝ (Set.range W))ᗮ = ⊥) :
    ∑' i, inner ℝ (MemLp.toLp K hK) (W i) ^ 2 = hsNorm K ^ 2 := by
  have hnorm : ‖MemLp.toLp K hK‖ ^ 2 = hsNorm K ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_toLp_toLp hK hK, hsNorm_sq K]
    exact integral_congr_ae (Filter.Eventually.of_forall fun p => by ring)
  have hterm : ∀ i : ι, inner ℝ (MemLp.toLp K hK) (W i)
      * inner ℝ (W i) (MemLp.toLp K hK) = inner ℝ (MemLp.toLp K hK) (W i) ^ 2 := by
    intro i
    rw [real_inner_comm (W i) (MemLp.toLp K hK)]
    ring
  have hb := (HilbertBasis.mkOfOrthogonalEqBot hW hcomp).tsum_inner_mul_inner
    (MemLp.toLp K hK) (MemLp.toLp K hK)
  simp only [HilbertBasis.coe_mkOfOrthogonalEqBot] at hb
  rw [show (fun i : ι => inner ℝ (MemLp.toLp K hK) (W i) ^ 2)
        = (fun i : ι => inner ℝ (MemLp.toLp K hK) (W i)
            * inner ℝ (W i) (MemLp.toLp K hK)) from
      funext (fun i => (hterm i).symm),
    hb, real_inner_self_eq_norm_sq]
  exact hnorm

/-- The ≥-half in inequality form: `hsNorm K² ≤ ∑' i, ⟪K, W i⟫²`. -/
theorem hsNorm_sq_le_tsum_inner_sq_of_complete {ι : Type*}
    {W : ι → MeasureTheory.Lp ℝ 2 vol2}
    (hW : Orthonormal ℝ W) (hcomp : (span ℝ (Set.range W))ᗮ = ⊥) :
    hsNorm K ^ 2 ≤ ∑' i, inner ℝ (MemLp.toLp K hK) (W i) ^ 2 :=
  (hsNorm_sq_eq_tsum_inner_sq_of_complete hW hcomp).ge

/-- **Unconditional kernel-space Parseval**: against ANY Hilbert basis of the kernel
space `L²(vol2)` (supplied by Zorn), `∑' ⟪K, b i⟫² = hsNorm K²`.  No compactness or
symmetry hypotheses. -/
theorem hsNorm_sq_eq_tsum_inner_sq_of_hilbertBasis {ι : Type}
    (b : HilbertBasis ι ℝ (MeasureTheory.Lp ℝ 2 vol2)) :
    ∑' i, inner ℝ (MemLp.toLp K hK) (b i) ^ 2 = hsNorm K ^ 2 :=
  hsNorm_sq_eq_tsum_inner_sq_of_complete b.orthonormal
    (orthogonalComplement_eq_bot_of_dense_span (HilbertBasis.dense_span b))

/-! ### C. The section (tensor) family in the kernel space -/

/-- **Orthonormality of the section family**: `p ↦ v p.2 ⊗ v p.1` is orthonormal in
`L²(vol2)` whenever `v` is orthonormal in `L²` (transfer through `inner_prodKernel`). -/
theorem orthonormal_prodKernel {ι : Type*} {v : ι → L2} (hv : Orthonormal ℝ v) :
    Orthonormal ℝ (fun p : ι × ι => prodKernel (v p.2) (v p.1)) := by
  refine ⟨fun p => ?_, fun p q hpq => ?_⟩
  · show ‖prodKernel (v p.2) (v p.1)‖ = 1
    have h1 : inner ℝ (prodKernel (v p.2) (v p.1)) (prodKernel (v p.2) (v p.1)) = 1 := by
      rw [inner_prodKernel, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
        hv.1, hv.1]
      norm_num
    have h3 : ‖prodKernel (v p.2) (v p.1)‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq]
      exact h1
    have h5 : Real.sqrt (‖prodKernel (v p.2) (v p.1)‖ ^ 2) = 1 := by rw [h3, Real.sqrt_one]
    rwa [Real.sqrt_sq (norm_nonneg _)] at h5
  · show inner ℝ (prodKernel (v p.2) (v p.1)) (prodKernel (v q.2) (v q.1)) = 0
    by_cases h2 : p.2 = q.2
    · have h1 : p.1 ≠ q.1 := by
        intro h
        exact hpq (by ext <;> assumption)
      rw [inner_prodKernel, hv.2 h1, mul_zero]
    · rw [inner_prodKernel, hv.2 h2, zero_mul]

/-- **The kernel pairing transferred to operator pairings**: the coordinate of `K`
along the section `v p.2 ⊗ v p.1` is the operator matrix entry
`⟪TOp K (v p.1), v p.2⟫` (this orientation makes the outer tsum index the operator's
input vector). -/
theorem inner_prodKernel_pairing {ι : Type*} {v : ι → L2} (p : ι × ι) :
    inner ℝ (MemLp.toLp K hK) (prodKernel (v p.2) (v p.1))
      = inner ℝ (TOp K hK (v p.1)) (v p.2) := by
  calc inner ℝ (MemLp.toLp K hK) (prodKernel (v p.2) (v p.1))
      = inner ℝ (prodKernel (v p.2) (v p.1)) (MemLp.toLp K hK) :=
        real_inner_comm (prodKernel (v p.2) (v p.1)) (MemLp.toLp K hK)
    _ = kpair K (v p.1) (v p.2) := inner_prodKernel_kernel _ _
    _ = inner ℝ (TOp K hK (v p.1)) (v p.2) := (inner_TOp hK _ _).symm

/-! ### D. The reverse HS-norm identity -/

/-- **The reverse HS-norm identity (general section-family form)**: if `v` is a complete
orthonormal family of `L²` and `W` is a complete orthonormal family of the kernel space
whose coordinates along `K` are the operator matrix entries `⟪TOp K (v p.2), v p.1⟫`
(take `W p := prodKernel (v p.2) (v p.1)`, complete by `orthonormal_prodKernel` + `hsec`),
then Parseval gives the **equality** `hsNorm K² = ∑' j, ‖TOp K (v j)‖²` — the ≥-half
closing the Bessel upper bound of `Hurst.HSNormIdentity`. -/
theorem hsNorm_sq_eq_tsum_norm_sq_of_complete {ι : Type*} {v : ι → L2}
    {W : ι × ι → MeasureTheory.Lp ℝ 2 vol2}
    (hv : Orthonormal ℝ v) (hcomp : (span ℝ (Set.range v))ᗮ = ⊥)
    (hWorth : Orthonormal ℝ W) (hsec : (span ℝ (Set.range W))ᗮ = ⊥)
    (hterm : ∀ p : ι × ι, inner ℝ (MemLp.toLp K hK) (W p)
      = inner ℝ (TOp K hK (v p.1)) (v p.2)) :
    hsNorm K ^ 2 = ∑' j, ‖TOp K hK (v j)‖ ^ 2 := by
  -- the term rewrite and the summability of the paired family
  have hfe2 : (fun p : ι × ι => inner ℝ (TOp K hK (v p.1)) (v p.2) ^ 2)
      = (fun p : ι × ι => inner ℝ (MemLp.toLp K hK) (W p) ^ 2) :=
    funext (fun p => by rw [(hterm p).symm])
  have hf : (fun p : ι × ι => inner ℝ (MemLp.toLp K hK) (W p) ^ 2)
      = (fun p : ι × ι => inner ℝ (TOp K hK (v p.1)) (v p.2) ^ 2) :=
    funext (fun p => by rw [hterm p])
  have hsmC : Summable (fun p : ι × ι => inner ℝ (TOp K hK (v p.1)) (v p.2) ^ 2) := by
    have hsm0 : Summable (fun p : ι × ι => ‖inner ℝ (W p) (MemLp.toLp K hK)‖ ^ 2) :=
      hWorth.inner_products_summable _
    have hfe : (fun p : ι × ι => inner ℝ (MemLp.toLp K hK) (W p) ^ 2)
        = (fun p : ι × ι => ‖inner ℝ (W p) (MemLp.toLp K hK)‖ ^ 2) := by
      funext p
      rw [real_inner_comm (W p) (MemLp.toLp K hK), Real.norm_eq_abs, sq_abs]
    rw [hfe2, hfe]
    exact hsm0
  -- fiberwise summability (Bessel) and fiber Parseval (reverse, from section A)
  have hsmfib : ∀ j : ι,
      Summable (fun i : ι => inner ℝ (TOp K hK (v (j, i).1)) (v (j, i).2) ^ 2) := by
    intro j
    have h0 := hv.inner_products_summable (TOp K hK (v j))
    have hfe : (fun i : ι => inner ℝ (TOp K hK (v (j, i).1)) (v (j, i).2) ^ 2)
        = (fun i : ι => ‖inner ℝ (v i) (TOp K hK (v j))‖ ^ 2) := by
      funext i
      have he : inner ℝ (TOp K hK (v (j, i).1)) (v (j, i).2)
          = inner ℝ (v i) (TOp K hK (v j)) := by
        show inner ℝ (TOp K hK (v j)) (v i) = _
        exact real_inner_comm (v i) (TOp K hK (v j))
      rw [he, Real.norm_eq_abs, sq_abs]
    rw [hfe]
    exact h0
  have hJ : ∀ j : ι, (∑' i : ι, inner ℝ (TOp K hK (v j)) (v i) ^ 2)
      = ‖TOp K hK (v j)‖ ^ 2 :=
    fun j => (norm_sq_eq_tsum_inner_sq_of_complete hv hcomp (TOp K hK (v j))).symm
  calc hsNorm K ^ 2
      = ∑' p : ι × ι, inner ℝ (MemLp.toLp K hK) (W p) ^ 2 :=
        (hsNorm_sq_eq_tsum_inner_sq_of_complete hWorth hsec).symm
    _ = ∑' p : ι × ι, inner ℝ (TOp K hK (v p.1)) (v p.2) ^ 2 := by rw [hf]
    _ = ∑' j : ι, ∑' i : ι, inner ℝ (TOp K hK (v (j, i).1)) (v (j, i).2) ^ 2 :=
        Summable.tsum_prod' hsmC hsmfib
    _ = ∑' j : ι, ‖TOp K hK (v j)‖ ^ 2 := by
        exact tsum_congr fun j => hJ j

/-- **The reverse HS-norm identity (section family instantiated)**: for a complete
orthonormal family `v` of `L²` whose section family `p ↦ v p.1 ⊗ v p.2` is complete in
the kernel space `L²(vol2)` (the tensor-ONB clause `hsec`), `hsNorm K² = ∑' ‖TOp K v j‖²`. -/
theorem hsNorm_sq_eq_tsum_norm_sq_of_complete_sections {ι : Type*} {v : ι → L2}
    (hv : Orthonormal ℝ v) (hcomp : (span ℝ (Set.range v))ᗮ = ⊥)
    (hsec : (span ℝ (Set.range (fun p : ι × ι => prodKernel (v p.2) (v p.1))))ᗮ = ⊥) :
    hsNorm K ^ 2 = ∑' j, ‖TOp K hK (v j)‖ ^ 2 :=
  hsNorm_sq_eq_tsum_norm_sq_of_complete hv hcomp
    (orthonormal_prodKernel hv) hsec (fun p => inner_prodKernel_pairing p)

/-- The ≥-half in inequality form: `hsNorm K² ≤ ∑' j, ‖TOp K (v j)‖²`, closing the
Parseval boundary of `Hurst.HSNormIdentity` under the completeness clauses. -/
theorem hsNorm_sq_le_tsum_norm_sq_of_complete_sections {ι : Type*} {v : ι → L2}
    (hv : Orthonormal ℝ v) (hcomp : (span ℝ (Set.range v))ᗮ = ⊥)
    (hsec : (span ℝ (Set.range (fun p : ι × ι => prodKernel (v p.2) (v p.1))))ᗮ = ⊥) :
    hsNorm K ^ 2 ≤ ∑' j, ‖TOp K hK (v j)‖ ^ 2 :=
  (hsNorm_sq_eq_tsum_norm_sq_of_complete_sections hv hcomp hsec).le

/-- **Eigenfamily corollary**: for a complete orthonormal eigenfamily `v j` of `L²` with
eigenvalues `κ j` (`TOp K (v j) = κ j • v j`) whose section family is complete in the
kernel space, `hsNorm K² = ∑' j, κ j ^ 2` — the multiplicity-enumeration energy identity
under the completeness clauses. -/
theorem hsNorm_sq_eq_tsum_eigenvalue_sq_of_complete_sections {ι : Type*} {v : ι → L2}
    {κ : ι → ℝ} (hv : Orthonormal ℝ v) (hcomp : (span ℝ (Set.range v))ᗮ = ⊥)
    (hsec : (span ℝ (Set.range (fun p : ι × ι => prodKernel (v p.2) (v p.1))))ᗮ = ⊥)
    (he : ∀ i, TOp K hK (v i) = κ i • v i) :
    hsNorm K ^ 2 = ∑' i, κ i ^ 2 := by
  rw [hsNorm_sq_eq_tsum_norm_sq_of_complete_sections (K := K) (hK := hK) hv hcomp hsec]
  have hfe : (fun j : ι => ‖TOp K hK (v j)‖ ^ 2) = (fun j : ι => κ j ^ 2) := by
    funext j
    rw [he j, norm_smul, Real.norm_eq_abs, hv.1 j, mul_one, sq_abs]
  rw [hfe]

/-! ### E. Parseval for operator images against complete families of `L²` -/

/-- **Parseval for operator images**: for a complete orthonormal family `v` of `L²`,
the squared norm of `TOp K f` is its squared matrix-entry series:
`‖TOp K f‖² = ∑' i, kpair K f (v i)²`.  Instantiation of the abstract reverse
Parseval at `f := TOp K f` with `inner_TOp`. -/
theorem norm_TOp_sq_eq_tsum_kpair_of_complete {ι : Type*} {v : ι → L2}
    (hv : Orthonormal ℝ v) (hcomp : (span ℝ (Set.range v))ᗮ = ⊥) (f : L2) :
    ‖TOp K hK f‖ ^ 2 = ∑' i : ι, kpair K f (v i) ^ 2 := by
  have h0 := norm_sq_eq_tsum_inner_sq_of_complete hv hcomp (TOp K hK f)
  rw [h0]
  have hfe : (fun i : ι => inner ℝ (TOp K hK f) (v i) ^ 2)
      = (fun i : ι => kpair K f (v i) ^ 2) := by
    funext i
    rw [inner_TOp hK]
  rw [hfe]

/-! ### F. Assembly prerequisites from the compact spectral decomposition -/

/-- **Spectral-to-family completeness bridge**: if the eigenfamily `v` spans all
eigenspaces of the kernel operator (`⨆ μ, eigenspace μ ≤ span (range v)`) then, by the
landed compact self-adjoint spectral decomposition (`eigenspace_orthogonal_eq_bot_of_compact`,
requires symmetry + compactness), the span of `v` has trivial orthogonal complement —
i.e. `v` is complete.  This is the missing-input side of the eigenfamily assembly. -/
theorem span_orthogonal_eq_bot_of_eigenspace_span {ι : Type*} {v : ι → L2}
    (hsym : ∀ p : ℝ × ℝ, K p = K p.swap) (hcompact : IsCompactOperator (TOp K hK))
    (hspan : (⨆ μ, Module.End.eigenspace ((TOp K hK : L2 →ₗ[ℝ] L2)) μ)
      ≤ span ℝ (Set.range v)) :
    (span ℝ (Set.range v))ᗮ = ⊥ :=
  orthogonalComplement_eq_bot_of_le (eigenspace_orthogonal_eq_bot_of_compact hK hsym hcompact)
    hspan

end HS

end
