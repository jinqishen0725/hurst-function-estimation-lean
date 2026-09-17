import Hurst.TensorONBCompleteness

/-!
# Tensor-Parseval trace pairing: `tr(TOp K ∘ TOp L) = cycle2 L K`

This file closes the **isolated gap** documented at the tail of
`Hurst.CycleTraceIdentification`: for Hilbert–Schmidt kernels, the operator-side
trace pairing of a product equals the kernel-side cycle integral,

`∑' i, ⟪TOp K hK (TOp L hL (e i)), e i⟫ = HS.cycle2 L K = ∫∫ L(x,y) K(y,x) dxdy`,

for *every* `HSKernel K`, `HSKernel L` and Hilbert basis `e` of `L2`.  This is the
peel step of the general-`k` trace-power induction `tr(T^{k+1}) = tr(T^k · T)`
(one kernel factor at a time), and its frozen target statement is exactly the one
prescribed for `HS.tracePair_comp_tsum`.

## Route (direct tensor Parseval; the density detour is unnecessary)

The tail of `Hurst.CycleTraceIdentification` prescribed: prove the identity for
degenerate kernels (its landed `tracePair_hasSum_degenerate`), then extend by the
trace-class Cauchy–Schwarz bound and `hsNorm`-density of degenerate kernels.
That detour is **not needed any more**: the blocker it was working around —
Parseval for the tensor-product system `ψ_{ij}(x,y) = (e i)(x) · (e j)(y)` in
`L²(vol.prod vol)` — has been discharged unconditionally by
`Hurst.TensorONBCompleteness.sections_span_orthogonal_eq_bot`.  Consequently the
section family `W p := prodKernel (e p.2) (e p.1)` of a Hilbert basis `e` is a
genuine **Hilbert basis of the kernel space** `L²(vol2)`, and the trace pairing is
*literally* a Parseval expansion in it:

1. `kernel_inner_eq_tsum_prodKernel` — kernel-space Parseval: for the tensor
   Hilbert basis, `⟪g₁, g₂⟫ = ∑' p, ⟪g₁, W p⟫ · ⟪g₂, W p⟫` (built from
   `HilbertBasis.mkOfOrthogonalEqBot` + `orthonormal_prodKernel` +
   `sections_span_orthogonal_eq_bot` + `HilbertBasis.tsum_inner_mul_inner`).
2. The `W`-coordinate of a kernel is its operator matrix entry:
   `⟪MemLp.toLp K hK, W p⟫ = ⟪TOp K hK (e p.1), e p.2⟫` (landed
   `inner_prodKernel_pairing`), and the transpose-kernel bridge
   `inner_TOp_transpose` (`kpair_transpose` + `inner_TOp`) gives
   `⟪MemLp.toLp (Kᵀ), W p⟫ = ⟪TOp K hK (e p.2), e p.1⟫`.
3. `cycle2_eq_tsum_pair` — hence `cycle2 L K` is the double series of matrix
   entries `∑' p, ⟪TOp K (e p.2), e p.1⟫ · ⟪TOp L (e p.1), e p.2⟫`.
4. Per fiber `i`, Parseval along `e` (`e.hasSum_inner_mul_inner`) expands
   `⟪TOp K (TOp L (e i)), e i⟫ = ∑' j, ⟪TOp K (e j), e i⟫ · ⟪TOp L (e i), e j⟫`
   (adjointness `TOp_adjoint` moves the transpose onto the fixed vector).
5. Absolute summability of the double family over `ℕ × ℕ` is the AM–GM
   Cauchy–Schwarz trace bound `|⟪TOp K (e j), e i⟫ · ⟪TOp L (e i), e j⟫| ≤
   (squares)`, with the squares summable by kernel-space Bessel/Parseval
   (`Orthonormal.inner_products_summable` against `W`), so
   `Summable.tsum_prod'` reassembles the fibers, and `tracePair_comp_tsum`
   identifies both sides.

## Main results

* `tracePair_comp_tsum` — **the frozen deliverable**:
  `∑' i, ⟪TOp K hK (TOp L hL (e i)), e i⟫ = HS.cycle2 L K` for all `HSKernel K`,
  `HSKernel L` and `e : HilbertBasis ℕ ℝ L2` (no symmetry/compactness hypotheses,
  no degeneracy restriction).
* `abs_tracePair_comp_le` — the trace-class (Cauchy–Schwarz) bound
  `|∑' i, ⟪TOp K (TOp L (e i)), e i⟫| ≤ hsNorm K * hsNorm L`.
* `tracePair_comp_summable` — the pairing series converges (absolutely, in the
  `ℝ`-sense that mathlib's `Summable` encodes).
* `tracePair_tsum` — the **isolated-gap form**: `∑' j, ⟪TOp K (e j), TOp L (e j)⟫
  `= ∫∫ K(x,y) L(x,y) dxdy`, i.e. the general-HS-kernel operator pairing equals
  the kernel inner product `⟪K, L⟫_{L²(vol²)}` — the exact statement the
  `CycleTraceIdentification` tail isolated as the gap.
* `cycle2_eq_tsum_pair`, `kernel_inner_eq_tsum_prodKernel` — reusable
  Parseval-expansion statements on the landed `HS` encoding.
-/

open MeasureTheory Measure Real Set Submodule
open scoped Real

noncomputable section

namespace HS

variable {K L : ℝ × ℝ → ℝ}

/-! ### Small helpers -/

/-- AM–GM: the pointwise Cauchy–Schwarz step `|x·y| ≤ x² + y²` used to dominate
the trace-pairing terms. -/
theorem abs_mul_le_sq_add_sq (x y : ℝ) : |x * y| ≤ x ^ 2 + y ^ 2 := by
  have hx : |x| ^ 2 = x ^ 2 := sq_abs x
  have hy : |y| ^ 2 = y ^ 2 := sq_abs y
  have h : 0 ≤ (|x| - |y|) ^ 2 := sq_nonneg _
  rw [abs_mul]
  nlinarith [hx, hy, h, sq_nonneg x, sq_nonneg y]

/-- Bessel along a Hilbert basis: squared coordinates of a fixed vector are
summable (real-`inner` form). -/
theorem summable_inner_sq_of_hilbertBasis {ι : Type*} (e : HilbertBasis ι ℝ L2)
    (u : L2) : Summable (fun i : ι => inner ℝ u (e i) ^ 2) := by
  have h0 := e.orthonormal.inner_products_summable u
  exact h0.congr fun i => by rw [real_inner_comm, Real.norm_eq_abs, sq_abs]

/-- Bessel in the kernel space against the tensor-section family of a Hilbert
basis: squared coordinates of a fixed kernel are summable. -/
theorem summable_inner_prodKernel_sq_of_basis (e : HilbertBasis ℕ ℝ L2)
    (g : MeasureTheory.Lp ℝ 2 vol2) :
    Summable (fun p : ℕ × ℕ => inner ℝ g (prodKernel (⇑e p.2) (⇑e p.1)) ^ 2) := by
  have h0 := (orthonormal_prodKernel e.orthonormal).inner_products_summable g
  exact h0.congr fun p => by rw [real_inner_comm, Real.norm_eq_abs, sq_abs]

/-- **The transpose-kernel bridge**: pairing against the operator of the
transposed kernel is the flipped pairing of the operator:
`⟪TOp (Kᵀ) u, v⟫ = ⟪TOp K v, u⟫`. -/
theorem inner_TOp_transpose {K : ℝ × ℝ → ℝ} (hK : HSKernel K) (u v : L2) :
    inner ℝ (TOp (ktranspose K) (hsKernel_transpose hK) u) v
      = inner ℝ (TOp K hK v) u :=
  (inner_TOp (hsKernel_transpose hK) u v).trans
    ((kpair_transpose hK v u).trans (inner_TOp hK v u).symm)

/-! ### The tensor-ONB Parseval expansion in the kernel space -/

/-- **Tensor-ONB Parseval**: the section family `p ↦ e p.2 ⊗ e p.1` of a Hilbert
basis `e` of `L2` is a Hilbert basis of the kernel space `L²(vol2)`, so the
kernel inner product is the coordinate series
`⟪g₁, g₂⟫ = ∑' p, ⟪g₁, e p.2 ⊗ e p.1⟫ · ⟪g₂, e p.2 ⊗ e p.1⟫`.
This is the discharged form of the Parseval gap isolated in
`Hurst.CycleTraceIdentification` (completeness by
`sections_span_orthogonal_eq_bot`). -/
theorem kernel_inner_eq_tsum_prodKernel (e : HilbertBasis ℕ ℝ L2)
    (g₁ g₂ : MeasureTheory.Lp ℝ 2 vol2) :
    inner ℝ g₁ g₂ = ∑' p : ℕ × ℕ,
      inner ℝ g₁ (prodKernel (⇑e p.2) (⇑e p.1))
        * inner ℝ g₂ (prodKernel (⇑e p.2) (⇑e p.1)) := by
  have hWe : (span ℝ (Set.range ⇑e))ᗮ = ⊥ :=
    orthogonalComplement_eq_bot_of_dense_span e.dense_span
  have hWcomp : (span ℝ (Set.range fun p : ℕ × ℕ => prodKernel (⇑e p.2) (⇑e p.1)))ᗮ
      = ⊥ := sections_span_orthogonal_eq_bot hWe
  have hexp := (HilbertBasis.mkOfOrthogonalEqBot (orthonormal_prodKernel e.orthonormal)
    hWcomp).tsum_inner_mul_inner g₁ g₂
  simp only [HilbertBasis.coe_mkOfOrthogonalEqBot] at hexp
  refine hexp.symm.trans (tsum_congr fun p => ?_)
  rw [real_inner_comm (prodKernel (⇑e p.2) (⇑e p.1)) g₂]

/-- The `W`-coordinate of the transposed kernel is the flipped matrix entry:
`⟪Kᵀ, e p.2 ⊗ e p.1⟫ = ⟪TOp K (e p.2), e p.1⟫`. -/
theorem inner_prodKernel_transpose_pairing (e : HilbertBasis ℕ ℝ L2)
    (hK : HSKernel K) (p : ℕ × ℕ) :
    inner ℝ (MemLp.toLp (ktranspose K) (hsKernel_transpose hK))
        (prodKernel (⇑e p.2) (⇑e p.1))
      = inner ℝ (TOp K hK (e p.2)) (e p.1) :=
  (inner_prodKernel_pairing (K := ktranspose K) (hK := hsKernel_transpose hK)
    (v := ⇑e) p).trans (inner_TOp_transpose hK (e p.1) (e p.2))

/-- **`cycle2` as the matrix-entry double series**: for Hilbert–Schmidt kernels,
`cycle2 L K = ∑' (i, j), ⟪TOp K (e j), e i⟫ · ⟪TOp L (e i), e j⟫`, the
kernel-side Parseval expansion of `∫∫ L(x,y) K(y,x)` along the tensor-ONB. -/
theorem cycle2_eq_tsum_pair (hK : HSKernel K) (hL : HSKernel L)
    (e : HilbertBasis ℕ ℝ L2) :
    HS.cycle2 L K = ∑' p : ℕ × ℕ,
      inner ℝ (TOp K hK (e p.2)) (e p.1) * inner ℝ (TOp L hL (e p.1)) (e p.2) := by
  have hcyc : HS.cycle2 L K = ∫ p : ℝ × ℝ, L p * (ktranspose K) p ∂vol2 := rfl
  have key := kernel_inner_eq_tsum_prodKernel e (MemLp.toLp L hL)
    (MemLp.toLp (ktranspose K) (hsKernel_transpose hK))
  rw [inner_toLp_toLp hL (hsKernel_transpose hK)] at key
  refine hcyc.trans (key.trans (tsum_congr fun p => ?_))
  rw [inner_prodKernel_pairing (K := L) (hK := hL) (v := ⇑e) p,
    inner_prodKernel_transpose_pairing e hK p, mul_comm]

/-! ### The trace-pairing identification -/

/-- **The trace pairing of a kernel product equals the kernel cycle pairing**
(the frozen deliverable): for Hilbert–Schmidt kernels `K, L` and a Hilbert basis
`e` of `L2`,
`∑' i, ⟪TOp K hK (TOp L hL (e i)), e i⟫ = HS.cycle2 L K = ∫∫ L(x,y) K(y,x) dxdy`.
This is the peel step `tr(T^{k+1}) = tr(T^k · T)` of the general-`k` trace-power
induction at `k = 2` with one `TOp L` factor, valid for ALL `HSKernel` kernels —
the extension from degenerate kernels needs no density argument because the
tensor-ONB Parseval gap (`Hurst.TensorONBCompleteness`) is discharged
unconditionally. -/
theorem tracePair_comp_tsum (hK : HSKernel K) (hL : HSKernel L)
    (e : HilbertBasis ℕ ℝ L2) :
    (∑' i : ℕ, inner ℝ (TOp K hK (TOp L hL (e i))) (e i)) = HS.cycle2 L K := by
  classical
  have hKt : HSKernel (ktranspose K) := hsKernel_transpose hK
  -- per-fiber Parseval along `e`: the transpose sits on the fixed vector
  have hfib : ∀ i : ℕ, HasSum
      (fun j : ℕ => inner ℝ (TOp K hK (e j)) (e i) * inner ℝ (TOp L hL (e i)) (e j))
      (inner ℝ (TOp K hK (TOp L hL (e i))) (e i)) := by
    intro i
    have hval : inner ℝ (TOp (ktranspose K) hKt (e i)) (TOp L hL (e i))
        = inner ℝ (TOp K hK (TOp L hL (e i))) (e i) := by
      rw [← ContinuousLinearMap.adjoint_inner_right (TOp K hK) (TOp L hL (e i)) (e i),
        TOp_adjoint hK, real_inner_comm]
    have h1 := e.hasSum_inner_mul_inner (TOp (ktranspose K) hKt (e i)) (TOp L hL (e i))
    rw [hval] at h1
    refine h1.congr_fun fun j => ?_
    rw [inner_TOp_transpose hK, real_inner_comm (TOp L hL (e i)) (e j)]
  -- fiberwise summability: AM–GM domination by Bessel-summable squares
  have hDfib : ∀ i : ℕ, Summable
      (fun j : ℕ => inner ℝ (TOp K hK (e j)) (e i) * inner ℝ (TOp L hL (e i)) (e j)) := by
    intro i
    have hdom : Summable (fun j : ℕ =>
        inner ℝ (TOp (ktranspose K) hKt (e i)) (e j) ^ 2
          + inner ℝ (TOp L hL (e i)) (e j) ^ 2) :=
      (summable_inner_sq_of_hilbertBasis e _).add (summable_inner_sq_of_hilbertBasis e _)
    refine Summable.of_norm_bounded hdom fun j => ?_
    rw [Real.norm_eq_abs, ← inner_TOp_transpose hK]
    exact abs_mul_le_sq_add_sq _ _
  -- full-family summability: AM–GM domination by kernel-space Parseval squares
  have hD : Summable (fun p : ℕ × ℕ =>
      inner ℝ (TOp K hK (e p.2)) (e p.1) * inner ℝ (TOp L hL (e p.1)) (e p.2)) := by
    have hdom : Summable (fun p : ℕ × ℕ =>
        inner ℝ (MemLp.toLp L hL) (prodKernel (⇑e p.2) (⇑e p.1)) ^ 2
          + inner ℝ (MemLp.toLp (ktranspose K) hKt)
              (prodKernel (⇑e p.2) (⇑e p.1)) ^ 2) :=
      (summable_inner_prodKernel_sq_of_basis e _).add (summable_inner_prodKernel_sq_of_basis e _)
    refine Summable.of_norm_bounded hdom fun p => ?_
    rw [Real.norm_eq_abs, ← inner_prodKernel_pairing (K := L) (hK := hL) (v := ⇑e) p,
      ← inner_prodKernel_transpose_pairing e hK p, mul_comm]
    exact abs_mul_le_sq_add_sq _ _
  -- reassemble the fibers and invoke the kernel-side Parseval expansion
  calc (∑' i : ℕ, inner ℝ (TOp K hK (TOp L hL (e i))) (e i))
      = ∑' i : ℕ, ∑' j : ℕ,
          inner ℝ (TOp K hK (e j)) (e i) * inner ℝ (TOp L hL (e i)) (e j) :=
        tsum_congr fun i => (hfib i).tsum_eq.symm
    _ = ∑' p : ℕ × ℕ,
          inner ℝ (TOp K hK (e p.2)) (e p.1) * inner ℝ (TOp L hL (e p.1)) (e p.2) :=
        (Summable.tsum_prod' hD hDfib).symm
    _ = HS.cycle2 L K := (cycle2_eq_tsum_pair hK hL e).symm

/-- **The trace-class (Cauchy–Schwarz) bound**: the trace pairing of a kernel
product is dominated by the product of the kernel HS-norms —
`|∑' i, ⟪TOp K (TOp L (e i)), e i⟫| ≤ hsNorm L * hsNorm K` (equal to
`hsNorm K * hsNorm L` by commutativity). -/
theorem abs_tracePair_comp_le (hK : HSKernel K) (hL : HSKernel L)
    (e : HilbertBasis ℕ ℝ L2) :
    |∑' i : ℕ, inner ℝ (TOp K hK (TOp L hL (e i))) (e i)| ≤ hsNorm L * hsNorm K := by
  rw [tracePair_comp_tsum hK hL e]
  exact cycle2_bound hL hK

/-- **Absolute summability** of the trace-pairing series (for `ℝ`, mathlib's
`Summable` is exactly absolute convergence). -/
theorem tracePair_comp_summable (hK : HSKernel K) (hL : HSKernel L)
    (e : HilbertBasis ℕ ℝ L2) :
    Summable (fun i : ℕ => inner ℝ (TOp K hK (TOp L hL (e i))) (e i)) := by
  have hKt : HSKernel (ktranspose K) := hsKernel_transpose hK
  have h1 : Summable (fun i : ℕ => ‖TOp (ktranspose K) hKt (e i)‖ ^ 2) :=
    summable_norm_TOp_sq e.orthonormal
  have h2 : Summable (fun i : ℕ => ‖TOp L hL (e i)‖ ^ 2) :=
    summable_norm_TOp_sq e.orthonormal
  refine Summable.of_norm_bounded (h1.add h2) fun i => ?_
  have hval : inner ℝ (TOp K hK (TOp L hL (e i))) (e i)
      = inner ℝ (TOp (ktranspose K) hKt (e i)) (TOp L hL (e i)) := by
    rw [← ContinuousLinearMap.adjoint_inner_right (TOp K hK) (TOp L hL (e i)) (e i),
      TOp_adjoint hK, real_inner_comm]
  rw [hval, Real.norm_eq_abs]
  refine (abs_real_inner_le_norm _ _).trans ?_
  have h := abs_mul_le_sq_add_sq (‖TOp (ktranspose K) hKt (e i)‖) (‖TOp L hL (e i)‖)
  rwa [abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))] at h

/-! ### The isolated-gap form: operator pairing = kernel inner product -/

/-- **The isolated-gap statement** (verbatim target of the gap isolated at the
tail of `Hurst.CycleTraceIdentification`): for general Hilbert–Schmidt kernels
the operator trace pairing is the kernel inner product,
`∑' j, ⟪TOp K (e j), TOp L (e j)⟫ = ⟪K, L⟫_{L²(vol²)} = ∫∫ K(x,y) L(x,y) dxdy`.
No symmetry, compactness or degeneracy hypotheses. -/
theorem tracePair_tsum (hK : HSKernel K) (hL : HSKernel L)
    (e : HilbertBasis ℕ ℝ L2) :
    (∑' j : ℕ, inner ℝ (TOp K hK (e j)) (TOp L hL (e j)))
      = ∫ p : ℝ × ℝ, K p * L p ∂vol2 := by
  classical
  -- per-fiber Parseval along `e`
  have hfib : ∀ j : ℕ, HasSum
      (fun i : ℕ => inner ℝ (TOp L hL (e j)) (e i) * inner ℝ (TOp K hK (e j)) (e i))
      (inner ℝ (TOp K hK (e j)) (TOp L hL (e j))) := by
    intro j
    have h1 := e.hasSum_inner_mul_inner (TOp L hL (e j)) (TOp K hK (e j))
    rw [real_inner_comm (TOp K hK (e j)) (TOp L hL (e j))] at h1
    refine h1.congr_fun fun i => ?_
    rw [real_inner_comm (e i) (TOp K hK (e j))]
  -- fiberwise and full summability (both coordinates are plain operator entries)
  have hEfib : ∀ j : ℕ, Summable
      (fun i : ℕ => inner ℝ (TOp L hL (e j)) (e i) * inner ℝ (TOp K hK (e j)) (e i)) := by
    intro j
    have hdom : Summable (fun i : ℕ =>
        inner ℝ (TOp L hL (e j)) (e i) ^ 2 + inner ℝ (TOp K hK (e j)) (e i) ^ 2) :=
      (summable_inner_sq_of_hilbertBasis e _).add (summable_inner_sq_of_hilbertBasis e _)
    refine Summable.of_norm_bounded hdom fun i => ?_
    rw [Real.norm_eq_abs]
    exact abs_mul_le_sq_add_sq _ _
  have hE : Summable (fun p : ℕ × ℕ =>
      inner ℝ (TOp L hL (e p.1)) (e p.2) * inner ℝ (TOp K hK (e p.1)) (e p.2)) := by
    have hdom : Summable (fun p : ℕ × ℕ =>
        inner ℝ (MemLp.toLp L hL) (prodKernel (⇑e p.2) (⇑e p.1)) ^ 2
          + inner ℝ (MemLp.toLp K hK) (prodKernel (⇑e p.2) (⇑e p.1)) ^ 2) :=
      (summable_inner_prodKernel_sq_of_basis e _).add (summable_inner_prodKernel_sq_of_basis e _)
    refine Summable.of_norm_bounded hdom fun p => ?_
    rw [Real.norm_eq_abs, ← inner_prodKernel_pairing (K := L) (hK := hL) (v := ⇑e) p,
      ← inner_prodKernel_pairing (K := K) (hK := hK) (v := ⇑e) p]
    exact abs_mul_le_sq_add_sq _ _
  -- reassemble and read off the kernel inner product
  have key := kernel_inner_eq_tsum_prodKernel e (MemLp.toLp L hL) (MemLp.toLp K hK)
  rw [inner_toLp_toLp hL hK] at key
  have hterm : ∀ p : ℕ × ℕ,
      inner ℝ (TOp L hL (e p.1)) (e p.2) * inner ℝ (TOp K hK (e p.1)) (e p.2)
        = inner ℝ (MemLp.toLp L hL) (prodKernel (⇑e p.2) (⇑e p.1))
          * inner ℝ (MemLp.toLp K hK) (prodKernel (⇑e p.2) (⇑e p.1)) := by
    intro p
    rw [← inner_prodKernel_pairing (K := L) (hK := hL) (v := ⇑e) p,
      ← inner_prodKernel_pairing (K := K) (hK := hK) (v := ⇑e) p]
  calc (∑' j : ℕ, inner ℝ (TOp K hK (e j)) (TOp L hL (e j)))
      = ∑' j : ℕ, ∑' i : ℕ,
          inner ℝ (TOp L hL (e j)) (e i) * inner ℝ (TOp K hK (e j)) (e i) :=
        tsum_congr fun j => (hfib j).tsum_eq.symm
    _ = ∑' p : ℕ × ℕ,
          inner ℝ (TOp L hL (e p.1)) (e p.2) * inner ℝ (TOp K hK (e p.1)) (e p.2) :=
        (Summable.tsum_prod' hE hEfib).symm
    _ = ∫ p : ℝ × ℝ, K p * L p ∂vol2 := by
        refine (tsum_congr hterm).trans (key.symm.trans ?_)
        exact integral_congr_ae (Filter.Eventually.of_forall fun p => mul_comm (L p) (K p))

end HS

end
