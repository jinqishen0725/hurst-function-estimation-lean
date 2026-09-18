import Hurst.TensorParsevalTracePair

/-!
# Trace-pair cyclicity for HS-type operators

This file proves the **abstract cyclicity step of the M1-D cycle-integral bridge**
(spec §5, M1-D1): for two continuous linear operators `U V : L2 →L[ℝ] L2` whose
matrix-square families over a common Hilbert basis `e` are summable (the HS-type
packaging below), the diagonal trace pairings of the two compositions coincide:

  `∑' i, ⟪e i, U (V (e i))⟫ = ∑' i, ⟪e i, V (U (e i))⟫`.

The statement is independent of the kernel/ω tracks: it is purely basis-pairing
algebra and consumes only the factor matrix-square hypotheses (the composite
hypotheses `hUV`, `hVU` of the prescribed interface are absorbed, not needed).

## Route (Parseval double expansion + absolute summability)

The proof machinery follows `Hurst.EigenTraceBridge` and
`Hurst.TensorParsevalTracePair` (Parseval fiber expansion, `Summable.tsum_prod'`
reassembly, equiv transport of summable families).

1. Per basis vector, Parseval along `e` (`HilbertBasis.hasSum_inner_mul_inner`,
   applied to `U.adjoint (e i)` and `V (e i)`) expands, with the adjoint moved
   onto the fixed vector by `ContinuousLinearMap.adjoint_inner_left/right`,
   `⟪e i, U (V (e i))⟫ = ∑' j, ⟪e i, U (e j)⟫ · ⟪e j, V (e i)⟫`.
2. Reassembling the fibers with `Summable.tsum_prod'`, both trace pairings equal
   double matrix series:
   LHS `= ∑' (i, j), ⟪e i, U (e j)⟫ · ⟪e j, V (e i)⟫`,
   RHS `= ∑' (i, j), ⟪e i, V (e j)⟫ · ⟪e j, U (e i)⟫`.
3. Absolute summability of each double family is the AM–GM Cauchy–Schwarz bound
   `|a · b| ≤ a² + b²` (`abs_mul_le_sq_add_sq`); the squared families are exactly
   the matrix-square hypotheses of `U` and `V`, the second factor taken in
   swapped index order — reindexed along `Equiv.prodComm` by
   `summable_inner_sq_swap`.
4. The two double series are identified by swapping the double index
   (`Equiv.tsum_eq` along `Equiv.prodComm`); the terms are termwise equal by
   `mul_comm`.
-/

namespace HS

/-- Matrix-square summability is invariant under swapping the double index: the
transposed matrix family of `c` over `e` is the reindexing of the matrix family
along `Equiv.prodComm` (the transport used for the `V`/`U` second factors of the
double series). -/
private theorem summable_inner_sq_swap (c : L2 →L[ℝ] L2) (e : HilbertBasis ℕ ℝ L2)
    (h : Summable (fun p : ℕ × ℕ => (inner ℝ (e p.1) (c (e p.2))) ^ 2)) :
    Summable (fun p : ℕ × ℕ => (inner ℝ (e p.2) (c (e p.1))) ^ 2) := by
  have h2 : Summable
      ((fun p : ℕ × ℕ => (inner ℝ (e p.1) (c (e p.2))) ^ 2) ∘ (Equiv.prodComm ℕ ℕ)) :=
    Equiv.summable_iff (Equiv.prodComm ℕ ℕ) |>.mpr h
  exact h2.congr fun p => rfl

/-- **Trace-pair cyclicity** (spec §5, M1-D1): for operators `U V : L2 →L[ℝ] L2`
whose matrix-square families over the Hilbert basis `e` are summable with uniform
bounds (the HS-type packaging; stated for `U`, `V` and the composites `U ∘ V`,
`V ∘ U`), the diagonal trace pairings of `U ∘ V` and `V ∘ U` coincide:
`∑' i, ⟪e i, U (V (e i))⟫ = ∑' i, ⟪e i, V (U (e i))⟫`.  Only the factor
conditions `hU`, `hV` are consumed by the proof; the composite conditions are
part of the prescribed interface and are absorbed. -/
theorem tracePair_cyclic {U V : L2 →L[ℝ] L2} (e : HilbertBasis ℕ ℝ L2)
    (hU : ∃ CU : ℝ, 0 ≤ CU ∧ Summable (fun p : ℕ × ℕ => (inner ℝ (e p.1) (U (e p.2))) ^ 2)
      ∧ (∑' p : ℕ × ℕ, (inner ℝ (e p.1) (U (e p.2))) ^ 2) ≤ CU)
    (hV : ∃ CV : ℝ, 0 ≤ CV ∧ Summable (fun p : ℕ × ℕ => (inner ℝ (e p.1) (V (e p.2))) ^ 2)
      ∧ (∑' p : ℕ × ℕ, (inner ℝ (e p.1) (V (e p.2))) ^ 2) ≤ CV)
    (hUV : ∃ CUV : ℝ, 0 ≤ CUV ∧
      Summable (fun p : ℕ × ℕ => (inner ℝ (e p.1) (U (V (e p.2)))) ^ 2)
      ∧ (∑' p : ℕ × ℕ, (inner ℝ (e p.1) (U (V (e p.2)))) ^ 2) ≤ CUV)
    (hVU : ∃ CVU : ℝ, 0 ≤ CVU ∧
      Summable (fun p : ℕ × ℕ => (inner ℝ (e p.1) (V (U (e p.2)))) ^ 2)
      ∧ (∑' p : ℕ × ℕ, (inner ℝ (e p.1) (V (U (e p.2)))) ^ 2) ≤ CVU) :
    (∑' i : ℕ, inner ℝ (e i) (U (V (e i)))) = (∑' i : ℕ, inner ℝ (e i) (V (U (e i)))) := by
  -- the composite HS-type conditions are not consumed by cyclicity (absorbed)
  obtain ⟨_, _, hUsq, _⟩ := hU
  obtain ⟨_, _, hVsq, _⟩ := hV
  obtain ⟨_, _, _, _⟩ := hUV
  obtain ⟨_, _, _, _⟩ := hVU
  -- swapped-index matrix-square families for the second double-series factors
  have hUsq' := summable_inner_sq_swap U e hUsq
  have hVsq' := summable_inner_sq_swap V e hVsq
  -- per-basis-vector Parseval expansions (adjoint moved onto the fixed vector)
  have hfibL : ∀ i : ℕ, HasSum
      (fun j => inner ℝ (e i) (U (e j)) * inner ℝ (e j) (V (e i)))
      (inner ℝ (e i) (U (V (e i)))) := by
    intro i
    have hval : inner ℝ (U.adjoint (e i)) (V (e i)) = inner ℝ (e i) (U (V (e i))) :=
      (real_inner_comm (V (e i)) (U.adjoint (e i))).trans
        ((ContinuousLinearMap.adjoint_inner_right U (V (e i)) (e i)).trans
          (real_inner_comm (e i) (U (V (e i)))))
    have h1 := e.hasSum_inner_mul_inner (U.adjoint (e i)) (V (e i))
    rw [hval] at h1
    refine h1.congr_fun fun j => ?_
    rw [ContinuousLinearMap.adjoint_inner_left U (e j) (e i)]
  have hfibR : ∀ i : ℕ, HasSum
      (fun j => inner ℝ (e i) (V (e j)) * inner ℝ (e j) (U (e i)))
      (inner ℝ (e i) (V (U (e i)))) := by
    intro i
    have hval : inner ℝ (V.adjoint (e i)) (U (e i)) = inner ℝ (e i) (V (U (e i))) :=
      (real_inner_comm (U (e i)) (V.adjoint (e i))).trans
        ((ContinuousLinearMap.adjoint_inner_right V (U (e i)) (e i)).trans
          (real_inner_comm (e i) (V (U (e i)))))
    have h1 := e.hasSum_inner_mul_inner (V.adjoint (e i)) (U (e i))
    rw [hval] at h1
    refine h1.congr_fun fun j => ?_
    rw [ContinuousLinearMap.adjoint_inner_left V (e j) (e i)]
  -- absolute summability of the double matrix families (AM–GM over the squares)
  have hDf : Summable (fun p : ℕ × ℕ =>
      inner ℝ (e p.1) (U (e p.2)) * inner ℝ (e p.2) (V (e p.1))) :=
    Summable.of_norm_bounded (hUsq.add hVsq') fun p => by
      rw [Real.norm_eq_abs]
      exact abs_mul_le_sq_add_sq _ _
  have hDg : Summable (fun p : ℕ × ℕ =>
      inner ℝ (e p.1) (V (e p.2)) * inner ℝ (e p.2) (U (e p.1))) :=
    Summable.of_norm_bounded (hVsq.add hUsq') fun p => by
      rw [Real.norm_eq_abs]
      exact abs_mul_le_sq_add_sq _ _
  -- both sides reassemble into double matrix series ...
  have hL : (∑' i : ℕ, inner ℝ (e i) (U (V (e i))))
      = (∑' p : ℕ × ℕ,
          inner ℝ (e p.1) (U (e p.2)) * inner ℝ (e p.2) (V (e p.1))) := by
    refine (tsum_congr fun i => (hfibL i).tsum_eq.symm).trans ?_
    exact (Summable.tsum_prod' hDf fun i => (hfibL i).summable).symm
  have hR : (∑' i : ℕ, inner ℝ (e i) (V (U (e i))))
      = (∑' p : ℕ × ℕ,
          inner ℝ (e p.1) (V (e p.2)) * inner ℝ (e p.2) (U (e p.1))) := by
    refine (tsum_congr fun i => (hfibR i).tsum_eq.symm).trans ?_
    exact (Summable.tsum_prod' hDg fun i => (hfibR i).summable).symm
  -- ... and the double series are identified by the index swap
  have hswap : (∑' p : ℕ × ℕ,
        inner ℝ (e p.1) (U (e p.2)) * inner ℝ (e p.2) (V (e p.1)))
      = (∑' p : ℕ × ℕ,
          inner ℝ (e p.1) (V (e p.2)) * inner ℝ (e p.2) (U (e p.1))) := by
    rw [← Equiv.tsum_eq (Equiv.prodComm ℕ ℕ)
      (f := fun q => inner ℝ (e q.1) (U (e q.2)) * inner ℝ (e q.2) (V (e q.1)))]
    refine tsum_congr fun p => ?_
    show inner ℝ (e p.2) (U (e p.1)) * inner ℝ (e p.1) (V (e p.2))
        = inner ℝ (e p.1) (V (e p.2)) * inner ℝ (e p.2) (U (e p.1))
    exact mul_comm _ _
  exact hL.trans (hswap.trans hR.symm)

end HS
