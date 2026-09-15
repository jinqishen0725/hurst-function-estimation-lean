import Hurst.SpectralEnumeration

/-!
# Frozen spectral enumeration for the Riesz kernel operator

The decreasing (with multiplicity) eigenvalue enumeration of the compact symmetric
kernel operator `TOp K hK` (`Hurst.HSOperatorFoundation`, `Hurst.HSOperatorLayer2`),
conditional on the explicit hypotheses

```
hCompact : IsCompactOperator (TOp K hK)
hPos     : ∀ f : L2, 0 ≤ inner ℝ (TOp K hK f) f
```

consumed by the P2 spectrum construction (`Hurst.P2SpectrumConstruction`).

## What is landed here

* **The enumeration bundle** `HS.EigenEnumeration`: a sequence `val : ℕ → ℝ` of
  nonzero eigenvalues together with matching eigenvectors `vec : ℕ → L2` — the
  object the P2/P3 consumers consume.
* **(i)** every enumerated entry is an eigenvalue with its eigenvector
  (`EigenEnumeration.hasEigenvalue`, `EigenEnumeration.exists_hasEigenvector`).
* **(ii)** `|val j| ≤ hsNorm K` (`EigenEnumeration.abs_le_hsNorm`, via
  `‖T (vec j)‖ = |val j| · ‖vec j‖ = |val j|` and `HS.TOp_norm_le`), hence the
  per-entry square bound `val j ^ 2 ≤ hsNorm K ^ 2` (`sq_le_hsNorm_sq`); under
  `hPos` also `0 ≤ val j` (`val_nonneg`, via the landed
  `HS.eigenvalue_nonneg_of_pos`).
* **Unit-eigenvector helpers**: `hasEigenvector_smul_unit`,
  `hasEigenvector_norm_inv` (scaling invariance, used to normalize per level).
* **Orthogonality** of eigenvectors for distinct eigenvalues
  (`inner_eigenvector_eq_zero_of_ne`) — the glue P3 needs to combine basis
  vectors across levels.
* **The compactness contradiction core** (the analysis behind "only finitely many
  eigenvalues accumulate above any `ε > 0`"): `not_injective_eigenvalues_ge` —
  there is *no injective* sequence of eigenvalues all of modulus `≥ ε` with unit
  eigenvectors: the `T`-images stay in the compact image of the unit ball
  (`IsCompactOperator.image_closedBall_subset_compact`), so
  `IsCompact.tendsto_subseq` extracts a convergent subsequence, while pairwise
  orthogonality forces the separation `‖T e i - T e j‖² = val i² + val j² ≥ 2 ε²`,
  contradicting Cauchyness.

## Documented gaps (exact statements, not landed this round)

1. **Set-level finiteness / countability**: from `Set.Infinite
   {μ | HasEigenvalue TE μ ∧ ε ≤ |μ|}` extract an injective sequence with chosen
   unit eigenvectors (choice plumbing through `Set.Infinite.nonempty` /
   `Countable.exists_surjective_nat`-style recursion) and apply
   `not_injective_eigenvalues_ge`.  Countability of
   `{μ | HasEigenvalue TE μ ∧ μ ≠ 0}` follows as `⋃ n, {μ | 1/(n+1) ≤ |μ|}`
   (countable `bUnion` of the finite levels).
2. **Enumeration existence**: `Countable.exists_surjective_nat` on the
   multiplicity sigma type `Σ μ : {μ // HasEigenvalue TE μ ∧ μ ≠ 0},
   Fin (finrank ℝ (eigenspace μ))` (countable base by 1, finite fibers by
   `finiteDimensional_eigenspace_TOp`) produces a sequence in which every nonzero
   eigenvalue appears exactly `finrank` (eigenspace) times; the degenerate case
   (no nonzero eigenvalue) is handled by the identically-zero P2 sequence.
3. **Square-summability / the Parseval-adjacent bound (iii)**: `Σ_j val j² ≤
   hsNorm K²` (hence `Summable (val · ^ 2)`) requires the section/Bessel
   analysis: per `x`, Bessel on the kernel section `K(x, ·)` gives
   `Σ_j |T (e j) x|² ≤ ∫ K(x,y)² dy`, and integration (`∫∫ K² = hsNorm K²`)
   finishes.  This needs the a.e. pointwise section formula
   `(T f) x = ∫ K(x,y) f y dy`, which `Hurst.HSOperatorFoundation` does NOT land
   (`TOpFun` is defined through the Riesz representer; only the pairing formula
   `inner_TOpFun` is available).  The exact identity `Σ κ_j² = hsNorm K²` needs
   the same input.

## Decreasing order is NOT necessary

`HasSum` / `Summable` of `ℕ`-indexed **nonnegative** sequences is permutation
invariant (both depend only on the finite partial sums as a filtered net, and
reindexing by a bijection of `ℕ` preserves them).  With `hPos` every enumerated
eigenvalue is `≥ 0`, so the P2 power sums (`fun j => val j ^ k`, `k ≥ 2`) are
nonnegative sequences and ANY enumeration with correct multiplicity gives the
same `HasSum` target.  The strictly-decreasing arrangement (for P3 matching) is
a cosmetic reindexing of the same multiset and carries no proof obligation for
the HasSum consumption; landing the order-sensitive P3 form was out of budget.
-/

open MeasureTheory Measure Real Set
open scoped Real

noncomputable section

namespace HS

/-! ### The endomorphism and the bundle -/

/-- The kernel operator as a real endomorphism (the mathlib spectral API shape). -/
abbrev TOpEnd' (K : ℝ × ℝ → ℝ) (hK : HSKernel K) : Module.End ℝ L2 :=
  ((TOp K hK : L2 →L[ℝ] L2) : L2 →ₗ[ℝ] L2)

variable {K : ℝ × ℝ → ℝ} {hK : HSKernel K}

/-- Scaling an eigenvector by a nonzero scalar keeps an eigenvector. -/
theorem hasEigenvector_smul_unit {μ c : ℝ} {v : L2}
    (hv : Module.End.HasEigenvector (TOpEnd' K hK) μ v) (hc : c ≠ 0) :
    Module.End.HasEigenvector (TOpEnd' K hK) μ (c • v) := by
  refine ⟨?_, ?_⟩
  · show c • v ∈ (TOpEnd' K hK).eigenspace μ
    rw [Module.End.mem_eigenspace_iff, map_smul, hv.apply_eq_smul, smul_smul,
      smul_smul, mul_comm]
  · intro h
    rcases smul_eq_zero.mp h with h' | h'
    · exact hc h'
    · exact hv.2 h'

/-- The unit rescaling of an eigenvector is a unit eigenvector. -/
theorem hasEigenvector_norm_inv {μ : ℝ} {v : L2}
    (hv : Module.End.HasEigenvector (TOpEnd' K hK) μ v) :
    Module.End.HasEigenvector (TOpEnd' K hK) μ (‖v‖⁻¹ • v) ∧
      ‖(‖v‖⁻¹ • v)‖ = 1 := by
  have hpos : (0:ℝ) < ‖v‖ := norm_pos_iff.mpr hv.2
  refine ⟨hasEigenvector_smul_unit hv (inv_ne_zero hpos.ne'), ?_⟩
  rw [norm_smul]
  have habs : ‖(‖v‖⁻¹ : ℝ)‖ = ‖v‖⁻¹ := by
    rw [Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg v)]
  rw [habs, inv_mul_cancel₀ hpos.ne']

/-- **The eigenvalue enumeration bundle** (with multiplicity): a sequence of
nonzero eigenvalues with matching eigenvectors.  Multiplicity-exact coverage of
every nonzero eigenvalue is packaged at the construction site (documented gap). -/
structure EigenEnumeration (K : ℝ × ℝ → ℝ) (hK : HSKernel K) where
  /-- The eigenvalue sequence. -/
  val : ℕ → ℝ
  /-- The matching eigenvector sequence. -/
  vec : ℕ → L2
  /-- Every entry is an eigenvector with its eigenvalue. -/
  hvec : ∀ j, Module.End.HasEigenvector (TOpEnd' K hK) (val j) (vec j)
  /-- The zero eigenvalue is excluded. -/
  hval : ∀ j, val j ≠ 0

/-! ### Property (i): every entry is an eigenvalue, with an eigenvector -/

/-- **(i)** every enumerated entry is an eigenvalue. -/
theorem EigenEnumeration.hasEigenvalue (E : EigenEnumeration K hK) (j : ℕ) :
    Module.End.HasEigenvalue (TOpEnd' K hK) (E.val j) :=
  Module.End.hasEigenvalue_of_hasEigenvector (E.hvec j)

/-- **(i, consumer form)** every enumerated entry admits an eigenvector. -/
theorem EigenEnumeration.exists_hasEigenvector (E : EigenEnumeration K hK) (j : ℕ) :
    ∃ v : L2, Module.End.HasEigenvector (TOpEnd' K hK) (E.val j) v :=
  ⟨E.vec j, E.hvec j⟩

/-- Concrete membership: an enumerated eigenvector lies in its eigenspace. -/
theorem EigenEnumeration.mem_eigenspace (E : EigenEnumeration K hK) (j : ℕ) :
    E.vec j ∈ Module.End.eigenspace (TOpEnd' K hK) (E.val j) := (E.hvec j).1

/-! ### Property (ii): the uniform bound by the HS norm -/

/-- **(ii)** every enumerated eigenvalue satisfies `|val j| ≤ ‖TOp K‖`. -/
theorem EigenEnumeration.abs_le_norm (E : EigenEnumeration K hK) (j : ℕ) :
    |E.val j| ≤ ‖TOp K hK‖ := by
  have hve := E.hvec j
  have h2 : (0:ℝ) < ‖E.vec j‖ := norm_pos_iff.mpr hve.2
  have h3 : ‖(TOpEnd' K hK) (E.vec j)‖ ≤ ‖TOp K hK‖ * ‖E.vec j‖ :=
    ContinuousLinearMap.le_opNorm (TOp K hK) (E.vec j)
  rw [hve.apply_eq_smul, norm_smul, Real.norm_eq_abs,
    mul_comm (|E.val j|) (‖E.vec j‖), mul_comm (‖TOp K hK‖) (‖E.vec j‖)] at h3
  exact (mul_le_mul_iff_right₀ h2).mp h3

/-- **(ii, kernel-norm form)** `|val j| ≤ hsNorm K` for every enumerated entry. -/
theorem EigenEnumeration.abs_le_hsNorm (E : EigenEnumeration K hK) (j : ℕ) :
    |E.val j| ≤ hsNorm K :=
  (E.abs_le_norm j).trans (TOp_norm_le hK)

/-- **(ii, squared form)** the per-entry square bound feeding the
Parseval-adjacent sum bound: `val j ^ 2 ≤ hsNorm K ^ 2`. -/
theorem EigenEnumeration.sq_le_hsNorm_sq (E : EigenEnumeration K hK) (j : ℕ) :
    E.val j ^ 2 ≤ hsNorm K ^ 2 := by
  have h := E.abs_le_hsNorm j
  have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
  rw [sq_abs] at h2
  exact h2

/-- **Under `hPos`** every enumerated eigenvalue is nonnegative (landed corollary
`HS.eigenvalue_nonneg_of_pos`): the P2 power-sum sequences are nonnegative, hence
permutation-invariant under reindexing. -/
theorem EigenEnumeration.val_nonneg {E : EigenEnumeration K hK}
    (hPos : ∀ f : L2, 0 ≤ inner ℝ (TOp K hK f) f) (j : ℕ) : 0 ≤ E.val j :=
  eigenvalue_nonneg_of_pos hPos (E.hasEigenvalue j)

/-! ### Orthogonality across distinct eigenvalues -/

/-- Eigenvectors of *distinct* eigenvalues of the symmetric kernel operator are
orthogonal: `μ ⟪v,w⟫ = ⟪Tv,w⟫ = ⟪v,Tw⟫ = ν ⟪v,w⟫` and `μ ≠ ν`. -/
theorem inner_eigenvector_eq_zero_of_ne
    (hsym : (↑(TOp K hK) : L2 →ₗ[ℝ] L2).IsSymmetric)
    {μ ν : ℝ} {v w : L2}
    (hv : Module.End.HasEigenvector (TOpEnd' K hK) μ v)
    (hw : Module.End.HasEigenvector (TOpEnd' K hK) ν w)
    (hne : μ ≠ ν) : inner ℝ v w = 0 := by
  have e0 : inner ℝ (TOpEnd' K hK v) w = inner ℝ v (TOpEnd' K hK w) := hsym v w
  rw [hv.apply_eq_smul, hw.apply_eq_smul, real_inner_smul_left,
    real_inner_smul_right] at e0
  have hzero : (μ - ν) * inner ℝ v w = 0 := by
    rw [sub_mul]
    linarith
  rcases mul_eq_zero.mp hzero with h | h
  · exact absurd (sub_eq_zero.mp h) hne
  · exact h

/-! ### The compactness contradiction core -/

set_option maxHeartbeats 1000000 in
/-- There is no injective sequence of eigenvalues all of modulus `≥ ε` (`ε > 0`)
carrying unit eigenvectors: the `T`-images live in the compact image of the unit
ball, so `IsCompact.tendsto_subseq` extracts a convergent subsequence, while
pairwise orthogonality forces the separation
`dist (T e i) (T e j)² = val i² + val j² ≥ 2 ε²`, contradicting Cauchyness.
Combined with injective-sequence extraction from an infinite eigenvalue set
(pure choice plumbing), this yields `Set.Finite {μ | HasEigenvalue μ ∧ ε ≤ |μ|}`. -/
theorem not_injective_eigenvalues_ge    (hCompact : IsCompactOperator (TOp K hK))
    (hsym : (↑(TOp K hK) : L2 →ₗ[ℝ] L2).IsSymmetric)
    {ε : ℝ} (hε : 0 < ε)
    (val : ℕ → ℝ) (e : ℕ → L2)
    (hevec : ∀ n, Module.End.HasEigenvector (TOpEnd' K hK) (val n) (e n))
    (hunit : ∀ n, ‖e n‖ = 1)
    (hbound : ∀ n, ε ≤ |val n|)
    (hinj : Function.Injective val) : False := by
  -- pairwise orthogonality of the unit eigenvectors
  have horth : ∀ i j, i ≠ j → inner ℝ (e i) (e j) = 0 := by
    intro i j hij
    refine inner_eigenvector_eq_zero_of_ne hsym (hevec i) (hevec j) fun hμ => hij ?_
    exact hinj hμ
  -- the T-images live in the compact image of the unit ball
  obtain ⟨Kimg, hKcomp, hKsub⟩ := hCompact.image_closedBall_subset_compact (1 : ℝ)
  have hmem : ∀ n, TOp K hK (e n) ∈ Kimg := by
    intro n
    refine hKsub (Set.mem_image_of_mem (TOp K hK) ?_)
    rw [Metric.mem_closedBall, dist_zero_right, hunit n]
  obtain ⟨a, -, φ, hφmono, hφten⟩ := hKcomp.tendsto_subseq hmem
  -- separation: dist² = val i² + val j² ≥ 2 ε²
  have hsep : ∀ i j, i ≠ j → ε * ε ≤ dist (TOp K hK (e i)) (TOp K hK (e j)) ^ 2 := by
    intro i j hij
    have hne : i ≠ j := hij
    have key : dist (TOp K hK (e i)) (TOp K hK (e j))
        = ‖val i • e i - val j • e j‖ := by
      rw [dist_eq_norm, show (TOp K hK) (e i) - (TOp K hK) (e j)
          = (TOpEnd' K hK) (e i) - (TOpEnd' K hK) (e j) from rfl,
        (hevec i).apply_eq_smul, (hevec j).apply_eq_smul]
    have hexp : dist (TOp K hK (e i)) (TOp K hK (e j)) ^ 2
        = val i ^ 2 + val j ^ 2 := by
      rw [key, ← real_inner_self_eq_norm_sq, real_inner_sub_sub_self]
      simp only [real_inner_smul_left, real_inner_smul_right,
        real_inner_self_eq_norm_sq, hunit i, hunit j, horth i j hne,
        norm_smul, Real.norm_eq_abs, mul_one, sq_abs]
      ring
    calc ε * ε ≤ |val i| * |val j| :=
          mul_le_mul (hbound i) (hbound j) (le_of_lt hε) (abs_nonneg _)
      _ ≤ (|val i| * |val i| + |val j| * |val j|) / 2 := by
          nlinarith [sq_nonneg (|val i| - |val j|)]
      _ = (|val i| ^ 2 + |val j| ^ 2) / 2 := by ring
      _ ≤ val i ^ 2 + val j ^ 2 := by
          rw [sq_abs, sq_abs]
          linarith [sq_nonneg (val i), sq_nonneg (val j)]
      _ = dist (TOp K hK (e i)) (TOp K hK (e j)) ^ 2 := hexp.symm
  -- contradiction with the convergence of the subsequence
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hφten (ε / 2) (by positivity)
  simp only [Function.comp_apply] at hN
  have hd1 : dist (TOp K hK (e (φ N))) a < ε / 2 := hN N (Nat.le_refl N)
  have hd2 : dist (TOp K hK (e (φ (N + 1)))) a < ε / 2 := hN (N + 1) (Nat.le_succ N)
  have hlt : dist (TOp K hK (e (φ N))) (TOp K hK (e (φ (N + 1)))) < ε := by
    have h1 := dist_triangle (TOp K hK (e (φ N))) a (TOp K hK (e (φ (N + 1))))
    rw [dist_comm a] at h1
    calc dist (TOp K hK (e (φ N))) (TOp K hK (e (φ (N + 1))))
        ≤ dist (TOp K hK (e (φ N))) a + dist (TOp K hK (e (φ (N + 1)))) a := h1
      _ < ε := by linarith
  have hsq : ε * ε ≤ dist (TOp K hK (e (φ N))) (TOp K hK (e (φ (N + 1)))) ^ 2 :=
    hsep (φ N) (φ (N + 1)) (fun h => by
      have hlt := hφmono (Nat.lt_succ_self N)
      rw [h] at hlt
      exact Nat.lt_irrefl _ hlt)
  have hlt2 : dist (TOp K hK (e (φ N))) (TOp K hK (e (φ (N + 1)))) ^ 2 < ε * ε := by
    have hd := hlt
    have h1 : dist (TOp K hK (e (φ N))) (TOp K hK (e (φ (N + 1)))) ^ 2
        ≤ dist (TOp K hK (e (φ N))) (TOp K hK (e (φ (N + 1)))) * ε := by
      rw [pow_two]
      have hdnn : (0:ℝ) ≤ dist (TOp K hK (e (φ N)))
          (TOp K hK (e (φ (N + 1)))) := dist_nonneg
      exact mul_le_mul_of_nonneg_left hd.le hdnn
    exact lt_of_le_of_lt h1 (mul_lt_mul_of_pos_right hd hε)
  exact lt_irrefl _ (lt_of_le_of_lt hsq hlt2)

end HS

end
