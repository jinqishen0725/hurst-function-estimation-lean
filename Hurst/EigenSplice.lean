import Hurst.FrozenSpectralCount
import Hurst.HSNormIdentity

/-!
# ON-splice bookkeeping: `Summable λ²` for the multiplicity-exact enumeration

Closes the documented gap at the tail of `Hurst.HSNormIdentity` ("the missing step is
per-eigenspace Gram–Schmidt ... splice over the countable set of nonzero eigenvalues
into ONE orthonormal family").  The Bessel bound (`summable_eigenvalues_sq` /
`hsNorm_sq_ge_sum_norm_sq_of_orthonormal`) applies only to ORTHONORMAL families, but the
eigenvectors of the multiplicity enumeration (`HS.exists_multiplicity_enumeration`) are
pairwise orthogonal only ACROSS distinct eigenvalues; WITHIN one eigenspace its
`finrank`-many entries need not be orthogonal.

The fix, in three steps:

* `HS.exists_spliced_orthonormal_family` — each nonzero eigenspace (finite-dimensional,
  by the mathlib compact spectral theorem) carries `stdOrthonormalBasis`, an orthonormal
  basis indexed by `Fin (finrank (eigenspace μ))`; splicing these bases over the nonzero
  eigenvalues (index type `HS.spliceIdx = Σ μ, Fin (finrank (eigenspace μ))`) yields ONE
  orthonormal family of unit eigenvectors: orthogonality within a level from the basis,
  across levels from the landed `inner_eigenvector_eq_zero_of_ne`;
* the enumeration's value map is caught by the spliced family through per-level
  equivalences `{j // val j = μ} ≃ Fin (finrank (eigenspace μ))` (from the
  multiplicity-exactness clause `Nat.card {j // val j = μ} = finrank (eigenspace μ)`):
  a fiber-wise injection `φ` into the spliced index satisfies
  `|val j| = ‖TOp K hK (w (φ j))‖`, so every finite partial sum of `val j ^ 2` is the
  Bessel sum of the orthonormal family over a finite index set, hence `≤ hsNorm K²`;
* `HS.summable_val_sq_of_multiplicityEnumeration` — bounded partial sums of a nonnegative
  series give `Summable (fun j => val j ^ 2)` (`summable_of_sum_le`);
  `HS.exists_multiplicity_enumeration_summable` packages the enumeration together with
  the summability clause (the `Summable λ²` clause of `IsRieszSpectrumSequence` on the
  constructed spectrum).

No countability input is needed: Bessel bounds finite sub-families of the spliced
family regardless of the index cardinality, and `Summable` on `ℕ` follows from the
uniform partial-sum bound alone.
-/

open MeasureTheory Measure Real Set
open scoped Real

noncomputable section

namespace HS

variable {K : ℝ × ℝ → ℝ} {hK : HSKernel K}

/-- The spliced index type: a nonzero eigenvalue (an element of `S`) together with an
index into an orthonormal basis of its eigenspace. -/
abbrev spliceIdx (TE : Module.End ℝ L2) (S : Set ℝ) : Type :=
  Σ a : ↥S, Fin (Module.finrank ℝ (Module.End.eigenspace TE a.val))

set_option maxHeartbeats 1000000 in
/-- **The ON-splice lemma**: the orthonormal bases of the (finite-dimensional)
eigenspaces of the compact symmetric kernel operator, indexed by
`Fin (finrank (eigenspace μ))`, splice over any set `S` of nonzero eigenvalues into ONE
orthonormal family `w` of unit eigenvectors: `TOp K hK (w σ) = σ.1.val • w σ` and
`‖w σ‖ = 1`.  Orthogonality within a level is the eigenspace basis; across levels it is
`inner_eigenvector_eq_zero_of_ne`. -/
theorem exists_spliced_orthonormal_family (hCompact : IsCompactOperator (TOp K hK))
    (hsym : (↑(TOp K hK) : L2 →ₗ[ℝ] L2).IsSymmetric)
    (S : Set ℝ) (hS : ∀ a : ↥S, Module.End.HasEigenvalue (TOpEnd' K hK) a.val ∧ a.val ≠ 0) :
    ∃ w : spliceIdx (TOpEnd' K hK) S → L2,
      Orthonormal ℝ w ∧ ∀ σ, TOp K hK (w σ) = σ.1.val • w σ ∧ ‖w σ‖ = 1 := by
  classical
  -- every eigenspace over `S` is finite-dimensional (compact operator, μ ≠ 0)
  haveI hfd : ∀ a : ↥S,
      FiniteDimensional ℝ ↥(Module.End.eigenspace (TOpEnd' K hK) a.val) :=
    fun a => finiteDimensional_eigenspace_TOp hCompact (hS a).2
  -- the per-level orthonormal basis, indexed by `Fin (finrank (eigenspace a))`
  have B : ∀ a : ↥S, OrthonormalBasis
      (Fin (Module.finrank ℝ (Module.End.eigenspace (TOpEnd' K hK) a.val))) ℝ
      ↥(Module.End.eigenspace (TOpEnd' K hK) a.val) := fun a => stdOrthonormalBasis ℝ _
  -- every spliced vector has norm 1
  have hnorm : ∀ σ : spliceIdx (TOpEnd' K hK) S, ‖((B σ.1) σ.2 : L2)‖ = 1 :=
    fun σ => (Submodule.norm_coe (B σ.1 σ.2)).trans ((B σ.1).orthonormal.1 σ.2)
  -- in particular every spliced vector is nonzero
  have hnz : ∀ σ : spliceIdx (TOpEnd' K hK) S, ((B σ.1) σ.2 : L2) ≠ 0 :=
    fun σ => norm_ne_zero_iff.mp (by rw [hnorm σ]; norm_num)
  refine ⟨fun σ => ((B σ.1) σ.2 : L2), ⟨hnorm, ?_⟩,
    fun σ => ⟨(mem_eigenspace_TOp_iff _).mp ((B σ.1) σ.2).2, hnorm σ⟩⟩
  · -- orthogonality: within a level from the basis, across levels from the symmetry
    intro σ σ' hσ
    rcases σ with ⟨a, i⟩
    rcases σ' with ⟨a', i'⟩
    by_cases hac : a.val = a'.val
    · -- same eigenvalue: two distinct basis vectors of one eigenspace
      have haa : a = a' := Subtype.ext hac
      subst haa
      have hii : i ≠ i' := fun h => hσ (by rw [h])
      show inner ℝ ((B a i : L2)) ((B a i' : L2)) = 0
      rw [← Submodule.coe_inner]
      exact (B a).orthonormal.2 hii
    · -- distinct eigenvalues: the landed orthogonality of eigenvectors
      show inner ℝ ((B a i : L2)) ((B a' i' : L2)) = 0
      exact inner_eigenvector_eq_zero_of_ne hsym
        ⟨(B a i).2, hnz ⟨⟨a, a.2⟩, i⟩⟩
        ⟨(B a' i').2, hnz ⟨⟨a', a'.2⟩, i'⟩⟩ hac

set_option maxHeartbeats 1000000 in
/-- **The Summable-λ² clause for the multiplicity-exact enumeration**: if `val : ℕ → ℝ`
enumerates eigenvalues of the compact symmetric kernel operator (each entry `0` or an
eigenvalue with its eigenvector `vec`), and every nonzero eigenvalue `μ` appears exactly
`finrank (eigenspace μ)` times (`Nat.card {j // val j = μ} = finrank (eigenspace μ)`),
then `Summable (fun j => val j ^ 2)`.

The proof catches the enumeration by the spliced orthonormal family: for a finite set
of indices, each nonzero entry `val j` is injected through its per-level equivalence
`{j // val j = μ} ≃ Fin (finrank (eigenspace μ))` into the spliced index, on which
`val j` agrees in absolute value with the Bessel term `‖TOp K hK (w (φ j))‖`; the finite
Bessel bound then bounds the partial sum by `hsNorm K²`, and bounded partial sums of a
nonnegative series give summability. -/
theorem summable_val_sq_of_multiplicityEnumeration
    (hCompact : IsCompactOperator (TOp K hK))
    (hsym : (↑(TOp K hK) : L2 →ₗ[ℝ] L2).IsSymmetric)
    {val : ℕ → ℝ} {vec : ℕ → L2}
    (hval : ∀ j, val j = 0 ∨ Module.End.HasEigenvector (TOpEnd' K hK) (val j) (vec j))
    (hmult : ∀ μ : ℝ, Module.End.HasEigenvalue (TOpEnd' K hK) μ → μ ≠ 0 →
      Nat.card {j : ℕ // val j = μ}
        = Module.finrank ℝ (Module.End.eigenspace (TOpEnd' K hK) μ)) :
    Summable (fun j => val j ^ 2) := by
  classical
  set S : Set ℝ := {μ : ℝ | Module.End.HasEigenvalue (TOpEnd' K hK) μ ∧ μ ≠ 0} with hSdef
  -- the spliced orthonormal family of unit eigenvectors over the nonzero spectrum
  obtain ⟨w, hwON, hb⟩ :=
    exists_spliced_orthonormal_family hCompact hsym S (fun a => ⟨a.2.1, a.2.2⟩)
  have hweig : ∀ σ, TOp K hK (w σ) = σ.1.val • w σ := fun σ => (hb σ).1
  have hwnorm : ∀ σ, ‖w σ‖ = 1 := fun σ => (hb σ).2
  -- finite-dimensionality of the eigenspaces over the nonzero spectrum
  haveI hfd : ∀ a : ↥S, FiniteDimensional ℝ ↥(Module.End.eigenspace (TOpEnd' K hK) a.val) :=
    fun a => finiteDimensional_eigenspace_TOp hCompact a.2.2
  -- every partial sum is bounded by the Bessel sum of the spliced family
  have hub : ∀ u : Finset ℕ, ∑ j ∈ u, val j ^ 2 ≤ hsNorm K ^ 2 := by
    intro u
    -- zero entries contribute nothing
    have hstep1 : ∑ j ∈ u, val j ^ 2
        = ∑ j ∈ u.filter (fun j => val j ≠ 0), val j ^ 2 :=
      (Finset.sum_subset (Finset.filter_subset (fun j => val j ≠ 0) u) (fun j hj hjf => by
        have hv0 : val j = 0 := by
          by_contra hne
          exact hjf (Finset.mem_filter.mpr ⟨hj, hne⟩)
        rw [hv0]
        norm_num)).symm
    set u' : Finset ℕ := u.filter (fun j => val j ≠ 0) with hu'def
    -- membership of the filtered set lands in the nonzero spectrum
    have hmemS : ∀ j ∈ u', val j ∈ S ∧ val j ≠ 0 := by
      intro j hj
      rw [hu'def, Finset.mem_filter] at hj
      cases hval j with
      | inl h0 => exact absurd h0 hj.2
      | inr hv => exact ⟨⟨Module.End.hasEigenvalue_of_hasEigenvector hv, hj.2⟩, hj.2⟩
    -- the finite set of attained levels
    set Lv : Finset ℝ := u'.image val with hLvdef
    have hLvS : ∀ a ∈ Lv, a ∈ S := by
      intro a ha
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
      exact (hmemS j hj).1
    have hLvne : ∀ a ∈ Lv, a ≠ 0 := by
      intro a ha
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
      exact (hmemS j hj).2
    -- each level's fiber inside u' is no larger than the eigenspace dimension
    have hfible : ∀ a ∈ Lv, (u'.filter (fun j => a = val j)).card
        ≤ Module.finrank ℝ ↥(Module.End.eigenspace (TOpEnd' K hK) a) := by
      intro a ha
      haveI hfd : FiniteDimensional ℝ ↥(Module.End.eigenspace (TOpEnd' K hK) a) :=
        finiteDimensional_eigenspace_TOp hCompact (hLvne a ha)
      haveI hfin : Finite {j : ℕ // val j = a} := by
        by_contra hnf
        haveI hinf : Infinite {j : ℕ // val j = a} := not_finite_iff_infinite.mp hnf
        have hpos : 0 < Module.finrank ℝ ↥(Module.End.eigenspace (TOpEnd' K hK) a) := by
          obtain ⟨v, hv⟩ := (hLvS a ha).1.exists_hasEigenvector
          haveI hnt : Nontrivial ↥(Module.End.eigenspace (TOpEnd' K hK) a) :=
            ⟨0, ⟨v, hv.1⟩, fun h => hv.2 (Subtype.ext_iff.mp h).symm⟩
          exact Module.finrank_pos
        have hm := hmult a (hLvS a ha).1 (hLvne a ha)
        rw [Nat.card_eq_zero_of_infinite] at hm
        exact absurd hm.symm (by omega)
      have hle : Nat.card {j : ℕ // val j = a}
          ≤ Module.finrank ℝ ↥(Module.End.eigenspace (TOpEnd' K hK) a) := by
        rw [hmult a (hLvS a ha).1 (hLvne a ha)]
      haveI : Fintype {j : ℕ // val j = a} := Fintype.ofFinite (α := {j : ℕ // val j = a})
      have hcardcoe : (u'.filter (fun j => a = val j)).card
          = Fintype.card {x : ℕ // x ∈ u'.filter (fun j => a = val j)} := (Fintype.card_coe _).symm
      have hfin1 : Fintype.card {x : ℕ // x ∈ u'.filter (fun j => a = val j)}
          ≤ Fintype.card {j : ℕ // val j = a} :=
        Fintype.card_le_of_injective
          (f := fun m : {x : ℕ // x ∈ u'.filter (fun j => a = val j)} =>
            (⟨m.1, (Finset.mem_filter.mp m.2).2.symm⟩ : {j : ℕ // val j = a}))
          (fun m m' h => Subtype.ext (by simpa using congrArg Subtype.val h))
      have hnat1 : Fintype.card {j : ℕ // val j = a}
          ≤ Nat.card {j : ℕ // val j = a} := le_of_eq Nat.card_eq_fintype_card.symm
      refine le_trans (le_trans (le_of_eq hcardcoe) (le_trans hfin1 hnat1)) hle
    -- the level-indexed norm computation
    have hnormlv : ∀ (a : ↥S) (i : Fin (Module.finrank ℝ ↥(Module.End.eigenspace (TOpEnd' K hK) a.val))),
        ‖TOp K hK (w ⟨a, i⟩)‖ ^ 2 = (a : ℝ) ^ 2 := by
      intro a i
      rw [hweig ⟨a, i⟩, norm_smul, Real.norm_eq_abs, hwnorm ⟨a, i⟩, mul_one, sq_abs]
    -- the spliced index set over the attained levels
    set T : Finset (spliceIdx (TOpEnd' K hK) S) := Lv.attach.biUnion (fun a =>
      (Finset.univ : Finset (Fin (Module.finrank ℝ ↥(Module.End.eigenspace (TOpEnd' K hK) (a : ℝ))))).image
        (fun i => (⟨⟨(a : ℝ), hLvS a.1 a.2⟩, i⟩ : spliceIdx (TOpEnd' K hK) S))) with hTdef
    have hdisj : Set.PairwiseDisjoint (↑Lv.attach) (fun a : ↥Lv =>
      (Finset.univ : Finset (Fin (Module.finrank ℝ ↥(Module.End.eigenspace (TOpEnd' K hK) (a : ℝ))))).image
        (fun i => (⟨⟨(a : ℝ), hLvS a.1 a.2⟩, i⟩ : spliceIdx (TOpEnd' K hK) S))) := by
      intro a _ b _ hab
      refine Finset.disjoint_iff_ne.mpr fun σ hσ σ' hσ' heq => hab ?_
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hσ
      obtain ⟨i', -, rfl⟩ := Finset.mem_image.mp hσ'
      have hfs : (⟨(a : ℝ), hLvS a.1 a.2⟩ : ↥S) = ⟨(b : ℝ), hLvS b.1 b.2⟩ :=
        congrArg Sigma.fst heq
      have hrr : (a : ℝ) = (b : ℝ) := (congrArg (Subtype.val : ↥S → ℝ) hfs)
      exact Subtype.ext hrr
    calc ∑ j ∈ u, val j ^ 2 = ∑ j ∈ u', val j ^ 2 := hstep1
      _ = ∑ a ∈ Lv, ∑ j ∈ u', (if a = val j then val j ^ 2 else 0) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [Finset.sum_ite_eq']
          have hmem : val j ∈ Lv := Finset.mem_image_of_mem _ hj
          rw [if_pos hmem]
      _ = ∑ a ∈ Lv, (a : ℝ) ^ 2 * ↑(u'.filter (fun j => a = val j)).card := by
          refine Finset.sum_congr rfl fun a ha => ?_
          have h1 : ∀ j ∈ u'.filter (fun j => a = val j),
              (if a = val j then val j ^ 2 else 0) = val j ^ 2 :=
            fun j hj => if_pos (Finset.mem_filter.mp hj).2
          have h2 : ∑ j ∈ u'.filter (fun j => a = val j),
              (if a = val j then val j ^ 2 else 0)
              = ∑ j ∈ u', (if a = val j then val j ^ 2 else 0) :=
            (Finset.sum_subset (Finset.filter_subset (fun j => a = val j) u') (fun j hj hjf => by
              rw [if_neg (fun hc => hjf (Finset.mem_filter.mpr ⟨hj, hc⟩))]))
          have h3 : ∑ j ∈ u'.filter (fun j => a = val j), val j ^ 2
              = (a : ℝ) ^ 2 * ↑(u'.filter (fun j => a = val j)).card := by
            rw [Finset.sum_congr rfl (fun (j : ℕ) (hj : j ∈ u'.filter (fun j' => a = val j')) =>
              by rw [(Finset.mem_filter.mp hj).2])), Finset.sum_const, nsmul_eq_mul, mul_comm]
          have h4 : ∑ j ∈ u', (if a = val j then val j ^ 2 else 0)
              = ∑ j ∈ u'.filter (fun j' => a = val j'), val j ^ 2 := by
            rw [← h2]
            refine Finset.sum_congr rfl fun (j : ℕ) (hj : j ∈ u'.filter (fun j' => a = val j')) => ?_
            rw [(Finset.mem_filter.mp hj).2]
            exact if_pos rfl
          rw [h4, ← h3]
      _ ≤ ∑ σ ∈ T, ‖TOp K hK (w σ)‖ ^ 2 := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun a ha => ?_) (fun σ _ => sq_nonneg _)
          have hcomp2 : (a : ℝ) ^ 2 * ↑(u'.filter (fun j => a = val j)).card
              ≤ ∑ i ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ ↥(Module.End.eigenspace (TOpEnd' K hK) a))))),
                (a : ℝ) ^ 2 := by
            rw [← hcomp]
            exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (hfible a ha)) (sq_nonneg a)
          rw [← hsumimg, hcomp2]
      _ ≤ hsNorm K ^ 2 := hsNorm_sq_ge_sum_norm_sq_of_orthonormal hwON _
  -- bounded partial sums of a nonnegative series converge
  exact summable_of_sum_le (fun j => sq_nonneg (val j)) hub

/-- **The multiplicity-exact spectral sequence carries the `Summable λ²` clause**:
packaging `exists_multiplicity_enumeration` with the spliced-Bessel summability —
the `Summable (λ j, λ_j²)` clause of `IsRieszSpectrumSequence` on the constructed
spectrum. -/
theorem exists_multiplicity_enumeration_summable
    (hCompact : IsCompactOperator (TOp K hK))
    (hsym : (↑(TOp K hK) : L2 →ₗ[ℝ] L2).IsSymmetric) :
    ∃ val : ℕ → ℝ, ∃ vec : ℕ → L2,
      (∀ j, val j = 0 ∨ Module.End.HasEigenvector (TOpEnd' K hK) (val j) (vec j)) ∧
      (∀ μ : ℝ, Module.End.HasEigenvalue (TOpEnd' K hK) μ → μ ≠ 0 →
        Nat.card {j : ℕ // val j = μ}
          = Module.finrank ℝ (Module.End.eigenspace (TOpEnd' K hK) μ)) ∧
      Summable (fun j => val j ^ 2) := by
  obtain ⟨val, vec, h1, h2⟩ := exists_multiplicity_enumeration hCompact hsym
  exact ⟨val, vec, h1, h2,
    summable_val_sq_of_multiplicityEnumeration hCompact hsym h1 h2⟩

end HS

end
