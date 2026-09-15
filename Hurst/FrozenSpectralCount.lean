import Hurst.FrozenSpectralEnumeration

/-!
# Set-level counting for the frozen spectral enumeration

The choice-plumbing layer on top of `Hurst.FrozenSpectralEnumeration`, closing the
documented gap "set-level finiteness / countability / enumeration existence":

* `HS.eigenvalue_set_finite` — for every `ε > 0` the set of eigenvalues of modulus
  `≥ ε` is **finite**: an infinite one would contain an injective eigenvalue sequence
  with unit eigenvectors (via `Set.Infinite.natEmbedding` and the landed
  `hasEigenvector_norm_inv`), contradicting `HS.not_injective_eigenvalues_ge`;
* `HS.eigenvalue_set_countable` — the nonzero eigenvalues form a **countable** set,
  as the countable union `⋃ n, {μ | HasEigenvalue μ ∧ 1/(n+1) ≤ |μ|}` of the finite
  levels (`Set.countable_iUnion`);
* `HS.exists_multiplicity_enumeration` — a sequence `val : ℕ → ℝ` with matching
  eigenvectors `vec : ℕ → L2` in which every nonzero eigenvalue `μ` appears **exactly
  `Module.finrank ℝ (eigenspace μ)` times** (`Nat.card {j // val j = μ} = finrank …`).
  Entries are either `0` or nonzero eigenvalues with their eigenvectors; trailing zeros
  pad the finitely-many-eigenvalues case, and the identically-zero sequence covers the
  degenerate case (no nonzero eigenvalues).  As documented in
  `Hurst.FrozenSpectralEnumeration`, no nonincreasing rearrangement is needed: the
  P2 `HasSum` consumption is order-insensitive for nonnegative entries.
-/

open MeasureTheory Measure Real Set
open scoped Real

noncomputable section

namespace HS

variable {K : ℝ × ℝ → ℝ} {hK : HSKernel K}

/-! ### A unit eigenvector for every eigenvalue -/

/-- Every eigenvalue of the kernel operator admits a **unit** eigenvector
(per-eigenvalue `exists_hasEigenvector` + `hasEigenvector_norm_inv`). -/
theorem exists_unit_hasEigenvector {μ : ℝ}
    (hμ : Module.End.HasEigenvalue (TOpEnd' K hK) μ) :
    ∃ e : L2, Module.End.HasEigenvector (TOpEnd' K hK) μ e ∧ ‖e‖ = 1 := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  exact ⟨‖v‖⁻¹ • v, (hasEigenvector_norm_inv hv).1, (hasEigenvector_norm_inv hv).2⟩

/-! ### Item 1: set-level finiteness -/

set_option maxHeartbeats 1000000 in
/-- **Finiteness**: for every `ε > 0`, the eigenvalues of the kernel operator of
modulus `≥ ε` form a finite set. -/
theorem eigenvalue_set_finite (hCompact : IsCompactOperator (TOp K hK))
    (hsym : (↑(TOp K hK) : L2 →ₗ[ℝ] L2).IsSymmetric)
    {ε : ℝ} (hε : 0 < ε) :
    Set.Finite {μ : ℝ | Module.End.HasEigenvalue (TOpEnd' K hK) μ ∧ ε ≤ |μ|} := by
  by_contra hinf
  -- an injective eigenvalue sequence inside the set (embedding ℕ into the infinite set)
  obtain ⟨val, hmem, hinj⟩ :
      ∃ val : ℕ → ℝ,
        (∀ n, val n ∈ {μ : ℝ | Module.End.HasEigenvalue (TOpEnd' K hK) μ ∧ ε ≤ |μ|}) ∧
          Function.Injective val := by
    have f := Set.Infinite.natEmbedding
      {μ : ℝ | Module.End.HasEigenvalue (TOpEnd' K hK) μ ∧ ε ≤ |μ|} hinf
    exact ⟨fun n => (f n : ℝ), fun n => (f n).2,
      fun i j hij => f.injective (Subtype.ext hij)⟩
  -- unit eigenvectors, one per sequence entry
  have hpair : ∀ n : ℕ, Module.End.HasEigenvalue (TOpEnd' K hK) (val n) ∧ ε ≤ |val n| :=
    fun n => Set.mem_setOf.mp (hmem n)
  choose e he1 he2 using fun n : ℕ => exists_unit_hasEigenvector (hpair n).1
  exact not_injective_eigenvalues_ge hCompact hsym hε val e he1 he2
    (fun n => (hpair n).2) hinj

/-! ### Item 2: countability of the nonzero eigenvalues -/

/-- **Countability**: the nonzero eigenvalues of the compact symmetric kernel operator
form a countable set, as the countable union of the finite levels
`{μ | HasEigenvalue μ ∧ 1/(n+1) ≤ |μ|}`. -/
theorem eigenvalue_set_countable (hCompact : IsCompactOperator (TOp K hK))
    (hsym : (↑(TOp K hK) : L2 →ₗ[ℝ] L2).IsSymmetric) :
    Set.Countable {μ : ℝ | Module.End.HasEigenvalue (TOpEnd' K hK) μ ∧ μ ≠ 0} := by
  have hEq : {μ : ℝ | Module.End.HasEigenvalue (TOpEnd' K hK) μ ∧ μ ≠ 0}
      = ⋃ n : ℕ, {μ : ℝ | Module.End.HasEigenvalue (TOpEnd' K hK) μ ∧ 1 / (n + 1) ≤ |μ|} := by
    ext μ
    constructor
    · rintro ⟨hμ, hμ0⟩
      have habs : 0 < |μ| := abs_pos.mpr hμ0
      obtain ⟨n, hn⟩ := exists_nat_gt (1 / |μ|)
      refine Set.mem_iUnion.mpr ⟨n, Set.mem_setOf.mpr ⟨hμ, ?_⟩⟩
      have hn' : (1:ℝ) / |μ| ≤ (n:ℝ) + 1 := by linarith
      have h2 : (1:ℝ) = |μ| * (1 / |μ|) := by
        rw [one_div]
        exact (mul_inv_cancel₀ (ne_of_gt habs)).symm
      have hkey : (1:ℝ) ≤ |μ| * ((n:ℝ) + 1) := by
        calc (1:ℝ) = |μ| * (1 / |μ|) := h2
          _ ≤ |μ| * ((n:ℝ) + 1) := mul_le_mul_of_nonneg_left hn' (abs_nonneg μ)
      exact (div_le_iff₀ (show (0:ℝ) < (n:ℝ) + 1 by positivity)).mpr hkey
    · intro hmem2
      obtain ⟨n, hmu2⟩ := Set.mem_iUnion.mp hmem2
      obtain ⟨hμe, hn⟩ := Set.mem_setOf.mp hmu2
      refine ⟨hμe, fun hzero => ?_⟩
      rw [hzero, abs_zero] at hn
      have hpos : 0 < (1:ℝ) / (n + 1) := by positivity
      linarith
  rw [hEq]
  exact Set.countable_iUnion fun n =>
    (eigenvalue_set_finite hCompact hsym
      (show (0:ℝ) < 1 / (n + 1) by positivity)).countable

/-! ### Item 3: multiplicity-exact enumeration -/

/-- The multiplicity index type: a nonzero eigenvalue (as an element of `S`) together
with an index into its finite-dimensional eigenspace. -/
abbrev multIdx (TE : Module.End ℝ L2) (S : Set ℝ) : Type :=
  Σ a : ↥S, Fin (Module.finrank ℝ (Module.End.eigenspace TE a.val))

/-- Generic counting: the `μ'`-fiber of the multiplicity index type has the cardinality
of the `μ'`-eigenspace index type. -/
private theorem natCard_multIdx_fiber (TE : Module.End ℝ L2) (S : Set ℝ) (μ' : ↥S) :
    Nat.card {σ : multIdx TE S // σ.1.val = μ'.val}
      = Nat.card (Fin (Module.finrank ℝ (Module.End.eigenspace TE μ'.val))) :=
  Nat.card_congr
    { toFun := fun σ =>
        cast (congrArg (fun x : ℝ => Fin (Module.finrank ℝ (Module.End.eigenspace TE x))) σ.2)
          σ.1.2
      invFun := fun k => ⟨⟨μ', k⟩, rfl⟩
      left_inv := by
        rintro ⟨⟨⟨a, ha⟩, k⟩, hk⟩
        exact Subtype.ext (by
          rw [Sigma.mk.injEq]
          exact ⟨Subtype.ext hk.symm, cast_heq _ k⟩)
      right_inv := fun _ => rfl }

/-- The enumeration value map: entries over the range of the section `ρ` read off `fv`,
everything else is `0`. -/
private noncomputable def enumVal {ι : Type} (ρ : ι → ℕ) (hρinj : Function.Injective ρ)
    (fv : ι → ℝ) (j : ℕ) : ℝ :=
  @dite _ (j ∈ Set.range ρ) (Classical.propDecidable _)
    (fun h => fv ((Equiv.ofInjective ρ hρinj).symm ⟨j, h⟩)) (fun _ => 0)

/-- The matching eigenvector map (same shape as `enumVal`). -/
private noncomputable def enumVec {ι : Type} (ρ : ι → ℕ) (hρinj : Function.Injective ρ)
    (w : ι → L2) (j : ℕ) : L2 :=
  @dite _ (j ∈ Set.range ρ) (Classical.propDecidable _)
    (fun h => w ((Equiv.ofInjective ρ hρinj).symm ⟨j, h⟩)) (fun _ => 0)

private theorem enumVal_of_mem {ι : Type} {ρ : ι → ℕ} (hρinj : Function.Injective ρ)
    {fv : ι → ℝ} {j : ℕ} (hj : j ∈ Set.range ρ) :
    enumVal ρ hρinj fv j = fv ((Equiv.ofInjective ρ hρinj).symm ⟨j, hj⟩) := dif_pos hj

private theorem enumVal_of_notMem {ι : Type} {ρ : ι → ℕ} (hρinj : Function.Injective ρ)
    {fv : ι → ℝ} {j : ℕ} (hj : j ∉ Set.range ρ) :
    enumVal ρ hρinj fv j = 0 := dif_neg hj

private theorem enumVec_of_mem {ι : Type} {ρ : ι → ℕ} (hρinj : Function.Injective ρ)
    {w : ι → L2} {j : ℕ} (hj : j ∈ Set.range ρ) :
    enumVec ρ hρinj w j = w ((Equiv.ofInjective ρ hρinj).symm ⟨j, hj⟩) := dif_pos hj

private theorem enumVec_of_notMem {ι : Type} {ρ : ι → ℕ} (hρinj : Function.Injective ρ)
    {w : ι → L2} {j : ℕ} (hj : j ∉ Set.range ρ) :
    enumVec ρ hρinj w j = 0 := dif_neg hj

set_option maxHeartbeats 1000000 in
/-- **Multiplicity-exact enumeration**: there is a sequence `val : ℕ → ℝ` with matching
`vec : ℕ → L2` such that

* every entry is either `0` or a nonzero eigenvalue **with its eigenvector**;
* every nonzero eigenvalue `μ` is enumerated **exactly
  `Module.finrank ℝ (eigenspace μ)` times**: `Nat.card {j // val j = μ} = finrank …`.

The construction: the multiplicity index type `multIdx` (nonzero eigenvalues × an
eigenspace basis index) is countable (countable base by item 2, finite fibers by
`finiteDimensional_eigenspace_TOp`); a surjection `ℕ → multIdx` yields an injective
section `ρ`, the maps `val`/`vec` read off the section, and the fiber bijection
`{j // val j = μ} ≃ {σ // σ.1.val = μ}` plus `natCard_multIdx_fiber` and
`Nat.card_fin` finish the count.  Trailing zeros pad; the identically-zero sequence
covers the degenerate case. -/
theorem exists_multiplicity_enumeration (hCompact : IsCompactOperator (TOp K hK))
    (hsym : (↑(TOp K hK) : L2 →ₗ[ℝ] L2).IsSymmetric) :
    ∃ val : ℕ → ℝ, ∃ vec : ℕ → L2,
      (∀ j, val j = 0 ∨ Module.End.HasEigenvector (TOpEnd' K hK) (val j) (vec j)) ∧
      (∀ μ : ℝ, Module.End.HasEigenvalue (TOpEnd' K hK) μ → μ ≠ 0 →
        Nat.card {j : ℕ // val j = μ}
          = Module.finrank ℝ (Module.End.eigenspace (TOpEnd' K hK) μ)) := by
  classical
  set S : Set ℝ := {μ : ℝ | Module.End.HasEigenvalue (TOpEnd' K hK) μ ∧ μ ≠ 0} with hS
  have hScount : S.Countable := eigenvalue_set_countable hCompact hsym
  haveI : Countable ↥S := hScount.to_subtype
  -- a unit eigenvector for each nonzero eigenvalue
  choose u hu1 hu2 using fun (a : ↥S) =>
    exists_unit_hasEigenvector
      (show Module.End.HasEigenvalue (TOpEnd' K hK) a.val from a.2.1)
  -- nontrivial nonzero eigenspaces, hence positive finrank
  have hdimp : ∀ a : ↥S,
      0 < Module.finrank ℝ (Module.End.eigenspace (TOpEnd' K hK) a.val) := by
    intro a
    haveI : Module.Finite ℝ (Module.End.eigenspace (TOpEnd' K hK) a.val) :=
      finiteDimensional_eigenspace_TOp hCompact (show a.val ≠ 0 from a.2.2)
    haveI : Nontrivial (Module.End.eigenspace (TOpEnd' K hK) a.val) :=
      ⟨0, ⟨u a, (hu1 a).1⟩, fun h => (hu1 a).2 (Subtype.ext_iff.mp h).symm⟩
    exact Module.finrank_pos
  -- the multiplicity index type is countable (countable base, finite fibers)
  haveI : ∀ a : ↥S,
      Countable (Fin (Module.finrank ℝ (Module.End.eigenspace (TOpEnd' K hK) a.val))) :=
    fun _ => inferInstance
  haveI : Countable (multIdx (TOpEnd' K hK) S) := inferInstance
  rcases isEmpty_or_nonempty (multIdx (TOpEnd' K hK) S) with hempty | hne
  · -- degenerate case: no nonzero eigenvalues — the identically-zero P2 sequence
    refine ⟨fun _ => 0, fun _ => 0, fun _ => Or.inl rfl, ?_⟩
    intro μ hμ hμ0
    exact (hempty.false
      (⟨⟨μ, hμ, hμ0⟩, ⟨0, hdimp ⟨μ, hμ, hμ0⟩⟩⟩ : multIdx (TOpEnd' K hK) S)).elim
  · -- main case: enumerate the multiplicity index type via a section of a surjection
    haveI : Nonempty (multIdx (TOpEnd' K hK) S) := hne
    obtain ⟨g, hg⟩ := exists_surjective_nat (multIdx (TOpEnd' K hK) S)
    obtain ⟨ρ, hρ⟩ := hg.hasRightInverse
    have hρinj : Function.Injective ρ := hρ.injective
    refine ⟨enumVal ρ hρinj (fun σ : multIdx (TOpEnd' K hK) S => σ.1.val),
      enumVec ρ hρinj (fun σ => u σ.1), ?_, ?_⟩
    · -- (i) every entry is 0 or a nonzero eigenvalue with its eigenvector
      intro j
      by_cases hj : j ∈ Set.range ρ
      · rw [enumVal_of_mem hρinj hj, enumVec_of_mem hρinj hj]
        exact Or.inr (hu1 ((Equiv.ofInjective ρ hρinj).symm ⟨j, hj⟩).1)
      · rw [enumVal_of_notMem hρinj hj, enumVec_of_notMem hρinj hj]
        exact Or.inl rfl
    · -- (ii) fibers have exactly the eigenspace dimension
      intro μ hμ hμ0
      -- the section is right inverse to the surjection; `Equiv.ofInjective` inverts it
      have heqsec : ∀ (j : ℕ) (hj : j ∈ Set.range ρ),
          ρ ((Equiv.ofInjective ρ hρinj).symm ⟨j, hj⟩) = j :=
        fun j hj => Equiv.apply_ofInjective_symm hρinj ⟨j, hj⟩
      have heq : ∀ q : {σ : multIdx (TOpEnd' K hK) S // σ.1.val = μ},
          (Equiv.ofInjective ρ hρinj).symm ⟨ρ q.1, Set.mem_range_self q.1⟩ = q.1 := by
        intro q
        have hEq1 : Equiv.ofInjective ρ hρinj q.1 = ⟨ρ q.1, Set.mem_range_self q.1⟩ :=
          Subtype.ext rfl
        rw [← hEq1]
        exact Equiv.symm_apply_apply _ _
      have hp1 : ∀ p : {j : ℕ // enumVal ρ hρinj
          (fun σ : multIdx (TOpEnd' K hK) S => σ.1.val) j = μ},
          p.1 ∈ Set.range ρ := by
        intro p
        have p2 : (if h : p.1 ∈ Set.range ρ then
            ((Equiv.ofInjective ρ hρinj).symm ⟨p.1, h⟩).1.val else (0:ℝ)) = μ := p.2
        by_contra hc
        rw [dif_neg hc] at p2
        exact absurd p2.symm hμ0
      have hp2 : ∀ p : {j : ℕ // enumVal ρ hρinj
          (fun σ : multIdx (TOpEnd' K hK) S => σ.1.val) j = μ},
          ((Equiv.ofInjective ρ hρinj).symm ⟨p.1, hp1 p⟩).1.val = μ := fun p =>
        (enumVal_of_mem (fv := fun σ : multIdx (TOpEnd' K hK) S => σ.1.val) hρinj
          (hp1 p)).symm.trans p.2
      have hE : Nat.card {j : ℕ // enumVal ρ hρinj
          (fun σ : multIdx (TOpEnd' K hK) S => σ.1.val) j = μ}
          = Nat.card {σ : multIdx (TOpEnd' K hK) S // σ.1.val = μ} := by
        refine Nat.card_congr ⟨fun p => ⟨(Equiv.ofInjective ρ hρinj).symm ⟨p.1, hp1 p⟩, hp2 p⟩,
          fun q => ⟨ρ q.1, ?_⟩, ?_, ?_⟩
        · have hm : ρ q.1 ∈ Set.range ρ := Set.mem_range_self q.1
          rw [enumVal_of_mem hρinj hm, heq q]
          exact q.2
        · intro p
          exact Subtype.ext (heqsec p.1 (hp1 p))
        · intro q
          exact Subtype.ext (heq q)
      refine Eq.trans hE ?_
      refine Eq.trans (natCard_multIdx_fiber (TOpEnd' K hK) S ⟨μ, hμ, hμ0⟩) ?_
      exact Nat.card_fin _

end HS

end
