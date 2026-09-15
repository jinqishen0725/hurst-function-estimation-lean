import Hurst.RieszCompactEnumeration
import Hurst.FrozenSpectralCount
import Hurst.HSNormIdentity
import Hurst.CycleTraceIdentification
import Hurst.HSCycleComposition
import Hurst.RieszSpectralTrace

/-!
# P2 close-out: the constructed spectrum of the uniform-`ω` Riesz kernel

This file assembles the **constructed** spectrum of the compact self-adjoint operator
`T = TOp K_R` of the uniform-`ω` truncated weighted Riesz kernel
`K_R = HS.rieszKernel psi c omega` (the encoding of `Hurst.HSOperatorFoundation` /
`Hurst.HSOperatorLayer2`: `L2 = L²(vol)`, `vol2 = vol.prod vol`, `hsNorm K = ‖K‖_{L²(vol2)}`),
and states honestly which clauses of the P2 contract
(`Hurst.IsRieszSpectrumSequence`, `Hurst.P2SpectrumConstruction`) close now.

## The constructed spectrum

* `HS.rieszSpectrumVal` / `HS.rieszSpectrumVec` (packaged as `HS.rieszSpectrumOf`) — the
  multiplicity-exact enumeration `HS.exists_multiplicity_enumeration` of
  `Hurst.FrozenSpectralCount`, instantiated at the Riesz operator with
  `hCompact := isCompactOperator_TOp_riesz` (the landed Riesz compactness of
  `Hurst.RieszCompactEnumeration`) and
  `hsym := isSymmetric_TOp_rieszKernel` (the landed self-adjointness).  The zero-extension
  is built into the enumeration: every entry is `0` or a nonzero eigenvalue with its unit
  eigenvector, and the degenerate case (no nonzero spectrum) yields the identically-zero
  sequence.  Each nonzero eigenvalue `μ` occurs exactly `finrank (eigenspace μ)` times.

## Clause status

* **(i) nonnegativity — CONDITIONAL (documented).**  `HS.rieszSpectrum_nonneg_of_posTOp`:
  `0 ≤ rieszSpectrumVal j` holds under the operator-positivity hypothesis
  `∀ f, 0 ≤ ⟪T f, f⟫` (the landed Rayleigh lemma `eigenvalue_nonneg_of_pos`).  The
  unconditional statement is FALSE in `omega`: for `omega ≡ -1` the odd cycle integrals are
  the negatives of the unit-weight ones (`HS.nonneg_spectrum_forces_odd_cycle_nonneg`,
  `Hurst.P2SpectrumConstruction`), so a nonnegative spectrum cannot match them.  The PSD of
  the uniform-`ω` kernel (the Fourier route) remains deferred exactly as documented in
  `Hurst.HSOperatorLayer4` / `Hurst.P2SpectrumConstruction`; for SIGNED spectra the
  even-power peeling chain of `Hurst.EvenPeeling` covers the matching (`Σ λ^k = Σ |λ|^k`
  at even `k`, cofinal in the tail).
* **(ii) `Summable (fun j => val j ^ 2)` — PROVED.**  `HS.rieszSpectrum_sq_summable`, via
  the ON-splice/Bessel chain re-landed here (`HS.exists_orthonormal_eigenFamily` +
  `HS.sum_val_sq_le_hsNorm_sq_of_multEnum`): the spliced family of unit eigenvectors over
  the nonzero spectrum is orthonormal (within a level by the `stdOrthonormalBasis` of the
  finite-dimensional eigenspace, across levels by the landed
  `inner_eigenvector_eq_zero_of_ne`), the finite Bessel bound
  `hsNorm_sq_ge_sum_norm_sq_of_orthonormal` bounds every partial sum
  `∑_{j ∈ u} val j² ≤ hsNorm K_R²` through the level-fiber counts
  `#{j ∈ u | val j = μ} ≤ finrank (eigenspace μ)` (from the multiplicity clause), and
  bounded partial sums of a nonnegative series give summability.  The tsum form
  `∑' j, val j² ≤ hsNorm K_R²` is `HS.rieszSpectrum_sq_tsum_le_hsNorm_sq`.
  (This re-lands the chain of `Hurst.EigenSplice`, whose module does not build — a
  `rw [Finset.sum_const]` higher-order-unification failure in its penultimate step; the
  step is reproved here with an explicit-value `Finset.sum_const` rewrite.)
* **(iii) `HasSum` at `k = 2` — PROVED UP TO THE PARSEVAL EQUALITY; the honest closed form
  is the upper bound.**  `HS.rieszSpectrum_two_tsum_le_cycleIntegral`:
  `∑' j, val j² ≤ weightedRieszCycleIntegral 2 psi c omega`, by
  `HS.rieszSpectrum_sq_tsum_le_hsNorm_sq` and the landed identification
  `HS.weightedRieszCycleIntegral_two_eq_hsNorm_sq` (`Hurst.RieszSpectralTrace`):
  `weightedRieszCycleIntegral 2 psi c omega = hsNorm K_R²`.  Upgrading the inequality to
  the `HasSum`-with-that-target clause of `IsWeightedRieszSpectrum` needs the REVERSE
  inequality `hsNorm K_R² ≤ ∑' val j²` — the kernel expansion
  `K_R = ∑_σ μ_σ (w_σ ⊗ w_σ)` in `L²(vol2)` (Parseval of the tensor family), the isolated
  gap documented in `Hurst.HSNormIdentity` (equality half), `Hurst.CycleTraceIdentification`
  (the isolated product-basis Parseval gap) and `Hurst.RieszSpectralTrace` (gap report:
  the a.e. section formula `(T f) x = ∫ K(x,y) f y ∂vol` is not landed).
* **general `k ≥ 3` — DOCUMENTED BOUNDARY.**  The composition peel induction
  (`C_{k}(K) = C_{k-1}(compKernel K K)`, peeling one kernel factor per step) is architected
  in the gap report of `Hurst.HSCycleComposition` with its analytic ingredients landed
  (`hsNorm_comp_le`, `integral_compKernel_diag`, the `k = 2` anchors `cycleIntegral_two` /
  `cycle2_self_sq`, the `k = 3` expansions `cycle2_compKernel_eq_triple` modulo the
  `hA`/`hB` integrability discharges); the `HasSum` at general `k` follows once that
  induction completes.  `HS.rieszSpectrumSequence_full_of_powerHasSums` packages the exact
  consumption: given the `k = 2` `HasSum` and the general-`k` `HasSum`s as hypotheses, the
  full `Hurst.IsRieszSpectrumSequence` contract closes
  (`HS.isRieszSpectrumSequence_of_hasSum`).
-/

open MeasureTheory Measure Real Set
open scoped Real

noncomputable section

namespace HS

/-! ### The ON-splice layer (re-land of the `EigenSplice` chain, repaired) -/

variable {K : ℝ × ℝ → ℝ} {hK : HSKernel K}

/-- The spliced index type: a nonzero eigenvalue (an element of `S`) together with an
index into an orthonormal basis of its eigenspace. -/
abbrev spliceIdxP2 (TE : Module.End ℝ L2) (S : Set ℝ) : Type :=
  Σ a : ↥S, Fin (Module.finrank ℝ (Module.End.eigenspace TE a.val))

set_option maxHeartbeats 1000000 in
/-- **The ON-splice lemma**: the orthonormal bases of the (finite-dimensional)
eigenspaces of the compact symmetric kernel operator, indexed by
`Fin (finrank (eigenspace μ))`, splice over any set `S` of nonzero eigenvalues into ONE
orthonormal family `w` of unit eigenvectors: `TOp K hK (w σ) = σ.1.val • w σ` and
`‖w σ‖ = 1`.  Orthogonality within a level is the eigenspace basis; across levels it is
`inner_eigenvector_eq_zero_of_ne`. -/
theorem exists_orthonormal_eigenFamily (hCompact : IsCompactOperator (TOp K hK))
    (hsym : (↑(TOp K hK) : L2 →ₗ[ℝ] L2).IsSymmetric)
    (S : Set ℝ) (hS : ∀ a : ↥S, Module.End.HasEigenvalue (TOpEnd' K hK) a.val ∧ a.val ≠ 0) :
    ∃ w : spliceIdxP2 (TOpEnd' K hK) S → L2,
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
  have hnorm : ∀ σ : spliceIdxP2 (TOpEnd' K hK) S, ‖((B σ.1) σ.2 : L2)‖ = 1 :=
    fun σ => (Submodule.norm_coe (B σ.1 σ.2)).trans ((B σ.1).orthonormal.1 σ.2)
  -- in particular every spliced vector is nonzero
  have hnz : ∀ σ : spliceIdxP2 (TOpEnd' K hK) S, ((B σ.1) σ.2 : L2) ≠ 0 :=
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
/-- **The finite Bessel bound for the multiplicity-exact enumeration**: if `val : ℕ → ℝ`
enumerates eigenvalues of the compact symmetric kernel operator (each entry `0` or an
eigenvalue with its eigenvector `vec`), and every nonzero eigenvalue `μ` appears exactly
`finrank (eigenspace μ)` times (`Nat.card {j // val j = μ} = finrank (eigenspace μ)`),
then every finite partial sum satisfies `∑_{j ∈ u} val j² ≤ hsNorm K²`.

Proof: zero entries contribute nothing; the attained nonzero levels `Lv` are finitely many;
per level the fiber inside `u` injects into `{j // val j = μ}`, whose cardinality is the
eigenspace dimension; the level sums are caught by the Bessel sum of the spliced
orthonormal family (`exists_orthonormal_eigenFamily`), whose `T`-images have norm exactly
`|μ|`. -/
theorem sum_val_sq_le_hsNorm_sq_of_multEnum
    (hCompact : IsCompactOperator (TOp K hK))
    (hsym : (↑(TOp K hK) : L2 →ₗ[ℝ] L2).IsSymmetric)
    {val : ℕ → ℝ} {vec : ℕ → L2}
    (hval : ∀ j, val j = 0 ∨ Module.End.HasEigenvector (TOpEnd' K hK) (val j) (vec j))
    (hmult : ∀ μ : ℝ, Module.End.HasEigenvalue (TOpEnd' K hK) μ → μ ≠ 0 →
      Nat.card {j : ℕ // val j = μ}
        = Module.finrank ℝ (Module.End.eigenspace (TOpEnd' K hK) μ))
    (u : Finset ℕ) :
    ∑ j ∈ u, val j ^ 2 ≤ hsNorm K ^ 2 := by
  classical
  set S : Set ℝ := {μ : ℝ | Module.End.HasEigenvalue (TOpEnd' K hK) μ ∧ μ ≠ 0} with hSdef
  -- the spliced orthonormal family of unit eigenvectors over the nonzero spectrum
  obtain ⟨w, hwON, hb⟩ :=
    exists_orthonormal_eigenFamily hCompact hsym S (fun a => ⟨a.2.1, a.2.2⟩)
  have hweig : ∀ σ, TOp K hK (w σ) = σ.1.val • w σ := fun σ => (hb σ).1
  have hwnorm : ∀ σ, ‖w σ‖ = 1 := fun σ => (hb σ).2
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
    exact le_trans (le_of_eq hcardcoe) (le_trans hfin1 (le_trans hnat1 hle))
  -- the level-indexed norm computation: a spliced vector over level `a` has T-image `a • v`
  have hnormlv : ∀ (a : ↥S)
      (i : Fin (Module.finrank ℝ ↥(Module.End.eigenspace (TOpEnd' K hK) a.val))),
      ‖TOp K hK (w ⟨a, i⟩)‖ ^ 2 = (a : ℝ) ^ 2 := by
    intro a i
    rw [hweig ⟨a, i⟩, norm_smul, Real.norm_eq_abs, hwnorm ⟨a, i⟩, mul_one, sq_abs]
  -- the spliced index set over the attained levels
  set T : Finset (spliceIdxP2 (TOpEnd' K hK) S) := Lv.attach.biUnion (fun a : ↥Lv =>
    (Finset.univ : Finset (Fin (Module.finrank ℝ ↥(Module.End.eigenspace (TOpEnd' K hK) (a : ℝ))))).image
      (fun i => (⟨⟨(a : ℝ), hLvS a.1 a.2⟩, i⟩ : spliceIdxP2 (TOpEnd' K hK) S))) with hTdef
  -- the level images in `T` are pairwise disjoint (their `Sigma` first components differ)
  have hdisj : Set.PairwiseDisjoint
      (↑(Lv.attach) : Set ↥Lv)
      (fun a : ↥Lv =>
        (Finset.univ : Finset (Fin (Module.finrank ℝ ↥(Module.End.eigenspace (TOpEnd' K hK) (a : ℝ))))).image
          (fun i => (⟨⟨(a : ℝ), hLvS a.1 a.2⟩, i⟩ : spliceIdxP2 (TOpEnd' K hK) S))) := by
    intro x _ y _ hxy
    refine Finset.disjoint_left.mpr fun σ hx hy => ?_
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨i', -, hEq⟩ := Finset.mem_image.mp hy
    rw [Sigma.mk.injEq] at hEq
    exact hxy (Subtype.ext (congrArg (fun z : ↥S => z.1) hEq.1).symm)
  calc ∑ j ∈ u, val j ^ 2 = ∑ j ∈ u', val j ^ 2 := hstep1
    _ = ∑ a ∈ Lv, ∑ j ∈ u', (if a = val j then val j ^ 2 else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hmem : val j ∈ Lv := Finset.mem_image_of_mem _ hj
        have hsub : ∑ a ∈ {val j}, (if a = val j then val j ^ 2 else 0)
            = ∑ a ∈ Lv, (if a = val j then val j ^ 2 else 0) := by
          refine Finset.sum_subset (Finset.singleton_subset_iff.mpr hmem) ?_
          intro a ha han
          rw [if_neg (fun heq => han (Finset.mem_singleton.mpr heq))]
        rw [← hsub, Finset.sum_singleton, if_pos rfl]
    _ = ∑ a ∈ Lv, (a : ℝ) ^ 2 * (u'.filter (fun j => a = val j)).card := by
        refine Finset.sum_congr rfl fun a ha => ?_
        have hA : ∑ j ∈ u', (if a = val j then val j ^ 2 else 0)
            = ∑ j ∈ u', (if a = val j then (a : ℝ) ^ 2 else 0) := by
          refine Finset.sum_congr rfl fun j hj => ?_
          by_cases hm : a = val j
          · rw [if_pos hm, if_pos hm, hm]
          · rw [if_neg hm, if_neg hm]
        have hB : ∑ j ∈ u', (if a = val j then (a : ℝ) ^ 2 else 0)
            = ∑ j ∈ u'.filter (fun j => a = val j), (a : ℝ) ^ 2 := by
          have hB1 : ∑ j ∈ u'.filter (fun j => a = val j),
              (if a = val j then (a : ℝ) ^ 2 else 0)
              = ∑ j ∈ u', (if a = val j then (a : ℝ) ^ 2 else 0) :=
            Finset.sum_subset (Finset.filter_subset (fun j => a = val j) u') (fun j hj hjf =>
              by rw [if_neg (fun hc => hjf (Finset.mem_filter.mpr ⟨hj, hc⟩))])
          refine hB1.symm.trans (Finset.sum_congr rfl fun j hj => ?_)
          rw [if_pos (Finset.mem_filter.mp hj).2]
        have hC : ∑ j ∈ u'.filter (fun j => a = val j), (a : ℝ) ^ 2
            = (u'.filter (fun j => a = val j)).card • (a : ℝ) ^ 2 := Finset.sum_const _
        refine (hA.trans (hB.trans hC)).trans ?_
        rw [nsmul_eq_mul, mul_comm]
    _ ≤ ∑ a ∈ Lv, ∑ i ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ ↥(
              Module.End.eigenspace (TOpEnd' K hK) a)))), (a : ℝ) ^ 2 := by
        refine Finset.sum_le_sum fun a ha => ?_
        calc (a : ℝ) ^ 2 * ((u'.filter (fun j => a = val j)).card : ℝ)
            ≤ (a : ℝ) ^ 2
                * (Module.finrank ℝ ↥(Module.End.eigenspace (TOpEnd' K hK) a) : ℝ) :=
              mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (hfible a ha)) (sq_nonneg a)
          _ = ∑ i ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ ↥(
                Module.End.eigenspace (TOpEnd' K hK) a)))), (a : ℝ) ^ 2 := by
              rw [Finset.sum_const ((a : ℝ) ^ 2), Finset.card_univ, Fintype.card_fin,
                nsmul_eq_mul, mul_comm]
    _ ≤ ∑ x ∈ Lv.attach, ∑ i ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ ↥(
              Module.End.eigenspace (TOpEnd' K hK) (↑x))))), (↑x : ℝ) ^ 2 :=
        Eq.le (Finset.sum_attach Lv (fun a : ℝ => ∑ i ∈ (Finset.univ : Finset (Fin (
          Module.finrank ℝ ↥(Module.End.eigenspace (TOpEnd' K hK) a)))), (a : ℝ) ^ 2)).symm
    _ ≤ ∑ σ ∈ T, ‖TOp K hK (w σ)‖ ^ 2 := by
        rw [hTdef, Finset.sum_biUnion hdisj]
        refine Finset.sum_le_sum fun x hx => ?_
        have hinj : ∀ i ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ ↥(
                Module.End.eigenspace (TOpEnd' K hK) (↑x))))),
            ∀ i' ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ ↥(
                Module.End.eigenspace (TOpEnd' K hK) (↑x))))),
              (⟨⟨(↑x : ℝ), hLvS x.1 x.2⟩, i⟩ : spliceIdxP2 (TOpEnd' K hK) S)
                = (⟨⟨(↑x : ℝ), hLvS x.1 x.2⟩, i'⟩ : spliceIdxP2 (TOpEnd' K hK) S) → i = i' := by
          intro i _ i' _ h
          injection h with _ h2
        rw [Finset.sum_image hinj]
        exact Finset.sum_le_sum fun i _ =>
          (hnormlv (a := ⟨(↑x : ℝ), hLvS x.1 x.2⟩) (i := i)).symm.le
    _ ≤ hsNorm K ^ 2 := hsNorm_sq_ge_sum_norm_sq_of_orthonormal hwON T

/-- **The tsum form of the enumeration Bessel bound**:
`∑' j, val j² ≤ hsNorm K²` (all finite partial sums bounded, series nonnegative). -/
theorem tsum_val_sq_le_hsNorm_sq_of_multEnum
    (hCompact : IsCompactOperator (TOp K hK))
    (hsym : (↑(TOp K hK) : L2 →ₗ[ℝ] L2).IsSymmetric)
    {val : ℕ → ℝ} {vec : ℕ → L2}
    (hval : ∀ j, val j = 0 ∨ Module.End.HasEigenvector (TOpEnd' K hK) (val j) (vec j))
    (hmult : ∀ μ : ℝ, Module.End.HasEigenvalue (TOpEnd' K hK) μ → μ ≠ 0 →
      Nat.card {j : ℕ // val j = μ}
        = Module.finrank ℝ (Module.End.eigenspace (TOpEnd' K hK) μ)) :
    ∑' j, val j ^ 2 ≤ hsNorm K ^ 2 :=
  Real.tsum_le_of_sum_le (fun j => sq_nonneg (val j))
    (fun u => sum_val_sq_le_hsNorm_sq_of_multEnum hCompact hsym hval hmult u)

/-- **The `Summable (λ²)` clause for the multiplicity-exact enumeration**
(bounded partial sums of a nonnegative series). -/
theorem summable_val_sq_of_multEnum
    (hCompact : IsCompactOperator (TOp K hK))
    (hsym : (↑(TOp K hK) : L2 →ₗ[ℝ] L2).IsSymmetric)
    {val : ℕ → ℝ} {vec : ℕ → L2}
    (hval : ∀ j, val j = 0 ∨ Module.End.HasEigenvector (TOpEnd' K hK) (val j) (vec j))
    (hmult : ∀ μ : ℝ, Module.End.HasEigenvalue (TOpEnd' K hK) μ → μ ≠ 0 →
      Nat.card {j : ℕ // val j = μ}
        = Module.finrank ℝ (Module.End.eigenspace (TOpEnd' K hK) μ)) :
    Summable (fun j => val j ^ 2) :=
  summable_of_sum_le (fun j => sq_nonneg (val j))
    (fun u => sum_val_sq_le_hsNorm_sq_of_multEnum hCompact hsym hval hmult u)

end HS

section Riesz
open HS
namespace HS

/-! ### The constructed Riesz spectrum -/

variable (psi c : ℝ) (omega : ℝ → ℝ) (M : ℝ)

/-- The enumeration existence for the uniform-`ω` Riesz operator (the
multiplicity-exact enumeration of `Hurst.FrozenSpectralCount` at the Riesz operator,
with the summability clause of the spliced-Bessel chain). -/
theorem exists_multiplicity_enumeration_summable_riesz
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y) :
    ∃ val : ℕ → ℝ, ∃ vec : ℕ → L2,
      (∀ j, val j = 0 ∨ Module.End.HasEigenvector
        (TOpEnd' (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg))
        (val j) (vec j)) ∧
      (∀ μ : ℝ, Module.End.HasEigenvalue
        (TOpEnd' (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg)) μ →
        μ ≠ 0 →
        Nat.card {j : ℕ // val j = μ}
          = Module.finrank ℝ (Module.End.eigenspace
            (TOpEnd' (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg)) μ)) ∧
      Summable (fun j => val j ^ 2) := by
  obtain ⟨val, vec, h1, h2⟩ :=
    exists_multiplicity_enumeration
      (isCompactOperator_TOp_riesz hpow homega hbdd hg hconst)
      (isSymmetric_TOp_rieszKernel hpow homega hbdd hg hconst)
  exact ⟨val, vec, h1, h2,
    summable_val_sq_of_multEnum
      (isCompactOperator_TOp_riesz hpow homega hbdd hg hconst)
      (isSymmetric_TOp_rieszKernel hpow homega hbdd hg hconst) h1 h2⟩

/-- The value part of the constructed Riesz spectrum: the multiplicity-exact
eigenvalue enumeration of the compact self-adjoint Riesz operator
(`exists_multiplicity_enumeration_summable_riesz`, i.e. `Hurst.FrozenSpectralCount`'s
`exists_multiplicity_enumeration` at `isCompactOperator_TOp_riesz` /
`isSymmetric_TOp_rieszKernel`), extended by zeros (the enumeration's entries are `0` or
nonzero eigenvalues; trailing zeros pad and the degenerate case is identically zero). -/
noncomputable def rieszSpectrumVal
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y) :
    ℕ → ℝ :=
  @Classical.choose _ (fun val : ℕ → ℝ => ∃ vec : ℕ → L2,
      (∀ j, val j = 0 ∨ Module.End.HasEigenvector
        (TOpEnd' (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg))
        (val j) (vec j)) ∧
      (∀ μ : ℝ, Module.End.HasEigenvalue
        (TOpEnd' (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg)) μ →
        μ ≠ 0 →
        Nat.card {j : ℕ // val j = μ}
          = Module.finrank ℝ (Module.End.eigenspace
            (TOpEnd' (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg)) μ)) ∧
      Summable (fun j => val j ^ 2))
    (exists_multiplicity_enumeration_summable_riesz psi c omega M hpow homega hbdd hg hconst)

/-- The vector part of the constructed Riesz spectrum: the unit eigenvector matched to
each nonzero entry of `rieszSpectrumVal` (the zero-padded entries carry the zero vector). -/
noncomputable def rieszSpectrumVec
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y) :
    ℕ → L2 :=
  @Classical.choose _ (fun vec : ℕ → L2 =>
      (∀ j, rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j = 0 ∨
        Module.End.HasEigenvector
          (TOpEnd' (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg))
          (rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j) (vec j)) ∧
      (∀ μ : ℝ, Module.End.HasEigenvalue
        (TOpEnd' (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg)) μ →
        μ ≠ 0 →
        Nat.card {j : ℕ // rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j = μ}
          = Module.finrank ℝ (Module.End.eigenspace
            (TOpEnd' (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg)) μ)) ∧
      Summable (fun j => rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j ^ 2))
    (Classical.choose_spec (exists_multiplicity_enumeration_summable_riesz
      psi c omega M hpow homega hbdd hg hconst))

/-- The three spectral clauses of the constructed spectrum, bundled (the extraction of the
choice data: entries, multiplicity, and the `Summable (λ²)` clause). -/
theorem rieszSpectrum_pack
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y) :
    (∀ j, rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j = 0 ∨
        Module.End.HasEigenvector
          (TOpEnd' (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg))
          (rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j)
          (rieszSpectrumVec psi c omega M hpow homega hbdd hg hconst j))
    ∧ (∀ μ : ℝ, Module.End.HasEigenvalue
        (TOpEnd' (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg)) μ →
        μ ≠ 0 →
        Nat.card {j : ℕ // rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j = μ}
          = Module.finrank ℝ (Module.End.eigenspace
            (TOpEnd' (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg)) μ))
    ∧ Summable (fun j => rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j ^ 2) := by
  have h := exists_multiplicity_enumeration_summable_riesz psi c omega M hpow homega hbdd hg hconst
  have hvaleq : rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst
      = Classical.choose h := rfl
  have hveceq : rieszSpectrumVec psi c omega M hpow homega hbdd hg hconst
      = Classical.choose (Classical.choose_spec h) := rfl
  rw [hvaleq, hveceq]
  exact Classical.choose_spec (Classical.choose_spec h)

/-- The constructed spectrum as a `(value, vector)` pair `ℕ → ℝ × L2`. -/
noncomputable def rieszSpectrumOf
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y) :
    ℕ → ℝ × L2 :=
  fun j => (rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j,
    rieszSpectrumVec psi c omega M hpow homega hbdd hg hconst j)

/-- **Entry clause**: every entry of the constructed spectrum is `0` or a nonzero
eigenvalue with its (unit) eigenvector. -/
theorem rieszSpectrum_entry
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y)
    (j : ℕ) :
    rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j = 0 ∨
      Module.End.HasEigenvector
        (TOpEnd' (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg))
        (rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j)
        (rieszSpectrumVec psi c omega M hpow homega hbdd hg hconst j) :=
  (rieszSpectrum_pack psi c omega M hpow homega hbdd hg hconst).1 j

/-- **Multiplicity clause**: every nonzero eigenvalue `μ` of the Riesz operator appears
exactly `finrank (eigenspace μ)` times in the constructed spectrum. -/
theorem rieszSpectrum_multiplicity
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y)
    {μ : ℝ} (hμ : Module.End.HasEigenvalue
      (TOpEnd' (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg)) μ)
    (hμ0 : μ ≠ 0) :
    Nat.card {j : ℕ // rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j = μ}
      = Module.finrank ℝ (Module.End.eigenspace
        (TOpEnd' (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg)) μ) :=
  (rieszSpectrum_pack psi c omega M hpow homega hbdd hg hconst).2.1 μ hμ hμ0

/-- **(ii) CLOSED — square summability of the constructed spectrum**:
`Summable (fun j => rieszSpectrumVal j ^ 2)` (the spliced-family Bessel chain). -/
theorem rieszSpectrum_sq_summable
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y) :
    Summable (fun j => rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j ^ 2) :=
  (rieszSpectrum_pack psi c omega M hpow homega hbdd hg hconst).2.2

/-- The finite Bessel bound for the constructed spectrum: every partial sum of the
squared spectrum is at most `hsNorm K_R²`. -/
theorem rieszSpectrum_sq_sum_le_hsNorm_sq
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y)
    (u : Finset ℕ) :
    ∑ j ∈ u, rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j ^ 2
      ≤ hsNorm (rieszKernel psi c omega) ^ 2 :=
  sum_val_sq_le_hsNorm_sq_of_multEnum
    (isCompactOperator_TOp_riesz hpow homega hbdd hg hconst)
    (isSymmetric_TOp_rieszKernel hpow homega hbdd hg hconst)
    (rieszSpectrum_entry psi c omega M hpow homega hbdd hg hconst)
    (fun _μ hμ hμ0 =>
      rieszSpectrum_multiplicity psi c omega M hpow homega hbdd hg hconst hμ hμ0) u

/-- The tsum Bessel bound for the constructed spectrum:
`∑' j, rieszSpectrumVal j² ≤ hsNorm K_R²`. -/
theorem rieszSpectrum_sq_tsum_le_hsNorm_sq
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y) :
    ∑' j, rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j ^ 2
      ≤ hsNorm (rieszKernel psi c omega) ^ 2 :=
  tsum_val_sq_le_hsNorm_sq_of_multEnum
    (isCompactOperator_TOp_riesz hpow homega hbdd hg hconst)
    (isSymmetric_TOp_rieszKernel hpow homega hbdd hg hconst)
    (rieszSpectrum_entry psi c omega M hpow homega hbdd hg hconst)
    (fun _μ hμ hμ0 =>
      rieszSpectrum_multiplicity psi c omega M hpow homega hbdd hg hconst hμ hμ0)

/-- **(iii) at `k = 2`, honest closed form**: the sum of the squared spectrum is at most
the `k = 2` weighted Riesz cycle integral —
`∑' j, rieszSpectrumVal j² ≤ weightedRieszCycleIntegral 2 psi c omega`,
by the tsum Bessel bound and the landed identification
`weightedRieszCycleIntegral 2 psi c omega = hsNorm K_R²`
(`weightedRieszCycleIntegral_two_eq_hsNorm_sq`).  The upgrade of this inequality to the
`HasSum`-with-target clause requires the reverse Parseval inequality (the kernel expansion
`K_R = ∑_σ μ_σ (w_σ ⊗ w_σ)` in `L²(vol2)`) — the documented boundary. -/
theorem rieszSpectrum_two_tsum_le_cycleIntegral
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y) :
    ∑' j, rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j ^ 2
      ≤ Hurst.weightedRieszCycleIntegral 2 psi c omega := by
  rw [weightedRieszCycleIntegral_two_eq_hsNorm_sq hconst]
  exact rieszSpectrum_sq_tsum_le_hsNorm_sq psi c omega M hpow homega hbdd hg hconst

/-- **(i) CONDITIONAL — nonnegativity of the constructed spectrum** under operator
positivity (`hPos`: `∀ f, 0 ≤ ⟪T f, f⟫`, the landed Rayleigh form
`eigenvalue_nonneg_of_pos`).  Unconditionally FALSE in `omega` (the `omega ≡ -1`
odd-cycle obstruction of `Hurst.P2SpectrumConstruction`); the PSD of the uniform-`ω`
kernel stays deferred (Fourier route, `Hurst.HSOperatorLayer4`), and signed spectra are
covered by the even-power peeling of `Hurst.EvenPeeling`. -/
theorem rieszSpectrum_nonneg_of_posTOp
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y)
    (hPos : ∀ f : L2, 0 ≤ inner ℝ
      (TOp (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg) f) f)
    (j : ℕ) :
    0 ≤ rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j := by
  rcases rieszSpectrum_entry psi c omega M hpow homega hbdd hg hconst j with h0 | hv
  · rw [h0]
  · exact eigenvalue_nonneg_of_pos hPos (Module.End.hasEigenvalue_of_hasEigenvector hv)

/-- **The honest two-closed package for the constructed spectrum**:

* the entry clause and the multiplicity-exactness of the enumeration (proved);
* **(ii)** `Summable (fun j => val j ^ 2)` and its `HasSum` form to the own tsum (proved);
* **(iii, `k = 2`)** the closed upper bound
  `∑' val² ≤ weightedRieszCycleIntegral 2 psi c omega` (proved); the full
  `HasSum … (weightedRieszCycleIntegral 2 psi c omega)` needs the reverse Parseval
  inequality `hsNorm K_R² ≤ ∑' val j²` (the kernel expansion in `L²(vol2)`) — NOT landed;
* **(i)** nonnegativity under the operator-positivity hypothesis `hPos` (conditional; the
  unconditional clause is false in `omega`, PSD deferred, signed route `EvenPeeling`);
* **general `k ≥ 3`** — not stated: needs the composition peel induction architected in
  the gap report of `Hurst.HSCycleComposition` (ingredients landed there:
  `hsNorm_comp_le`, `integral_compKernel_diag`, `cycleIntegral_two`; plus the same
  Parseval-type expansion for the operator-side trace pairing,
  `Hurst.CycleTraceIdentification`).

Consumption shape: `HS.rieszSpectrumSequence_full_of_powerHasSums` shows the full
`Hurst.IsRieszSpectrumSequence` contract closes once the `k = 2` `HasSum` and the
general-`k` `HasSum`s are supplied. -/
theorem rieszSpectrumSequence_twoClosed
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y) :
    (∀ j, rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j = 0 ∨
        Module.End.HasEigenvector
          (TOpEnd' (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg))
          (rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j)
          (rieszSpectrumVec psi c omega M hpow homega hbdd hg hconst j))
    ∧ (∀ μ : ℝ, Module.End.HasEigenvalue
        (TOpEnd' (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg)) μ →
        μ ≠ 0 →
        Nat.card {j : ℕ // rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j = μ}
          = Module.finrank ℝ (Module.End.eigenspace
            (TOpEnd' (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg)) μ))
    ∧ Summable (fun j => rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j ^ 2)
    ∧ HasSum (fun j => rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j ^ 2)
        (∑' j, rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j ^ 2)
    ∧ (∑' j, rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j ^ 2
        ≤ Hurst.weightedRieszCycleIntegral 2 psi c omega)
    ∧ ((∀ f : L2, 0 ≤ inner ℝ
          (TOp (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg) f) f) →
        ∀ j, 0 ≤ rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j) := by
  refine ⟨rieszSpectrum_entry psi c omega M hpow homega hbdd hg hconst,
    fun μ hμ hμ0 =>
      rieszSpectrum_multiplicity psi c omega M hpow homega hbdd hg hconst hμ hμ0,
    rieszSpectrum_sq_summable psi c omega M hpow homega hbdd hg hconst,
    (rieszSpectrum_sq_summable psi c omega M hpow homega hbdd hg hconst).hasSum,
    rieszSpectrum_two_tsum_le_cycleIntegral psi c omega M hpow homega hbdd hg hconst,
    rieszSpectrum_nonneg_of_posTOp psi c omega M hpow homega hbdd hg hconst⟩

/-- **The exact consumption boundary, as a theorem**: the constructed spectrum satisfies
the FULL P2 contract `Hurst.IsRieszSpectrumSequence` as soon as the two missing
identifications are supplied — the `k = 2` `HasSum` to the cycle integral (needs the
reverse Parseval inequality: `hsNorm K_R² ≤ ∑' val j²`, i.e. the kernel expansion
`K_R = ∑_σ μ_σ (w_σ ⊗ w_σ)`) and the general-`k ≥ 3` `HasSum`s (needs the composition peel
induction of `Hurst.HSCycleComposition`).  Nonnegativity is taken from the operator
positivity (`rieszSpectrum_nonneg_of_posTOp`). -/
theorem rieszSpectrumSequence_full_of_powerHasSums
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y)
    (hPos : ∀ f : L2, 0 ≤ inner ℝ
      (TOp (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg) f) f)
    (h2 : HasSum (fun j => rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j ^ 2)
      (Hurst.weightedRieszCycleIntegral 2 psi c omega))
    (hgen : ∀ k : ℕ, 2 ≤ k → HasSum
      (fun j => rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j ^ k)
      (Hurst.weightedRieszCycleIntegral k psi c omega)) :
    Hurst.IsRieszSpectrumSequence psi c omega
      (rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst) :=
  isRieszSpectrumSequence_of_hasSum
    (rieszSpectrum_nonneg_of_posTOp psi c omega M hpow homega hbdd hg hconst hPos) h2 hgen

end HS
end Riesz

end
