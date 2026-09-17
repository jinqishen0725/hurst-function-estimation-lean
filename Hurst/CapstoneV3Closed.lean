import Hurst.EigenFamilySplice
import Hurst.P2SpectrumV2
import Hurst.CapstoneV3
import Hurst.LevelCakeTransfer

/-!
# Capstone v3 CLOSED: the `k = 2` exact bridge `hTwo` discharged

This file discharges the honest boundary hypothesis `hTwo` of
`Hurst.CapstoneV3.actualQ1LongStatistic_tendsto_secondChaos_v3` — the `k = 2` exact
spectral bridge `HasSum (fun j => val j ^ 2) (weightedRieszCycleIntegral 2 …)` for the
constructed P2 enumeration `HS.rieszSpectrumVal` — by assembling the LANDED Parseval
chain:

1. **Section-family completeness** (`Hurst.TensorONBCompleteness.sections_complete`,
   discharged unconditional);
2. **The constructed complete ON eigenfamily** (`Hurst.EigenFamilySplice.exists_complete_eigenfamily`,
   unconditional at the Riesz operator, ending in `hsNorm K_R² = ∑' i, κ i²`);
3. **The multiplicity comparison** (landed HERE, `HS.tsum_kappaSq_eq_tsum_valSq`): the
   energy of the complete eigenfamily equals the energy of the multiplicity-exact
   enumeration `∑' j, val j²` — both series group level-by-level into
   `∑_{μ eigenvalue ≠ 0} finrank (eigenspace μ) · μ²`.  The `κ`-fiber cardinality is
   computed exactly (`HS.natCard_kappaFiber_eq_finrank`: linear independence from
   orthonormality gives `≤`, and the completeness of `v` — every eigenvector of a level
   is orthogonal to the fiber's span outside it, hence `y ⊥ range v → y = 0` — gives
   `≥` through `Module.Basis` + `finrank_eq_card_basis`);
4. **The reverse Parseval inequality** `hsNorm K_R² ≤ ∑' j, val j²` follows as an
   EQUALITY, and `HS.hasSum_two_exact_iff_reverseParseval`
   (`Hurst.P2SpectrumV2`) promotes it to the exact `k = 2` `HasSum`.

## Main results

* `HS.natCard_kappaFiber_eq_finrank` — the `κ`-fiber cardinal identity.
* `HS.tsum_kappaSq_eq_tsum_valSq` — the multiplicity comparison of the two energies.
* `HS.rieszSpectrum_two_hasSum_cycle_closed` — **THE DISCHARGE**: for the constructed
  Riesz enumeration, `HasSum (fun j => val j ^ 2) (weightedRieszCycleIntegral 2 …)`,
  unconditionally in the Riesz data.
* `Hurst.actualQ1LongStatistic_tendsto_secondChaos_v3_closed` — capstone v3 verbatim
  MINUS `hTwo`, with the discharged `HasSum` delivered as an additional conclusion
  conjunct; the remaining spectral hypotheses are exactly `hPos` (the conditional
  nonnegativity clause) and `hGen` (the general-`k` bridge, `Hurst.HSCycleComposition`
  residue), plus `hAnti`/`hane`/`hwnn`.
* `Hurst.actualQ1LongStatistic_tendsto_secondChaos_v3_closed_degreeOne` — the `r = 1`
  variant with `hwnn` discharged from the balanced-window moment criterion
  (`Hurst.SpectralWeightNonneg`).
* `Hurst.actualQ1LongStatistic_tendsto_secondChaos_v3_closed_antitone` — the RESORTED
  form: stated at `lam := Hurst.antitoneResort val` with `hAnti` DISCHARGED by
  construction (`Hurst.AntitoneResort`) and the `k = 2`/general-`k` `HasSum`s
  transported by the level-cake transfer (`Hurst.LevelCakeTransfer`), so the remaining
  spectral hypotheses are exactly `hPos` + `hGen` (about the raw enumeration) +
  `hane`/`hwnn`.
-/

set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Measure Real Set Submodule
open scoped Real

namespace HS

variable {K : ℝ × ℝ → ℝ} {hK : HSKernel K}

/-! ### A. The finite fiber-group identity -/

/-- **The fiber-group identity**: the squared sum over a finite set groups by level:
`∑ x ∈ t, g x² = ∑ μ ∈ t.image g, #{x ∈ t | μ = g x} · μ²`. -/
private theorem finset_sum_sq_fiberGroup {α : Type*} [DecidableEq α]
    (t : Finset α) (g : α → ℝ) :
    ∑ x ∈ t, g x ^ 2
      = ∑ μ ∈ t.image g, (t.filter (fun x => μ = g x)).card * μ ^ 2 := by
  have step1 : ∑ x ∈ t, g x ^ 2
      = ∑ μ ∈ t.image g, ∑ x ∈ t, (if μ = g x then g x ^ 2 else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hmem : g x ∈ t.image g := Finset.mem_image_of_mem _ hx
    have hsub : ∑ μ ∈ {g x}, (if μ = g x then g x ^ 2 else 0)
        = ∑ μ ∈ t.image g, (if μ = g x then g x ^ 2 else 0) := by
      refine Finset.sum_subset (Finset.singleton_subset_iff.mpr hmem) ?_
      intro a ha han
      rw [if_neg (fun heq => han (Finset.mem_singleton.mpr heq))]
    rw [← hsub, Finset.sum_singleton, if_pos rfl]
  refine step1.trans (Finset.sum_congr rfl fun μ _ => ?_)
  have hA : ∑ x ∈ t, (if μ = g x then g x ^ 2 else 0)
      = ∑ x ∈ t, (if μ = g x then μ ^ 2 else 0) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hm : μ = g x
    · rw [if_pos hm, if_pos hm, hm]
    · rw [if_neg hm, if_neg hm]
  have hB : ∑ x ∈ t, (if μ = g x then μ ^ 2 else 0)
      = ∑ x ∈ t.filter (fun x => μ = g x), μ ^ 2 := by
    have hB1 : ∑ x ∈ t.filter (fun x => μ = g x), (if μ = g x then μ ^ 2 else 0)
        = ∑ x ∈ t, (if μ = g x then μ ^ 2 else 0) :=
      Finset.sum_subset (Finset.filter_subset (fun x => μ = g x) t) (fun x hxmem hx' => by
        refine if_neg (fun hc => hx' ?_)
        exact Finset.mem_filter.mpr ⟨hxmem, hc⟩)
    refine hB1.symm.trans (Finset.sum_congr rfl fun x hx => ?_)
    exact if_pos (Finset.mem_filter.mp hx).2
  rw [hA, hB, Finset.sum_const _, nsmul_eq_mul]

/-! ### B. The `κ`-fiber cardinal identity -/

/-- The nonzero-`κ`-level fiber is finite (an infinite one would give a linearly
independent family in a finite-dimensional eigenspace indexed by `ℕ`). -/
private theorem kappaFiber_finite
    (hCompact : IsCompactOperator (TOp K hK))
    {ι : Type} {v : ι → L2} {κ : ι → ℝ}
    (hv : Orthonormal ℝ v) (he : ∀ i, TOp K hK (v i) = κ i • v i)
    {μ : ℝ} (_hμev : Module.End.HasEigenvalue (TOpEnd' K hK) μ) (hμ0 : μ ≠ 0) :
    ({i : ι | κ i = μ} : Set ι).Finite := by
  by_contra hinf
  haveI hfd := finiteDimensional_eigenspace_TOp hCompact hμ0
  haveI hI : ({i : ι | κ i = μ} : Set ι).Infinite := hinf
  obtain ⟨f, hf⟩ := hI.natEmbedding
  -- the composed family `v ∘ (coe ∘ f)` is orthonormal in L2 and lives in the eigenspace
  have hcoeinj : Function.Injective (fun n : ℕ => ((f n : {i : ι // κ i = μ}) : ι)) := by
    intro a b hab
    exact hf (Subtype.ext hab)
  have hON : Orthonormal ℝ (fun n : ℕ => v ((f n : {i : ι // κ i = μ}) : ι)) :=
    hv.comp _ hcoeinj
  have hwmem : ∀ n : ℕ,
      v ((f n : {i : ι // κ i = μ}) : ι) ∈ Module.End.eigenspace (TOpEnd' K hK) μ := by
    intro n
    refine Module.End.mem_eigenspace_iff.mpr ?_
    exact (he _).trans (congrArg (fun z : ℝ => z • v _) (Set.mem_setOf.mp (f n).2))
  have hLI2 : LinearIndependent ℝ
      (fun n : ℕ => (⟨v ((f n : {i : ι // κ i = μ}) : ι), hwmem n⟩ :
        ↥(Module.End.eigenspace (TOpEnd' K hK) μ))) := by
    refine LinearIndependent.of_comp
      (Module.End.eigenspace (TOpEnd' K hK) μ).subtype ?_
    have hfe : ((Module.End.eigenspace (TOpEnd' K hK) μ).subtype ∘
        fun n : ℕ => (⟨v ((f n : {i : ι // κ i = μ}) : ι), hwmem n⟩ :
          ↥(Module.End.eigenspace (TOpEnd' K hK) μ)))
        = (fun n : ℕ => v ((f n : {i : ι // κ i = μ}) : ι)) := by
      funext n; rfl
    rw [hfe]
    exact hON.linearIndependent
  exact absurd (LinearIndependent.cardinalMk_le_finrank (R := ℝ) hLI2)
    (by rw [Cardinal.mk_nat]; exact not_le.mpr Cardinal.natCast_lt_aleph0)

/-- **The `κ`-fiber cardinal identity**: for the complete orthonormal eigenfamily
`(v, κ)` of the compact symmetric kernel operator, each nonzero eigenvalue `μ` is
attained on EXACTLY `finrank (eigenspace μ)` indices:
`Nat.card {i // κ i = μ} = finrank (eigenspace μ)`.  (`≤` from linear independence of
the fiber family; `≥` from the completeness of `v`: a vector of the eigenspace
orthogonal to the fiber family is orthogonal to every `v i`, hence `= 0`.) -/
theorem natCard_kappaFiber_eq_finrank
    (hCompact : IsCompactOperator (TOp K hK))
    (hsym : (↑(TOp K hK) : L2 →ₗ[ℝ] L2).IsSymmetric)
    {ι : Type} {v : ι → L2} {κ : ι → ℝ}
    (hv : Orthonormal ℝ v) (he : ∀ i, TOp K hK (v i) = κ i • v i)
    (hcomp : (span ℝ (Set.range v))ᗮ = ⊥)
    {μ : ℝ} (hμev : Module.End.HasEigenvalue (TOpEnd' K hK) μ) (hμ0 : μ ≠ 0) :
    Nat.card {i : ι // κ i = μ}
      = Module.finrank ℝ (Module.End.eigenspace (TOpEnd' K hK) μ) := by
  classical
  haveI hfd := finiteDimensional_eigenspace_TOp hCompact hμ0
  set W := Module.End.eigenspace (TOpEnd' K hK) μ with hW
  have hvz : ∀ i : ι, v i ≠ 0 := fun i => norm_ne_zero_iff.mp (by rw [hv.1 i]; norm_num)
  have hve : ∀ i : ι, Module.End.HasEigenvector (TOpEnd' K hK) (κ i) (v i) := fun i =>
    Module.End.hasEigenvector_iff.mpr ⟨(mem_eigenspace_TOp_iff (v i) (μ := κ i)).mpr (he i), hvz i⟩
  have hwmem : ∀ x : {i : ι // κ i = μ}, v (x : ι) ∈ W := fun x => by
    refine Module.End.mem_eigenspace_iff.mpr ?_
    exact (he x.1).trans (congrArg (fun z : ℝ => z • v (x : ι)) x.2)
  set w : {i : ι // κ i = μ} → ↥W := fun x => ⟨v (x : ι), hwmem x⟩ with hwdef
  -- linear independence of the fiber family (in W)
  have hwON : Orthonormal ℝ (fun x : {i : ι // κ i = μ} => v (x : ι)) :=
    hv.comp Subtype.val Subtype.val_injective
  have hfe : (W.subtype ∘ w) = (fun x : {i : ι // κ i = μ} => v (x : ι)) := by
    funext x; rfl
  have hwLI : LinearIndependent ℝ w := by
    refine LinearIndependent.of_comp W.subtype ?_
    rw [hfe]
    exact hwON.linearIndependent
  -- finiteness of the fiber
  have hFfin : ({i : ι | κ i = μ} : Set ι).Finite :=
    kappaFiber_finite hCompact hv he hμev hμ0
  haveI hsubF : Finite {i : ι // κ i = μ} := hFfin.to_subtype
  haveI : Fintype {i : ι // κ i = μ} := Fintype.ofFinite _
  -- the fiber family spans W: a vector of W orthogonal to it is orthogonal to all of v
  have hspW : (span ℝ (Set.range w))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    by_cases hy0 : (y : L2) = 0
    · exact Subtype.ext hy0
    · have hyEV : Module.End.HasEigenvector (TOpEnd' K hK) μ (y : L2) :=
        Module.End.hasEigenvector_iff.mpr ⟨y.2, hy0⟩
      have hyall : ∀ i : ι, inner ℝ (v i) (y : L2) = 0 := by
        intro i
        by_cases himem : κ i = μ
        · have hmemrange : w ⟨i, himem⟩ ∈ span ℝ (Set.range w) :=
            Submodule.subset_span (Set.mem_range.mpr ⟨⟨i, himem⟩, rfl⟩)
          have h1 : inner ℝ (w ⟨i, himem⟩) y = 0 :=
            (Submodule.mem_orthogonal (span ℝ (Set.range w)) y).mp hy _ hmemrange
          have h2 : inner ℝ ((w ⟨i, himem⟩ : L2)) (y : L2)
              = inner ℝ (w ⟨i, himem⟩) y := (Submodule.coe_inner _ _ _).symm
          show inner ℝ ((w ⟨i, himem⟩ : L2)) (y : L2) = 0
          rw [h2]
          exact h1
        · exact (real_inner_comm (v i) (y : L2)).symm.trans
            (inner_eigenvector_eq_zero_of_ne hsym hyEV (hve i)
              (fun h => himem h.symm))
      have hyOrtho : (y : L2) ∈ (span ℝ (Set.range v))ᗮ := by
        rw [Submodule.mem_orthogonal]
        intro z hz
        induction hz using Submodule.span_induction with
        | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hyall i
        | zero => simp
        | add x z _ _ hx hz2 => rw [inner_add_left, hx, hz2, add_zero]
        | smul c x _ hx => rw [real_inner_smul_left, hx, mul_zero]
      rw [hcomp] at hyOrtho
      rw [Submodule.mem_bot ℝ] at hyOrtho
      exact Subtype.ext hyOrtho
  -- conclude: the fiber family is a basis of W
  have htop : span ℝ (Set.range w) = ⊤ := Submodule.orthogonal_eq_bot_iff.mp hspW
  have hBasis : Module.Basis {i : ι // κ i = μ} ℝ ↥W :=
    Module.Basis.mk hwLI (le_of_eq htop.symm)
  calc Nat.card {i : ι // κ i = μ}
      = Fintype.card {i : ι // κ i = μ} := Nat.card_eq_fintype_card
    _ = Module.finrank ℝ ↥W := (Module.finrank_eq_card_basis hBasis).symm

/-! ### C. The multiplicity comparison of the two energies -/

/-- **The multiplicity comparison**: the complete-eigenfamily energy equals the
multiplicity-exact enumeration energy,
`∑' i, κ i² = ∑' j, val j²`.  Both series group level-by-level into
`∑_{μ eigenvalue ≠ 0} finrank (eigenspace μ) · μ²`; the `κ`-side uses
`natCard_kappaFiber_eq_finrank`, the `val`-side the multiplicity-exactness
`Nat.card {j // val j = μ} = finrank (eigenspace μ)`. -/
theorem tsum_kappaSq_eq_tsum_valSq
    (hCompact : IsCompactOperator (TOp K hK))
    (hsym : (↑(TOp K hK) : L2 →ₗ[ℝ] L2).IsSymmetric)
    {ι : Type} {v : ι → L2} {κ : ι → ℝ}
    (hv : Orthonormal ℝ v) (he : ∀ i, TOp K hK (v i) = κ i • v i)
    (hcomp : (span ℝ (Set.range v))ᗮ = ⊥)
    {val : ℕ → ℝ} {vec : ℕ → L2}
    (hval : ∀ j, val j = 0 ∨ Module.End.HasEigenvector (TOpEnd' K hK) (val j) (vec j))
    (hmult : ∀ μ : ℝ, Module.End.HasEigenvalue (TOpEnd' K hK) μ → μ ≠ 0 →
      Nat.card {j : ℕ // val j = μ}
        = Module.finrank ℝ (Module.End.eigenspace (TOpEnd' K hK) μ)) :
    (∑' i, κ i ^ 2) = (∑' j, val j ^ 2) := by
  classical
  have hvz : ∀ i : ι, v i ≠ 0 := fun i => norm_ne_zero_iff.mp (by rw [hv.1 i]; norm_num)
  have hve : ∀ i : ι, Module.End.HasEigenvector (TOpEnd' K hK) (κ i) (v i) := fun i =>
    Module.End.hasEigenvector_iff.mpr ⟨(mem_eigenspace_TOp_iff (v i) (μ := κ i)).mpr (he i), hvz i⟩
  have hSm : Summable (fun i : ι => κ i ^ 2) := by
    have hfe : ∀ i : ι, κ i ^ 2 = ‖TOp K hK (v i)‖ ^ 2 := by
      intro i
      rw [he i, norm_smul, Real.norm_eq_abs, hv.1 i, mul_one, sq_abs]
    have h2 : Summable (fun i : ι => ‖TOp K hK (v i)‖ ^ 2) :=
      summable_of_sum_le (fun i => sq_nonneg _) (fun s => sum_norm_TOp_sq_le hv s)
    exact h2.congr (fun i => (hfe i).symm)
  have hSmV : Summable (fun j : ℕ => val j ^ 2) :=
    summable_val_sq_of_multEnum hCompact hsym hval hmult
  -- a nonzero level attained by `κ` is a nonzero eigenvalue
  have hLvEVκ : ∀ (s : Finset ι) {μ : ℝ}, μ ∈ (s.filter (fun i => κ i ≠ 0)).image κ →
      Module.End.HasEigenvalue (TOpEnd' K hK) μ ∧ μ ≠ 0 := by
    intro s μ hμ
    obtain ⟨i, hi, hμκ⟩ := Finset.mem_image.mp hμ
    have hκne : κ i ≠ 0 := (Finset.mem_filter.mp hi).2
    have hev := Module.End.hasEigenvalue_of_hasEigenvector (hve i)
    rw [hμκ] at hev
    exact ⟨hev, fun h => hκne (hμκ.trans h)⟩
  -- the eigenspace over an attained level is nontrivial, hence positive-dimensional
  have hfrPos : ∀ {μ : ℝ}, Module.End.HasEigenvalue (TOpEnd' K hK) μ → μ ≠ 0 →
      0 < Module.finrank ℝ (Module.End.eigenspace (TOpEnd' K hK) μ) := by
    intro μ hμev hμ0
    haveI hfd := finiteDimensional_eigenspace_TOp hCompact hμ0
    obtain ⟨w, hw⟩ := hμev.exists_hasEigenvector
    haveI : Nontrivial ↥(Module.End.eigenspace (TOpEnd' K hK) μ) :=
      ⟨0, ⟨w, hw.1⟩, fun h => hw.2 (Subtype.ext_iff.mp h).symm⟩
    exact Module.finrank_pos
  -- the val-side fiber set is finite (from the multiplicity identity)
  have hvalFfin : ∀ {μ : ℝ}, Module.End.HasEigenvalue (TOpEnd' K hK) μ → μ ≠ 0 →
      ({j : ℕ | val j = μ} : Set ℕ).Finite := by
    intro μ hμev hμ0
    by_contra hinf
    haveI hI : ({j : ℕ | val j = μ} : Set ℕ).Infinite := hinf
    haveI hsub : Infinite {j : ℕ // val j = μ} := hI.to_subtype
    have h0 : Nat.card {j : ℕ // val j = μ} = 0 := Nat.card_eq_zero.mpr (Or.inr hsub)
    have hnc := hmult μ hμev hμ0
    rw [h0] at hnc
    exact absurd hnc.symm (by linarith [hfrPos hμev hμ0])
  -- the κ-side fiber set is finite
  have hκFfin : ∀ {μ : ℝ}, Module.End.HasEigenvalue (TOpEnd' K hK) μ → μ ≠ 0 →
      ({i : ι | κ i = μ} : Set ι).Finite :=
    fun hμev hμ0 => kappaFiber_finite hCompact hv he hμev hμ0
  -- direction (≤): the κ-energy is caught by the enumeration energy
  have hBound1 : ∀ s : Finset ι, ∑ i ∈ s, κ i ^ 2 ≤ ∑' j, val j ^ 2 := by
    intro s
    set s' := s.filter (fun i => κ i ≠ 0) with hs'
    have hdrop : ∑ i ∈ s, κ i ^ 2 = ∑ i ∈ s', κ i ^ 2 :=
      (Finset.sum_subset (Finset.filter_subset (fun i => κ i ≠ 0) s) (fun i hi hi' => by
        have h0 : κ i = 0 := by
          by_contra hne
          exact hi' (Finset.mem_filter.mpr ⟨hi, hne⟩)
        rw [h0]; norm_num)).symm
    set Lv : Finset ℝ := s'.image κ with hLv
    have hLvE : ∀ μ ∈ Lv, Module.End.HasEigenvalue (TOpEnd' K hK) μ ∧ μ ≠ 0 :=
      fun μ hμ => hLvEVκ s hμ
    -- the κ-fiber card is at most the enumeration card at the same level
    have hcard : ∀ μ : ℝ, Module.End.HasEigenvalue (TOpEnd' K hK) μ → μ ≠ 0 →
        (s'.filter (fun i => μ = κ i)).card ≤ Nat.card {j : ℕ // val j = μ} := by
      intro μ hμev hμ0
      haveI hfin : Fintype {i : ι // κ i = μ} :=
        @Fintype.ofFinite {i : ι // κ i = μ}
          (kappaFiber_finite hCompact hv he hμev hμ0).to_subtype
      have hinj : Function.Injective
          (fun m : {x : ι // x ∈ s'.filter (fun i => μ = κ i)} =>
            (⟨m.1, (Finset.mem_filter.mp m.2).2.symm⟩ : {i : ι // κ i = μ})) := by
        intro m m' h
        exact Subtype.ext (by simpa using congrArg Subtype.val h)
      calc (s'.filter (fun i => μ = κ i)).card
          = Fintype.card {x : ι // x ∈ s'.filter (fun i => μ = κ i)} :=
            (Fintype.card_coe _).symm
        _ ≤ Fintype.card {i : ι // κ i = μ} := Fintype.card_le_of_injective _ hinj
        _ = Nat.card {i : ι // κ i = μ} := Nat.card_eq_fintype_card.symm
        _ = Module.finrank ℝ (Module.End.eigenspace (TOpEnd' K hK) μ) :=
            natCard_kappaFiber_eq_finrank hCompact hsym hv he hcomp hμev hμ0
        _ = Nat.card {j : ℕ // val j = μ} := (hmult μ hμev hμ0).symm
    -- per-level absorption into the enumeration fiber
    have hlevel : ∀ (μ : ℝ) (_hμev : Module.End.HasEigenvalue (TOpEnd' K hK) μ)
        (_hμ0 : μ ≠ 0), (s'.filter (fun i => μ = κ i)).card * μ ^ 2
          ≤ ∑ j ∈ (hvalFfin _hμev _hμ0).toFinset, val j ^ 2 := by
      intro μ hμev hμ0
      have hcard' := hcard μ hμev hμ0
      have hFfin := hvalFfin hμev hμ0
      haveI : Fintype ↥({j : ℕ | val j = μ} : Set ℕ) := hFfin.fintype
      have hsumF : ∑ j ∈ hFfin.toFinset, val j ^ 2 = hFfin.toFinset.card * μ ^ 2 := by
        have hall : ∀ j ∈ hFfin.toFinset, val j = μ := fun j hj =>
          hFfin.mem_toFinset.mp hj
        calc ∑ j ∈ hFfin.toFinset, val j ^ 2
            = ∑ j ∈ hFfin.toFinset, μ ^ 2 :=
              Finset.sum_congr rfl fun j hj => by rw [hall j hj]
          _ = hFfin.toFinset.card * μ ^ 2 := by rw [Finset.sum_const _, nsmul_eq_mul]
      have hcardF : hFfin.toFinset.card = Nat.card {j : ℕ // val j = μ} :=
        hFfin.card_toFinset.trans Nat.card_eq_fintype_card.symm
      calc (s'.filter (fun i => μ = κ i)).card * μ ^ 2
          ≤ Nat.card {j : ℕ // val j = μ} * μ ^ 2 :=
            mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard') (sq_nonneg μ)
        _ = ∑ j ∈ hFfin.toFinset, val j ^ 2 := by rw [hsumF, hcardF]
    -- assemble the level masses into the disjoint union of enumeration fibers
    set U : Finset ℕ := Lv.attach.biUnion (fun p : {x : ℝ // x ∈ Lv} =>
      ((hvalFfin (hLvE p.1 p.2).1 (hLvE p.1 p.2).2).toFinset)) with hUdef
    have hpd : Set.PairwiseDisjoint (↑Lv.attach : Set {x : ℝ // x ∈ Lv})
        fun p : {x : ℝ // x ∈ Lv} =>
          ((hvalFfin (hLvE p.1 p.2).1 (hLvE p.1 p.2).2).toFinset) := by
      intro x _ y _ hxy
      refine Set.Finite.disjoint_toFinset.mpr ?_
      rw [Set.disjoint_left]
      intro j hj1 hj2
      exact hxy (Subtype.ext (hj1.symm.trans hj2))
    calc ∑ i ∈ s, κ i ^ 2
        = ∑ μ ∈ Lv, (s'.filter (fun i => μ = κ i)).card * μ ^ 2 := by
          rw [hdrop, finset_sum_sq_fiberGroup]
      _ ≤ ∑ j ∈ U, val j ^ 2 := by
          rw [hUdef, Finset.sum_biUnion hpd, ← Finset.sum_attach]
          refine Finset.sum_le_sum fun p _hp => ?_
          exact hlevel p.1 (hLvE p.1 p.2).1 (hLvE p.1 p.2).2
      _ ≤ ∑' j, val j ^ 2 := Summable.sum_le_tsum _ (fun j _ => sq_nonneg _) hSmV
  -- direction (≥): the enumeration energy is caught by the κ-energy
  have hBound2 : ∀ u : Finset ℕ, ∑ j ∈ u, val j ^ 2 ≤ ∑' i, κ i ^ 2 := by
    intro u
    set u' := u.filter (fun j => val j ≠ 0) with hu'
    have hdrop : ∑ j ∈ u, val j ^ 2 = ∑ j ∈ u', val j ^ 2 :=
      (Finset.sum_subset (Finset.filter_subset (fun j => val j ≠ 0) u) (fun j hj hj' => by
        have h0 : val j = 0 := by
          by_contra hne
          exact hj' (Finset.mem_filter.mpr ⟨hj, hne⟩)
        rw [h0]; norm_num)).symm
    set Lv : Finset ℝ := u'.image val with hLv
    have hLvE : ∀ μ ∈ Lv, Module.End.HasEigenvalue (TOpEnd' K hK) μ ∧ μ ≠ 0 := by
      intro μ hμ
      obtain ⟨j0, hj0u, hjμ⟩ := Finset.mem_image.mp hμ
      have hvj0 : val j0 ≠ 0 := (Finset.mem_filter.mp hj0u).2
      refine ⟨?_, ?_⟩
      · rcases hval j0 with h0 | hv0
        · exact absurd h0 hvj0
        · exact Module.End.hasEigenvalue_of_hasEigenvector (by rw [← hjμ]; exact hv0)
      · rw [← hjμ]; exact hvj0
    -- the val-fiber inside u' is at most the full fiber
    have hcard : ∀ μ : ℝ, Module.End.HasEigenvalue (TOpEnd' K hK) μ → μ ≠ 0 →
        (u'.filter (fun j => val j = μ)).card ≤ Nat.card {j : ℕ // val j = μ} := by
      intro μ hμev hμ0
      haveI hfin : Fintype {j : ℕ // val j = μ} :=
        @Fintype.ofFinite {j : ℕ // val j = μ} (hvalFfin hμev hμ0).to_subtype
      have hinj : Function.Injective
          (fun m : {x : ℕ // x ∈ u'.filter (fun j => val j = μ)} =>
            (⟨m.1, (Finset.mem_filter.mp m.2).2⟩ : {j : ℕ // val j = μ})) := by
        intro m m' h
        exact Subtype.ext (by simpa using congrArg Subtype.val h)
      calc (u'.filter (fun j => val j = μ)).card
          = Fintype.card {x : ℕ // x ∈ u'.filter (fun j => val j = μ)} :=
            (Fintype.card_coe _).symm
        _ ≤ Fintype.card {j : ℕ // val j = μ} := Fintype.card_le_of_injective _ hinj
        _ = Nat.card {j : ℕ // val j = μ} := Nat.card_eq_fintype_card.symm
    -- per-level transport into the κ-fiber
    have hlevel : ∀ (μ : ℝ) (_hμev : Module.End.HasEigenvalue (TOpEnd' K hK) μ)
        (_hμ0 : μ ≠ 0), (u'.filter (fun j => val j = μ)).card * μ ^ 2
          ≤ ∑ i ∈ (hκFfin _hμev _hμ0).toFinset, κ i ^ 2 := by
      intro μ hμev hμ0
      have hcard' := hcard μ hμev hμ0
      have hcard2 : Nat.card {j : ℕ // val j = μ}
          = Nat.card {i : ι // κ i = μ} := by
        rw [hmult μ hμev hμ0,
          natCard_kappaFiber_eq_finrank hCompact hsym hv he hcomp hμev hμ0]
      have hκFfin := hκFfin hμev hμ0
      haveI : Fintype ↥({i : ι | κ i = μ} : Set ι) := hκFfin.fintype
      have hsumF : ∑ i ∈ hκFfin.toFinset, κ i ^ 2 = hκFfin.toFinset.card * μ ^ 2 := by
        have hall : ∀ i ∈ hκFfin.toFinset, κ i = μ := fun i hi =>
          hκFfin.mem_toFinset.mp hi
        calc ∑ i ∈ hκFfin.toFinset, κ i ^ 2
            = ∑ i ∈ hκFfin.toFinset, μ ^ 2 :=
              Finset.sum_congr rfl fun i hi => by rw [hall i hi]
          _ = hκFfin.toFinset.card * μ ^ 2 := by rw [Finset.sum_const _, nsmul_eq_mul]
      have hcardF : hκFfin.toFinset.card = Nat.card {i : ι // κ i = μ} :=
        hκFfin.card_toFinset.trans Nat.card_eq_fintype_card.symm
      calc (u'.filter (fun j => val j = μ)).card * μ ^ 2
          ≤ Nat.card {j : ℕ // val j = μ} * μ ^ 2 :=
            mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard') (sq_nonneg μ)
        _ = Nat.card {i : ι // κ i = μ} * μ ^ 2 := by rw [hcard2]
        _ = ∑ i ∈ hκFfin.toFinset, κ i ^ 2 := by rw [hsumF, hcardF]
    -- assemble the level masses into the disjoint union of κ-fibers
    set U : Finset ι := Lv.attach.biUnion (fun p : {x : ℝ // x ∈ Lv} =>
      ((hκFfin (hLvE p.1 p.2).1 (hLvE p.1 p.2).2).toFinset)) with hUdef
    have hpd : Set.PairwiseDisjoint (↑Lv.attach : Set {x : ℝ // x ∈ Lv})
        fun p : {x : ℝ // x ∈ Lv} =>
          ((hκFfin (hLvE p.1 p.2).1 (hLvE p.1 p.2).2).toFinset) := by
      intro x _ y _ hxy
      refine Set.Finite.disjoint_toFinset.mpr ?_
      rw [Set.disjoint_left]
      intro i hi1 hi2
      exact hxy (Subtype.ext (hi1.symm.trans hi2))
    calc ∑ j ∈ u, val j ^ 2
        = ∑ μ ∈ Lv, (u'.filter (fun j => val j = μ)).card * μ ^ 2 := by
          rw [hdrop, finset_sum_sq_fiberGroup]
          refine Finset.sum_congr rfl fun μ _ => ?_
          rw [Finset.filter_congr (fun j (_ : j ∈ u') => eq_comm :
            ∀ j ∈ u', μ = val j ↔ val j = μ)]
      _ ≤ ∑ i ∈ U, κ i ^ 2 := by
          rw [hUdef, Finset.sum_biUnion hpd, ← Finset.sum_attach]
          refine Finset.sum_le_sum fun p _hp => ?_
          exact hlevel p.1 (hLvE p.1 p.2).1 (hLvE p.1 p.2).2
      _ ≤ ∑' i, κ i ^ 2 := Summable.sum_le_tsum _ (fun i _ => sq_nonneg _) hSm
  exact le_antisymm
    (Real.tsum_le_of_sum_le (fun i => sq_nonneg (κ i)) hBound1)
    (Real.tsum_le_of_sum_le (fun j => sq_nonneg (val j)) hBound2)

end HS

section Riesz
open Set Filter MeasureTheory Matrix ProbabilityTheory
open scoped Topology RealInnerProductSpace Matrix.Norms.Frobenius
open HS
namespace Hurst

/-! ### D. THE DISCHARGE: the exact `k = 2` HasSum at the constructed enumeration -/

set_option maxHeartbeats 1000000 in
/-- **THE `hTwo` DISCHARGE**: for the constructed P2 enumeration
`HS.rieszSpectrumVal` of the uniform-`ω` Riesz operator, the exact `k = 2` bridge
`HasSum (fun j => val j ^ 2) (weightedRieszCycleIntegral 2 psi c omega)` holds
UNCONDITIONALLY in the Riesz data.  Route: the complete eigenfamily
(`HS.exists_complete_eigenfamily`) gives `hsNorm K_R² = ∑' i, κ i²`; the multiplicity
comparison (`HS.tsum_kappaSq_eq_tsum_valSq`) re-expresses it as `∑' j, val j²`; the
reverse Parseval inequality is then an EQUALITY, and
`HS.hasSum_two_exact_iff_reverseParseval` delivers the `HasSum`. -/
theorem rieszSpectrum_two_hasSum_cycle_closed
    (psi c : ℝ) (omega : ℝ → ℝ) (M : ℝ)
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y) :
    HasSum (fun j => rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j ^ 2)
      (Hurst.weightedRieszCycleIntegral 2 psi c omega) := by
  obtain ⟨ι, v, κ, hv, he, hcomp, hE⟩ :=
    exists_complete_eigenfamily (psi := psi) (c := c) (omega := omega) (M := M)
      hpow homega hbdd hg hconst
  have heq : (∑' j, rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j ^ 2)
      = hsNorm (rieszKernel psi c omega) ^ 2 :=
    (tsum_kappaSq_eq_tsum_valSq
      (isCompactOperator_TOp_riesz hpow homega hbdd hg hconst)
      (isSymmetric_TOp_rieszKernel hpow homega hbdd hg hconst) hv he hcomp
      (rieszSpectrum_entry psi c omega M hpow homega hbdd hg hconst)
      (fun μ hμ hμ0 =>
        rieszSpectrum_multiplicity psi c omega M hpow homega hbdd hg hconst hμ hμ0)).symm.trans
      hE.symm
  have hrev : hsNorm (rieszKernel psi c omega) ^ 2
      ≤ ∑' j, rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst j ^ 2 :=
    le_of_eq heq.symm
  exact (hasSum_two_exact_iff_reverseParseval psi c omega M hpow homega hbdd hg
    hconst).mpr hrev

/-! ### E. Capstone v3 CLOSED (general `r`, `hwnn` kept) -/

set_option maxHeartbeats 10000000 in
/-- **THE CAPSTONE V3, CLOSED**: `actualQ1LongStatistic_tendsto_secondChaos_v3` verbatim
MINUS `hTwo`.  The `k = 2` exact bridge is discharged by
`rieszSpectrum_two_hasSum_cycle_closed` (the landed Parseval chain: section-family
completeness + complete eigenfamily + multiplicity comparison) and delivered as the
THIRD conclusion conjunct.  Remaining hypotheses (the honest boundary): `hAnti`
(decreasing order), `hGen` (∀ `k ≥ 3` exact `HasSum`, the `Hurst.HSCycleComposition`
residue), `hPos` (operator positivity; the unconditional clause is false in `omega`),
plus `hane`/`hwnn`. -/
theorem actualQ1LongStatistic_tendsto_secondChaos_v3_closed
    (p a b M : ℝ) (r : ℕ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b)
    (hM : 0 ≤ M) (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hgrid : (1 - γ) * (2 - 2 * f t) < 2 - 2 * b)
    (MR : ℝ)
    (hpow : AEStronglyMeasurable
      (fun q : ℝ × ℝ => |q.1 - q.2| ^ (-(2 - 2 * f t))) HS.vol2)
    (homega : Measurable (equivalentKernel r))
    (hbdd : ∀ x : ℝ, |equivalentKernel r x| ≤ MR)
    (hg : Integrable (fun q : ℝ × ℝ => |q.1 - q.2| ^ (-2 * (2 - 2 * f t))) HS.vol2)
    (hconst : ∀ x y : ℝ, (HS.I : Set ℝ).indicator (equivalentKernel r) x
      = (HS.I : Set ℝ).indicator (equivalentKernel r) y)
    (hPos : ∀ g : HS.L2, 0 ≤ inner ℝ
      (HS.TOp (HS.rieszKernel (2 - 2 * f t) (f t * (2 * f t - 1)) (equivalentKernel r))
        (HS.hsKernel_rieszKernel hpow homega hbdd hg) g) g)
    (hAnti : Antitone (HS.rieszSpectrumVal (2 - 2 * f t) (f t * (2 * f t - 1))
      (equivalentKernel r) MR hpow homega hbdd hg hconst))
    (hGen : ∀ k : ℕ, 3 ≤ k → HasSum
      (fun j : ℕ => HS.rieszSpectrumVal (2 - 2 * f t) (f t * (2 * f t - 1))
        (equivalentKernel r) MR hpow homega hbdd hg hconst j ^ k)
      (weightedRieszCycleIntegral k (2 - 2 * f t) (f t * (2 * f t - 1))
        (equivalentKernel r)))
    (hane : ∀ (n : ℕ) (k : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card),
      ∑ i, actualQ1Coeff n ((n : ℝ) ^ (-γ)) t k i •
        actualQ1Obs f n (midpointSampleHurst f hf.1 n) i ≠ 0)
    (hwnn : ∀ᶠ n : ℕ in atTop,
      ∀ i : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
      0 ≤ actualQ1SpectralWeight f r n ((n : ℝ) ^ (-γ)) t i) :
    Summable (fun j : ℕ => HS.rieszSpectrumVal (2 - 2 * f t) (f t * (2 * f t - 1))
        (equivalentKernel r) MR hpow homega hbdd hg hconst j ^ 2)
      ∧ (∑' j : ℕ, HS.rieszSpectrumVal (2 - 2 * f t) (f t * (2 * f t - 1))
          (equivalentKernel r) MR hpow homega hbdd hg hconst j ^ 2
        ≤ weightedRieszCycleIntegral 2 (2 - 2 * f t) (f t * (2 * f t - 1))
          (equivalentKernel r))
      ∧ HasSum
          (fun j : ℕ => HS.rieszSpectrumVal (2 - 2 * f t) (f t * (2 * f t - 1))
            (equivalentKernel r) MR hpow homega hbdd hg hconst j ^ 2)
          (weightedRieszCycleIntegral 2 (2 - 2 * f t) (f t * (2 * f t - 1))
            (equivalentKernel r))
      ∧ ∃ Q : (ℕ → ℝ) → ℝ,
          IsSecondChaosSeriesLaw gaussianSeqMeasure Q
            (HS.rieszSpectrumVal (2 - 2 * f t) (f t * (2 * f t - 1))
              (equivalentKernel r) MR hpow homega hbdd hg hconst)
          ∧ TendstoInDistribution
              (fun (n : ℕ) x => gaussianLogQuadraticStatistic
                (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
                (actualQ1SpectralWeight f r n ((n : ℝ) ^ (-γ)) t)
                (actualQ1Coeff n ((n : ℝ) ^ (-γ)) t) x)
              atTop Q
              (fun n => featureGaussian
                (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))
              gaussianSeqMeasure := by
  have hTwo : HasSum
      (fun j : ℕ => HS.rieszSpectrumVal (2 - 2 * f t) (f t * (2 * f t - 1))
        (equivalentKernel r) MR hpow homega hbdd hg hconst j ^ 2)
      (weightedRieszCycleIntegral 2 (2 - 2 * f t) (f t * (2 * f t - 1))
        (equivalentKernel r)) :=
    rieszSpectrum_two_hasSum_cycle_closed (2 - 2 * f t) (f t * (2 * f t - 1))
      (equivalentKernel r) MR hpow homega hbdd hg hconst
  obtain ⟨ha1, ha2, ha3⟩ :=
    actualQ1LongStatistic_tendsto_secondChaos_v3 p a b M r hp ha hb hab hM f hf
      hF t ht hlong γ hγ0 hγ1 hgrid MR hpow homega hbdd hg hconst hPos hAnti hTwo
      hGen hane hwnn
  exact ⟨ha1, ha2, hTwo, ha3⟩

/-! ### F. The `r = 1` degree-one variant (`hwnn` discharged) -/

set_option maxHeartbeats 10000000 in
/-- **THE CAPSTONE V3 CLOSED, degree-one (`r = 1`) variant with `hwnn` discharged**
from the balanced-window moment criterion `μ1 · x ≤ μ2` via
`Hurst.SpectralWeightNonneg.spectralWeight_nonneg_of_localLinearCriterion` (the pattern
of `Hurst.SpectralWeightNonneg.actualQ1LongStatistic_tendsto_secondChaos_v2_degreeOne`).
`hTwo` is discharged by the closed Parseval chain. -/
theorem actualQ1LongStatistic_tendsto_secondChaos_v3_closed_degreeOne
    (p a b M : ℝ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b)
    (hM : 0 ≤ M) (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hgrid : (1 - γ) * (2 - 2 * f t) < 2 - 2 * b)
    (MR : ℝ)
    (hpow : AEStronglyMeasurable
      (fun q : ℝ × ℝ => |q.1 - q.2| ^ (-(2 - 2 * f t))) HS.vol2)
    (homega : Measurable (equivalentKernel 1))
    (hbdd : ∀ x : ℝ, |equivalentKernel 1 x| ≤ MR)
    (hg : Integrable (fun q : ℝ × ℝ => |q.1 - q.2| ^ (-2 * (2 - 2 * f t))) HS.vol2)
    (hconst : ∀ x y : ℝ, (HS.I : Set ℝ).indicator (equivalentKernel 1) x
      = (HS.I : Set ℝ).indicator (equivalentKernel 1) y)
    (hPos : ∀ g : HS.L2, 0 ≤ inner ℝ
      (HS.TOp (HS.rieszKernel (2 - 2 * f t) (f t * (2 * f t - 1)) (equivalentKernel 1))
        (HS.hsKernel_rieszKernel hpow homega hbdd hg) g) g)
    (hAnti : Antitone (HS.rieszSpectrumVal (2 - 2 * f t) (f t * (2 * f t - 1))
      (equivalentKernel 1) MR hpow homega hbdd hg hconst))
    (hGen : ∀ k : ℕ, 3 ≤ k → HasSum
      (fun j : ℕ => HS.rieszSpectrumVal (2 - 2 * f t) (f t * (2 * f t - 1))
        (equivalentKernel 1) MR hpow homega hbdd hg hconst j ^ k)
      (weightedRieszCycleIntegral k (2 - 2 * f t) (f t * (2 * f t - 1))
        (equivalentKernel 1)))
    (hane : ∀ (n : ℕ) (k : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card),
      ∑ i, actualQ1Coeff n ((n : ℝ) ^ (-γ)) t k i •
        actualQ1Obs f n (midpointSampleHurst f hf.1 n) i ≠ 0)
    (hcrit : ∀ n : ℕ, 1 ≤ n → ∀ j : Fin (n - 1),
      (localDesignGram 1 n 1 ((n : ℝ) ^ (-γ)) t) (0 : Fin 2) (1 : Fin 2)
          * ((grid n j.val - t) / ((n : ℝ) ^ (-γ)))
        ≤ (localDesignGram 1 n 1 ((n : ℝ) ^ (-γ)) t) (1 : Fin 2) (1 : Fin 2)) :
    Summable (fun j : ℕ => HS.rieszSpectrumVal (2 - 2 * f t) (f t * (2 * f t - 1))
        (equivalentKernel 1) MR hpow homega hbdd hg hconst j ^ 2)
      ∧ (∑' j : ℕ, HS.rieszSpectrumVal (2 - 2 * f t) (f t * (2 * f t - 1))
          (equivalentKernel 1) MR hpow homega hbdd hg hconst j ^ 2
        ≤ weightedRieszCycleIntegral 2 (2 - 2 * f t) (f t * (2 * f t - 1))
          (equivalentKernel 1))
      ∧ HasSum
          (fun j : ℕ => HS.rieszSpectrumVal (2 - 2 * f t) (f t * (2 * f t - 1))
            (equivalentKernel 1) MR hpow homega hbdd hg hconst j ^ 2)
          (weightedRieszCycleIntegral 2 (2 - 2 * f t) (f t * (2 * f t - 1))
            (equivalentKernel 1))
      ∧ ∃ Q : (ℕ → ℝ) → ℝ,
          IsSecondChaosSeriesLaw gaussianSeqMeasure Q
            (HS.rieszSpectrumVal (2 - 2 * f t) (f t * (2 * f t - 1))
              (equivalentKernel 1) MR hpow homega hbdd hg hconst)
          ∧ TendstoInDistribution
              (fun (n : ℕ) x => gaussianLogQuadraticStatistic
                (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
                (actualQ1SpectralWeight f 1 n ((n : ℝ) ^ (-γ)) t)
                (actualQ1Coeff n ((n : ℝ) ^ (-γ)) t) x)
              atTop Q
              (fun n => featureGaussian
                (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))
              gaussianSeqMeasure :=
  actualQ1LongStatistic_tendsto_secondChaos_v3_closed p a b M 1 hp ha hb hab hM f hf
    hF t ht hlong γ hγ0 hγ1 hgrid MR hpow homega hbdd hg hconst hPos hAnti hGen hane
    (spectralWeight_nonneg_of_localLinearCriterion f t γ hcrit)

/-! ### G. The resorted form (`hAnti` discharged) -/

set_option maxHeartbeats 10000000 in
/-- **THE CAPSTONE V3 CLOSED, resorted form (`hAnti` discharged)**: stated at the
antitone re-sort `lam := Hurst.antitoneResort val` of the constructed enumeration.
The `Antitone`/nonnegativity clauses hold by construction
(`Hurst.AntitoneResort.antitoneResort_antitone` / `.antitoneResort_nonneg` from
`hPos`-entrywise nonnegativity + square-summability); the `k = 2` exact bridge is
transported to `lam` by the level-cake transfer
(`Hurst.LevelCakeTransfer.hasSum_pow_of_resort_lvlCount`) composed with the discharged
enumeration bridge; the general-`k` clause `hGen` (about the RAW enumeration) is
transported identically, using the landed general-`k` summability
(`HS.rieszSpectrum_hasSum_general_k`).  Remaining spectral hypotheses: `hPos` +
`hGen` + `hane`/`hwnn`. -/
theorem actualQ1LongStatistic_tendsto_secondChaos_v3_closed_antitone
    (p a b M : ℝ) (r : ℕ) (hp : 1 ≤ p) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b)
    (hM : 0 ≤ M) (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (hF : MapsTo f (Ioo (0 : ℝ) 1) (Icc a b))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hlong : 3 / 4 < f t)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hgrid : (1 - γ) * (2 - 2 * f t) < 2 - 2 * b)
    (MR : ℝ)
    (hpow : AEStronglyMeasurable
      (fun q : ℝ × ℝ => |q.1 - q.2| ^ (-(2 - 2 * f t))) HS.vol2)
    (homega : Measurable (equivalentKernel r))
    (hbdd : ∀ x : ℝ, |equivalentKernel r x| ≤ MR)
    (hg : Integrable (fun q : ℝ × ℝ => |q.1 - q.2| ^ (-2 * (2 - 2 * f t))) HS.vol2)
    (hconst : ∀ x y : ℝ, (HS.I : Set ℝ).indicator (equivalentKernel r) x
      = (HS.I : Set ℝ).indicator (equivalentKernel r) y)
    (hPos : ∀ g : HS.L2, 0 ≤ inner ℝ
      (HS.TOp (HS.rieszKernel (2 - 2 * f t) (f t * (2 * f t - 1)) (equivalentKernel r))
        (HS.hsKernel_rieszKernel hpow homega hbdd hg) g) g)
    (hGen : ∀ k : ℕ, 3 ≤ k → HasSum
      (fun j : ℕ => HS.rieszSpectrumVal (2 - 2 * f t) (f t * (2 * f t - 1))
        (equivalentKernel r) MR hpow homega hbdd hg hconst j ^ k)
      (weightedRieszCycleIntegral k (2 - 2 * f t) (f t * (2 * f t - 1))
        (equivalentKernel r)))
    (hane : ∀ (n : ℕ) (k : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card),
      ∑ i, actualQ1Coeff n ((n : ℝ) ^ (-γ)) t k i •
        actualQ1Obs f n (midpointSampleHurst f hf.1 n) i ≠ 0)
    (hwnn : ∀ᶠ n : ℕ in atTop,
      ∀ i : Fin (localWeightActiveSet n 1 ((n : ℝ) ^ (-γ)) t).card,
      0 ≤ actualQ1SpectralWeight f r n ((n : ℝ) ^ (-γ)) t i) :
    Antitone (antitoneResort (HS.rieszSpectrumVal (2 - 2 * f t) (f t * (2 * f t - 1))
        (equivalentKernel r) MR hpow homega hbdd hg hconst))
      ∧ (∀ j, 0 ≤ antitoneResort (HS.rieszSpectrumVal (2 - 2 * f t)
          (f t * (2 * f t - 1)) (equivalentKernel r) MR hpow homega hbdd hg hconst) j)
      ∧ HasSum
          (fun j : ℕ => antitoneResort (HS.rieszSpectrumVal (2 - 2 * f t)
            (f t * (2 * f t - 1)) (equivalentKernel r) MR hpow homega hbdd hg hconst) j ^ 2)
          (weightedRieszCycleIntegral 2 (2 - 2 * f t) (f t * (2 * f t - 1))
            (equivalentKernel r))
      ∧ ∃ Q : (ℕ → ℝ) → ℝ,
          IsSecondChaosSeriesLaw gaussianSeqMeasure Q
            (antitoneResort (HS.rieszSpectrumVal (2 - 2 * f t) (f t * (2 * f t - 1))
              (equivalentKernel r) MR hpow homega hbdd hg hconst))
          ∧ TendstoInDistribution
              (fun (n : ℕ) x => gaussianLogQuadraticStatistic
                (actualQ1Obs f n (midpointSampleHurst f hf.1 n))
                (actualQ1SpectralWeight f r n ((n : ℝ) ^ (-γ)) t)
                (actualQ1Coeff n ((n : ℝ) ^ (-γ)) t) x)
              atTop Q
              (fun n => featureGaussian
                (actualQ1Obs f n (midpointSampleHurst f hf.1 n)))
              gaussianSeqMeasure := by
  set val := HS.rieszSpectrumVal (2 - 2 * f t) (f t * (2 * f t - 1)) (equivalentKernel r)
    MR hpow homega hbdd hg hconst with hvaldef
  have hnn : ∀ j, 0 ≤ val j :=
    HS.rieszSpectrum_nonneg_of_posTOp (2 - 2 * f t) (f t * (2 * f t - 1))
      (equivalentKernel r) MR hpow homega hbdd hg hconst hPos
  have hsq : Summable (fun j : ℕ => val j * val j) := by
    simpa [pow_two] using HS.rieszSpectrum_sq_summable (2 - 2 * f t)
      (f t * (2 * f t - 1)) (equivalentKernel r) MR hpow homega hbdd hg hconst
  -- the enumeration bridge at k = 2, transported to the resort
  have hTwo : HasSum (fun j : ℕ => antitoneResort val j ^ 2)
      (weightedRieszCycleIntegral 2 (2 - 2 * f t) (f t * (2 * f t - 1))
        (equivalentKernel r)) := by
    have h1 : HasSum (fun j : ℕ => antitoneResort val j ^ 2)
        (∑' j : ℕ, val j ^ 2) :=
      hasSum_pow_of_resort_lvlCount val hnn hsq 2 (by norm_num)
        (HS.rieszSpectrum_sq_summable (2 - 2 * f t) (f t * (2 * f t - 1))
          (equivalentKernel r) MR hpow homega hbdd hg hconst)
    have h2 : (∑' j : ℕ, val j ^ 2)
        = weightedRieszCycleIntegral 2 (2 - 2 * f t) (f t * (2 * f t - 1))
          (equivalentKernel r) :=
      (rieszSpectrum_two_hasSum_cycle_closed (2 - 2 * f t) (f t * (2 * f t - 1))
        (equivalentKernel r) MR hpow homega hbdd hg hconst).tsum_eq
    rw [h2] at h1; exact h1
  -- general k ≥ 3: the level-cake transport of hGen
  have hRiesz : ∀ k : ℕ, 2 ≤ k → HasSum
      (fun j : ℕ => antitoneResort val j ^ k)
      (weightedRieszCycleIntegral k (2 - 2 * f t) (f t * (2 * f t - 1))
        (equivalentKernel r)) := by
    intro k hk
    by_cases h2 : k = 2
    · subst h2; exact hTwo
    · have hsmk : Summable (fun j : ℕ => val j ^ k) := by
        have hgen := HS.rieszSpectrum_hasSum_general_k (2 - 2 * f t)
          (f t * (2 * f t - 1)) (equivalentKernel r) MR hpow homega hbdd hg hconst k hk
        have habs : Summable (fun j : ℕ => |val j ^ k|) :=
          (summable_congr (fun j => (abs_pow (val j) k).symm)).mp hgen.1.summable
        exact summable_abs_iff.mp habs
      rw [← (hGen k (by omega)).tsum_eq]
      exact hasSum_pow_of_resort_lvlCount val hnn hsq k (by omega) hsmk
  exact ⟨antitoneResort_antitone hnn hsq, antitoneResort_nonneg hnn hsq, hTwo,
    actualQ1LongStatistic_tendsto_secondChaos_v2 p a b M r hp ha hb hab hM f hf
      hF t ht hlong γ hγ0 hγ1 hgrid (antitoneResort val)
      ⟨antitoneResort_antitone hnn hsq, antitoneResort_nonneg hnn hsq⟩ hRiesz hane
      hwnn⟩

end Hurst
end Riesz
