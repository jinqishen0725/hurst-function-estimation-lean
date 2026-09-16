import Hurst.RieszCompactEnumeration
import Hurst.HSNormIdentity
import Hurst.RieszK2Anchor
import Hurst.RieszSpectralTrace
import Hurst.HSOperatorLayer2
import Hurst.P2SpectrumCloseout

/-!
# P2 spectrum construction close-out v2: the constructed Riesz spectrum, packaged

The close-out of the P2 spectrum construction at the RIESZ operator: the
multiplicity-exact enumeration `Hurst.rieszSpectrumOf` of the compact self-adjoint
operator `T = HS.TOp K_R` of the uniform-`ω` truncated weighted Riesz kernel
`K_R = HS.rieszKernel psi c omega`, assembled from the freshly built layers with
`hCompact` DISCHARGED (`HS.isCompactOperator_TOp_riesz`,
`Hurst.RieszCompactEnumeration`) — no hypotheses beyond the ordinary operator data
(`hpow`, `homega`, `hbdd`, `hg`) and the kernel datum `hconst`.

## The constructed enumeration

`Hurst.rieszSpectrumOf` is the value part of the multiplicity-exact enumeration
`HS.exists_multiplicity_enumeration` (`Hurst.FrozenSpectralCount`) instantiated at
`hCompact := isCompactOperator_TOp_riesz` and
`hsym := isSymmetric_TOp_rieszKernel` (via
`HS.exists_multiplicity_enumeration_summable_riesz` of `Hurst.P2SpectrumCloseout`):
every entry is `0` or a nonzero eigenvalue carrying a unit eigenvector, the zero
entries pad the tail (and the degenerate no-spectrum case is identically zero), and
each nonzero eigenvalue `μ` occurs exactly `finrank (eigenspace μ)` times
(`rieszSpectrumOf_multiplicity`).  The definition is (rfl-)the value part
`HS.rieszSpectrumVal` of `Hurst.P2SpectrumCloseout`'s constructed spectrum, so every
landed clause transfers.

## The exact application shape of the Bessel route (checked)

`HS.summable_eigenvalues_sq` (`Hurst.HSNormIdentity`) requires an ORTHONORMAL
eigen-family.  Checked against the enumeration production
(`Hurst.FrozenSpectralCount.exists_multiplicity_enumeration`): the vector companion
assigns the SAME unit eigenvector `u σ` to every member of a level fiber
(`enumVec ρ hρinj (fun σ => u σ.1)`), so within one eigenspace of dimension `≥ 2`
the enumeration's vectors coincide and are NOT orthonormal; consequently
`HS.summable_two_riesz` / `HS.tsum_two_riesz_le_cycle` / `HS.hasSum_two_riesz`
(`Hurst.RieszK2Anchor` — the verbatim `summable_eigenvalues_sq` instantiations at the
Riesz operator) apply to any orthonormal eigen-family but NOT verbatim to
`(rieszSpectrumOf, rieszSpectrumVecOf)`.  The honest route, landed here: the
per-eigenspace orthonormal bases splice over the nonzero spectrum into ONE
orthonormal family (`HS.exists_orthonormal_eigenFamily`, the family to which the
RieszK2Anchor Bessel lemmas apply verbatim), and the level-fiber counts
(`rieszSpectrumOf_multiplicity`) transport its finite Bessel bound
(`HS.hsNorm_sq_ge_sum_norm_sq_of_orthonormal`) to every partial sum of
`rieszSpectrumOf²` — the landed chain `HS.summable_val_sq_of_multEnum` /
`HS.tsum_val_sq_le_hsNorm_sq_of_multEnum` of `Hurst.P2SpectrumCloseout`, instantiated
here at the constructed enumeration.

## What is closed (exit-0 content, no hypotheses beyond the operator data)

* `rieszSpectrumOf_summable` — `Summable (fun j => rieszSpectrumOf … j ^ 2)` (Bessel
  route above);
* `rieszSpectrumOf_k2_tsum_le` — `∑' j, rieszSpectrumOf … j ^ 2 ≤
  Hurst.weightedRieszCycleIntegral 2 psi c omega` (Bessel tsum anchor + the landed
  kernel identity `HS.weightedRieszCycleIntegral_two_eq_hsNorm_sq` — the same
  two-step structure as `HS.tsum_two_riesz_le_cycle`, at the multiplicity
  enumeration);
* `rieszSpectrumOf_k2_hasSum` — `HasSum (fun j => rieszSpectrumOf … j ^ 2)
  (∑' j, rieszSpectrumOf … j ^ 2)` (tautological from Summable);
* `rieszSpectrumOf_closeout` — the bundle: entry clause, multiplicity-exactness,
  square-summability, the `k = 2` HasSum to the own tsum, the `k = 2` tsum bound,
  and nonnegativity under operator positivity;
* `rieszSpectrumOf_contract_of_powerHasSums` — the full
  `Hurst.IsRieszSpectrumSequence` contract closes from the power-`HasSum`
  identifications.

## The honest boundary (documented, not forced)

* **`k = 2` exact target**: `HasSum (rieszSpectrumOf²) (J₂)` is EQUIVALENT to the
  reverse Parseval inequality `hsNorm K_R² ≤ ∑' val²`
  (`rieszSpectrumOf_k2_hasSum_iff_reverseParseval`); the forward `≤` is the Bessel
  anchor, and the reverse direction is the kernel expansion
  `K_R = ∑_σ μ_σ (w_σ ⊗ w_σ)` in `L²(vol2)` — the documented Parseval gap of
  `Hurst.HSNormIdentity` / `Hurst.RieszSpectralTrace` (only the `≤` half is landed).
  Under the completeness clause the exact HasSum holds
  (`rieszSpectrumOf_k2_hasSum_of_complete`); `HS.hasSum_two_riesz` +
  `HS.weightedRieszCycleIntegral_two_eq_hsNorm_sq` cover the `k = 2` clause exactly
  for orthonormal eigen-enumerations under the same gate.
* **general `k ≥ 3`**: the exact HasSum `∑_j val_j^k = weightedRieszCycleIntegral k`
  is gated on (a) the operator-side Parseval (the same reverse expansion, which
  identifies `⟪(T^k)·,·⟫` trace pairings with the cycle integrals over the eigenbasis,
  cf. the documented gaps of `Hurst.RieszSpectralTrace` / `Hurst.CycleTraceIdentification`)
  and (b) the composition peel-induction integrability discharges (the `hA`/`hB`
  residues architected in the gap report of `Hurst.HSCycleComposition`).  Neither is
  forced here; the summability side of the enumeration for every `k ≥ 2` is landed in
  `Hurst.GeneralKHasSum` (`summable_pow_of_multEnum`), so the exact clause closes the
  moment (a)+(b) land, via `HasSum` transport to the identified target.
* **nonnegativity**: conditional on operator positivity (the landed Rayleigh lemma);
  the unconditional clause is FALSE in `omega` (the `ω ≡ -1` odd-cycle obstruction,
  `Hurst.P2SpectrumConstruction`); the PSD of the uniform-`ω` kernel stays deferred
  (`Hurst.HSOperatorLayer4`), signed spectra covered by the even-power peeling.
-/

open MeasureTheory Measure Real Set
open scoped Real

noncomputable section

namespace Hurst

open HS

variable (psi c : ℝ) (omega : ℝ → ℝ) (M : ℝ)

/-! ### The constructed multiplicity-exact Riesz spectrum -/

/-- **The constructed Riesz spectrum** (the close-out entry point): the
multiplicity-exact eigenvalue enumeration of the compact self-adjoint Riesz operator
`TOp K_R` (`hCompact` discharged by `HS.isCompactOperator_TOp_riesz`), i.e. the value
part of `HS.exists_multiplicity_enumeration_summable_riesz` — every entry is `0` or a
nonzero eigenvalue with a unit eigenvector, zeros pad the tail, the degenerate case is
identically zero, and each nonzero eigenvalue occurs exactly `finrank (eigenspace μ)`
times.  (rfl-equal to `HS.rieszSpectrumVal` of `Hurst.P2SpectrumCloseout`.) -/
noncomputable def rieszSpectrumOf
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

/-- The vector companion of the constructed spectrum: the unit eigenvector matched to
each nonzero entry (the zero-padded entries carry the zero vector). -/
noncomputable def rieszSpectrumVecOf
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y) :
    ℕ → L2 :=
  @Classical.choose _ (fun vec : ℕ → L2 =>
      (∀ j, rieszSpectrumOf psi c omega M hpow homega hbdd hg hconst j = 0 ∨
        Module.End.HasEigenvector
          (TOpEnd' (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg))
          (rieszSpectrumOf psi c omega M hpow homega hbdd hg hconst j) (vec j)) ∧
      (∀ μ : ℝ, Module.End.HasEigenvalue
        (TOpEnd' (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg)) μ →
        μ ≠ 0 →
        Nat.card {j : ℕ // rieszSpectrumOf psi c omega M hpow homega hbdd hg hconst j = μ}
          = Module.finrank ℝ (Module.End.eigenspace
            (TOpEnd' (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg)) μ)) ∧
      Summable (fun j => rieszSpectrumOf psi c omega M hpow homega hbdd hg hconst j ^ 2))
    (Classical.choose_spec (exists_multiplicity_enumeration_summable_riesz
      psi c omega M hpow homega hbdd hg hconst))

/-- Transparency remark: the constructed spectrum is (definitionally) the value part
`HS.rieszSpectrumVal` of `Hurst.P2SpectrumCloseout`'s constructed Riesz spectrum, so
every landed clause of that module transfers verbatim. -/
theorem rieszSpectrumOf_eq_rieszSpectrumVal
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y) :
    rieszSpectrumOf psi c omega M hpow homega hbdd hg hconst
      = HS.rieszSpectrumVal psi c omega M hpow homega hbdd hg hconst :=
  rfl

/-- The three spectral clauses of the constructed spectrum (the choice extraction):
entries, multiplicity-exactness, and square-summability. -/
theorem rieszSpectrumOf_pack
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y) :
    (∀ j, rieszSpectrumOf psi c omega M hpow homega hbdd hg hconst j = 0 ∨
        Module.End.HasEigenvector
          (TOpEnd' (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg))
          (rieszSpectrumOf psi c omega M hpow homega hbdd hg hconst j)
          (rieszSpectrumVecOf psi c omega M hpow homega hbdd hg hconst j))
    ∧ (∀ μ : ℝ, Module.End.HasEigenvalue
        (TOpEnd' (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg)) μ →
        μ ≠ 0 →
        Nat.card {j : ℕ // rieszSpectrumOf psi c omega M hpow homega hbdd hg hconst j = μ}
          = Module.finrank ℝ (Module.End.eigenspace
            (TOpEnd' (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg)) μ))
    ∧ Summable (fun j => rieszSpectrumOf psi c omega M hpow homega hbdd hg hconst j ^ 2) := by
  have h := exists_multiplicity_enumeration_summable_riesz psi c omega M hpow homega hbdd hg hconst
  have hvaleq : rieszSpectrumOf psi c omega M hpow homega hbdd hg hconst
      = Classical.choose h := rfl
  have hveceq : rieszSpectrumVecOf psi c omega M hpow homega hbdd hg hconst
      = Classical.choose (Classical.choose_spec h) := rfl
  rw [hvaleq, hveceq]
  exact Classical.choose_spec (Classical.choose_spec h)

/-! ### The close-out clauses -/

/-- **Entry clause**: every entry of the constructed spectrum is `0` or a nonzero
eigenvalue with its unit eigenvector. -/
theorem rieszSpectrumOf_entry
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y)
    (j : ℕ) :
    rieszSpectrumOf psi c omega M hpow homega hbdd hg hconst j = 0 ∨
      Module.End.HasEigenvector
        (TOpEnd' (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg))
        (rieszSpectrumOf psi c omega M hpow homega hbdd hg hconst j)
        (rieszSpectrumVecOf psi c omega M hpow homega hbdd hg hconst j) :=
  (rieszSpectrumOf_pack psi c omega M hpow homega hbdd hg hconst).1 j

/-- **Multiplicity-exactness**: every nonzero eigenvalue `μ` of the Riesz operator
occurs exactly `finrank (eigenspace μ)` times in the constructed spectrum. -/
theorem rieszSpectrumOf_multiplicity
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y)
    {μ : ℝ} (hμ : Module.End.HasEigenvalue
      (TOpEnd' (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg)) μ)
    (hμ0 : μ ≠ 0) :
    Nat.card {j : ℕ // rieszSpectrumOf psi c omega M hpow homega hbdd hg hconst j = μ}
      = Module.finrank ℝ (Module.End.eigenspace
        (TOpEnd' (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg)) μ) :=
  (rieszSpectrumOf_pack psi c omega M hpow homega hbdd hg hconst).2.1 μ hμ hμ0

/-- **(ii) CLOSED — square summability of the constructed Riesz spectrum**:
`Summable (fun j => rieszSpectrumOf … j ^ 2)`.

Bessel route (the exact application shape, see the module docstring):
`HS.summable_eigenvalues_sq` needs an orthonormal eigen-family; the enumeration's
vector companion repeats one eigenvector per level fiber (checked against the
`Hurst.FrozenSpectralCount` production), so the bound is carried from the spliced
per-eigenspace ON family — the family to which `HS.summable_two_riesz` /
`HS.tsum_two_riesz_le_cycle` (`Hurst.RieszK2Anchor`) apply verbatim — through the
level-fiber counts `rieszSpectrumOf_multiplicity`: the landed chain
`HS.summable_val_sq_of_multEnum` (bounded partial sums of the nonnegative series,
each caught by `HS.hsNorm_sq_ge_sum_norm_sq_of_orthonormal`). -/
theorem rieszSpectrumOf_summable
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y) :
    Summable (fun j => rieszSpectrumOf psi c omega M hpow homega hbdd hg hconst j ^ 2) :=
  summable_val_sq_of_multEnum
    (isCompactOperator_TOp_riesz hpow homega hbdd hg hconst)
    (isSymmetric_TOp_rieszKernel hpow homega hbdd hg hconst)
    (rieszSpectrumOf_entry psi c omega M hpow homega hbdd hg hconst)
    (fun _μ hμ hμ0 =>
      rieszSpectrumOf_multiplicity psi c omega M hpow homega hbdd hg hconst hμ hμ0)

/-- The tsum Bessel bound for the constructed spectrum:
`∑' j, rieszSpectrumOf j² ≤ hsNorm K_R²`. -/
theorem rieszSpectrumOf_sq_tsum_le_hsNorm_sq
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y) :
    ∑' j, rieszSpectrumOf psi c omega M hpow homega hbdd hg hconst j ^ 2
      ≤ hsNorm (rieszKernel psi c omega) ^ 2 :=
  tsum_val_sq_le_hsNorm_sq_of_multEnum
    (isCompactOperator_TOp_riesz hpow homega hbdd hg hconst)
    (isSymmetric_TOp_rieszKernel hpow homega hbdd hg hconst)
    (rieszSpectrumOf_entry psi c omega M hpow homega hbdd hg hconst)
    (fun _μ hμ hμ0 =>
      rieszSpectrumOf_multiplicity psi c omega M hpow homega hbdd hg hconst hμ hμ0)

/-- **(iii, `k = 2`) CLOSED — the tsum bound against the cycle integral**:
`∑' j, rieszSpectrumOf … j ^ 2 ≤ Hurst.weightedRieszCycleIntegral 2 psi c omega`.
The two-step structure of `HS.tsum_two_riesz_le_cycle` (Bessel anchor, then the landed
kernel identity `weightedRieszCycleIntegral 2 ψ c ω = hsNorm K_R²`), instantiated at
the multiplicity-exact enumeration through the fiber-count transport (module
docstring). -/
theorem rieszSpectrumOf_k2_tsum_le
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y) :
    ∑' j, rieszSpectrumOf psi c omega M hpow homega hbdd hg hconst j ^ 2
      ≤ Hurst.weightedRieszCycleIntegral 2 psi c omega := by
  calc ∑' j, rieszSpectrumOf psi c omega M hpow homega hbdd hg hconst j ^ 2
      ≤ hsNorm (rieszKernel psi c omega) ^ 2 :=
        rieszSpectrumOf_sq_tsum_le_hsNorm_sq psi c omega M hpow homega hbdd hg hconst
    _ = Hurst.weightedRieszCycleIntegral 2 psi c omega :=
        (weightedRieszCycleIntegral_two_eq_hsNorm_sq hconst).symm

/-- **(iii, `k = 2`) CLOSED — the HasSum to the own tsum**:
`HasSum (fun j => rieszSpectrumOf … j ^ 2) (∑' j, rieszSpectrumOf … j ^ 2)`
(tautological from `rieszSpectrumOf_summable`). -/
theorem rieszSpectrumOf_k2_hasSum
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y) :
    HasSum (fun j => rieszSpectrumOf psi c omega M hpow homega hbdd hg hconst j ^ 2)
      (∑' j, rieszSpectrumOf psi c omega M hpow homega hbdd hg hconst j ^ 2) :=
  (rieszSpectrumOf_summable psi c omega M hpow homega hbdd hg hconst).hasSum

/-! ### The honest boundary: the `k = 2` exact target and general `k` -/

/-- **The `k = 2` exact-target HasSum under multiplicity completeness**: if the
constructed spectrum's squared tsum equals the full kernel energy (the
multiplicity-completeness clause — which holds exactly when the reverse Parseval
inequality below holds), then
`HasSum (fun j => rieszSpectrumOf … j ^ 2) (weightedRieszCycleIntegral 2 psi c omega)`.
This is the shape of `HS.hasSum_two_riesz` (`Hurst.RieszK2Anchor`, stated there for
orthonormal eigen-enumerations) at the multiplicity enumeration: no orthonormality
hypothesis, the same completeness gate. -/
theorem rieszSpectrumOf_k2_hasSum_of_complete
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y)
    (hcomplete : ∑' j, rieszSpectrumOf psi c omega M hpow homega hbdd hg hconst j ^ 2
      = hsNorm (rieszKernel psi c omega) ^ 2) :
    HasSum (fun j => rieszSpectrumOf psi c omega M hpow homega hbdd hg hconst j ^ 2)
      (Hurst.weightedRieszCycleIntegral 2 psi c omega) := by
  rw [weightedRieszCycleIntegral_two_eq_hsNorm_sq hconst, ← hcomplete]
  exact (rieszSpectrumOf_summable psi c omega M hpow homega hbdd hg hconst).hasSum

/-- **The honest boundary, as a theorem**: the exact-target `k = 2` HasSum
`HasSum (rieszSpectrumOf²) (weightedRieszCycleIntegral 2 psi c omega)` is EQUIVALENT
to the reverse Parseval inequality `hsNorm K_R² ≤ ∑' j, rieszSpectrumOf j²`.  The
forward `≤` is the landed Bessel anchor (`rieszSpectrumOf_sq_tsum_le_hsNorm_sq`);
the reverse direction is the kernel expansion `K_R = ∑_σ μ_σ (w_σ ⊗ w_σ)` in
`L²(vol2)` — the documented Parseval gap (`Hurst.HSNormIdentity` equality half,
`Hurst.RieszSpectralTrace` gap report), NOT forced here. -/
theorem rieszSpectrumOf_k2_hasSum_iff_reverseParseval
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y) :
    HasSum (fun j => rieszSpectrumOf psi c omega M hpow homega hbdd hg hconst j ^ 2)
        (Hurst.weightedRieszCycleIntegral 2 psi c omega)
      ↔ hsNorm (rieszKernel psi c omega) ^ 2
        ≤ ∑' j, rieszSpectrumOf psi c omega M hpow homega hbdd hg hconst j ^ 2 := by
  constructor
  · intro h
    have h1 : (∑' j, rieszSpectrumOf psi c omega M hpow homega hbdd hg hconst j ^ 2)
        = hsNorm (rieszKernel psi c omega) ^ 2 := by
      rw [h.tsum_eq, weightedRieszCycleIntegral_two_eq_hsNorm_sq hconst]
    exact h1.symm.le
  · intro hrev
    exact rieszSpectrumOf_k2_hasSum_of_complete psi c omega M hpow homega hbdd hg hconst
      (le_antisymm
        (rieszSpectrumOf_sq_tsum_le_hsNorm_sq psi c omega M hpow homega hbdd hg hconst)
        hrev)

/-- **(i) CONDITIONAL — nonnegativity** under the operator-positivity hypothesis
`∀ f, 0 ≤ ⟪T f, f⟫` (the landed Rayleigh lemma `eigenvalue_nonneg_of_pos`).
Unconditionally FALSE in `omega` (`ω ≡ -1` flips the odd cycle integrals,
`Hurst.P2SpectrumConstruction`); PSD of the uniform-`ω` kernel deferred
(`Hurst.HSOperatorLayer4`), signed route `Hurst.EvenPeeling`. -/
theorem rieszSpectrumOf_nonneg_of_posTOp
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y)
    (hPos : ∀ f : L2, 0 ≤ inner ℝ
      (TOp (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg) f) f)
    (j : ℕ) :
    0 ≤ rieszSpectrumOf psi c omega M hpow homega hbdd hg hconst j := by
  rcases rieszSpectrumOf_entry psi c omega M hpow homega hbdd hg hconst j with h0 | hv
  · rw [h0]
  · exact eigenvalue_nonneg_of_pos hPos (Module.End.hasEigenvalue_of_hasEigenvector hv)

/-! ### The close-out bundle and the full-contract consumption -/

/-- **P2 SPECTRUM CONSTRUCTION CLOSE-OUT (the bundle)**: the constructed
multiplicity-exact spectrum of the uniform-`ω` Riesz operator satisfies

1. the entry clause (`0` or nonzero eigenvalue with unit eigenvector);
2. multiplicity-exactness (`finrank (eigenspace μ)` occurrences per level);
3. **(ii)** `Summable (fun j => val j ^ 2)` — the Bessel route;
4. **(iii, `k = 2`)** `HasSum (val²) (∑' val²)` — the own-tsum HasSum;
5. **(iii, `k = 2`)** `∑' val² ≤ weightedRieszCycleIntegral 2 psi c omega` — the
   Bessel anchor bridged by the kernel identity;
6. **(i, conditional)** nonnegativity under operator positivity.

The exact-target `k = 2` HasSum and the general-`k ≥ 3` HasSums are the documented
boundary (module docstring: reverse Parseval; operator-side Parseval + peel-induction
integrability). -/
theorem rieszSpectrumOf_closeout
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y) :
    (∀ j, rieszSpectrumOf psi c omega M hpow homega hbdd hg hconst j = 0 ∨
        Module.End.HasEigenvector
          (TOpEnd' (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg))
          (rieszSpectrumOf psi c omega M hpow homega hbdd hg hconst j)
          (rieszSpectrumVecOf psi c omega M hpow homega hbdd hg hconst j))
    ∧ (∀ μ : ℝ, Module.End.HasEigenvalue
        (TOpEnd' (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg)) μ →
        μ ≠ 0 →
        Nat.card {j : ℕ // rieszSpectrumOf psi c omega M hpow homega hbdd hg hconst j = μ}
          = Module.finrank ℝ (Module.End.eigenspace
            (TOpEnd' (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg)) μ))
    ∧ Summable (fun j => rieszSpectrumOf psi c omega M hpow homega hbdd hg hconst j ^ 2)
    ∧ HasSum (fun j => rieszSpectrumOf psi c omega M hpow homega hbdd hg hconst j ^ 2)
        (∑' j, rieszSpectrumOf psi c omega M hpow homega hbdd hg hconst j ^ 2)
    ∧ (∑' j, rieszSpectrumOf psi c omega M hpow homega hbdd hg hconst j ^ 2
        ≤ Hurst.weightedRieszCycleIntegral 2 psi c omega)
    ∧ ((∀ f : L2, 0 ≤ inner ℝ
          (TOp (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg) f) f) →
        ∀ j, 0 ≤ rieszSpectrumOf psi c omega M hpow homega hbdd hg hconst j) :=
  ⟨rieszSpectrumOf_entry psi c omega M hpow homega hbdd hg hconst,
    fun _μ hμ hμ0 =>
      rieszSpectrumOf_multiplicity psi c omega M hpow homega hbdd hg hconst hμ hμ0,
    rieszSpectrumOf_summable psi c omega M hpow homega hbdd hg hconst,
    rieszSpectrumOf_k2_hasSum psi c omega M hpow homega hbdd hg hconst,
    rieszSpectrumOf_k2_tsum_le psi c omega M hpow homega hbdd hg hconst,
    rieszSpectrumOf_nonneg_of_posTOp psi c omega M hpow homega hbdd hg hconst⟩

/-- **The full P2 contract closes from the power-HasSum identifications**: the
constructed spectrum satisfies `Hurst.IsRieszSpectrumSequence psi c omega` as soon as
the `k = 2` exact-target HasSum and the general-`k ≥ 2` exact-target HasSums are
supplied (the documented boundary: reverse Parseval at `k = 2`; operator-side
Parseval + composition peel-induction integrability at `k ≥ 3`).  Nonnegativity from
operator positivity. -/
theorem rieszSpectrumOf_contract_of_powerHasSums
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y)
    (hPos : ∀ f : L2, 0 ≤ inner ℝ
      (TOp (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg) f) f)
    (h2 : HasSum (fun j => rieszSpectrumOf psi c omega M hpow homega hbdd hg hconst j ^ 2)
      (Hurst.weightedRieszCycleIntegral 2 psi c omega))
    (hgen : ∀ k : ℕ, 2 ≤ k → HasSum
      (fun j => rieszSpectrumOf psi c omega M hpow homega hbdd hg hconst j ^ k)
      (Hurst.weightedRieszCycleIntegral k psi c omega)) :
    Hurst.IsRieszSpectrumSequence psi c omega
      (rieszSpectrumOf psi c omega M hpow homega hbdd hg hconst) :=
  isRieszSpectrumSequence_of_hasSum
    (rieszSpectrumOf_nonneg_of_posTOp psi c omega M hpow homega hbdd hg hconst hPos) h2 hgen

end Hurst

end
