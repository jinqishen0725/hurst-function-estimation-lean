import Hurst.RieszCompactEnumeration
import Hurst.HSNormIdentity
import Hurst.RieszSpectralTrace

/-!
# The `k = 2` HasSum anchor at the Riesz operator (Bessel route)

The `k = 2` clause of `Hurst.IsRieszSpectrumSequence` / the `Summable` clause of
`Hurst.IsWeightedRieszSpectrum`, landed at the compact self-adjoint Riesz operator
`TOp K_R` of `Hurst.HSOperatorLayer2` for the uniform-`ω` weight, for any
orthonormal eigen-enumeration `(val, vec)` of the operator.

## Main results (all for a fixed orthonormal eigen-family `vec` with eigenvalues `val`)

* `HS.summable_two_riesz` — **square-summability (Bessel)**: `Summable (fun j => val j ^ 2)`.
  Direct instantiation of `HS.summable_eigenvalues_sq`; no compactness or symmetry input.
* `HS.tsum_two_riesz_le_hsNorm_sq` — **the Bessel anchor**: `∑' j, val j ^ 2 ≤ hsNorm K_R ^ 2`
  (the landed ≤-half `hsNorm_sq_ge_tsum_norm_sq_of_orthonormal` at the eigen-family, with the
  unit-eigenvector rewrite `‖T (vec j)‖² = val j²`).
* `HS.tsum_two_riesz_le_cycle` — **the bridge to the cycle integral**: the same bound with
  `hsNorm K_R²` replaced by `Hurst.weightedRieszCycleIntegral 2 ψ c ω` via the landed kernel
  identity `weightedRieszCycleIntegral_two_eq_hsNorm_sq`.
* `HS.hasSum_two_riesz` — **the `k = 2` HasSum**: `HasSum (fun j => val j ^ 2)
  (Hurst.weightedRieszCycleIntegral 2 ψ c ω)`, gated on the multiplicity-completeness clause
  `hcomplete : ∑' j, val j ^ 2 = hsNorm (rieszKernel ψ c ω) ^ 2`.
* `HS.riesz_k2_anchor` — the packaging with the full Riesz signature (`hCompact`, `hsym` from
  `Hurst.RieszCompactEnumeration`) delivering the `k = 2` clause of `IsRieszSpectrumSequence`:
  square-summability + the `HasSum` at `k = 2`, together with the unconditional Bessel bound.

## The gate, documented

The `HasSum` target `hsNorm K_R²` is the FULL kernel energy.  The enumeration side
`∑' j, val j ^ 2` equals it exactly iff the eigen-family is multiplicity-complete
(the square-summability over the whole nonzero spectrum counted with eigenspace
multiplicities).  Mathematically this holds for a multiplicity-exact enumeration
(one per eigendirection), but the proof needs the reverse Parseval inequality
`hsNorm K² ≤ Σ_i ‖T e_i‖²` over a complete ONB — the documented-blocked gap of
`Hurst.HSNormIdentity` (its header: only the `≤` direction is landed).  Accordingly
`hasSum_two_riesz` carries the completeness clause `hcomplete` as an explicit
hypothesis; once the Parseval gap closes, `hcomplete` discharges for the
multiplicity-exact enumeration and `riesz_k2_anchor` becomes unconditional.
The unconditional content landed here — `Summable (val²)` and
`∑' val² ≤ weightedRieszCycleIntegral 2 ψ c ω` — is exactly the `k = 2` Bessel
anchor bridged to the cycle integral.

Note on hypotheses: the Bessel route consumes only the Hilbert–Schmidt kernel data;
`hCompact`/`hsym` appear in `riesz_k2_anchor` because they are the inputs of the
enumeration production (`HS.exists_multiplicity_enumeration_riesz`), and the
per-eigenspace Gram–Schmidt making that enumeration orthonormal is part of the same
documented gap.
-/

open MeasureTheory Measure Real Set
open scoped Real

noncomputable section

namespace HS

variable {psi c : ℝ} {omega : ℝ → ℝ} {M : ℝ}

/-! ### The Bessel square-summability and the ≤-anchor -/

/-- **Square-summability of the Riesz eigenvalues (Bessel)**: for any orthonormal
eigen-family `vec` of the uniform-`ω` Riesz kernel operator with eigenvalues `val`,
the squared-eigenvalue series converges.  Direct instantiation of
`HS.summable_eigenvalues_sq`; no compactness or symmetry input. -/
theorem summable_two_riesz
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    {val : ℕ → ℝ} {vec : ℕ → L2} (hvec : Orthonormal ℝ vec)
    (hvecval : ∀ j, TOp (rieszKernel psi c omega)
      (hsKernel_rieszKernel hpow homega hbdd hg) (vec j) = val j • vec j) :
    Summable (fun j => val j ^ 2) :=
  summable_eigenvalues_sq hvec hvecval

/-- **Unit-eigenvector bridge**: on an orthonormal eigen-family of the Riesz operator,
the image norm square IS the squared eigenvalue: `‖T (vec j)‖² = val j²`. -/
theorem norm_TOp_vec_sq_eq_sq_riesz
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    {val : ℕ → ℝ} {vec : ℕ → L2} (hvec : Orthonormal ℝ vec)
    (hvecval : ∀ j, TOp (rieszKernel psi c omega)
      (hsKernel_rieszKernel hpow homega hbdd hg) (vec j) = val j • vec j) :
    ∀ j, val j ^ 2
      = ‖TOp (rieszKernel psi c omega)
          (hsKernel_rieszKernel hpow homega hbdd hg) (vec j)‖ ^ 2 := by
  intro j
  rw [hvecval j, norm_smul, Real.norm_eq_abs, hvec.1 j, mul_one, sq_abs]

/-- **The Bessel `k = 2` anchor at the Riesz operator**: the squared-eigenvalue tsum of
any orthonormal eigen-enumeration is bounded by the squared HS norm of the Riesz kernel —
the landed ≤-half `hsNorm_sq_ge_tsum_norm_sq_of_orthonormal` read at the eigen-family
through the unit-eigenvector bridge. -/
theorem tsum_two_riesz_le_hsNorm_sq
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    {val : ℕ → ℝ} {vec : ℕ → L2} (hvec : Orthonormal ℝ vec)
    (hvecval : ∀ j, TOp (rieszKernel psi c omega)
      (hsKernel_rieszKernel hpow homega hbdd hg) (vec j) = val j • vec j) :
    ∑' j, val j ^ 2 ≤ hsNorm (rieszKernel psi c omega) ^ 2 := by
  calc ∑' j, val j ^ 2
      = ∑' j, ‖TOp (rieszKernel psi c omega)
          (hsKernel_rieszKernel hpow homega hbdd hg) (vec j)‖ ^ 2 :=
        tsum_congr (norm_TOp_vec_sq_eq_sq_riesz hpow homega hbdd hg hvec hvecval)
    _ ≤ hsNorm (rieszKernel psi c omega) ^ 2 :=
        hsNorm_sq_ge_tsum_norm_sq_of_orthonormal hvec

/-! ### The bridge to the cycle integral -/

/-- **The `k = 2` Bessel anchor, bridged to the cycle integral**: for any orthonormal
eigen-enumeration of the uniform-`ω` Riesz operator,
`∑' j, val j ^ 2 ≤ Hurst.weightedRieszCycleIntegral 2 ψ c ω` — the Bessel bound with
the right-hand side stated as the `k = 2` weighted Riesz cycle integral, via the landed
kernel identity `weightedRieszCycleIntegral_two_eq_hsNorm_sq`. -/
theorem tsum_two_riesz_le_cycle
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y)
    {val : ℕ → ℝ} {vec : ℕ → L2} (hvec : Orthonormal ℝ vec)
    (hvecval : ∀ j, TOp (rieszKernel psi c omega)
      (hsKernel_rieszKernel hpow homega hbdd hg) (vec j) = val j • vec j) :
    ∑' j, val j ^ 2 ≤ Hurst.weightedRieszCycleIntegral 2 psi c omega :=
  (tsum_two_riesz_le_hsNorm_sq hpow homega hbdd hg hvec hvecval).trans
    (weightedRieszCycleIntegral_two_eq_hsNorm_sq hconst).symm.le

/-! ### The `k = 2` HasSum -/

/-- **The `k = 2` HasSum anchor at the Riesz operator**: for any orthonormal
eigen-enumeration `(val, vec)` of the uniform-`ω` Riesz operator, the squared-eigenvalue
series has sum exactly `Hurst.weightedRieszCycleIntegral 2 ψ c ω` — the `k = 2` clause of
`Hurst.IsRieszSpectrumSequence` (the `h2` shape of
`HS.isRieszSpectrumSequence_of_hasSum`) — gated on the multiplicity-completeness clause
`hcomplete : ∑' j, val j ^ 2 = hsNorm (rieszKernel ψ c ω) ^ 2` (the documented Parseval
gap; see the module docstring).  The proof: the automatic `HasSum` of a summable family
to its tsum, with the tsum re-expressed through `hcomplete` and the cycle-integral
identification `weightedRieszCycleIntegral_two_eq_hsNorm_sq`. -/
theorem hasSum_two_riesz
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y)
    {val : ℕ → ℝ} {vec : ℕ → L2} (hvec : Orthonormal ℝ vec)
    (hvecval : ∀ j, TOp (rieszKernel psi c omega)
      (hsKernel_rieszKernel hpow homega hbdd hg) (vec j) = val j • vec j)
    (hcomplete : ∑' j, val j ^ 2 = hsNorm (rieszKernel psi c omega) ^ 2) :
    HasSum (fun j => val j ^ 2) (Hurst.weightedRieszCycleIntegral 2 psi c omega) := by
  rw [weightedRieszCycleIntegral_two_eq_hsNorm_sq hconst, ← hcomplete]
  exact (summable_two_riesz hpow homega hbdd hg hvec hvecval).hasSum

/-- **The Riesz `k = 2` anchor, full signature**: packaging of the `k = 2` clause of
`Hurst.IsRieszSpectrumSequence` at the compact self-adjoint Riesz operator
(`hCompact : isCompactOperator_TOp_riesz`, `hsym : isSymmetric_TOp_rieszKernel` —
the inputs of the enumeration production), for any orthonormal eigen-enumeration
`vec` with eigenvalues `val`.  Delivers: square-summability of `val` (the
`Summable` clause of `IsWeightedRieszSpectrum`), the unconditional Bessel bound of
the enumeration against the `k = 2` cycle integral, and — under the
multiplicity-completeness gate (see module docstring) — the `k = 2` `HasSum`. -/
theorem riesz_k2_anchor
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y)
    (_hCompact : IsCompactOperator (TOp (rieszKernel psi c omega)
      (hsKernel_rieszKernel hpow homega hbdd hg)))
    (_hsym : (↑(TOp (rieszKernel psi c omega)
      (hsKernel_rieszKernel hpow homega hbdd hg)) : L2 →ₗ[ℝ] L2).IsSymmetric)
    {val : ℕ → ℝ} {vec : ℕ → L2} (hvec : Orthonormal ℝ vec)
    (hvecval : ∀ j, TOp (rieszKernel psi c omega)
      (hsKernel_rieszKernel hpow homega hbdd hg) (vec j) = val j • vec j)
    (hcomplete : ∑' j, val j ^ 2 = hsNorm (rieszKernel psi c omega) ^ 2) :
    Summable (fun j => val j ^ 2) ∧
    ∑' j, val j ^ 2 ≤ Hurst.weightedRieszCycleIntegral 2 psi c omega ∧
    HasSum (fun j => val j ^ 2) (Hurst.weightedRieszCycleIntegral 2 psi c omega) :=
  ⟨summable_two_riesz hpow homega hbdd hg hvec hvecval,
   tsum_two_riesz_le_cycle hpow homega hbdd hg hconst hvec hvecval,
   hasSum_two_riesz hpow homega hbdd hg hconst hvec hvecval hcomplete⟩

end HS

end
