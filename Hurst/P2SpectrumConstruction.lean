import Hurst.ExternalSecondChaosLimit

/-!
# Package P2: construction of the Riesz spectrum sequence

`IsWeightedRieszSpectrum` (in `Hurst/ExternalSecondChaosLimit.lean`) asks for a
real sequence `lambda` such that `sum lambda j ^ 2` is summable and, for every
`k >= 2`, the `k`-th powers have sum exactly `weightedRieszCycleIntegral k psi
c omega`.  The written construction (direct_proofs/23, sections A1-A6) forms
`B = K^(1/2) M_omega K^(1/2)` on `L^2([-1,1])` and enumerates the eigenvalues
of the compact self-adjoint operator `B` with multiplicity.

That enumeration **cannot yet be carried out**: Mathlib v4.31.0 has no
Hilbert-Schmidt operator API at all (file23 A3 has to be built from scratch),
no construction of a bounded/compact integral operator from an `L^2` kernel,
no `K^(1/2)` (the Laplace factorisation of file23 A4/A5), no eigenvalue
enumeration *with multiplicity* behind the two available spectral-theorem
lemmas (`ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot`,
`ContinuousLinearMap.finite_dimensional_eigenspace`), and no trace-power
`tr(B^k)` API for which the cycle-integral identification A5/A9 could even be
stated.  Accordingly this file lands, with no placeholders and no new postulates:

* `IsRieszSpectrumSequence` - the complete P2 obligation for one candidate
  sequence as a single predicate, proved equivalent to
  `(forall j, 0 <= lambda j) ∧ IsWeightedRieszSpectrum psi c omega lambda`
  so that a later construction only has to produce the data once;
* `rieszSpectrumZero` - a genuinely *constructed* sequence (a `def`, not an
  `exists`) satisfying all three obligation clauses, for the model instance
  `omega ≡ 0` where every cycle integral vanishes;
* the exact antisymmetry `weightedRieszCycleIntegral k psi c (fun _ => -1) =
  (-1)^k * weightedRieszCycleIntegral k psi c (fun _ => 1)`;
* the derivable necessary conditions: a nonnegative spectrum forces every odd
  power sum (hence every odd cycle integral of the negated weight) to be
  nonnegative, and the unit-weight odd cycle integral to be nonpositive.

**Interface correction (documented deviation).**  The target clause
`0 <= rieszSpectrum psi c omega j` cannot hold *unconditionally* in `omega`:
for the weight `omega ≡ -1` the `k = 3` cycle integral is the negative of the
unit-weight one, and the latter is strictly positive for `0 < psi < 1/2,
0 < c` (the integrand dominates `c^3 * 2^(-3 psi)` on the cube `[-1,1]^3`,
whose volume is `8`).  The strict-positivity step needs the absolute
integrability of the `k = 3` Riesz cycle integral - exactly file23 A2 - which
is part of the missing operator formalisation, so only the derived nonpositivity
is proved here; the nonnegativity clause must therefore be read with a
nonnegative weight (`forall x in [-1,1], 0 <= omega x`), under which the
constructed operator `B` is positive semidefinite and its eigenvalues are
nonnegative.
-/

noncomputable section
open Set MeasureTheory Filter
namespace Hurst

/-! ### The P2 delivery contract -/

/-- The complete P2 obligation for one candidate sequence `lambda`:  everywhere
nonnegative, square-summable, and all power sums `k >= 2` equal the weighted
Riesz cycle integrals of the weight `omega`. -/
def IsRieszSpectrumSequence (psi c : ℝ) (omega : ℝ → ℝ)
    (lambda : ℕ → ℝ) : Prop :=
  (∀ j, 0 ≤ lambda j) ∧ Summable (fun j => lambda j ^ 2) ∧
    ∀ k : ℕ, 2 ≤ k → HasSum (fun j => lambda j ^ k)
      (weightedRieszCycleIntegral k psi c omega)

/-- The P2 contract is exactly a nonnegativity clause on top of
`IsWeightedRieszSpectrum`; the square-summability and the `HasSum` clauses
coincide definitionally. -/
theorem isRieszSpectrumSequence_iff (psi c : ℝ) (omega : ℝ → ℝ)
    (lambda : ℕ → ℝ) :
    IsRieszSpectrumSequence psi c omega lambda ↔
      (∀ j, 0 ≤ lambda j) ∧ IsWeightedRieszSpectrum psi c omega lambda :=
  ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

/-- Any sequence already known to satisfy the spectral characterisation with
nonnegative entries delivers the P2 contract. -/
theorem isRieszSpectrumSequence_of_nonneg (psi c : ℝ) (omega : ℝ → ℝ)
    {lambda : ℕ → ℝ} (hnn : ∀ j, 0 ≤ lambda j)
    (hspec : IsWeightedRieszSpectrum psi c omega lambda) :
    IsRieszSpectrumSequence psi c omega lambda :=
  ⟨hnn, hspec.1, hspec.2⟩

/-! ### Generic necessary condition: nonnegative spectra and odd powers -/

/-- A series of nonnegative reals has a nonnegative sum; for odd `k` the
`k`-th powers of a nonnegative sequence are nonnegative, so any `HasSum` target
of them is nonnegative. -/
theorem hasSum_odd_pow_nonneg {lambda : ℕ → ℝ} {t : ℝ}
    (hnn : ∀ j, 0 ≤ lambda j) (h : HasSum (fun j => lambda j ^ k) t)
    (hkodd : Odd k) : 0 ≤ t := by
  rcases hkodd with ⟨m, rfl⟩
  exact hasSum_le (fun j => pow_nonneg (hnn j) (2 * m + 1)) hasSum_zero h

/-! ### A fully constructed instance: the zero weight -/

/-- The constructed Riesz spectrum sequence for the zero weight: identically
zero.  This is a definition, not an existence statement. -/
def rieszSpectrumZero (psi c : ℝ) : ℕ → ℝ := fun _ => 0

theorem rieszSpectrumZero_nonneg (psi c : ℝ) (j : ℕ) :
    0 ≤ rieszSpectrumZero psi c j := le_refl _

theorem rieszSpectrumZero_sq_summable (psi c : ℝ) :
    Summable (fun j => rieszSpectrumZero psi c j ^ 2) := by
  have hterm : ∀ j : ℕ, rieszSpectrumZero psi c j ^ 2 = (0 : ℝ) := fun j => by
    simp [rieszSpectrumZero]
  exact ⟨0, funext hterm ▸ hasSum_zero⟩

/-- For the zero weight every cycle integral vanishes: one factor of the
product is already zero. -/
theorem weightedRieszCycleIntegral_zero_weight (k : ℕ) (psi c : ℝ)
    (hk : 1 ≤ k) :
    weightedRieszCycleIntegral k psi c (fun _ => 0) = 0 := by
  have hzero : ∀ z : Fin k → ℝ,
      (∏ i : Fin k, (Icc (-1 : ℝ) 1).indicator (fun _ => 0) (z i) * c *
        |z i - z (finCyclicSucc i)| ^ (-psi)) = (0 : ℝ) :=
    fun z => Finset.prod_eq_zero (i := ⟨0, by omega⟩) (Finset.mem_univ _) (by
      by_cases hm : z ⟨0, by omega⟩ ∈ Icc (-1 : ℝ) 1
      · rw [Set.indicator_of_mem hm]; ring
      · rw [Set.indicator_of_notMem hm]; ring)
  unfold weightedRieszCycleIntegral
  rw [integral_congr_ae (Filter.Eventually.of_forall hzero)]
  simp

/-- The constructed zero-weight spectrum has, for every `k >= 2`, exactly the
vanishing cycle integral as its `k`-th power sum. -/
theorem rieszSpectrumZero_hasSum (psi c : ℝ) (k : ℕ) (hk : 2 ≤ k) :
    HasSum (fun j => rieszSpectrumZero psi c j ^ k)
      (weightedRieszCycleIntegral k psi c (fun _ => 0)) := by
  rw [weightedRieszCycleIntegral_zero_weight _ _ _ (by omega)]
  have hterm : ∀ j : ℕ, rieszSpectrumZero psi c j ^ k = (0 : ℝ) := fun j => by
    simp [rieszSpectrumZero, zero_pow (show k ≠ 0 by omega)]
  exact funext hterm ▸ hasSum_zero

/-- The zero weight carries the complete P2 contract with the constructed
sequence `rieszSpectrumZero`. -/
theorem isRieszSpectrumSequence_zero_weight (psi c : ℝ) :
    IsRieszSpectrumSequence psi c (fun _ => 0) (rieszSpectrumZero psi c) :=
  ⟨fun j => rieszSpectrumZero_nonneg psi c j, rieszSpectrumZero_sq_summable psi c,
    rieszSpectrumZero_hasSum psi c⟩

/-! ### Odd-power antisymmetry under negating the weight -/

/-- Negating the weight multiplies the `k`-th cycle integral by `(-1)^k`. -/
theorem weightedRieszCycleIntegral_neg_one_weight (k : ℕ) (psi c : ℝ) :
    weightedRieszCycleIntegral k psi c (fun _ => -1)
      = (-1 : ℝ) ^ k * weightedRieszCycleIntegral k psi c (fun _ => 1) := by
  have hfac : ∀ (z : Fin k → ℝ) (i : Fin k),
      (Icc (-1 : ℝ) 1).indicator (fun _ => -(1 : ℝ)) (z i) * c *
        |z i - z (finCyclicSucc i)| ^ (-psi)
      = -((Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) (z i) * c *
        |z i - z (finCyclicSucc i)| ^ (-psi)) := by
    intro z i
    by_cases hm : z i ∈ Icc (-1 : ℝ) 1
    · rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm]; ring
    · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm]; ring
  have hprod : ∀ z : Fin k → ℝ,
      (∏ i : Fin k, (Icc (-1 : ℝ) 1).indicator (fun _ => -(1 : ℝ)) (z i) * c *
        |z i - z (finCyclicSucc i)| ^ (-psi))
      = (-1 : ℝ) ^ k * ∏ i : Fin k,
        (Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) (z i) * c *
        |z i - z (finCyclicSucc i)| ^ (-psi) := by
    intro z
    calc ∏ i : Fin k, (Icc (-1 : ℝ) 1).indicator (fun _ => -(1 : ℝ)) (z i) * c *
        |z i - z (finCyclicSucc i)| ^ (-psi)
        = ∏ i : Fin k, -((Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) (z i) * c *
        |z i - z (finCyclicSucc i)| ^ (-psi)) :=
          Finset.prod_congr rfl fun i _ => hfac z i
      _ = (-1 : ℝ) ^ Finset.univ.card * ∏ i : Fin k,
        (Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) (z i) * c *
        |z i - z (finCyclicSucc i)| ^ (-psi) := Finset.prod_neg _
      _ = (-1 : ℝ) ^ k * _ := by rw [Finset.card_univ, Fintype.card_fin]
  unfold weightedRieszCycleIntegral
  rw [integral_congr_ae (Filter.Eventually.of_forall hprod), integral_const_mul]

/-- A nonnegative spectrum of the negated weight forces every odd cycle
integral of that weight to be nonnegative. -/
theorem nonneg_spectrum_forces_odd_cycle_nonneg (psi c : ℝ)
    {lambda : ℕ → ℝ} (hnn : ∀ j, 0 ≤ lambda j)
    (hspec : IsWeightedRieszSpectrum psi c (fun _ => -1) lambda)
    (k : ℕ) (hk : 2 ≤ k) (hkodd : Odd k) :
    0 ≤ weightedRieszCycleIntegral k psi c (fun _ => -1) :=
  hasSum_odd_pow_nonneg hnn (hspec.2 k hk) hkodd

/-- Consequently, if the negated weight has a nonnegative spectrum, every odd
unit-weight cycle integral is nonpositive.  Combined with the strict
positivity of `weightedRieszCycleIntegral 3 psi c (fun _ => 1)` for
`0 < psi < 1/2, 0 < c` (whose formalisation is blocked by the missing absolute
integrability of the cycle integrand, file23 A2), this shows the nonnegativity
clause of the P2 contract needs a nonnegative weight. -/
theorem odd_cycle_integral_nonpos_of_nonneg_spectrum (psi c : ℝ)
    {lambda : ℕ → ℝ} (hnn : ∀ j, 0 ≤ lambda j)
    (hspec : IsWeightedRieszSpectrum psi c (fun _ => -1) lambda)
    (k : ℕ) (hk : 2 ≤ k) (hkodd : Odd k) :
    weightedRieszCycleIntegral k psi c (fun _ => 1) ≤ 0 := by
  rcases hkodd with ⟨m, rfl⟩
  have h1 := nonneg_spectrum_forces_odd_cycle_nonneg psi c hnn hspec (2 * m + 1)
    (by omega) ⟨m, rfl⟩
  rw [weightedRieszCycleIntegral_neg_one_weight,
    show ((-1 : ℝ) ^ (2 * m + 1) = -1) by
      rw [pow_succ, pow_mul, pow_two]; norm_num] at h1
  linarith

end Hurst

