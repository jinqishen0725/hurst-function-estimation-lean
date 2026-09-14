import Hurst.PeelingInduction
import Hurst.SpectralMatchingTail
import Hurst.SignedInterfaceFinal

/-!
# P3 signed matching packaging: separate positive/negative sorting

This file implements the PACKAGE P3 of
`direct_proofs/23_spectral_probability_support.md` (sections B1-B5, D1): the
signed matching packaging by SEPARATE sorting of the positive and the negative
part of a signed coefficient array.

Given a signed coefficient row `c : Fin m → ℝ`, its positive part
`signedPosPart c i = max (c i) 0` and its absolute negative part
`signedAbsNegPart c i = max (- c i) 0` are both nonnegative, satisfy
`c i = signedPosPart c i - signedAbsNegPart c i` and
`|c i| = signedPosPart c i + signedAbsNegPart c i`, and each is sorted by the
canonical `decreasingSpectralPerm` (i.e. through `padRearranged`).

Main contents:

* deterministic core (B3/B5.1):
  - `signed_pow_decompose`, `sum_pow_signed_decompose` : the per-term and
    summed power decomposition with the `(-1)^k` sign bookkeeping;
  - `sum_pow_even_of_neg` : the B5.1 caution, even power sums do not identify
    signs (`c` and `-c` have identical even power sums);
  - `sum_pow_abs_decompose`, `sum_sq_signed_decompose` : the absolute-value
    (hence square-sum) decomposition into positive/negative masses;
* interleaved zero-padding (D1):
  - `zeroPaddedRow`, `zeroPadding_identDistrib` : inserting zeros into a
    coefficient row does not change the law of the centered spectral-square
    statistic (reusing `centeredSpectralPrefix_identDistrib`);
  - `signedInterleavedRow` : the B3 interleaved row (positive part sorted
    decreasingly at even positions, negative part sorted decreasingly at odd
    positions), with `signedInterleavedRow_sum_sq` : its square sum equals the
    square sum of the original row;
* tail bounds (B4): `spectralTailBound_of_paddedSorting` packages the
  translation of `padRearranged`-convergence into the input shape of
  `spectralTailBound_of_padded_coefficient_convergence`; instantiated for the
  positive part (`posPart_spectralTailBound`) and, in the vanishing regime,
  for the negative part (`negPart_spectralTailBound_of_negMass`);
* the composed signed matching theorem (B3+B4+D1 route with vanishing negative
  mass): from (i) positive-part sorted convergence to `lamP` (through the
  peeling power sums `hp`), and (ii) vanishing squared negative mass
  `hNegMass`, conclude the FULL signed matching data consumed by
  `centeredSpectralSquares_tendsto_secondChaos_of_signedMatching`:
  - `sum_absNegPart_pow_tendsto_zero` : all negative-part power sums vanish;
  - `paddedAbsRearranged_tendsto_of_posSorting_and_negMass` : the `hAbs` shape
    `padRearranged (|c|) → lamP`;
  - `sum_sq_tendsto_of_posSorting_and_negMass` : the `htr2` shape;
  - `signedMatchingData_of_posSorting_and_negMass` : the data conjunction;
  - `centeredSpectralSquares_tendsto_secondChaos_of_posSorting_and_negMass` :
    the composed `TendstoInDistribution` endpoint.

Known gap (documented, not hidden): the distributional identity between the
original row and the interleaved sorted row `signedInterleavedRow` (the second
half of D1) requires a sign-aware value-matching permutation of the zero
padded row; only the zero-padding half and the deterministic square-sum
identity are landed here.  The composed theorem below bypasses it via the
peeling route (`paddedRearranged_tendsto`).
-/

set_option maxHeartbeats 4000000

noncomputable section
namespace Hurst

open Filter Topology MeasureTheory ProbabilityTheory

/-! ## Deterministic core: positive and negative parts (B3/B5.1) -/

section Parts

/-- The positive part of a signed coefficient array: `max (c i) 0`. -/
def signedPosPart {m : ℕ} (c : Fin m → ℝ) : Fin m → ℝ := fun i => max (c i) 0

/-- The absolute negative part of a signed coefficient array: `max (- c i) 0`.
Its square is the squared negative mass `(min (c i) 0) ^ 2`. -/
def signedAbsNegPart {m : ℕ} (c : Fin m → ℝ) : Fin m → ℝ := fun i => max (-c i) 0

theorem signedPosPart_nonneg {m : ℕ} (c : Fin m → ℝ) (i : Fin m) :
    0 ≤ signedPosPart c i := le_max_right _ _

theorem signedAbsNegPart_nonneg {m : ℕ} (c : Fin m → ℝ) (i : Fin m) :
    0 ≤ signedAbsNegPart c i := le_max_right _ _

/-- The absolute negative part is the negative of the negative-part function
`min (c i) 0` used by the `hNegMass` hypothesis of the signed packaging. -/
theorem signedAbsNegPart_eq_neg_min {m : ℕ} (c : Fin m → ℝ) (i : Fin m) :
    signedAbsNegPart c i = -min (c i) 0 := by
  by_cases h : 0 ≤ c i
  · rw [signedAbsNegPart, max_eq_right (by linarith : -c i ≤ 0), min_eq_right h, neg_zero]
  · rw [signedAbsNegPart, max_eq_left (by linarith : 0 ≤ -c i), min_eq_left (by linarith : c i ≤ 0)]

/-- Pointwise signed decomposition: `c = pos - |neg|`. -/
theorem signed_eq_sub_parts {m : ℕ} (c : Fin m → ℝ) (i : Fin m) :
    c i = signedPosPart c i - signedAbsNegPart c i := by
  by_cases h : 0 ≤ c i
  · rw [signedPosPart, max_eq_left h, signedAbsNegPart, max_eq_right (by linarith : -c i ≤ 0),
      sub_zero]
  · rw [signedPosPart, max_eq_right (by linarith : c i ≤ 0), signedAbsNegPart,
      max_eq_left (by linarith : 0 ≤ -c i), zero_sub, neg_neg]

/-- Pointwise absolute decomposition: `|c| = pos + |neg|`. -/
theorem signed_abs_eq_add_parts {m : ℕ} (c : Fin m → ℝ) (i : Fin m) :
    |c i| = signedPosPart c i + signedAbsNegPart c i := by
  by_cases h : 0 ≤ c i
  · rw [abs_of_nonneg h, signedPosPart, max_eq_left h, signedAbsNegPart,
      max_eq_right (by linarith : -c i ≤ 0), add_zero]
  · rw [abs_of_nonpos (by linarith : c i ≤ 0), signedPosPart,
      max_eq_right (by linarith : c i ≤ 0), signedAbsNegPart,
      max_eq_left (by linarith : 0 ≤ -c i), zero_add]

/-- Per-term signed power decomposition with the `(-1) ^ k` bookkeeping
(each index has at most one nonzero part, so no binomial terms appear). -/
theorem signed_pow_decompose {m : ℕ} (c : Fin m → ℝ) (i : Fin m) {k : ℕ} (hk : 0 < k) :
    c i ^ k = signedPosPart c i ^ k + (-1 : ℝ) ^ k * signedAbsNegPart c i ^ k := by
  by_cases h : 0 ≤ c i
  · rw [signedPosPart, max_eq_left h, signedAbsNegPart, max_eq_right (by linarith : -c i ≤ 0),
      zero_pow (by omega), mul_zero, add_zero]
  · rw [signedPosPart, max_eq_right (by linarith : c i ≤ 0), zero_pow (by omega), zero_add,
      signedAbsNegPart, max_eq_left (by linarith : 0 ≤ -c i), ← mul_pow, neg_mul_neg, one_mul]

/-- **Summed signed power decomposition (B5.1 made precise).**  For `k ≥ 1`
the `k`-th power sum of a signed row is the positive-part power sum plus
`(-1) ^ k` times the absolute-negative-part power sum.  At EVEN `k` this is
the sum of the two squared masses at `k = 2` and shows why even power sums
alone cannot separate the positive from the negative spectrum. -/
theorem sum_pow_signed_decompose {m : ℕ} (c : Fin m → ℝ) {k : ℕ} (hk : 0 < k) :
    (∑ i : Fin m, c i ^ k)
      = (∑ i : Fin m, signedPosPart c i ^ k)
        + (-1 : ℝ) ^ k * ∑ i : Fin m, signedAbsNegPart c i ^ k := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => signed_pow_decompose c i hk

/-- The B5.1 caution: even power sums do not identify signs. -/
theorem sum_pow_even_of_neg {m : ℕ} (c : Fin m → ℝ) {k : ℕ} (hk : Even k) :
    (∑ i : Fin m, c i ^ k) = ∑ i : Fin m, (-c i) ^ k :=
  Finset.sum_congr rfl fun i _ => by
    rw [← abs_pow_even (a := -c i) hk, abs_neg, abs_pow_even hk]

/-- Absolute-value power decomposition (no sign factor). -/
theorem sum_pow_abs_decompose {m : ℕ} (c : Fin m → ℝ) {k : ℕ} (hk : 0 < k) :
    (∑ i : Fin m, |c i| ^ k)
      = (∑ i : Fin m, signedPosPart c i ^ k)
        + ∑ i : Fin m, signedAbsNegPart c i ^ k := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by
    by_cases h : 0 ≤ c i
    · rw [abs_of_nonneg h, signedPosPart, max_eq_left h, signedAbsNegPart,
        max_eq_right (by linarith : -c i ≤ 0), zero_pow (by omega), add_zero]
    · rw [abs_of_nonpos (by linarith : c i ≤ 0), signedPosPart,
        max_eq_right (by linarith : c i ≤ 0), zero_pow (by omega), zero_add, signedAbsNegPart,
        max_eq_left (by linarith : 0 ≤ -c i)]

/-- The square-sum decomposition `∑ c² = ∑ pos² + ∑ |neg|²`. -/
theorem sum_sq_signed_decompose {m : ℕ} (c : Fin m → ℝ) :
    (∑ i : Fin m, c i ^ 2)
      = (∑ i : Fin m, signedPosPart c i ^ 2)
        + ∑ i : Fin m, signedAbsNegPart c i ^ 2 := by
  have h := sum_pow_signed_decompose c (k := 2) (by norm_num)
  rw [show (-1 : ℝ) ^ 2 = 1 by norm_num, one_mul] at h
  exact h

end Parts

/-! ## Negative-part power sums vanish with the negative mass -/

section NegMass

variable {m : ℕ → ℕ} {c : ∀ n, Fin (m n) → ℝ}

/-- **All absolute-negative-part power sums vanish with the negative mass.**
For `k ≥ 2`, once the total squared negative mass is at most `1`, every
negative entry is at most `1`, so the `k`-th power is dominated by the
square. -/
theorem sum_absNegPart_pow_tendsto_zero
    (hNegMass : Tendsto (fun n ↦ ∑ i : Fin (m n), (min (c n i) 0) ^ 2) atTop (𝓝 0))
    {k : ℕ} (hk : 2 ≤ k) :
    Tendsto (fun n ↦ ∑ i : Fin (m n), signedAbsNegPart (c n) i ^ k) atTop (𝓝 0) := by
  have h2 : Tendsto (fun n ↦ ∑ i : Fin (m n), signedAbsNegPart (c n) i ^ 2)
      atTop (𝓝 0) := by
    refine hNegMass.congr fun n => ?_
    exact Finset.sum_congr rfl fun i _ => by rw [signedAbsNegPart_eq_neg_min, neg_sq]
  have h1 : ∀ᶠ n in atTop,
      (∑ i : Fin (m n), signedAbsNegPart (c n) i ^ 2) ≤ 1 := by
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
      (Metric.tendsto_nhds.mp h2 (1 : ℝ) one_pos)
    refine Filter.eventually_atTop.2 ⟨N, fun n hn => ?_⟩
    have habs := hN n hn
    rw [Real.dist_eq] at habs
    have hlt : (∑ i : Fin (m n), signedAbsNegPart (c n) i ^ 2) < 1 := by
      have h2' := abs_lt.mp habs
      linarith
    linarith
  have hle : ∀ᶠ n in atTop,
      (∑ i : Fin (m n), signedAbsNegPart (c n) i ^ k)
        ≤ (∑ i : Fin (m n), signedAbsNegPart (c n) i ^ 2) := by
    filter_upwards [h1] with n hn
    refine Finset.sum_le_sum fun i _ => ?_
    have hi : signedAbsNegPart (c n) i ≤ 1 := by
      have hsingle := Finset.single_le_sum
        (f := fun j : Fin (m n) => signedAbsNegPart (c n) j ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i)
      have hsq : signedAbsNegPart (c n) i ^ 2 ≤ 1 := le_trans hsingle hn
      have hnn : 0 ≤ signedAbsNegPart (c n) i := signedAbsNegPart_nonneg _ i
      by_cases hlt : 1 < signedAbsNegPart (c n) i
      · exact absurd hsq (by nlinarith [hlt])
      · exact not_lt.mp hlt
    have hpow2 : signedAbsNegPart (c n) i ^ k ≤ signedAbsNegPart (c n) i ^ 2 := by
      have hsplit : signedAbsNegPart (c n) i ^ k
          = signedAbsNegPart (c n) i ^ (k - 2) * signedAbsNegPart (c n) i ^ 2 := by
        rw [← pow_add, Nat.sub_add_cancel hk]
      calc signedAbsNegPart (c n) i ^ k
          = signedAbsNegPart (c n) i ^ (k - 2) * signedAbsNegPart (c n) i ^ 2 := hsplit
        _ ≤ 1 * signedAbsNegPart (c n) i ^ 2 := by
            refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
            have hp := pow_le_pow_left₀ (signedAbsNegPart_nonneg _ i) hi (k - 2)
            rwa [one_pow] at hp
        _ ≤ signedAbsNegPart (c n) i ^ 2 := by rw [one_mul]
    exact hpow2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2
    (Eventually.of_forall fun n =>
      Finset.sum_nonneg fun i _ => pow_nonneg (signedAbsNegPart_nonneg _ i) k) hle

end NegMass

/-! ## Interleaved zero-padding (D1): the padding half -/

section Padding

/-- The coefficient row `c` padded with `m` zeros to length `2 * m`. -/
def zeroPaddedRow {m : ℕ} (c : Fin m → ℝ) : Fin (2 * m) → ℝ :=
  fun i => if h : i.val < m then c ⟨i.val, h⟩ else 0

theorem centeredSpectralSquares_zeroPaddedRow_eq_prefix {m : ℕ} (c : Fin m → ℝ)
    (x : EuclideanSpace ℝ (Fin (2 * m))) :
    centeredSpectralSquares (zeroPaddedRow c) x = centeredSpectralPrefix (zeroPaddedRow c) m x := by
  unfold centeredSpectralSquares centeredSpectralPrefix zeroPaddedRow
  exact Finset.sum_congr rfl fun i _ => by
    by_cases h : i.val < m <;> simp [h]

/-- **Zero padding preserves the law (D1, padding half).**  The centered
spectral-square statistic of a row padded with `m` zeros has the same
distribution as the statistic of the original row (the first `m` coordinates
of the larger standard Gaussian vector are standard Gaussian and the extra
coordinates are multiplied by zero). -/
theorem zeroPadding_identDistrib {m : ℕ} (c : Fin m → ℝ) :
    IdentDistrib (centeredSpectralSquares (zeroPaddedRow c))
      (centeredSpectralSquares c)
      (stdGaussian (EuclideanSpace ℝ (Fin (2 * m))))
      (stdGaussian (EuclideanSpace ℝ (Fin m))) := by
  have hle : m ≤ 2 * m := by omega
  have hfun : centeredSpectralSquares (zeroPaddedRow c)
      = centeredSpectralPrefix (zeroPaddedRow c) m :=
    funext (centeredSpectralSquares_zeroPaddedRow_eq_prefix c)
  rw [hfun]
  have h1 := centeredSpectralPrefix_identDistrib (zeroPaddedRow c) m hle
  have hcoef : (fun j : Fin m ↦ zeroPaddedRow c (Fin.castLE hle j)) = c := by
    funext j
    simp [zeroPaddedRow]
  rw [hcoef] at h1
  exact h1

end Padding

/-! ## The interleaved sorted row (B3) and its square sum -/

section Interleaved

/-- The B3 interleaved row: at even positions the decreasingly rearranged
positive part, at odd positions the NEGATIVE of the decreasingly rearranged
absolute negative part (both zero-padded to length `m`). -/
def signedInterleavedRow {m : ℕ} (c : Fin m → ℝ) : Fin (2 * m) → ℝ :=
  fun i => if h : i.val % 2 = 0 then padRearranged (signedPosPart c) (i.val / 2)
    else -padRearranged (signedAbsNegPart c) (i.val / 2)

/-- Sum over the even positions reindexes over `Fin m`. -/
private theorem sum_even_block {m : ℕ} (g : ℕ → ℝ) :
    (∑ i : Fin (2 * m), if i.val % 2 = 0 then g (i.val / 2) else 0)
      = ∑ j : Fin m, g j.val := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun i hi => (⟨i.val / 2, ?_⟩ : Fin m)) ?_ ?_ ?_ ?_
  · have h2 : i.val % 2 = 0 := (Finset.mem_filter.mp hi).2
    have hlt : i.val < 2 * m := i.isLt
    have h3 := Nat.mod_add_div i.val 2
    omega
  · intro a _
    exact Finset.mem_univ _
  · intro a ha b hb hEq
    have ha2 : a.val % 2 = 0 := (Finset.mem_filter.mp ha).2
    have hb2 : b.val % 2 = 0 := (Finset.mem_filter.mp hb).2
    have h1 := Nat.mod_add_div a.val 2
    have h2 := Nat.mod_add_div b.val 2
    have hval : a.val / 2 = b.val / 2 := congrArg Fin.val hEq
    exact Fin.ext (by omega)
  · intro b _
    have hblt : b.val < m := b.isLt
    have h2 : (2 * b.val) % 2 = 0 := by omega
    refine ⟨⟨2 * b.val, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩, ?_⟩
    exact Fin.ext (show ((2 * b.val) / 2 : ℕ) = b.val by omega)
  · intro a _
    rfl

/-- Sum over the odd positions reindexes over `Fin m`. -/
private theorem sum_odd_block {m : ℕ} (g : ℕ → ℝ) :
    (∑ i : Fin (2 * m), if i.val % 2 = 1 then g (i.val / 2) else 0)
      = ∑ j : Fin m, g j.val := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun i hi => (⟨i.val / 2, ?_⟩ : Fin m)) ?_ ?_ ?_ ?_
  · have h2 : i.val % 2 = 1 := (Finset.mem_filter.mp hi).2
    have hlt : i.val < 2 * m := i.isLt
    have h3 := Nat.mod_add_div i.val 2
    omega
  · intro a _
    exact Finset.mem_univ _
  · intro a ha b hb hEq
    have ha2 : a.val % 2 = 1 := (Finset.mem_filter.mp ha).2
    have hb2 : b.val % 2 = 1 := (Finset.mem_filter.mp hb).2
    have h1 := Nat.mod_add_div a.val 2
    have h2 := Nat.mod_add_div b.val 2
    have hval : a.val / 2 = b.val / 2 := congrArg Fin.val hEq
    exact Fin.ext (by omega)
  · intro b _
    have hblt : b.val < m := b.isLt
    have h2 : (2 * b.val + 1) % 2 = 1 := by omega
    refine ⟨⟨2 * b.val + 1, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩, ?_⟩
    exact Fin.ext (show ((2 * b.val + 1) / 2 : ℕ) = b.val by omega)
  · intro a _
    rfl

/-- The sum of the squares of the padded decreasing rearrangement equals the
sum of squares (the permutation does not change the total). -/
private theorem sum_padRearranged_sq {m : ℕ} (x : Fin m → ℝ) :
    (∑ j : Fin m, padRearranged x j ^ 2) = ∑ i : Fin m, x i ^ 2 := by
  rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) =>
    congrArg (fun z : ℝ => z ^ 2) (padRearranged_of_lt x (Fin.isLt j)))]
  exact Equiv.sum_comp (decreasingSpectralPerm x) (fun i => x i ^ 2)

/-- **The interleaved row has the same square sum as the original row.**
This is the deterministic square-mass bookkeeping of the B3 construction: the
interleaved row contains every nonzero entry of `c` exactly once (plus extra
zeros). -/
theorem signedInterleavedRow_sum_sq {m : ℕ} (c : Fin m → ℝ) :
    (∑ i : Fin (2 * m), signedInterleavedRow c i ^ 2)
      = ∑ i : Fin m, c i ^ 2 := by
  have hsplit : ∀ i : Fin (2 * m),
      signedInterleavedRow c i ^ 2
        = (if i.val % 2 = 0 then padRearranged (signedPosPart c) (i.val / 2) ^ 2 else 0)
          + (if i.val % 2 = 1 then padRearranged (signedAbsNegPart c) (i.val / 2) ^ 2 else 0) := by
    intro i
    rcases Nat.mod_two_eq_zero_or_one i.val with h | h
    · have h1 : ¬(i.val % 2 = 1) := by omega
      simp [signedInterleavedRow, h, h1]
    · have h0 : ¬(i.val % 2 = 0) := by omega
      simp [signedInterleavedRow, h, h0, neg_sq]
  calc ∑ i : Fin (2 * m), signedInterleavedRow c i ^ 2
      = (∑ i : Fin (2 * m),
          if i.val % 2 = 0 then padRearranged (signedPosPart c) (i.val / 2) ^ 2 else 0)
        + ∑ i : Fin (2 * m),
          if i.val % 2 = 1 then padRearranged (signedAbsNegPart c) (i.val / 2) ^ 2 else 0 := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => hsplit i
    _ = (∑ j : Fin m, padRearranged (signedPosPart c) j ^ 2)
        + ∑ j : Fin m, padRearranged (signedAbsNegPart c) j ^ 2 := by
        rw [sum_even_block (fun j : ℕ => padRearranged (signedPosPart c) j ^ 2),
          sum_odd_block (fun j : ℕ => padRearranged (signedAbsNegPart c) j ^ 2)]
    _ = (∑ j : Fin m, signedPosPart c j ^ 2)
        + ∑ j : Fin m, signedAbsNegPart c j ^ 2 := by
        refine congrArg₂ (HAdd.hAdd (α := ℝ) (β := ℝ) (γ := ℝ))
          (sum_padRearranged_sq (signedPosPart c)) (sum_padRearranged_sq (signedAbsNegPart c))
    _ = ∑ i : Fin m, c i ^ 2 := (sum_sq_signed_decompose c).symm

end Interleaved

/-! ## Tail bounds (B4) for the separately sorted parts -/

section TailBounds

/-- **Packaged tail bound from padded sorting convergence (B4).**  The
translation of `padRearranged`-convergence plus square-sum convergence into
the exact input shape of
`spectralTailBound_of_padded_coefficient_convergence`. -/
theorem spectralTailBound_of_paddedSorting (m : ℕ → ℕ) (d : ∀ n, Fin (m n) → ℝ)
    (lam : ℕ → ℝ) (hsum : Summable (fun j : ℕ => lam j ^ 2))
    (hm : Tendsto m atTop atTop)
    (hcoeff : ∀ j : ℕ, Tendsto (fun n ↦ padRearranged (d n) j) atTop (𝓝 (lam j)))
    (htr2 : Tendsto (fun n ↦ ∑ i : Fin (m n), d n i ^ 2)
      atTop (𝓝 (∑' j : ℕ, lam j ^ 2))) :
    ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧
      ∀ K : ℕ, ∀ᶠ n in atTop,
        2 * (∑ i : Fin (m n),
          if K ≤ i.val then d n ((decreasingSpectralPerm (d n)) i) ^ 2 else 0) ≤ e K := by
  have hcoeff' : ∀ j : ℕ, Tendsto (fun n ↦ if hj : j < m n then
      d n ((decreasingSpectralPerm (d n)) ⟨j, hj⟩) else 0)
      atTop (𝓝 (lam j)) := by
    intro j
    exact Tendsto.congr (fun _ => rfl) (hcoeff j)
  have htr2' : Tendsto (fun n ↦ ∑ i : Fin (m n),
      (d n ((decreasingSpectralPerm (d n)) i)) ^ 2)
      atTop (𝓝 (∑' j : ℕ, lam j ^ 2)) := by
    refine Tendsto.congr (fun n => ?_) htr2
    exact (Equiv.sum_comp (decreasingSpectralPerm (d n)) (fun i => d n i ^ 2)).symm
  exact spectralTailBound_of_padded_coefficient_convergence m
    (fun n i => d n ((decreasingSpectralPerm (d n)) i)) lam hsum hm hcoeff' htr2'

/-- **Tail bound for the separately sorted POSITIVE part (B4, item 3).** -/
theorem posPart_spectralTailBound (m : ℕ → ℕ) (c : ∀ n, Fin (m n) → ℝ)
    (lamP : ℕ → ℝ) (hP : Antitone lamP ∧ ∀ j, 0 ≤ lamP j ∧ Summable (fun j => lamP j ^ 2))
    (hm : Tendsto m atTop atTop)
    (hPos : ∀ j : ℕ, Tendsto (fun n ↦ padRearranged (signedPosPart (c n)) j)
      atTop (𝓝 (lamP j)))
    (hp2 : Tendsto (fun n ↦ ∑ i : Fin (m n), signedPosPart (c n) i ^ 2)
      atTop (𝓝 (∑' j : ℕ, lamP j ^ 2))) :
    ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧
      ∀ K : ℕ, ∀ᶠ n in atTop,
        2 * (∑ i : Fin (m n),
          if K ≤ i.val then
            signedPosPart (c n) ((decreasingSpectralPerm (signedPosPart (c n))) i) ^ 2
          else 0) ≤ e K :=
  spectralTailBound_of_paddedSorting m (fun n => signedPosPart (c n)) lamP (hP.2 0).2 hm hPos hp2

/-- **Tail bound for the separately sorted NEGATIVE part in the vanishing
regime (B4, item 3).**  When the squared negative mass vanishes, the negative
part sorts against the zero profile, and the tail bound holds with a universal
error function. -/
theorem negPart_spectralTailBound_of_negMass (m : ℕ → ℕ) (c : ∀ n, Fin (m n) → ℝ)
    (hm0 : ∀ n, 0 < m n) (hm : Tendsto m atTop atTop)
    (hNegMass : Tendsto (fun n ↦ ∑ i : Fin (m n), (min (c n i) 0) ^ 2) atTop (𝓝 0)) :
    ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧
      ∀ K : ℕ, ∀ᶠ n in atTop,
        2 * (∑ i : Fin (m n),
          if K ≤ i.val then
            signedAbsNegPart (c n) ((decreasingSpectralPerm (signedAbsNegPart (c n))) i) ^ 2
          else 0) ≤ e K := by
  have hzero : ∀ j : ℕ, Tendsto (fun n ↦ padRearranged (signedAbsNegPart (c n)) j)
      atTop (𝓝 0) := by
    intro j
    have hk0 : ∀ k : ℕ, 2 ≤ k → (∑' i : ℕ, (fun _ : ℕ => (0:ℝ)) i ^ k) = 0 := by
      intro k _
      simp
    have h := paddedRearranged_tendsto m (fun n i => signedAbsNegPart (c n) i)
      (fun _ : ℕ => (0:ℝ)) hm0 hm
      (fun n i => signedAbsNegPart_nonneg (c n) i)
      ⟨antitone_const, fun j => ⟨le_refl 0,
        (summable_zero.congr fun j : ℕ => (zero_pow (two_ne_zero)).symm)⟩⟩
      (fun k hk => by rw [hk0 k hk]; exact sum_absNegPart_pow_tendsto_zero hNegMass hk)
    exact h j
  have htr2 : Tendsto (fun n ↦ ∑ i : Fin (m n), signedAbsNegPart (c n) i ^ 2)
      atTop (𝓝 (∑' j : ℕ, (fun _ : ℕ => (0:ℝ)) j ^ 2)) := by
    have hz : (∑' j : ℕ, (fun _ : ℕ => (0:ℝ)) j ^ 2) = 0 := by simp
    rw [hz]
    refine hNegMass.congr fun n => ?_
    exact Finset.sum_congr rfl fun i _ => by rw [signedAbsNegPart_eq_neg_min, neg_sq]
  exact spectralTailBound_of_paddedSorting m (fun n => signedAbsNegPart (c n))
    (fun _ : ℕ => (0:ℝ)) (summable_zero.congr fun j : ℕ => (zero_pow (two_ne_zero)).symm)
    hm hzero htr2

end TailBounds

/-! ## The composed signed matching theorem (vanishing negative mass) -/

section Composed

variable {m : ℕ → ℕ} {c : ∀ n, Fin (m n) → ℝ} {lamP : ℕ → ℝ}

/-- **The `hAbs` shape of the signed matching data from separate sorting
(item 4).**  If the positive part sorts against the nonnegative antitone
square-summable profile `lamP` (through the power sums `hp`) and the squared
negative mass vanishes, then the padded decreasing rearrangement of the
ABSOLUTE coefficients converges to `lamP`: this is exactly the `hAbs` input of
`centeredSpectralSquares_tendsto_secondChaos_of_signedMatching`. -/
theorem paddedAbsRearranged_tendsto_of_posSorting_and_negMass
    (m : ℕ → ℕ) (c : ∀ n, Fin (m n) → ℝ) (lamP : ℕ → ℝ)
    (hm0 : ∀ n, 0 < m n) (hmtop : Tendsto m atTop atTop)
    (hP : Antitone lamP ∧ ∀ j, 0 ≤ lamP j ∧ Summable (fun j => lamP j ^ 2))
    (hp : ∀ k : ℕ, 2 ≤ k → Tendsto (fun n => ∑ i : Fin (m n), signedPosPart (c n) i ^ k)
      atTop (𝓝 (∑' j : ℕ, lamP j ^ k)))
    (hNegMass : Tendsto (fun n ↦ ∑ i : Fin (m n), (min (c n i) 0) ^ 2) atTop (𝓝 0)) :
    ∀ j : ℕ, Tendsto (fun n ↦ padRearranged (fun i : Fin (m n) => |c n i|) j)
      atTop (𝓝 (lamP j)) := by
  have hpow : ∀ k : ℕ, 2 ≤ k → Tendsto (fun n => ∑ i : Fin (m n), |c n i| ^ k)
      atTop (𝓝 (∑' j : ℕ, lamP j ^ k)) := by
    intro k hk
    have hneg := sum_absNegPart_pow_tendsto_zero hNegMass hk
    have hsplit : ∀ n : ℕ, (∑ i : Fin (m n), |c n i| ^ k)
        = (∑ i : Fin (m n), signedPosPart (c n) i ^ k)
          + ∑ i : Fin (m n), signedAbsNegPart (c n) i ^ k :=
      fun n => sum_pow_abs_decompose (c n) (by omega)
    have h3 := (hp k hk).add hneg
    rw [add_zero] at h3
    rw [funext hsplit]
    exact h3
  exact paddedRearranged_tendsto m (fun n i => |c n i|) lamP hm0 hmtop
    (fun n i => abs_nonneg _) hP hpow

/-- **The `htr2` shape of the signed matching data from separate sorting.** -/
theorem sum_sq_tendsto_of_posSorting_and_negMass
    (m : ℕ → ℕ) (c : ∀ n, Fin (m n) → ℝ) (lamP : ℕ → ℝ)
    (hp : ∀ k : ℕ, 2 ≤ k → Tendsto (fun n => ∑ i : Fin (m n), signedPosPart (c n) i ^ k)
      atTop (𝓝 (∑' j : ℕ, lamP j ^ k)))
    (hNegMass : Tendsto (fun n ↦ ∑ i : Fin (m n), (min (c n i) 0) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∑ i : Fin (m n), (c n i) ^ 2)
      atTop (𝓝 (∑' j : ℕ, lamP j ^ 2)) := by
  have hneg := sum_absNegPart_pow_tendsto_zero hNegMass (k := 2) (by norm_num)
  have hsplit : ∀ n : ℕ, (∑ i : Fin (m n), (c n i) ^ 2)
      = (∑ i : Fin (m n), signedPosPart (c n) i ^ 2)
        + ∑ i : Fin (m n), signedAbsNegPart (c n) i ^ 2 :=
    fun n => sum_sq_signed_decompose (c n)
  have h3 := (hp 2 (by norm_num)).add hneg
  rw [add_zero] at h3
  rw [funext hsplit]
  exact h3

/-- **The full signed matching data consumed by the consumption theorem**
(the `hAbs`/`htr2`/`hNegMass` triple), assembled from the separate
positive/negative sorting data. -/
theorem signedMatchingData_of_posSorting_and_negMass
    (m : ℕ → ℕ) (c : ∀ n, Fin (m n) → ℝ) (lamP : ℕ → ℝ)
    (hm0 : ∀ n, 0 < m n) (hmtop : Tendsto m atTop atTop)
    (hP : Antitone lamP ∧ ∀ j, 0 ≤ lamP j ∧ Summable (fun j => lamP j ^ 2))
    (hp : ∀ k : ℕ, 2 ≤ k → Tendsto (fun n => ∑ i : Fin (m n), signedPosPart (c n) i ^ k)
      atTop (𝓝 (∑' j : ℕ, lamP j ^ k)))
    (hNegMass : Tendsto (fun n ↦ ∑ i : Fin (m n), (min (c n i) 0) ^ 2) atTop (𝓝 0)) :
    (∀ j : ℕ, Tendsto (fun n ↦ padRearranged (fun i : Fin (m n) => |c n i|) j)
        atTop (𝓝 (lamP j))) ∧
    Tendsto (fun n ↦ ∑ i : Fin (m n), (c n i) ^ 2)
      atTop (𝓝 (∑' j : ℕ, lamP j ^ 2)) ∧
    Tendsto (fun n ↦ ∑ i : Fin (m n), (min (c n i) 0) ^ 2) atTop (𝓝 0) :=
  ⟨paddedAbsRearranged_tendsto_of_posSorting_and_negMass m c lamP hm0 hmtop hP hp hNegMass,
    sum_sq_tendsto_of_posSorting_and_negMass m c lamP hp hNegMass, hNegMass⟩

/-- **The composed signed matching endpoint (P3 centerpiece).**  Given
(i) the positive part sorted against `lamP` through the peeling power sums,
(ii) the squared negative mass `hNegMass` vanishing, and the second-chaos law
of `lamP`, the centered spectral-square statistic of the SIGNED array
converges in distribution to that law.  This consumes exactly the same
`hAbs`/`hNegMass` data shapes as
`gaussianLogQuadraticStatistic_tendsto_secondChaos_of_signedMatching`
(whose feature-level wrapper is the mechanical substitution
`c n = (weightedFeatureQuadraticMatrix_isHermitian (v n) (a n) (w n)).eigenvalues`). -/
theorem centeredSpectralSquares_tendsto_secondChaos_of_posSorting_and_negMass
    (m : ℕ → ℕ) (c : ∀ n, Fin (m n) → ℝ)
    {Theta : Type*} [MeasurableSpace Theta]
    (P' : Measure Theta) [IsProbabilityMeasure P']
    (Q : Theta → ℝ) (lamP : ℕ → ℝ)
    (hQ : IsSecondChaosSeriesLaw P' Q lamP)
    (hm0 : ∀ n, 0 < m n) (hmtop : Tendsto m atTop atTop)
    (hP : Antitone lamP ∧ ∀ j, 0 ≤ lamP j ∧ Summable (fun j => lamP j ^ 2))
    (hp : ∀ k : ℕ, 2 ≤ k → Tendsto (fun n => ∑ i : Fin (m n), signedPosPart (c n) i ^ k)
      atTop (𝓝 (∑' j : ℕ, lamP j ^ k)))
    (hNegMass : Tendsto (fun n ↦ ∑ i : Fin (m n), (min (c n i) 0) ^ 2) atTop (𝓝 0)) :
    TendstoInDistribution (fun n ↦ centeredSpectralSquares (c n))
      atTop Q (fun n ↦ stdGaussian (EuclideanSpace ℝ (Fin (m n)))) P' := by
  have hdata := signedMatchingData_of_posSorting_and_negMass m c lamP hm0 hmtop hP hp hNegMass
  exact centeredSpectralSquares_tendsto_secondChaos_of_signedMatching
    m c P' Q lamP hQ hmtop hdata.1 hdata.2.1 hdata.2.2

end Composed

end Hurst
