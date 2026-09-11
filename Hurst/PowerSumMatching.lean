import Hurst.PowerSumMatchingHelpers
import Hurst.SpectralMatchingSort

/-!
# The power-sum peeling matching lemma

This file plugs the deterministic eigenvalue-matching gap left in
`Hurst/SpectralMatchingInterface.lean`: a bounded nonnegative array whose
power sums (of every order `k ≥ 2`) converge to those of a fixed decreasing
nonnegative `ℓ²` sequence `lambda` must have decreasingly rearranged,
zero-padded spectra converging coefficientwise to `lambda`.

Main contents:

* `decreasingRearrangementPadded`: the decreasingly rearranged, zero-padded
  spectrum of a finite array, built through the canonical
  `decreasingSpectralPerm` of `Hurst/SpectralMatchingSort.lean`;
* `powerSumMatching_peeling`: the peeling step.  If the residual power sums
  `∑' i, r n (i + J) ^ k` converge to the tail targets `T k` for every `k ≥ 2`
  and the k-th roots of `T` recover `lambda J`, then the `J`-th rearranged
  entry converges to `lambda J`;
* `tendsto_decreasingRearrangementPadded_of_powerSums`: the supply-side
  matching theorem - coefficientwise convergence of the canonically permuted
  spectra to `lambda` from power-sum convergence;
* `tendsto_padded_perm_of_powerSums`: the same statement with the rearranged
  function written out literally, matching the `hcoeff` hypothesis of
  `centeredMatrixQuadratic_tendsto_secondChaos_of_decreasing_matching`;
* `powerSums_determine_antitone_sequence`: uniqueness - two decreasing
  nonnegative `ℓ²` sequences with equal power sums for all `k ≥ 2` coincide.

Proof architecture (peeling / max-extraction).  All the analysis happens on
tails of the fixed sequence `lambda` with synchronized subtraction:

1. Tail extraction (`tailPowerSum_root_tendsto` in
   `Hurst/PowerSumMatchingHelpers.lean`): the k-th root of the tail power sums
   `T J k = ∑' i, lambda (i + J) ^ k` converges to `lambda J`;
2. Induction on `J`: subtract the `k`-th power of the `J`-th rearranged entry
   from both the array power sums and the targets, then apply the limsup bound
   (a single entry is dominated by the residual sum) and the liminf bound
   (all residual entries are dominated by the `J`-th entry, so
   `M n k ≤ (r n J) ^ (k - 2) * M n 2`, contradicting the k-th root limit for
   large `k`).
-/

noncomputable section
open Finset Filter Set Metric
open scoped Topology
namespace Hurst

/-! ### The zero-padded decreasing rearrangement -/

/-- The decreasingly rearranged, zero-padded spectrum of the finite array
`x n`, built through the canonical decreasing permutation
`decreasingSpectralPerm` of `Hurst/SpectralMatchingSort.lean`. -/
def decreasingRearrangementPadded (m : ℕ → ℕ) (x : ∀ n, Fin (m n) → ℝ) (n j : ℕ) : ℝ :=
  if hj : j < m n then x n ((decreasingSpectralPerm (x n)) ⟨j, hj⟩) else 0

/-- The zero-padded rearrangement is nonnegative for nonnegative input. -/
theorem decreasingRearrangementPadded_nonneg {m : ℕ → ℕ} {x : ∀ n, Fin (m n) → ℝ}
    (hx : ∀ n i, 0 ≤ x n i) (n j : ℕ) :
    0 ≤ decreasingRearrangementPadded m x n j := by
  rw [decreasingRearrangementPadded]
  split
  · exact hx n _
  · exact le_refl 0

/-- The zero-padded rearrangement vanishes outside the array. -/
theorem decreasingRearrangementPadded_eq_zero {m : ℕ → ℕ} {x : ∀ n, Fin (m n) → ℝ}
    (n j : ℕ) (hj : m n ≤ j) : decreasingRearrangementPadded m x n j = 0 := by
  rw [decreasingRearrangementPadded, dif_neg (by omega)]

/-- The zero-padded rearrangement is antitone in the index. -/
theorem decreasingRearrangementPadded_antitone {m : ℕ → ℕ} {x : ∀ n, Fin (m n) → ℝ}
    (hx : ∀ n i, 0 ≤ x n i) (n : ℕ) :
    Antitone (decreasingRearrangementPadded m x n) := by
  intro j k hjk
  rw [decreasingRearrangementPadded, decreasingRearrangementPadded]
  by_cases hkm : k < m n
  · rw [dif_pos hkm, dif_pos (lt_of_le_of_lt hjk hkm)]
    exact decreasingSpectralPerm_antitone (x n) (Fin.le_def.mpr hjk)
  · rw [dif_neg hkm]
    exact le_trans (le_refl 0) (decreasingRearrangementPadded_nonneg hx n j)

/-- For each fixed `n` and exponent `k ≥ 1`, the zero-padded rearrangement is
summable in the index. -/
theorem decreasingRearrangementPadded_summable {m : ℕ → ℕ} {x : ∀ n, Fin (m n) → ℝ}
    (n k : ℕ) (hk : 1 ≤ k) :
    Summable (fun i : ℕ => decreasingRearrangementPadded m x n i ^ k) := by
  refine summable_of_eventually_eq_zero ⟨m n, fun i hi => ?_⟩
  rw [decreasingRearrangementPadded_eq_zero n i hi, zero_pow (by omega)]

/-- For each fixed `n`, cut `J` and exponent `k ≥ 1`, the tail of the
zero-padded rearrangement is summable in the index. -/
theorem decreasingRearrangementPadded_summable_shift {m : ℕ → ℕ} {x : ∀ n, Fin (m n) → ℝ}
    (n k J : ℕ) (hk : 1 ≤ k) :
    Summable (fun i : ℕ => decreasingRearrangementPadded m x n (i + J) ^ k) := by
  refine summable_of_eventually_eq_zero ⟨m n - J, fun i hi => ?_⟩
  rw [decreasingRearrangementPadded_eq_zero n (i + J) (by omega), zero_pow (by omega)]

/-- The power sums of the array agree with the power sums of the zero-padded
rearrangement. -/
theorem sum_pow_eq_tsum_padded {m : ℕ → ℕ} {x : ∀ n, Fin (m n) → ℝ} (n k : ℕ) (hk : 1 ≤ k) :
    ∑ i : Fin (m n), x n i ^ k
      = ∑' i : ℕ, decreasingRearrangementPadded m x n i ^ k := by
  rw [tsum_eq_sum (f := fun i : ℕ => decreasingRearrangementPadded m x n i ^ k)
    (s := Finset.range (m n))]
  · rw [← Fin.sum_univ_eq_sum_range (fun j : ℕ => decreasingRearrangementPadded m x n j ^ k)
      (m n)]
    have hstep : ∀ i : Fin (m n),
        decreasingRearrangementPadded m x n ↑i ^ k
          = x n ((decreasingSpectralPerm (x n)) i) ^ k := by
      intro i
      rw [decreasingRearrangementPadded, dif_pos i.isLt]
    rw [Finset.sum_congr rfl (fun i _ => hstep i)]
    exact (Equiv.sum_comp (decreasingSpectralPerm (x n))
      (fun i : Fin (m n) => x n i ^ k)).symm
  · intro b hb
    rw [decreasingRearrangementPadded, dif_neg (Finset.mem_range.not.mp hb),
      zero_pow (by omega)]

/-! ### The peeling lemma -/

set_option maxHeartbeats 1500000 in
/-- **Peeling step.**  Let `r n : ℕ → ℝ` be a nonnegative array, `lambda` a
target sequence, and `T` residual power-sum targets: the residual sums
`∑' i, r n (i + J) ^ k` converge to `T k` for every `k ≥ 2`, the k-th roots of
`T` converge to `lambda J`, and `T 2` dominates `lambda J ^ 2` (and vanishes
when `lambda J` does).  Then the `J`-th entry of `r` converges to
`lambda J`. -/
theorem powerSumMatching_peeling
    {lambda : ℕ → ℝ} {r : ℕ → ℕ → ℝ} {J : ℕ} {T : ℕ → ℝ}
    (hnn : ∀ n i, 0 ≤ r n i) (hanti : ∀ n, Antitone (r n))
    (hsum : ∀ n k : ℕ, 2 ≤ k → Summable (fun i : ℕ => r n (i + J) ^ k))
    (hroot : Tendsto (fun k : ℕ => (T k) ^ ((k : ℝ)⁻¹)) atTop (𝓝 (lambda J)))
    (hTge : lambda J ^ 2 ≤ T 2) (hTzero : lambda J = 0 → T 2 = 0)
    (hM : ∀ k : ℕ, 2 ≤ k → Tendsto (fun n : ℕ => ∑' i : ℕ, r n (i + J) ^ k)
      atTop (𝓝 (T k))) :
    Tendsto (fun n : ℕ => r n J) atTop (𝓝 (lambda J)) := by
  have hMpos : ∀ k : ℕ, 2 ≤ k → 0 ≤ T k := fun k hk => by
    refine ge_of_tendsto' (hM k hk) (fun n => ?_)
    exact tsum_nonneg fun i => pow_nonneg (hnn n (i + J)) k
  have hlambda0 : 0 ≤ lambda J := by
    refine ge_of_tendsto hroot ((Filter.eventually_ge_atTop 2).mono fun k hk => ?_)
    exact Real.rpow_nonneg (hMpos k hk) ((k : ℝ)⁻¹)
  -- a single residual entry is dominated by the residual sum
  have hsingle : ∀ (n k : ℕ), 2 ≤ k → (r n J) ^ k ≤ ∑' i : ℕ, r n (i + J) ^ k := by
    intro n k hk
    have h1 := tsum_ge_term_of_nonneg (hsum n k hk)
      (fun i => pow_nonneg (hnn n (i + J)) k)
    rwa [Nat.zero_add] at h1
  -- the residual bound: M n k ≤ (r n J)^(k-2) * M n 2 for k ≥ 2
  have hres : ∀ (n k : ℕ), 2 ≤ k →
      ∑' i : ℕ, r n (i + J) ^ k ≤ (r n J) ^ (k - 2) * ∑' i : ℕ, r n (i + J) ^ 2 := by
    intro n k hk
    obtain ⟨mm, rfl⟩ : ∃ mm, k = mm + 2 := ⟨k - 2, by omega⟩
    refine tsum_le_const_mul_tsum _ (hsum n (mm + 2) (by omega)) (hsum n 2 (by linarith))
      fun i => ?_
    have hle : r n (i + J) ≤ r n J := hanti n (Nat.le_add_left J i)
    rw [pow_add]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (hnn n (i + J)) hle mm) (pow_nonneg (hnn n (i + J)) 2)
  by_cases hJ0 : lambda J = 0
  · -- Zero case: the residual square sum tends to zero, hence r n J → 0.
    have hT2 : T 2 = 0 := hTzero hJ0
    have hM2 : Tendsto (fun n : ℕ => ∑' i : ℕ, r n (i + J) ^ 2) atTop (𝓝 (0 : ℝ)) :=
      hT2 ▸ hM 2 (by linarith)
    have hsqrt' : Tendsto (fun n : ℕ => Real.sqrt (∑' i : ℕ, r n (i + J) ^ 2))
        atTop (𝓝 (0 : ℝ)) := by
      have hcmp := (Real.continuous_sqrt.continuousAt.tendsto).comp hM2
      rwa [Real.sqrt_zero] at hcmp
    have hle : ∀ n : ℕ, r n J ≤ Real.sqrt (∑' i : ℕ, r n (i + J) ^ 2) := fun n => by
      rw [hr n]
      exact Real.sqrt_le_sqrt (hsingle n 2 (by linarith))
    refine Metric.tendsto_nhds.mpr fun ε hε => ?_
    refine (Metric.tendsto_nhds.mp hsqrt' (ε / 2) (by linarith)).mono fun n hn => ?_
    rw [Real.dist_eq] at hn
    obtain ⟨-, hb⟩ := abs_lt.mp hn
    rw [Real.dist_eq, hJ0, sub_zero, abs_eq_self.mpr (hnn n J)]
    calc r n J ≤ Real.sqrt (∑' i : ℕ, r n (i + J) ^ 2) := hle n
      _ < ε := by linarith
  · -- Positive case.
    have ha0 : 0 < lambda J := lt_of_le_of_ne hlambda0 (Ne.symm hJ0)
    -- Upper bound: eventually r n J ≤ lambda J + δ for every δ > 0.
    have hub : ∀ δ : ℝ, 0 < δ →
        Filter.Eventually (fun n : ℕ => r n J ≤ lambda J + δ) atTop := by
      intro δ hδ
      by_contra hcon
      have hfreq0 : ∃ᶠ n in atTop, lambda J + δ < r n J :=
        ((Filter.not_eventually.mp hcon).mono fun n h => not_le.mp h)
      have hrootE : Filter.Eventually
          (fun k : ℕ => (T k) ^ ((k : ℝ)⁻¹) ≤ lambda J + δ / 2) atTop :=
        (Metric.tendsto_nhds.mp hroot (δ / 2) (by linarith)).mono fun k hk => by
          rw [Real.dist_eq] at hk
          have habs := abs_lt.mp hk
          exact le_of_lt (by linarith)
      obtain ⟨k₀, hk₀2, hk₀root⟩ := eventually_atTop_exists_ge hrootE 2
      have hiff : T k₀ ^ ((k₀ : ℝ)⁻¹) ≤ lambda J + δ / 2
          ↔ T k₀ ≤ (lambda J + δ / 2) ^ (k₀ : ℝ) :=
        real_rpow_inv_nat_le (k := k₀) (by linarith) (hMpos k₀ hk₀2) (by linarith)
      have h2 : T k₀ ≤ (lambda J + δ / 2) ^ k₀ := by
        have h3 := hiff.mp hk₀root
        rwa [Real.rpow_natCast] at h3
      have hTk : T k₀ < (lambda J + δ) ^ k₀ :=
        lt_of_le_of_lt h2 (pow_lt_pow_left_real (by linarith)
          (show lambda J + δ / 2 < lambda J + δ by linarith) k₀ (by linarith))
      have hfreq : Filter.Frequently
          (fun n : ℕ => (lambda J + δ) ^ k₀ ≤ ∑' i : ℕ, r n (i + J) ^ k₀) atTop :=
        (hfreq0.mono fun n h =>
          le_trans (le_of_lt (pow_lt_pow_left_real (by linarith) h k₀ hk₀2))
            (hsingle n k₀ hk₀2))
      have hfreqle : (lambda J + δ) ^ k₀ ≤ T k₀ :=
        tendsto_ge_of_frequently_le (hM k₀ (by linarith)) hfreq
      exact absurd hfreqle (not_le.mpr hTk)
    have hlb : ∀ δ : ℝ, 0 < δ → δ ≤ lambda J →
        Filter.Eventually (fun n : ℕ => lambda J - δ ≤ r n J) atTop := by
      intro δ hδpos hδλ
      by_contra hcon
      have hfreq0 : ∃ᶠ n in atTop, r n J < lambda J - δ :=
        ((Filter.not_eventually.mp hcon).mono fun n h => lt_of_not_ge h)
      have hc0 : (0 : ℝ) < lambda J - δ := by linarith
      have hcT : (lambda J - δ) ^ 2 < T 2 := by
        calc (lambda J - δ) ^ 2
            ≤ lambda J ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
          _ ≤ T 2 := hTge
      have hQ1 : (1 : ℝ) ≤ T 2 / (lambda J - δ) ^ 2 :=
        (one_le_div_iff₀ hc0).mpr (le_of_lt hcT)
      have hQroot : Tendsto
          (fun k : ℕ => (lambda J - δ) * (T 2 / (lambda J - δ) ^ 2) ^ ((k : ℝ)⁻¹))
          atTop (𝓝 ((lambda J - δ) * 1)) :=
        (tendsto_rpow_inv_nat_nhds_one hQ1).const_mul _
      -- for large k: (T k)^(1/k) > c * Q^(1/k), hence T k > c^k * Q
      have hbig : Filter.Eventually
          (fun k : ℕ => 2 ≤ k ∧
            (lambda J - δ) ^ k * (T 2 / (lambda J - δ) ^ 2) < T k) atTop := by
        have hdiff : Tendsto
            (fun k : ℕ => (T k) ^ ((k : ℝ)⁻¹)
              - (lambda J - δ) * (T 2 / (lambda J - δ) ^ 2) ^ ((k : ℝ)⁻¹))
            atTop (𝓝 (lambda J - (lambda J - δ))) :=
          hroot.sub hQroot
        refine (Metric.tendsto_nhds.mp hdiff ((lambda J - (lambda J - δ)) / 2)
          (by positivity)).mono fun k hk => ?_
        refine ⟨by linarith, ?_⟩
        rw [Real.dist_eq] at hk
        have habs := abs_lt.mp hk
        have hroot' : ¬ ((T k) ^ ((k : ℝ)⁻¹)
              ≤ (lambda J - δ) * (T 2 / (lambda J - δ) ^ 2) ^ ((k : ℝ)⁻¹)) := by
          intro hle
          rw [Real.dist_eq] at hk
          linarith
        have hiff2 : (T k) ^ ((k : ℝ)⁻¹)
              ≤ (lambda J - δ) * (T 2 / (lambda J - δ) ^ 2) ^ ((k : ℝ)⁻¹)
            ↔ T k ≤ ((lambda J - δ) * (T 2 / (lambda J - δ) ^ 2) ^ ((k : ℝ)⁻¹)) ^ (k : ℝ) :=
          real_rpow_inv_nat_le (k := k) (by linarith) (hMpos k hk) (by positivity)
        have h1 : ¬ (T k ≤ ((lambda J - δ)
              * (T 2 / (lambda J - δ) ^ 2) ^ ((k : ℝ)⁻¹)) ^ (k : ℝ)) :=
          mt hiff2.mp hroot'
        have h2 : ((lambda J - δ) * (T 2 / (lambda J - δ) ^ 2) ^ ((k : ℝ)⁻¹)) ^ (k : ℝ)
            < T k := lt_of_not_ge h1
        rw [Real.rpow_natCast, mul_pow,
          real_pow_rpow_inv (by positivity) (by linarith)] at h2
        exact h2
      obtain ⟨k₀, hk₀2, hk₀T⟩ := eventually_atTop_exists_ge hbig 2
      have hM2T : Tendsto (fun n : ℕ => (lambda J - δ) ^ (k₀ - 2)
          * ∑' i : ℕ, r n (i + J) ^ 2)
          atTop (𝓝 ((lambda J - δ) ^ (k₀ - 2) * T 2)) :=
        Tendsto.const_mul _ (hM 2 (by linarith))
      have hsplit : (lambda J - δ) ^ k₀ * (T 2 / (lambda J - δ) ^ 2)
          = (lambda J - δ) ^ (k₀ - 2) * T 2 := by
        rw [← pow_add]
        field_simp
      have hcontr : (lambda J - δ) ^ (k₀ - 2) * T 2 < T k₀ := by
        rw [← hsplit]
        exact hk₀T
      have hfreq : Filter.Frequently
          (fun n : ℕ => ∑' i : ℕ, r n (i + J) ^ k₀
            ≤ (lambda J - δ) ^ (k₀ - 2) * ∑' i : ℕ, r n (i + J) ^ 2) atTop :=
        (hfreq0.mono fun n h => by
          refine le_trans (hres n k₀ hk₀2) ?_
          refine mul_le_mul_of_nonneg_right ?_
            (tsum_nonneg fun i => pow_nonneg (hnn n (i + J)) 2)
          exact pow_le_pow_left₀ (hnn n J) (le_of_lt h) (k₀ - 2))
      have hle : T k₀ ≤ (lambda J - δ) ^ (k₀ - 2) * T 2 :=
        tendsto_le_of_frequently_le (hM k₀ (by linarith)) hM2T hfreq
      exact absurd hle (not_le.mpr hcontr)
    -- squeeze: upper and lower bounds at tolerance δ/2
    refine Metric.tendsto_nhds.mpr fun ε hε => ?_
    rcases le_or_lt lambda J (ε / 2) with hlow | hlow
    · refine (hub (ε / 2) (by linarith)).mono fun n h1 => ?_
      rw [Real.dist_eq]
      exact lt_of_le_of_lt (abs_le.mpr ⟨by linarith, by linarith⟩) (by linarith)
    · obtain hupper := hub (ε / 2) (by linarith)
      obtain hlower := hlb (ε / 2) (by linarith) (by linarith)
      refine (hupper.and hlower).mono fun n h => ?_
      obtain ⟨h1, h2⟩ := h
      rw [Real.dist_eq]
      exact lt_of_le_of_lt (abs_le.mpr ⟨by linarith, by linarith⟩) (by linarith)

/-! ### Supply-side matching -/

set_option maxHeartbeats 1500000 in
/-- **Supply-side matching (peeling).**  Let `x n` be nonnegative arrays of
spectra and `lambda` a decreasing, nonnegative, `ℓ²` sequence whose power
sums of every order `k ≥ 2` are the limits of the array power sums.  Then the
decreasingly rearranged, zero-padded spectra converge coefficientwise to
`lambda`: for every `j`, `decreasingRearrangementPadded m x n j → lambda j`,
i.e. the canonically permuted entry
`x n (decreasingSpectralPerm (x n) ⟨j, hj⟩)` (zero-padded) converges to
`lambda j`. -/
theorem tendsto_decreasingRearrangementPadded_of_powerSums
    (m : ℕ → ℕ) (x : ∀ n, Fin (m n) → ℝ) (lambda : ℕ → ℝ)
    (hanti : Antitone lambda) (hnn : ∀ j, 0 ≤ lambda j)
    (hsq : Summable (fun j : ℕ => lambda j ^ 2))
    (hxnn : ∀ n i, 0 ≤ x n i)
    (hp : ∀ k : ℕ, 2 ≤ k →
      Tendsto (fun n : ℕ => ∑ i : Fin (m n), x n i ^ k) atTop (𝓝 (∑' j : ℕ, lambda j ^ k))) :
    ∀ j : ℕ, Tendsto (fun n : ℕ => decreasingRearrangementPadded m x n j)
      atTop (𝓝 (lambda j)) := by
  have hpaddedsumshift : ∀ (n k J : ℕ), 1 ≤ k → Summable
      (fun i : ℕ => decreasingRearrangementPadded m x n (i + J) ^ k) :=
    decreasingRearrangementPadded_summable_shift
  have key : ∀ j : ℕ,
      (∀ k : ℕ, 2 ≤ k → Tendsto
        (fun n : ℕ => ∑' i : ℕ, decreasingRearrangementPadded m x n (i + j) ^ k)
        atTop (𝓝 (∑' i : ℕ, lambda (i + j) ^ k)))
      ∧ Tendsto (fun n : ℕ => decreasingRearrangementPadded m x n j)
        atTop (𝓝 (lambda j)) := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      have hQprev : ∀ i : ℕ, i < j → ∀ k : ℕ, 2 ≤ k → Tendsto
          (fun n : ℕ => ∑' i₁ : ℕ, decreasingRearrangementPadded m x n (i₁ + i) ^ k)
          atTop (𝓝 (∑' i₁ : ℕ, lambda (i₁ + i) ^ k)) := fun i hi k hk => (ih i hi).1 k hk
      have hRprev : ∀ i : ℕ, i < j → Tendsto
          (fun n : ℕ => decreasingRearrangementPadded m x n i) atTop (𝓝 (lambda i)) :=
        fun i hi => (ih i hi).2
      by_cases hj0 : j = 0
      · -- Base case j = 0: the full rearranged power sums converge.
        subst hj0
        refine ⟨fun k hk => ?_, ?_⟩
        · simp only [Nat.add_zero]
          refine Tendsto.congr'
            (Filter.Eventually.of_forall fun n => sum_pow_eq_tsum_padded n k (by omega))
            (hp k hk)
        · -- j = 0 is the peeling for the full spectrum
          have hTge : lambda 0 ^ 2 ≤ ∑' i : ℕ, lambda (i + 0) ^ 2 := by
            simp only [Nat.add_zero]
            exact tsum_ge_term_of_nonneg
              (tailPowerSum_summable hanti hnn hsq 0 2 (by linarith))
              (fun i => pow_nonneg (hnn i) 2)
          have hTzero : lambda 0 = 0 → ∑' i : ℕ, lambda (i + 0) ^ 2 = 0 := by
            intro h0
            have hall : ∀ i : ℕ, lambda i = 0 := by
              intro i
              have h1 : lambda i ≤ lambda 0 := hanti (Nat.zero_le i)
              have h2 : 0 ≤ lambda i := hnn _
              rw [h0] at h1
              linarith
            have hz : ∀ i : ℕ, lambda (i + 0) ^ 2 = 0 := by
              intro i
              rw [hall (i + 0)]
              exact zero_pow (by omega)
            simp only [Nat.add_zero, hz, tsum_zero]
          have hR := powerSumMatching_peeling
            (lambda := lambda) (r := fun n i => decreasingRearrangementPadded m x n i)
            (J := 0) (T := fun k => ∑' i : ℕ, lambda (i + 0) ^ k)
            (fun n i => decreasingRearrangementPadded_nonneg hxnn n i)
            (fun n => decreasingRearrangementPadded_antitone hxnn n)
            (fun n k hk => hpaddedsumshift n k 0 (by omega))
            (tailPowerSum_root_tendsto hanti hnn hsq 0) hTge hTzero ?_
          · rw [Nat.add_zero, Nat.add_zero]
            exact fun k hk => Tendsto.congr'
              (Filter.eventually_of_forall fun n => sum_pow_eq_tsum_padded n k (by omega))
              (hp k hk)
          · exact hR
      · -- Inductive step j = j' + 1
        obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        have hQj' : ∀ k : ℕ, 2 ≤ k → Tendsto
            (fun n : ℕ => ∑' i : ℕ, decreasingRearrangementPadded m x n (i + j') ^ k)
            atTop (𝓝 (∑' i : ℕ, lambda (i + j') ^ k)) := hQprev j' (by omega)
        have hRj' : Tendsto (fun n : ℕ => decreasingRearrangementPadded m x n j')
            atTop (𝓝 (lambda j')) := hRprev j' (by omega)
        have hsumTj' : ∀ k : ℕ, 2 ≤ k → Summable (fun i : ℕ => lambda (i + j') ^ k) :=
          tailPowerSum_summable hanti hnn hsq j'
        -- peeling facts at the stage j' + 1
        have hTge : lambda (j' + 1) ^ 2 ≤ ∑' i : ℕ, lambda (i + (j' + 1)) ^ 2 := by
          have h1 := tsum_ge_term_of_nonneg
            (tailPowerSum_summable hanti hnn hsq (j' + 1) 2 (by linarith))
            (fun i => pow_nonneg (hnn (i + (j' + 1))) 2)
          rwa [Nat.zero_add] at h1
        have hTzero : lambda (j' + 1) = 0 →
            ∑' i : ℕ, lambda (i + (j' + 1)) ^ 2 = 0 := by
          intro hj0
          have hall : ∀ i : ℕ, lambda (i + (j' + 1)) = 0 := by
            intro i
            have h1 : lambda (i + (j' + 1)) ≤ lambda (j' + 1) := hanti (by omega)
            have h2 : 0 ≤ lambda (i + (j' + 1)) := hnn _
            rw [hj0] at h1
            linarith
          refine tsum_congr fun i => ?_
          rw [hall i]
          simp
        -- residual convergence: synchronized subtraction
        have hQ : ∀ k : ℕ, 2 ≤ k → Tendsto
            (fun n : ℕ => ∑' i : ℕ, decreasingRearrangementPadded m x n (i + (j' + 1)) ^ k)
            atTop (𝓝 (∑' i : ℕ, lambda (i + (j' + 1)) ^ k)) := by
          intro k hk
          have h1 := hQj' k hk
          have h2 : Tendsto (fun n : ℕ => decreasingRearrangementPadded m x n j' ^ k)
              atTop (𝓝 (lambda j' ^ k)) := hRj'.pow k
          have hsplit1 : ∀ n : ℕ, ∑' i : ℕ,
                decreasingRearrangementPadded m x n (i + (j' + 1)) ^ k
              = ∑' i : ℕ, decreasingRearrangementPadded m x n (i + j') ^ k
                - decreasingRearrangementPadded m x n j' ^ k := by
            intro n
            have hg := (hpaddedsumshift n k j' (by omega)).sum_add_tsum_nat_add 1
            rw [Finset.sum_range_one] at hg
            have hreindex : ∑' i : ℕ,
                  decreasingRearrangementPadded m x n (i + 1 + j') ^ k
                = ∑' i : ℕ, decreasingRearrangementPadded m x n (i + j' + 1) ^ k :=
              tsum_congr fun i => congrArg (fun z => z ^ k) (by omega)
            rw [hreindex, Nat.zero_add] at hg
            linarith
          have htarget : ∑' i : ℕ, lambda (i + j') ^ k - lambda j' ^ k
              = ∑' i : ℕ, lambda (i + (j' + 1)) ^ k := by
            have hg' := (hsumTj' k hk).sum_add_tsum_nat_add 1
            rw [Finset.sum_range_one] at hg'
            have hreindex : ∑' i : ℕ, lambda (i + 1 + j') ^ k
                = ∑' i : ℕ, lambda (i + (j' + 1)) ^ k :=
              tsum_congr fun i => congrArg (fun z => z ^ k) (by omega)
            rw [hreindex, Nat.zero_add] at hg'
            linarith
          refine Tendsto.congr'
            (Filter.Eventually.of_forall fun n => (hsplit1 n).symm) ?_
          rw [htarget]
          exact h1.sub h2
        have hR := powerSumMatching_peeling
          (lambda := lambda) (r := fun n i => decreasingRearrangementPadded m x n i)
          (J := j' + 1) (T := fun k => ∑' i : ℕ, lambda (i + (j' + 1)) ^ k)
          (fun n i => decreasingRearrangementPadded_nonneg hxnn n i)
          (fun n => decreasingRearrangementPadded_antitone hxnn n)
          (fun n k hk => hpaddedsumshift n k (j' + 1) (by omega))
          (tailPowerSum_root_tendsto hanti hnn hsq (j' + 1)) hTge hTzero hQ
        exact ⟨hQ, hR⟩
  · -- final packaging
    intro j
    exact (key j).2

/-- The supply-side matching in the literal `hcoeff` shape consumed by
`centeredMatrixQuadratic_tendsto_secondChaos_of_decreasing_matching`: the
canonically decreasingly permuted, zero-padded eigenvalue-like entries of the
array converge coefficientwise to `lambda`. -/
theorem tendsto_padded_perm_of_powerSums
    (m : ℕ → ℕ) (x : ∀ n, Fin (m n) → ℝ) (lambda : ℕ → ℝ)
    (hanti : Antitone lambda) (hnn : ∀ j, 0 ≤ lambda j)
    (hsq : Summable (fun j : ℕ => lambda j ^ 2))
    (hxnn : ∀ n i, 0 ≤ x n i)
    (hp : ∀ k : ℕ, 2 ≤ k →
      Tendsto (fun n : ℕ => ∑ i : Fin (m n), x n i ^ k) atTop (𝓝 (∑' j : ℕ, lambda j ^ k)))
    (j : ℕ) :
    Tendsto (fun n : ℕ => if hj : j < m n then
        x n ((decreasingSpectralPerm (x n)) ⟨j, hj⟩) else 0) atTop (𝓝 (lambda j)) :=
  tendsto_decreasingRearrangementPadded_of_powerSums m x lambda hanti hnn hsq hxnn hp j

/-! ### Uniqueness -/

/-- A decreasing, nonnegative, `\u2113\u00b2` sequence is determined by its tails: if
the tails of two such sequences have equal power sums for every `k \u2265 2`, the
leading entries agree. -/
theorem tail_eq_of_tailPowerSums_eq
    {lambda mu : ℕ → ℝ} (hlambda : Antitone lambda) (hnn : ∀ j, 0 ≤ lambda j)
    (hmu : Antitone mu) (hmnn : ∀ j, 0 ≤ mu j)
    (hsq : Summable (fun j : ℕ => lambda j ^ 2))
    (hsqmu : Summable (fun j : ℕ => mu j ^ 2)) (j : ℕ)
    (htail : ∀ k : ℕ, 2 ≤ k → ∑' i : ℕ, lambda (i + j) ^ k = ∑' i : ℕ, mu (i + j) ^ k) :
    lambda j = mu j := by
  have hconv : Tendsto (fun k : ℕ => (∑' i : ℕ, mu (i + j) ^ k) ^ ((k : ℝ)⁻¹))
      atTop (𝓝 (lambda j)) := by
    refine Tendsto.congr' ?_ (tailPowerSum_root_tendsto hlambda hnn hsq j)
    refine (Filter.eventually_ge_atTop 2).mono fun k hk => ?_
    rw [htail k hk]
  exact tendsto_nhds_unique hconv (tailPowerSum_root_tendsto hmu hmnn hsqmu j)

set_option maxHeartbeats 1500000 in
/-- **Uniqueness.**  Two decreasing, nonnegative, `\u2113\u00b2` sequences with equal
power sums of every order `k \u2265 2` are equal. -/
theorem powerSums_determine_antitone_sequence
    {lambda mu : ℕ → ℝ} (hlambda : Antitone lambda) (hnn : ∀ j, 0 ≤ lambda j)
    (hmu : Antitone mu) (hmnn : ∀ j, 0 ≤ mu j)
    (hsq : Summable (fun j : ℕ => lambda j ^ 2))
    (hsqmu : Summable (fun j : ℕ => mu j ^ 2))
    (hp : ∀ k : ℕ, 2 ≤ k → ∑' j : ℕ, lambda j ^ k = ∑' j : ℕ, mu j ^ k) :
    lambda = mu := by
  have htailEq : ∀ j : ℕ, ∀ k : ℕ, 2 ≤ k →
      ∑' i : ℕ, lambda (i + j) ^ k = ∑' i : ℕ, mu (i + j) ^ k := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro k hk
      have hhead : ∑ i ∈ Finset.range j, lambda i ^ k
          = ∑ i ∈ Finset.range j, mu i ^ k :=
        Finset.sum_congr rfl fun i hi => by
          refine tail_eq_of_tailPowerSums_eq hlambda hnn hmu hmnn hsq hsqmu i ?_
          intro k2 hk2
          exact ih i (Finset.mem_range.mp hi) k2 hk2
      rw [tailPowerSum_split hlambda hnn hsq j k hk,
        tailPowerSum_split hmu hmnn hsqmu j k hk, hhead]
  funext j
  exact tail_eq_of_tailPowerSums_eq hlambda hnn hmu hmnn hsq hsqmu j (htailEq j)

end Hurst
