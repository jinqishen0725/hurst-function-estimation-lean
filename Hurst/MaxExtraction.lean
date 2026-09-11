import Hurst.TailExtraction

/-!
# Max extraction, limsup half

Setting: at time `n` we observe `x n i` for `i : Fin (m n)` (a growing number of
coordinates), all nonnegative.  The raw power sums of the observed coordinates
converge, for every fixed `k ≥ 2`, to `∑' j, lam j ^ k`, where `lam` is
antitone, nonnegative and `∑ lam j ^ 2` converges.

Since a single coordinate's `k`-th power is dominated by the total power sum,
each coordinate is eventually at most `lam 0 + ε`; hence so is the supremum,
and `limsup (fun n => ⨆ i, x n i) ≤ lam 0`.

The key input from `Hurst.TailExtraction` is `tailPowerSum_root_tendsto`:
`(∑' j, lam j ^ k) ^ (1/k) → lam 0` as `k → ∞` (at `J = 0`).
-/

namespace Hurst

open Filter Topology

variable {m : ℕ → ℕ} {x : ∀ n, Fin (m n) → ℝ} {lam : ℕ → ℝ}

/-- Single-coordinate ε-form: each observed coordinate is eventually at most
`lam 0 + ε`. -/
theorem max_forall_eventually_le
    (_hm : ∀ n, 0 < m n) (hb : ∀ n i, 0 ≤ x n i)
    (hp : ∀ k : ℕ, 2 ≤ k → Tendsto (fun n => ∑ i : Fin (m n), x n i ^ k) atTop
      (𝓝 (∑' j, lam j ^ k)))
    (hl : Antitone lam ∧ ∀ j, 0 ≤ lam j ∧ Summable (fun j => lam j ^ 2)) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ i, x n i ≤ lam 0 + ε := by
  intro ε hε
  obtain ⟨hlam, hpoint⟩ := hl
  have hnn : ∀ j, 0 ≤ lam j := fun j => (hpoint j).1
  have hsum : Summable (fun j => lam j ^ 2) := (hpoint 0).2
  -- Choose `k ≥ 2` with `(∑' j, lam j ^ k) ^ (1/k) < lam 0 + ε`.
  obtain ⟨k, hk2, hroot⟩ :
      ∃ k : ℕ, 2 ≤ k ∧ (∑' j, lam j ^ k) ^ ((k : ℝ) ⁻¹) < lam 0 + ε := by
    obtain ⟨k, hroot_lt, hk2⟩ :=
      ((tailPowerSum_root_eventually hlam hnn hsum 0 ε hε).and (eventually_ge_atTop 2)).exists
    refine ⟨k, hk2, ?_⟩
    simpa only [tailPowerSum, Nat.zero_add] using hroot_lt.2
  have hL0 : (0 : ℝ) < lam 0 + ε := by linarith [hnn 0]
  have hS0 : 0 ≤ ∑' j, lam j ^ k :=
    ge_of_tendsto (hp k hk2) ((eventually_ge_atTop 0).mono fun n _ =>
      Finset.sum_nonneg fun j _ => pow_nonneg (hb n j) k)
  have hroot0 : 0 ≤ (∑' j, lam j ^ k) ^ ((k : ℝ) ⁻¹) := Real.rpow_nonneg hS0 _
  -- Convert the root bound into `S_k < (lam 0 + ε) ^ k`.
  have hkey : ∑' j, lam j ^ k < (lam 0 + ε) ^ k := by
    have h1 := Real.rpow_lt_rpow hroot0 hroot
      (show (0 : ℝ) < (k : ℝ) by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_two hk2)
    have e1 : ((∑' j, lam j ^ k) ^ ((k : ℝ) ⁻¹)) ^ (k : ℝ) = ∑' j, lam j ^ k := by
      rw [← Real.rpow_mul hS0, inv_mul_cancel₀ (a := (k : ℝ))
        (by exact_mod_cast ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two hk2) : (k : ℝ) ≠ 0),
        Real.rpow_one]
    rw [Real.rpow_natCast (lam 0 + ε) k, e1] at h1
    exact h1
  -- Pass to the finite power sums, then to single coordinates.
  have hfin := (hp k hk2).eventually_lt_const hkey
  refine hfin.mono fun n hn i => ?_
  have hsingle : x n i ^ k ≤ ∑ j : Fin (m n), x n j ^ k :=
    Finset.single_le_sum (fun j _ => pow_nonneg (hb n j) k) (Finset.mem_univ i)
  have hpow : x n i ^ k < (lam 0 + ε) ^ k := lt_of_le_of_lt hsingle hn
  by_contra hcon
  exact absurd hpow (not_lt.2 (pow_le_pow_left₀ hL0.le (not_le.1 hcon).le k))

/-- Supremum ε-form: `⨆ i, x n i` is eventually at most `lam 0 + ε`. -/
theorem max_eventually_le
    (hm : ∀ n, 0 < m n) (hb : ∀ n i, 0 ≤ x n i)
    (hp : ∀ k : ℕ, 2 ≤ k → Tendsto (fun n => ∑ i : Fin (m n), x n i ^ k) atTop
      (𝓝 (∑' j, lam j ^ k)))
    (hl : Antitone lam ∧ ∀ j, 0 ≤ lam j ∧ Summable (fun j => lam j ^ 2)) :
    ∀ ε > 0, ∀ᶠ n in atTop, ⨆ i, x n i ≤ lam 0 + ε :=
  fun ε hε => (max_forall_eventually_le hm hb hp hl ε hε).mono fun n hn => by
    haveI : Nonempty (Fin (m n)) := ⟨⟨0, hm n⟩⟩
    exact ciSup_le hn

/-- **Max extraction, limsup half.**  Under convergent power sums against an
antitone summable-square profile `lam`, the limsup of the coordinate suprema is
at most `lam 0`. -/
theorem max_limsup_le
    (hm : ∀ n, 0 < m n) (hb : ∀ n i, 0 ≤ x n i)
    (hp : ∀ k : ℕ, 2 ≤ k → Tendsto (fun n => ∑ i : Fin (m n), x n i ^ k) atTop
      (𝓝 (∑' j, lam j ^ k)))
    (hl : Antitone lam ∧ ∀ j, 0 ≤ lam j ∧ Summable (fun j => lam j ^ 2)) :
    limsup (fun n => ⨆ i, x n i) atTop ≤ lam 0 := by
  have hsup : ∀ n : ℕ, (0 : ℝ) ≤ ⨆ i, x n i := fun n => by
    have h1 := le_ciSup (Set.finite_range (x n)).bddAbove ⟨0, hm n⟩
    exact (hb n ⟨0, hm n⟩).trans h1
  have h1 : ∀ ε > 0, limsup (fun n => ⨆ i, x n i) atTop ≤ lam 0 + ε := fun ε hε =>
    limsup_le_of_le
      (hf := isCoboundedUnder_le_of_eventually_le atTop (Eventually.of_forall hsup))
      (max_eventually_le hm hb hp hl ε hε)
  by_cases h : lam 0 < limsup (fun n => ⨆ i, x n i) atTop
  · have hpos : (0 : ℝ) <
        (limsup (fun n => ⨆ i, x n i) atTop - lam 0) / 2 :=
      div_pos (sub_pos.2 h) two_pos
    linarith [h1 _ hpos]
  · exact not_lt.1 h

end Hurst
