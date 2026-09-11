import Mathlib

/-!
# Tail extraction for power sums of an antitone sequence

For an antitone, nonnegative, square-summable sequence `lam : ℕ → ℝ` and a level
`J : ℕ`, define the tail power sum

`tailPowerSum lam J k = ∑' d, lam (J + d) ^ k`.

Then the `k`-th root of `tailPowerSum lam J k` converges to `lam J` as `k → ∞`:

* `tailPowerSum_root_eventually` : explicit `ε`-form squeeze, eventually in `k`;
* `tailPowerSum_root_tendsto` : the `Tendsto` formulation.

Mathematically, the term `d = 0` contributes exactly `lam J ^ k` (giving the lower
bound `lam J - ε`), while antitonicity gives the pointwise bound
`lam (J + d) ^ k ≤ lam J ^ (k - 2) * lam d ^ 2` for `k ≥ 2`, so the whole tail is
at most `(lam J)^(k-2) * ∑ lam j ^ 2`; since `lam J / (lam J + ε) < 1`, the
constant multiple of `(lam J)^k` is eventually absorbed by the `ε` slack.
-/

open Filter Topology

namespace Hurst

/-- The `k`-th tail power sum of the sequence `lam` above level `J`. -/
noncomputable def tailPowerSum (lam : ℕ → ℝ) (J k : ℕ) : ℝ :=
  ∑' d : ℕ, lam (J + d) ^ k

/-- For `k ≠ 0`, taking a `k`-th power and then the real `k`-th root is the
identity on nonnegative reals. -/
theorem rpow_root_pow {x : ℝ} (hx : 0 ≤ x) {k : ℕ} (hk : k ≠ 0) :
    (x ^ k) ^ ((k : ℝ) ⁻¹) = x :=
  Real.pow_rpow_inv_natCast hx hk

/-- **Tail extraction, `ε`-form.**  If `lam` is antitone, nonnegative and has a
summable sequence of squares, then for every `ε > 0` the `k`-th root of the tail
power sum at level `J` lies in `(lam J - ε, lam J + ε)` for all large `k`. -/
theorem tailPowerSum_root_eventually {lam : ℕ → ℝ} (hlam : Antitone lam)
    (hnn : ∀ j, 0 ≤ lam j) (hsum : Summable (fun j => lam j ^ 2)) (J : ℕ) :
    ∀ ε > 0, ∀ᶠ k : ℕ in atTop,
      (lam J - ε) < (tailPowerSum lam J k) ^ ((k : ℝ) ⁻¹) ∧
        (tailPowerSum lam J k) ^ ((k : ℝ) ⁻¹) < lam J + ε := by
  intro ε hε
  by_cases ha : lam J = 0
  · -- The whole tail vanishes identically.
    have hzero : ∀ j, J ≤ j → lam j = 0 := fun j hj => by
      have h1 := hnn j
      have h2 := hlam hj
      linarith
    refine Filter.eventually_atTop.2 ⟨1, fun k hk => ?_⟩
    have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (ne_of_gt hk)
    have hS : tailPowerSum lam J k = 0 := by
      have hterm : ∀ d : ℕ, lam (J + d) ^ k = 0 := by
        intro d
        rw [hzero (J + d) (Nat.le_add_right J d), zero_pow (by omega)]
      simp only [tailPowerSum, hterm, tsum_zero]
    rw [hS, Real.zero_rpow (inv_ne_zero hk0)]
    exact ⟨by linarith, by linarith⟩
  · -- Positive level `lam J`.
    have hapos : 0 < lam J := lt_of_le_of_ne (hnn J) (Ne.symm ha)
    set A : ℝ := ∑' j : ℕ, lam j ^ 2 with hAdef
    set r : ℝ := lam J / (lam J + ε) with hrdef
    have hrpos : 0 < r := by
      rw [hrdef]; exact div_pos hapos (by linarith)
    have hr1 : r < 1 := by
      rw [hrdef]; exact (div_lt_one (by linarith)).2 (by linarith)
    have hpow : Tendsto (fun k : ℕ => (A / lam J ^ 2) * r ^ k) atTop (𝓝 0) := by
      simpa using Tendsto.const_mul (A / lam J ^ 2)
        (tendsto_pow_atTop_nhds_zero_of_lt_one hrpos.le hr1)
    obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.1 (hpow.eventually (Iio_mem_nhds one_pos))
    refine Filter.eventually_atTop.2 ⟨max 2 N0, fun k hk => ?_⟩
    have hk2 : 2 ≤ k := le_trans (le_max_left 2 N0) hk
    have hC1 : (A / lam J ^ 2) * r ^ k < 1 := hN0 k (le_trans (le_max_right 2 N0) hk)
    have hkinv : (0 : ℝ) < (k : ℝ) ⁻¹ := inv_pos.2 (Nat.cast_pos.2 (by omega))
    -- Pointwise bound: each tail term is at most `lam J ^ (k-2) * lam d ^ 2`.
    have hpt : ∀ d : ℕ, lam (J + d) ^ k ≤ lam J ^ (k - 2) * lam d ^ 2 := by
      intro d
      have e0 : lam (J + d) ^ k = lam (J + d) ^ (k - 2) * lam (J + d) ^ 2 := by
        rw [← pow_add, Nat.sub_add_cancel hk2]
      have e1 : lam (J + d) ^ (k - 2) ≤ lam J ^ (k - 2) :=
        pow_le_pow_left₀ (hnn (J + d)) (hlam (Nat.le_add_right J d)) (k - 2)
      have e2 : lam (J + d) ^ 2 ≤ lam d ^ 2 :=
        pow_le_pow_left₀ (hnn (J + d)) (hlam (Nat.le_add_left d J)) 2
      rw [e0]
      calc lam (J + d) ^ (k - 2) * lam (J + d) ^ 2
          ≤ lam J ^ (k - 2) * lam (J + d) ^ 2 :=
            mul_le_mul_of_nonneg_right e1 (pow_nonneg (hnn (J + d)) 2)
        _ ≤ lam J ^ (k - 2) * lam d ^ 2 :=
            mul_le_mul_of_nonneg_left e2 (pow_nonneg (hnn J) (k - 2))
    have hconst : ∀ c : ℝ, Summable (fun d : ℕ => c * lam d ^ 2) := by
      intro c
      simpa [smul_eq_mul] using hsum.const_smul c
    have hsumk : Summable (fun d : ℕ => lam (J + d) ^ k) :=
      Summable.of_nonneg_of_le (fun d => pow_nonneg (hnn (J + d)) k) hpt
        (hconst (lam J ^ (k - 2)))
    -- Upper bound for the tail power sum.
    have hSle : tailPowerSum lam J k ≤ lam J ^ (k - 2) * A := by
      simp only [tailPowerSum]
      have h2 : HasSum (fun d : ℕ => lam J ^ (k - 2) * lam d ^ 2)
          (lam J ^ (k - 2) * ∑' d : ℕ, lam d ^ 2) := by
        simpa only [smul_eq_mul] using HasSum.const_smul (lam J ^ (k - 2)) hsum.hasSum
      exact hasSum_le hpt hsumk.hasSum h2
    -- Rewrite as a constant times `(lam J) ^ k` and squeeze against `(lam J + ε) ^ k`.
    have hpos2 : (0 : ℝ) < lam J + ε := by linarith
    have hne0 : lam J + ε ≠ 0 := ne_of_gt hpos2
    have hne2 : lam J ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hapos)
    have hrr : r * (lam J + ε) = lam J := by
      rw [hrdef]; field_simp
    have hak : lam J ^ k = r ^ k * (lam J + ε) ^ k := by
      rw [← mul_pow, hrr]
    have hkk2 : lam J ^ (k - 2) * A = (A / lam J ^ 2) * lam J ^ k := by
      have h1 : lam J ^ k = lam J ^ (k - 2) * lam J ^ 2 := by
        rw [← pow_add, Nat.sub_add_cancel hk2]
      rw [h1]
      field_simp
    have hSlt : tailPowerSum lam J k < (lam J + ε) ^ k := by
      calc tailPowerSum lam J k ≤ lam J ^ (k - 2) * A := hSle
        _ = (A / lam J ^ 2) * lam J ^ k := hkk2
        _ = (A / lam J ^ 2) * (r ^ k * (lam J + ε) ^ k) := by rw [hak]
        _ = (A / lam J ^ 2 * r ^ k) * (lam J + ε) ^ k := by ring
        _ < 1 * (lam J + ε) ^ k := mul_lt_mul_of_pos_right hC1 (pow_pos hpos2 k)
        _ = (lam J + ε) ^ k := one_mul _
    have hSnn : 0 ≤ tailPowerSum lam J k := by
      simp only [tailPowerSum]
      exact tsum_nonneg fun d => pow_nonneg (hnn (J + d)) k
    refine ⟨?_, ?_⟩
    · -- Lower bound: the `d = 0` term contributes exactly `lam J ^ k`.
      have hlow : lam J ^ k ≤ tailPowerSum lam J k := by
        simp only [tailPowerSum]
        have hsplit : ∑' d : ℕ, lam (J + d) ^ k
            = (∑ d ∈ Finset.range 1, lam (J + d) ^ k)
              + ∑' d : ℕ, lam (J + (d + 1)) ^ k := (hsumk.sum_add_tsum_nat_add 1).symm
        have hnn' : 0 ≤ ∑' d : ℕ, lam (J + (d + 1)) ^ k :=
          tsum_nonneg fun d => pow_nonneg (hnn (J + (d + 1))) k
        have hr0 : ∑ d ∈ Finset.range 1, lam (J + d) ^ k = lam J ^ k := by
          rw [Finset.sum_range_one]; simp
        linarith
      have hroot : ((lam J ^ k : ℝ) ^ ((k : ℝ) ⁻¹)) ≤
          (tailPowerSum lam J k) ^ ((k : ℝ) ⁻¹) :=
        Real.rpow_le_rpow (pow_nonneg (hnn J) k) hlow (le_of_lt hkinv)
      have hkey : ((lam J ^ k : ℝ)) ^ ((k : ℝ) ⁻¹) = lam J :=
        rpow_root_pow (hnn J) (by omega)
      rw [hkey] at hroot
      exact lt_of_lt_of_le (by linarith) hroot
    · -- Upper bound.
      have hroot : (tailPowerSum lam J k) ^ ((k : ℝ) ⁻¹) <
          ((lam J + ε) ^ k) ^ ((k : ℝ) ⁻¹) :=
        Real.rpow_lt_rpow hSnn hSlt hkinv
      have hkey : ((lam J + ε) ^ k) ^ ((k : ℝ) ⁻¹) = lam J + ε :=
        rpow_root_pow hpos2.le (by omega)
      rw [hkey] at hroot
      exact hroot

/-- **Tail extraction, `Tendsto` form.**  The `k`-th root of the tail power sum
at level `J` converges to `lam J` as `k → ∞` (the `k = 0` value is irrelevant to
the limit). -/
theorem tailPowerSum_root_tendsto {lam : ℕ → ℝ} (hlam : Antitone lam)
    (hnn : ∀ j, 0 ≤ lam j) (hsum : Summable (fun j => lam j ^ 2)) (J : ℕ) :
    Tendsto (fun k : ℕ => (tailPowerSum lam J k) ^ ((k : ℝ) ⁻¹)) atTop (𝓝 (lam J)) := by
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (tailPowerSum_root_eventually hlam hnn hsum J ε hε)
  refine ⟨N, fun n hn => ?_⟩
  have hk := hN n hn
  rw [Real.dist_eq, abs_lt]
  exact ⟨by linarith, by linarith⟩

end Hurst
