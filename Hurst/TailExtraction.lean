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

namespace Hurst

/-- The `k`-th tail power sum of the sequence `lam` above level `J`. -/
noncomputable def tailPowerSum (lam : ℕ → ℝ) (J k : ℕ) : ℝ :=
  ∑' d : ℕ, lam (J + d) ^ k

/-- For `k ≠ 0`, taking a `k`-th power and then the real `k`-th root is the
identity on nonnegative reals. -/
theorem rpow_root_pow {x : ℝ} (hx : 0 ≤ x) {k : ℕ} (hk : k ≠ 0) :
    (x ^ k) ^ ((k : ℝ) ⁻¹) = x := by
  rw [← Real.rpow_natCast x k, ← Real.rpow_pow hx (by positivity) (by positivity),
    mul_inv_cancel₀ (Nat.cast_ne_zero.2 hk), Real.rpow_one]

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
        rw [hzero (J + d) (Nat.le_add_left J d), zero_pow (by omega)]
      simp only [tailPowerSum, hterm, tsum_zero]
    rw [hS, Real.zero_rpow hk0]
    exact ⟨by linarith, hε⟩
  · -- Positive level `lam J`.
    have hapos : 0 < lam J := lt_of_le_of_ne (hnn J) ha
    set A : ℝ := ∑' j : ℕ, lam j ^ 2 with hAdef
    set r : ℝ := lam J / (lam J + ε) with hrdef
    have hrpos : 0 < r := by
      rw [hrdef]; exact div_pos hapos (by linarith)
    have hr1 : r < 1 := by
      rw [hrdef]; exact (div_lt_one (by linarith)).2 (by linarith)
    have hpow : Tendsto (fun k : ℕ => (A / lam J ^ 2) * r ^ k) atTop (𝓝 0) :=
      Tendsto.const_mul (A / lam J ^ 2)
        (Real.tendsto_pow_atTop_nhds_0_of_lt_one (abs_lt.2 ⟨by linarith, hr1⟩))
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
        pow_le_pow_left (hnn (J + d)) (hlam (Nat.le_add_left J d)) (k - 2)
      have e2 : lam (J + d) ^ 2 ≤ lam d ^ 2 :=
        pow_le_pow_left (hnn (J + d)) (hlam (Nat.le_add_left d J)) 2
      rw [e0]
      calc lam (J + d) ^ (k - 2) * lam (J + d) ^ 2
          ≤ lam J ^ (k - 2) * lam (J + d) ^ 2 :=
            mul_le_mul_of_nonneg_right e1 (pow_nonneg (hnn (J + d)) 2)
        _ ≤ lam J ^ (k - 2) * lam d ^ 2 :=
            mul_le_mul_of_nonneg_left e2 (pow_nonneg (hnn J) (k - 2))
    have hconst : ∀ c : ℝ, Summable (fun d : ℕ => c * lam d ^ 2) := by
      intro c
      simpa [smul_eq_mul] using hsum.const_smul c
    have hpull : ∀ c : ℝ, ∑' d : ℕ, c * lam d ^ 2 = c * ∑' d : ℕ, lam d ^ 2 := by
      intro c
      simpa [smul_eq_mul] using tsum_const_smul c hsum
    have hsumk : Summable (fun d : ℕ => lam (J + d) ^ k) :=
      summable_of_nonneg_of_le (fun d => pow_nonneg (hnn (J + d)) k) hpt
        (hconst (lam J ^ (k - 2)))
    -- Upper bound for the tail power sum.
    have hSle : tailPowerSum lam J k ≤ lam J ^ (k - 2) * A := by
      simp only [tailPowerSum]
      calc ∑' d : ℕ, lam (J + d) ^ k ≤ ∑' d : ℕ, (lam J ^ (k - 2) * lam d ^ 2) :=
            tsum_le_tsum hpt hsumk (hconst _)
        _ = lam J ^ (k - 2) * ∑' d : ℕ, lam d ^ 2 := hpull _
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
              + ∑' d : ℕ, lam (J + (1 + d)) ^ k := hsumk.sum_add_tsum_nat_add 1
        have hnn' : 0 ≤ ∑' d : ℕ, lam (J + (1 + d)) ^ k :=
          tsum_nonneg fun d => pow_nonneg (hnn (J + (1 + d))) k
        have hr0 : ∑ d ∈ Finset.range 1, lam (J + d) ^ k = lam J ^ k := by
          rw [Finset.sum_range_one]; simp
        linarith
      have hroot : ((lam J ^ k : ℝ) ^ ((k : ℝ) ⁻¹)) ≤
          (tailPowerSum lam J k) ^ ((k : ℝ) ⁻¹) :=
        Real.rpow_le_rpow (pow_nonneg (hnn J) k) hlow (le_of_lt hkinv)
      rw [rpow_root_pow (pow_nonneg (hnn J) k) (by omega)] at hroot
      exact lt_of_lt_of_le (by linarith) hroot
    · -- Upper bound.
      have hroot : (tailPowerSum lam J k) ^ ((k : ℝ) ⁻¹) <
          ((lam J + ε) ^ k) ^ ((k : ℝ) ⁻¹) :=
        Real.rpow_lt_rpow hSnn hSlt hkinv
      rw [rpow_root_pow hpos2.le (by omega)] at hroot
      exact hroot

/-- **Tail extraction, `Tendsto` form.**  The `k`-th root of the tail power sum
at level `J` converges to `lam J` as `k → ∞` (the `k = 0` value is irrelevant to
the limit). -/
theorem tailPowerSum_root_tendsto {lam : ℕ → ℝ} (hlam : Antitone lam)
    (hnn : ∀ j, 0 ≤ lam j) (hsum : Summable (fun j => lam j ^ 2)) (J : ℕ) :
    Tendsto (fun k : ℕ => (tailPowerSum lam J k) ^ ((k : ℝ) ⁻¹)) atTop (𝓝 (lam J)) := by
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  filter_upwards [tailPowerSum_root_eventually hlam hnn hsum J ε hε] with k hk
  rw [Real.dist_eq, abs_lt]
  exact ⟨by linarith, by linarith⟩

end Hurst
