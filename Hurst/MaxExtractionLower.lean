import Hurst.TailExtraction
import Hurst.MaxExtraction

/-!
# Max extraction, liminf half

Setting: at time `n` we observe `x n i` for `i : Fin (m n)` (a growing number of
coordinates), all nonnegative.  The raw power sums of the observed coordinates
converge, for every fixed `k ≥ 2`, to `∑' j, lam j ^ k`, where `lam` is
antitone, nonnegative, `lam 0 > 0` and `∑ lam j ^ 2` converges.

* `max_eventually_ge` : for every `ε > 0` with `2 * ε < lam 0`, the supremum of
  the observed coordinates is eventually at least `lam 0 - ε`.

Proof sketch (contradiction / peeling).  Suppose `⨆ i, x n i < c` (with
`c = lam 0 - ε`) for arbitrarily large `n`.  For such `n` and every `k ≥ 2`,
`∑ i, x n i ^ k = ∑ i, x n i ^ (k-2) * x n i ^ 2 ≤ c ^ (k-2) * ∑ i, x n i ^ 2`,
and since the second power sums converge to `S₂ = ∑' j, lam j ^ 2` while the
`k`-th power sums converge to `∑' j, lam j ^ k`, the rows with `⨆ i, x n i < c`
force `∑' j, lam j ^ k ≤ c ^ (k-2) * (S₂ + δ)` for every `δ > 0`.  Taking
`k`-th roots, the left side tends to `lam 0` (by `tailPowerSum_root_tendsto` at
level `0`), while the right side tends to `c = lam 0 - ε` (the exponent `k - 2`
is negligible against `k`, and `(S₂ + δ) ^ (1/k) → 1`).  Hence
`lam 0 ≤ lam 0 - ε`, contradicting `ε > 0`.
-/

namespace Hurst

open Filter Topology

variable {m : ℕ → ℕ} {x : ∀ n, Fin (m n) → ℝ} {lam : ℕ → ℝ}

/-- **Max extraction, liminf half.**  Under convergent power sums against an
antitone summable-square profile `lam` with `lam 0 > 0`, the coordinate suprema
are eventually at least `lam 0 - ε` for every `ε > 0` with `2 * ε < lam 0`. -/
theorem max_eventually_ge
    (hm : ∀ n, 0 < m n) (hb : ∀ n i, 0 ≤ x n i)
    (hp : ∀ k : ℕ, 2 ≤ k → Tendsto (fun n => ∑ i : Fin (m n), x n i ^ k) atTop
      (𝓝 (∑' j, lam j ^ k)))
    (hl : Antitone lam ∧ ∀ j, 0 ≤ lam j ∧ Summable (fun j => lam j ^ 2))
    (hpos : 0 < lam 0) :
    ∀ ε > 0, 2 * ε < lam 0 → ∀ᶠ n in atTop, lam 0 - ε ≤ ⨆ i, x n i := by
  intro ε hε htwo
  obtain ⟨hlam, hpoint⟩ := hl
  have hnn : ∀ j, 0 ≤ lam j := fun j => (hpoint j).1
  have hsum : Summable (fun j => lam j ^ 2) := (hpoint 0).2
  have hS₂nn : 0 ≤ ∑' j : ℕ, lam j ^ 2 := tsum_nonneg fun j => pow_nonneg (hnn j) 2
  have hS₂pos : 0 < ∑' j : ℕ, lam j ^ 2 := by
    have hsplit := (hsum.sum_add_tsum_nat_add 1).symm
    have hnn' : 0 ≤ ∑' d : ℕ, lam (d + 1) ^ 2 :=
      tsum_nonneg fun d => pow_nonneg (hnn (d + 1)) 2
    have hr0 : ∑ d ∈ Finset.range 1, lam d ^ 2 = lam 0 ^ 2 := by
      rw [Finset.sum_range_one]
    calc (0 : ℝ) < lam 0 ^ 2 := pow_pos hpos 2
      _ ≤ ∑' j : ℕ, lam j ^ 2 := by rw [hsplit]; linarith
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  push_neg at hcon
  set c : ℝ := lam 0 - ε with hcdef
  set S₂ : ℝ := ∑' j : ℕ, lam j ^ 2 with hS₂def
  have hcpos : 0 < c := by linarith
  have hSk_nn : ∀ k : ℕ, 0 ≤ ∑' j : ℕ, lam j ^ k := fun k =>
    tsum_nonneg fun j => pow_nonneg (hnn j) k
  -- The bad rows squeeze every `k`-th power sum by `c ^ (k - 2) * (S₂ + δ)`.
  have hkey : ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, δ > 0 → ∑' j : ℕ, lam j ^ k ≤ c ^ (k - 2) * (S₂ + δ) := by
    intro k hk δ hδ
    -- Row-wise bound under `⨆ i, x n i < c`.
    have hbnd : ∀ n : ℕ, ⨆ i, x n i < c →
        ∑ i : Fin (m n), x n i ^ k ≤ c ^ (k - 2) * ∑ i : Fin (m n), x n i ^ 2 := by
      intro n hsup
      have hnnx : ∀ i : Fin (m n), x n i < c := fun i =>
        lt_of_le_of_lt (le_ciSup (Set.finite_range (x n)).bddAbove i) hsup
      calc ∑ i : Fin (m n), x n i ^ k
          = ∑ i : Fin (m n), x n i ^ (k - 2) * x n i ^ 2 := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [← pow_add, Nat.sub_add_cancel hk]
        _ ≤ ∑ i : Fin (m n), c ^ (k - 2) * x n i ^ 2 :=
            Finset.sum_le_sum fun i _ =>
              mul_le_mul_of_nonneg_right
                (pow_le_pow_left₀ (hb n i) (hnnx i).le (k - 2)) (pow_nonneg (hb n i) 2)
        _ = c ^ (k - 2) * ∑ i : Fin (m n), x n i ^ 2 := by rw [Finset.mul_sum]
    by_contra hge
    have hgt : c ^ (k - 2) * (S₂ + δ) < ∑' j : ℕ, lam j ^ k := not_le.mp hge
    obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.1
      (Filter.Tendsto.eventually_const_lt hgt (hp k hk))
    have hgt2 : S₂ < S₂ + δ := by linarith
    obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.1
      ((hp 2 (Nat.le_refl 2)).eventually_le_const hgt2)
    obtain ⟨n, hnN, hnmax⟩ := frequently_atTop.1 hcon (max N1 N2)
    have hn1 := hN1 n (le_trans (le_max_left N1 N2) hnN)
    have hn2 := hN2 n (le_trans (le_max_right N1 N2) hnN)
    have h3 := hbnd n hnmax
    have h4 : c ^ (k - 2) * ∑ i : Fin (m n), x n i ^ 2 ≤ c ^ (k - 2) * (S₂ + δ) :=
      mul_le_mul_of_nonneg_left hn2 (pow_nonneg hcpos.le (k - 2))
    exact absurd (le_trans h3 h4) (not_le.mpr hn1)
  -- Pass to the `k`-th roots and let `k → ∞`.
  have hroot : ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, δ > 0 →
      (∑' j : ℕ, lam j ^ k) ^ ((k : ℝ) ⁻¹) ≤ (c ^ (k - 2) * (S₂ + δ)) ^ ((k : ℝ) ⁻¹) := by
    intro k hk δ hδ
    have hklt : (0 : ℕ) < k := by omega
    have hkinv : 0 ≤ ((k : ℝ) ⁻¹) := le_of_lt (inv_pos.2 (Nat.cast_pos.2 hklt))
    exact Real.rpow_le_rpow (hSk_nn k) (hkey k hk δ hδ) hkinv
  have hL : Tendsto (fun k : ℕ => (∑' j : ℕ, lam j ^ k) ^ ((k : ℝ) ⁻¹)) atTop
      (𝓝 (lam 0)) := by
    simpa only [tailPowerSum, Nat.zero_add] using tailPowerSum_root_tendsto hlam hnn hsum 0
  have hR : ∀ δ : ℝ, δ > 0 →
      Tendsto (fun k : ℕ => (c ^ (k - 2) * (S₂ + δ)) ^ ((k : ℝ) ⁻¹)) atTop (𝓝 c) := by
    intro δ hδ
    have hSδnn : 0 ≤ S₂ + δ := by linarith
    have hSδpos : 0 < S₂ + δ := by linarith
    have hinv0 : Tendsto (fun k : ℕ => ((k : ℝ) ⁻¹)) atTop (𝓝 0) :=
      Filter.Tendsto.inv_tendsto_atTop tendsto_natCast_atTop_atTop
    have hSδroot : Tendsto (fun k : ℕ => (S₂ + δ) ^ ((k : ℝ) ⁻¹)) atTop (𝓝 1) := by
      have hstep : ∀ k : ℕ, (S₂ + δ) ^ ((k : ℝ) ⁻¹)
          = Real.exp (Real.log (S₂ + δ) * ((k : ℝ) ⁻¹)) := fun k =>
        Real.rpow_def_of_pos hSδpos _
      have h1 : Tendsto (fun k : ℕ => Real.log (S₂ + δ) * ((k : ℝ) ⁻¹)) atTop
          (𝓝 (Real.log (S₂ + δ) * 0)) := hinv0.const_mul _
      rw [mul_zero] at h1
      have h2 : Tendsto (fun k : ℕ =>
            Real.exp (Real.log (S₂ + δ) * ((k : ℝ) ⁻¹))) atTop (𝓝 1) := by
        have hcomp := Filter.Tendsto.comp
          Real.continuous_exp.continuousAt.tendsto h1
        rw [Real.exp_zero] at hcomp
        exact hcomp
      simpa only [hstep] using h2
    -- rewrite the root as `c ^ ((k-2)/k) * (S₂ + δ) ^ (1/k)`
    have heq : ∀ k : ℕ, (c ^ (k - 2) * (S₂ + δ)) ^ ((k : ℝ) ⁻¹)
        = c ^ (((k - 2 : ℕ) : ℝ) * ((k : ℝ) ⁻¹)) * (S₂ + δ) ^ ((k : ℝ) ⁻¹) := by
      intro k
      have e1 : c ^ (k - 2) = c ^ ((k - 2 : ℕ) : ℝ) := by rw [Real.rpow_natCast]
      rw [e1, Real.mul_rpow (Real.rpow_nonneg hcpos.le ((k - 2 : ℕ) : ℝ)) hSδnn,
        ← Real.rpow_mul hcpos.le ((k - 2 : ℕ) : ℝ) ((k : ℝ) ⁻¹)]
    have hdiv : Tendsto (fun k : ℕ => ((k - 2 : ℕ) : ℝ) * ((k : ℝ) ⁻¹)) atTop (𝓝 1) := by
      have h2 : Tendsto (fun k : ℕ => 1 - 2 * ((k : ℝ) ⁻¹)) atTop (𝓝 1) := by
        simpa using (hinv0.const_mul 2).const_sub 1
      refine h2.congr' (Filter.eventually_atTop.2 ⟨2, fun k hk1 => ?_⟩)
      show 1 - 2 * ((k : ℝ) ⁻¹) = ((k - 2 : ℕ) : ℝ) * ((k : ℝ) ⁻¹)
      have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      have hcast : ((k - 2 : ℕ) : ℝ) = (k : ℝ) - 2 := by
        have h2' : ((k - 2 : ℕ) : ℝ) + ((2 : ℕ) : ℝ) = ((k : ℕ) : ℝ) := by
          have h4 : ((k - 2 : ℕ) + 2 : ℕ) = k := Nat.sub_add_cancel hk1
          rw [← Nat.cast_add, h4]
        have h5 : ((2 : ℕ) : ℝ) = 2 := Nat.cast_two
        linarith
      rw [hcast, sub_mul, mul_inv_cancel₀ hk0]
    have hexp : Tendsto (fun k : ℕ => c ^ (((k - 2 : ℕ) : ℝ) * ((k : ℝ) ⁻¹))) atTop
        (𝓝 c) := by
      have hstep : ∀ k : ℕ, c ^ (((k - 2 : ℕ) : ℝ) * ((k : ℝ) ⁻¹))
          = Real.exp (Real.log c * (((k - 2 : ℕ) : ℝ) * ((k : ℝ) ⁻¹))) := fun k =>
        Real.rpow_def_of_pos hcpos _
      have h1 : Tendsto (fun k : ℕ => Real.log c * (((k - 2 : ℕ) : ℝ) * ((k : ℝ) ⁻¹))) atTop
          (𝓝 (Real.log c * 1)) := hdiv.const_mul _
      rw [mul_one] at h1
      have h2 : Tendsto (fun k : ℕ =>
            Real.exp (Real.log c * (((k - 2 : ℕ) : ℝ) * ((k : ℝ) ⁻¹)))) atTop
          (𝓝 c) := by
        have hcomp := Filter.Tendsto.comp
          Real.continuous_exp.continuousAt.tendsto h1
        rw [Real.exp_log hcpos] at hcomp
        exact hcomp
      simpa only [hstep] using h2
    have hprod := hexp.mul hSδroot
    rw [mul_one] at hprod
    simp only [heq]
    exact hprod
  have hfinal : ∀ δ : ℝ, δ > 0 → lam 0 ≤ c := fun δ hδ =>
    le_of_tendsto_of_tendsto hL (hR δ hδ)
      ((Filter.eventually_ge_atTop 2).mono fun k hk => hroot k hk δ hδ)
  have hfin1 := hfinal (1 : ℝ) one_pos
  linarith

end Hurst
