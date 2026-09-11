import Hurst.TailExtraction

/-!
# Tail-adapted array max extraction

Setting: at time `n` we observe `y n i` for `i : Fin (m n)` (a growing number of
coordinates), all nonnegative.  For every fixed `k ≥ 2`, the raw `k`-th power
sums of the observed coordinates converge to `tailPowerSum lam J k = ∑' d, lam (J + d) ^ k`,
where `lam` is antitone, nonnegative, `lam J > 0` and `∑ lam j ^ 2` converges.

* `tail_array_max_eventually_ge` : (lower half) for every `ε > 0` with
  `2 * ε < lam J`, the supremum of the observed coordinates is eventually at
  least `lam J - ε`;
* `tail_array_max_eventually_le` : (upper half) for every `ε > 0`, the supremum
  of the observed coordinates is eventually at most `lam J + ε`;
* `tail_array_max_tendsto` : combining the two, `⨆ i, y n i → lam J`.

The proofs copy-adapt `Hurst.MaxExtraction` and `Hurst.MaxExtractionLower`, with
the total power sums `∑' j, lam j ^ k` replaced by the tail power sums
`tailPowerSum lam J k`; the common extraction input is
`tailPowerSum_root_tendsto` at level `J`.
-/

namespace Hurst

open Filter Topology

variable {m : ℕ → ℕ} {y : ∀ n, Fin (m n) → ℝ} {lam : ℕ → ℝ} {J : ℕ}

/-- Single-coordinate ε-form, upper half: each observed coordinate is eventually
at most `lam J + ε`. -/
theorem tail_array_forall_eventually_le
    (_hm : ∀ n, 0 < m n) (hb : ∀ n i, 0 ≤ y n i)
    (hy : ∀ k : ℕ, 2 ≤ k → Tendsto (fun n => ∑ i : Fin (m n), y n i ^ k) atTop
      (𝓝 (tailPowerSum lam J k)))
    (hl : Antitone lam ∧ ∀ j, 0 ≤ lam j ∧ Summable (fun j => lam j ^ 2)) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ i, y n i ≤ lam J + ε := by
  intro ε hε
  obtain ⟨hlam, hpoint⟩ := hl
  have hnn : ∀ j, 0 ≤ lam j := fun j => (hpoint j).1
  have hsum : Summable (fun j => lam j ^ 2) := (hpoint 0).2
  -- Choose `k ≥ 2` with `(tailPowerSum lam J k) ^ (1/k) < lam J + ε`.
  obtain ⟨k, hk2, hroot⟩ :
      ∃ k : ℕ, 2 ≤ k ∧ (tailPowerSum lam J k) ^ ((k : ℝ) ⁻¹) < lam J + ε := by
    obtain ⟨k, hroot_lt, hk2⟩ :=
      ((tailPowerSum_root_eventually hlam hnn hsum J ε hε).and (eventually_ge_atTop 2)).exists
    exact ⟨k, hk2, hroot_lt.2⟩
  have hL0 : (0 : ℝ) < lam J + ε := by linarith [hnn J]
  have hS0 : 0 ≤ tailPowerSum lam J k := by
    simp only [tailPowerSum]
    exact tsum_nonneg fun d => pow_nonneg (hnn (J + d)) k
  have hroot0 : 0 ≤ (tailPowerSum lam J k) ^ ((k : ℝ) ⁻¹) := Real.rpow_nonneg hS0 _
  -- Convert the root bound into `S_k < (lam J + ε) ^ k`.
  have hkey : tailPowerSum lam J k < (lam J + ε) ^ k := by
    have h1 := Real.rpow_lt_rpow hroot0 hroot
      (show (0 : ℝ) < (k : ℝ) by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_two hk2)
    have e1 : ((tailPowerSum lam J k) ^ ((k : ℝ) ⁻¹)) ^ (k : ℝ) = tailPowerSum lam J k := by
      rw [← Real.rpow_mul hS0, inv_mul_cancel₀ (a := (k : ℝ))
        (by exact_mod_cast ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two hk2) : (k : ℝ) ≠ 0),
        Real.rpow_one]
    rw [Real.rpow_natCast (lam J + ε) k, e1] at h1
    exact h1
  -- Pass to the finite power sums, then to single coordinates.
  have hfin := (hy k hk2).eventually_lt_const hkey
  refine hfin.mono fun n hn i => ?_
  have hsingle : y n i ^ k ≤ ∑ j : Fin (m n), y n j ^ k :=
    Finset.single_le_sum (fun j _ => pow_nonneg (hb n j) k) (Finset.mem_univ i)
  have hpow : y n i ^ k < (lam J + ε) ^ k := lt_of_le_of_lt hsingle hn
  by_contra hcon
  exact absurd hpow (not_lt.2 (pow_le_pow_left₀ hL0.le (not_le.1 hcon).le k))

/-- Supremum ε-form, upper half: `⨆ i, y n i` is eventually at most `lam J + ε`. -/
theorem tail_array_max_eventually_le
    (hm : ∀ n, 0 < m n) (hb : ∀ n i, 0 ≤ y n i)
    (hy : ∀ k : ℕ, 2 ≤ k → Tendsto (fun n => ∑ i : Fin (m n), y n i ^ k) atTop
      (𝓝 (tailPowerSum lam J k)))
    (hl : Antitone lam ∧ ∀ j, 0 ≤ lam j ∧ Summable (fun j => lam j ^ 2)) :
    ∀ ε > 0, ∀ᶠ n in atTop, ⨆ i, y n i ≤ lam J + ε :=
  fun ε hε => (tail_array_forall_eventually_le hm hb hy hl ε hε).mono fun n hn => by
    haveI : Nonempty (Fin (m n)) := ⟨⟨0, hm n⟩⟩
    exact ciSup_le hn

/-- **Tail-adapted array max extraction, lower half.**  Under convergent power
sums against an antitone summable-square profile `lam` with `lam J > 0`, the
coordinate suprema are eventually at least `lam J - ε` for every `ε > 0` with
`2 * ε < lam J`. -/
theorem tail_array_max_eventually_ge
    (_hm : ∀ n, 0 < m n) (hb : ∀ n i, 0 ≤ y n i)
    (hy : ∀ k : ℕ, 2 ≤ k → Tendsto (fun n => ∑ i : Fin (m n), y n i ^ k) atTop
      (𝓝 (tailPowerSum lam J k)))
    (hl : Antitone lam ∧ ∀ j, 0 ≤ lam j ∧ Summable (fun j => lam j ^ 2))
    (hpos : 0 < lam J) :
    ∀ ε > 0, 2 * ε < lam J → ∀ᶠ n in atTop, lam J - ε ≤ ⨆ i, y n i := by
  intro ε hε htwo
  obtain ⟨hlam, hpoint⟩ := hl
  have hnn : ∀ j, 0 ≤ lam j := fun j => (hpoint j).1
  have hsum : Summable (fun j => lam j ^ 2) := (hpoint 0).2
  have hsumJ2 : Summable (fun d : ℕ => lam (J + d) ^ 2) :=
    Summable.of_nonneg_of_le (fun d => pow_nonneg (hnn (J + d)) 2)
      (fun d => pow_le_pow_left₀ (hnn (J + d)) (hlam (Nat.le_add_left d J)) 2) hsum
  have hS₂nn : 0 ≤ tailPowerSum lam J 2 := by
    simp only [tailPowerSum]
    exact tsum_nonneg fun d => pow_nonneg (hnn (J + d)) 2
  have hS₂pos : 0 < tailPowerSum lam J 2 := by
    have hsplit := (hsumJ2.sum_add_tsum_nat_add 1).symm
    have hnn' : 0 ≤ ∑' d : ℕ, lam (J + (d + 1)) ^ 2 :=
      tsum_nonneg fun d => pow_nonneg (hnn (J + (d + 1))) 2
    have hr0 : ∑ d ∈ Finset.range 1, lam (J + d) ^ 2 = lam J ^ 2 := by
      rw [Finset.sum_range_one, Nat.add_zero]
    calc (0 : ℝ) < lam J ^ 2 := pow_pos hpos 2
      _ ≤ ∑' d : ℕ, lam (J + d) ^ 2 := by rw [hsplit]; linarith
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  push Not at hcon
  set c : ℝ := lam J - ε with hcdef
  set S₂ : ℝ := tailPowerSum lam J 2 with hS₂def
  have hcpos : 0 < c := by linarith
  have hSk_nn : ∀ k : ℕ, 0 ≤ tailPowerSum lam J k := fun k => by
    simp only [tailPowerSum]
    exact tsum_nonneg fun d => pow_nonneg (hnn (J + d)) k
  -- The bad rows squeeze every `k`-th power sum by `c ^ (k - 2) * (S₂ + δ)`.
  have hkey : ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, δ > 0 →
      tailPowerSum lam J k ≤ c ^ (k - 2) * (S₂ + δ) := by
    intro k hk δ hδ
    -- Row-wise bound under `⨆ i, y n i < c`.
    have hbnd : ∀ n : ℕ, ⨆ i, y n i < c →
        ∑ i : Fin (m n), y n i ^ k ≤ c ^ (k - 2) * ∑ i : Fin (m n), y n i ^ 2 := by
      intro n hsup
      have hnnx : ∀ i : Fin (m n), y n i < c := fun i =>
        lt_of_le_of_lt (le_ciSup (Set.finite_range (y n)).bddAbove i) hsup
      calc ∑ i : Fin (m n), y n i ^ k
          = ∑ i : Fin (m n), y n i ^ (k - 2) * y n i ^ 2 := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [← pow_add, Nat.sub_add_cancel hk]
        _ ≤ ∑ i : Fin (m n), c ^ (k - 2) * y n i ^ 2 :=
            Finset.sum_le_sum fun i _ =>
              mul_le_mul_of_nonneg_right
                (pow_le_pow_left₀ (hb n i) (hnnx i).le (k - 2)) (pow_nonneg (hb n i) 2)
        _ = c ^ (k - 2) * ∑ i : Fin (m n), y n i ^ 2 := by rw [Finset.mul_sum]
    by_contra hge
    have hgt : c ^ (k - 2) * (S₂ + δ) < tailPowerSum lam J k := not_le.mp hge
    obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.1
      (Filter.Tendsto.eventually_const_lt hgt (hy k hk))
    have hgt2 : S₂ < S₂ + δ := by linarith
    obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.1
      ((hy 2 (Nat.le_refl 2)).eventually_le_const hgt2)
    obtain ⟨n, hnN, hnmax⟩ := frequently_atTop.1 hcon (max N1 N2)
    have hn1 := hN1 n (le_trans (le_max_left N1 N2) hnN)
    have hn2 := hN2 n (le_trans (le_max_right N1 N2) hnN)
    have h3 := hbnd n hnmax
    have h4 : c ^ (k - 2) * ∑ i : Fin (m n), y n i ^ 2 ≤ c ^ (k - 2) * (S₂ + δ) :=
      mul_le_mul_of_nonneg_left hn2 (pow_nonneg hcpos.le (k - 2))
    exact absurd (le_trans h3 h4) (not_le.mpr hn1)
  -- Pass to the `k`-th roots and let `k → ∞`.
  have hroot : ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, δ > 0 →
      (tailPowerSum lam J k) ^ ((k : ℝ) ⁻¹) ≤ (c ^ (k - 2) * (S₂ + δ)) ^ ((k : ℝ) ⁻¹) := by
    intro k hk δ hδ
    have hklt : (0 : ℕ) < k := by omega
    have hkinv : 0 ≤ ((k : ℝ) ⁻¹) := le_of_lt (inv_pos.2 (Nat.cast_pos.2 hklt))
    exact Real.rpow_le_rpow (hSk_nn k) (hkey k hk δ hδ) hkinv
  have hL : Tendsto (fun k : ℕ => (tailPowerSum lam J k) ^ ((k : ℝ) ⁻¹)) atTop
      (𝓝 (lam J)) := tailPowerSum_root_tendsto hlam hnn hsum J
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
  have hfinal : ∀ δ : ℝ, δ > 0 → lam J ≤ c := fun δ hδ =>
    le_of_tendsto_of_tendsto hL (hR δ hδ)
      ((Filter.eventually_ge_atTop 2).mono fun k hk => hroot k hk δ hδ)
  have hfin1 := hfinal (1 : ℝ) one_pos
  linarith

/-- **Tail-adapted array max extraction.**  Under convergent power sums against
an antitone summable-square profile `lam` with `lam J > 0`, the suprema of the
observed coordinates converge to `lam J`. -/
theorem tail_array_max_tendsto
    (hm : ∀ n, 0 < m n) (hb : ∀ n i, 0 ≤ y n i)
    (hy : ∀ k : ℕ, 2 ≤ k → Tendsto (fun n => ∑ i : Fin (m n), y n i ^ k) atTop
      (𝓝 (tailPowerSum lam J k)))
    (hl : Antitone lam ∧ ∀ j, 0 ≤ lam j ∧ Summable (fun j => lam j ^ 2))
    (hpos : 0 < lam J) :
    Tendsto (fun n => ⨆ i, y n i) atTop (𝓝 (lam J)) := by
  have hsup : ∀ n : ℕ, (0 : ℝ) ≤ ⨆ i, y n i := fun n => by
    have h1 := le_ciSup (Set.finite_range (y n)).bddAbove ⟨0, hm n⟩
    exact (hb n ⟨0, hm n⟩).trans h1
  -- The two ε-form bounds squeeze the absolute distance.
  have hdist : ∀ ε > 0, ∀ᶠ n in atTop, |(⨆ i, y n i) - lam J| < ε := by
    intro ε hε
    have hd1 : (0 : ℝ) < ε / 2 := by linarith
    have hd2 : (0 : ℝ) < lam J / 4 := by linarith
    have hd3 : ε / 2 < ε := by linarith
    have hd4 : lam J / 4 < lam J := by linarith
    set δ : ℝ := min (ε / 2) (lam J / 4) with hδdef
    have hd : 0 < δ := lt_min hd1 hd2
    have hlt : 2 * δ < lam J := by
      have h5 : δ ≤ lam J / 4 := min_le_right _ _
      linarith
    have hle : δ < ε := lt_of_le_of_lt (min_le_left _ _) hd3
    have h1 := tail_array_max_eventually_ge hm hb hy hl hpos δ hd hlt
    have h2 := tail_array_max_eventually_le hm hb hy hl δ hd
    filter_upwards [h1, h2] with n hn1 hn2
    have h3 : 0 ≤ (⨆ i, y n i) := hsup n
    rw [abs_lt]
    constructor <;> linarith
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hdist (ε / 2) (by linarith))
  refine ⟨N, fun n hn => ?_⟩
  have h2 : ε / 2 < ε := by linarith
  rw [Real.dist_eq]
  exact lt_trans (hN n hn) h2

end Hurst
