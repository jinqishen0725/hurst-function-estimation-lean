import Hurst.CorrelationSums
import Mathlib.Analysis.Normed.Group.Tannery

noncomputable section
open Filter Set
open scoped Topology
namespace Hurst

theorem summable_cutoff_tail {d : ℕ → ℝ} (hd : Summable (fun k => d k ^ 2))
    (K : ℕ) : Summable (fun k => if K < k then d k ^ 2 else 0) := by
  have h := hd.indicator {k : ℕ | K < k}
  have hfun : (fun k => if K < k then d k ^ 2 else 0) =
      {k : ℕ | K < k}.indicator (fun k => d k ^ 2) := by
    funext k
    by_cases hk : K < k <;> simp [Set.indicator, hk]
  rw [hfun]
  exact h

theorem correlation_square_tail_average_le
    (d : ℕ → ℝ) (hd : Summable (fun k => d k ^ 2))
    (hd0 : ∀ k, 0 ≤ d k) (A e : ℝ) (hA : 0 ≤ A) (he : 0 ≤ e)
    (n K : ℕ) (hn : 0 < n) (r : Fin n → Fin n → ℝ)
    (hr : ∀ i j, |r i j| ≤ A * d (Nat.dist j.val i.val) + e) :
    (n : ℝ)⁻¹ * ∑ i, ∑ j,
      (if K < Nat.dist j.val i.val then |r i j| ^ 2 else 0) ≤
      4 * A ^ 2 * (∑' k, if K < k then d k ^ 2 else 0) + 2 * n * e ^ 2 := by
  let tail : ℕ → ℝ := fun k => if K < k then d k ^ 2 else 0
  have htailsum : Summable tail := summable_cutoff_tail hd K
  have htail0 : ∀ k, 0 ≤ tail k := by
    intro k
    dsimp only [tail]
    split_ifs <;> positivity
  have hinner : ∀ i : Fin n,
      (∑ j, if K < Nat.dist j.val i.val then |r i j| ^ 2 else 0) ≤
        4 * A ^ 2 * (∑' k, tail k) + 2 * n * e ^ 2 := by
    intro i
    have hs : (∑ j, if K < Nat.dist j.val i.val then |r i j| ^ 2 else 0) ≤
        ∑ j : Fin n, (2 * A ^ 2 * tail (Nat.dist j.val i.val) + 2 * e ^ 2) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : K < Nat.dist j.val i.val
      · simp only [hj, if_true, tail]
        have hpow := pow_le_pow_left₀ (abs_nonneg _) (hr i j) 2
        rw [sq_abs]
        rw [sq_abs] at hpow
        nlinarith [sq_nonneg (A * d (Nat.dist j.val i.val) - e)]
      · simp only [hj, if_false]
        positivity
    have hdist := grid_distance_sum_le_tsum tail htailsum htail0 n i
    have hm := mul_le_mul_of_nonneg_left hdist (show 0 ≤ 2 * A ^ 2 by positivity)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
    nlinarith
  have hout : (∑ i : Fin n, ∑ j,
      if K < Nat.dist j.val i.val then |r i j| ^ 2 else 0) ≤
      (n : ℝ) * (4 * A ^ 2 * (∑' k, tail k) + 2 * n * e ^ 2) := by
    calc
      _ ≤ ∑ _i : Fin n,
          (4 * A ^ 2 * (∑' k, tail k) + 2 * n * e ^ 2) :=
        Finset.sum_le_sum (fun i _ => hinner i)
      _ = _ := by simp; ring
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    (n : ℝ)⁻¹ * ∑ i, ∑ j,
        (if K < Nat.dist j.val i.val then |r i j| ^ 2 else 0) ≤
        (n : ℝ)⁻¹ * ((n : ℝ) *
          (4 * A ^ 2 * (∑' k, tail k) + 2 * n * e ^ 2)) :=
      mul_le_mul_of_nonneg_left hout (inv_nonneg.mpr hnR.le)
    _ = 4 * A ^ 2 * (∑' k, if K < k then d k ^ 2 else 0) + 2 * n * e ^ 2 := by
      dsimp only [tail]
      field_simp

theorem cutoff_square_tsum_tendsto_zero
    (d : ℕ → ℝ) (hd : Summable (fun k => d k ^ 2)) :
    Tendsto (fun K : ℕ => ∑' k, if K < k then d k ^ 2 else 0)
      atTop (nhds 0) := by
  have ht := tendsto_tsum_of_dominated_convergence
    (f := fun K k => if K < k then d k ^ 2 else 0)
    (g := fun _ : ℕ => (0 : ℝ)) hd (fun k => by
      apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0)).congr'
      filter_upwards [eventually_ge_atTop k] with K hK
      simp [not_lt_of_ge hK]) (Filter.Eventually.of_forall (fun K k => by
      by_cases hk : K < k
      · rw [if_pos hk, Real.norm_eq_abs, abs_sq]
      · simp only [hk, if_false, norm_zero]
        positivity))
  simpa only [tsum_zero] using ht

/-- A summable frozen decay envelope plus an actual-model perturbation whose
full-row square mass vanishes implies the exact covariance-tail condition used
by the Gaussian triangular-array CLT. -/
theorem correlation_square_average_tail_vanishes
    (m : ℕ → ℕ) (r : ∀ n, Fin (m n) → Fin (m n) → ℝ)
    (d : ℕ → ℝ) (hd : Summable (fun k => d k ^ 2))
    (hd0 : ∀ k, 0 ≤ d k) (A : ℝ) (hA : 0 ≤ A) (e : ℕ → ℝ)
    (he0 : ∀ᶠ n in atTop, 0 ≤ e n)
    (hm : ∀ᶠ n in atTop, 0 < m n)
    (herr : ∀ᶠ n in atTop, ∀ i j,
      |r n i j| ≤ A * d (Nat.dist j.val i.val) + e n)
    (herate : Tendsto (fun n => (m n : ℝ) * (e n) ^ 2) atTop (nhds 0)) :
    ∀ ε > 0, ∃ K : ℕ, ∀ᶠ n : ℕ in atTop,
      (m n : ℝ)⁻¹ * ∑ i, ∑ j,
        (if K < Nat.dist i.val j.val then |r n i j| ^ 2 else 0) ≤ ε := by
  intro ε hε
  have hden : 0 < 8 * A ^ 2 + 1 := by positivity
  have htail := (cutoff_square_tsum_tendsto_zero d hd).eventually
    (eventually_lt_nhds (div_pos hε hden))
  obtain ⟨K, hK⟩ := htail.exists
  have hsmall := herate.eventually
    (eventually_lt_nhds (show (0 : ℝ) < ε / 4 by linarith))
  refine ⟨K, ?_⟩
  filter_upwards [hm, he0, herr, hsmall] with n hmn hen hrn hsn
  have hb := correlation_square_tail_average_le d hd hd0 A (e n) hA hen
    (m n) K hmn (r n) hrn
  have hb' : (m n : ℝ)⁻¹ * ∑ i, ∑ j,
      (if K < Nat.dist i.val j.val then |r n i j| ^ 2 else 0) ≤
      4 * A ^ 2 * (∑' k, if K < k then d k ^ 2 else 0) + 2 * m n * (e n) ^ 2 := by
    simpa only [Nat.dist_comm] using hb
  apply hb'.trans
  have ht0 : 0 ≤ (∑' k, if K < k then d k ^ 2 else 0) :=
    tsum_nonneg (fun k => by split_ifs <;> positivity)
  have hfirst : 4 * A ^ 2 * (∑' k, if K < k then d k ^ 2 else 0) < ε / 2 := by
    have hprod := (lt_div_iff₀ hden).mp hK
    nlinarith
  nlinarith

end Hurst
