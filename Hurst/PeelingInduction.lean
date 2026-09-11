import Hurst.TailExtraction
import Hurst.PeelingSubtraction
import Hurst.ResidualMax
import Hurst.TailExtractionArray

/-!
# Peeling induction: coefficientwise convergence of the padded rearrangement

Fix a varying-size array `x n : Fin (m n) → ℝ` of nonnegative entries, with `m n`
tending to infinity, whose power sums converge to those of a limiting sequence
`lam` (antitone, nonnegative, square-summable).  By strong induction on the level
`j`, the `j`-th padded decreasingly rearranged entry converges:

* `residualTailPowerSum_restricted_tendsto` : the residual power-sum lemma of
  `Hurst.PeelingSubtraction`, with the induction hypothesis demanded only for
  levels `c < J` (which is all its proof ever consumes);
* `paddedRearranged_tendsto` : the main theorem — for every `j`,
  `padRearranged (x n) j → lam j`.

The step at `j` peels off the top `j` entries, identifies the supremum of the
residual with `padRearranged (x n) j` (eventually, since `j ≤ m n` eventually),
and applies `tail_array_max_tendsto` when `lam j > 0`, or the positivity-free
upper half `tail_array_max_eventually_le` when `lam j = 0`.
-/

namespace Hurst

open Filter Topology

/-- **Residual power-sum lemma, restricted induction hypothesis.**  If the power
sums of `x n` converge to those of `lam` and every padded rearranged entry at
levels `c < J` converges, then the power sums of the residual array (top `J`
entries removed) converge to `tailPowerSum lam J k`.  This is the proof of
`Hurst.PeelingSubtraction.residualTailPowerSum_tendsto` with `hip` demanded only
for `c < J` (the finite-sum limit `htoplim` is the only consumer). -/
theorem residualTailPowerSum_restricted_tendsto
    (m : ℕ → ℕ) (hm : ∀ n, 0 < m n) (x : ∀ n, Fin (m n) → ℝ) (lam : ℕ → ℝ)
    (hl : Antitone lam ∧ ∀ j, 0 ≤ lam j ∧ Summable (fun j => lam j ^ 2))
    (hp : ∀ k : ℕ, 2 ≤ k → Tendsto (fun n => ∑ i : Fin (m n), x n i ^ k) atTop
      (𝓝 (∑' j : ℕ, lam j ^ k)))
    (J k : ℕ) (hk : 2 ≤ k)
    (hip : ∀ c : ℕ, c < J → Tendsto (fun n => padRearranged (x n) c) atTop (𝓝 (lam c))) :
    Tendsto (fun n => ∑ i : Fin (m n), spectralResidual J (x n) i ^ k) atTop
      (𝓝 (tailPowerSum lam J k)) := by
  have hlam := hl.1
  have hnn : ∀ j, 0 ≤ lam j := fun j => (hl.2 j).1
  have hsum : Summable (fun j => lam j ^ 2) := (hl.2 0).2
  have h2k : k ≠ 0 := by omega
  have hsumk := summable_pow_of_square hlam hnn hk hsum
  have hlimval : (∑' j : ℕ, if J ≤ j then lam j ^ k else (0:ℝ))
      = tailPowerSum lam J k := by
    show (∑' j : ℕ, if J ≤ j then lam j ^ k else (0:ℝ))
      = ∑' d : ℕ, lam (J + d) ^ k
    exact tsum_pow_if_eq_shift hnn hsumk
  rw [← hlimval]
  have hsplit : ∀ n : ℕ,
      (∑ i : Fin (m n), (if J ≤ specDescendingRank (x n) i then x n i else (0:ℝ)) ^ k)
        + ∑ c ∈ Finset.range J, (padRearranged (x n) c) ^ k
      = ∑ i : Fin (m n), x n i ^ k := fun n => resid_split (m n) (x n) J k h2k
  have htoplim : Tendsto (fun n => ∑ c ∈ Finset.range J, (padRearranged (x n) c) ^ k)
      atTop (𝓝 (∑ c ∈ Finset.range J, lam c ^ k)) :=
    tendsto_finsetSum _ fun c hc => Tendsto.pow (hip c (Finset.mem_range.mp hc)) k
  have hseries : (∑' j : ℕ, lam j ^ k)
      = (∑ c ∈ Finset.range J, lam c ^ k) + ∑' d : ℕ, lam (J + d) ^ k := by
    have hs := hsumk.sum_add_tsum_nat_add J
    have hconv : (∑' d : ℕ, lam (d + J) ^ k) = (∑' d : ℕ, lam (J + d) ^ k) :=
      tsum_congr fun d => congrArg (fun z => z ^ k) (congrArg lam (Nat.add_comm d J))
    rw [← hs, hconv]
  have hlimval2 : (∑' j : ℕ, if J ≤ j then lam j ^ k else (0:ℝ))
      = (∑' j : ℕ, lam j ^ k) - ∑ c ∈ Finset.range J, lam c ^ k := by
    rw [tsum_pow_if_eq_shift hnn hsumk, hseries]
    ring
  have hfin : Tendsto (fun n => (∑ i : Fin (m n), x n i ^ k)
        - ∑ c ∈ Finset.range J, (padRearranged (x n) c) ^ k)
      atTop (𝓝 ((∑' j : ℕ, lam j ^ k) - ∑ c ∈ Finset.range J, lam c ^ k)) :=
    Tendsto.sub (hp k hk) htoplim
  have hfun : ∀ n : ℕ, (∑ i : Fin (m n), x n i ^ k)
        - ∑ c ∈ Finset.range J, (padRearranged (x n) c) ^ k
      = ∑ i : Fin (m n),
        (if J ≤ specDescendingRank (x n) i then x n i else (0:ℝ)) ^ k := by
    intro n
    have hsn := hsplit n
    linarith
  rw [hlimval2]
  exact Tendsto.congr hfun hfin

/-- **Coefficientwise convergence of the padded decreasing rearrangement.**
If the power sums of nonnegative arrays `x n` (with sizes `m n → ∞`) converge to
the power sums of an antitone, nonnegative, square-summable profile `lam`, then
every padded decreasingly rearranged entry converges to the corresponding entry
of `lam`. -/
theorem paddedRearranged_tendsto (m : ℕ → ℕ) (x : ∀ n, Fin (m n) → ℝ) (lam : ℕ → ℝ)
    (hm : ∀ n, 0 < m n) (hmtop : Tendsto m atTop atTop)
    (hb : ∀ n i, 0 ≤ x n i)
    (hl : Antitone lam ∧ ∀ j, 0 ≤ lam j ∧ Summable (fun j => lam j ^ 2))
    (hp : ∀ k : ℕ, 2 ≤ k → Tendsto (fun n => ∑ i : Fin (m n), x n i ^ k) atTop
      (𝓝 (∑' j, lam j ^ k))) :
    ∀ j : ℕ, Tendsto (fun n => padRearranged (x n) j) atTop (𝓝 (lam j)) := by
  -- The induction step at level `j`, assuming convergence below `j`.
  have hstep : ∀ j : ℕ,
      (∀ c : ℕ, c < j → Tendsto (fun n => padRearranged (x n) c) atTop (𝓝 (lam c))) →
      Tendsto (fun n => padRearranged (x n) j) atTop (𝓝 (lam j)) := by
    intro j ih
    -- The residual array is nonnegative.
    have hb' : ∀ n i, 0 ≤ spectralResidual j (x n) i := fun n i => by
      rw [spectralResidual_apply]
      by_cases h : j ≤ specDescendingRank (x n) i
      · rw [if_pos h]; exact hb n i
      · rw [if_neg h]
    -- Residual power sums converge to the `j`-tail power sums.
    have hy : ∀ k : ℕ, 2 ≤ k → Tendsto
        (fun n => ∑ i : Fin (m n), spectralResidual j (x n) i ^ k) atTop
        (𝓝 (tailPowerSum lam j k)) :=
      fun k hk => residualTailPowerSum_restricted_tendsto m hm x lam hl hp j k hk ih
    -- Eventually `j ≤ m n`, so the residual supremum is the `j`-th padded entry.
    have hev : ∀ᶠ n in atTop,
        (⨆ i : Fin (m n), spectralResidual j (x n) i) = padRearranged (x n) j := by
      filter_upwards [Filter.Tendsto.eventually_ge_atTop hmtop j] with n hn
      exact iSup_spectralResidual_eq_padRearranged j (x n) (hb n) hn
    by_cases hj0 : lam j = 0
    · -- Zero case: `lam j = 0`; the positivity-free upper half suffices.
      have hle := tail_array_max_eventually_le hm hb' hy hl
      have hdist : ∀ ε > 0, ∀ᶠ n in atTop, dist (padRearranged (x n) j) (lam j) < ε := by
        intro ε hε
        filter_upwards [hle (ε / 2) (by linarith), hev] with n hsupn hEq
        have hsupnn : 0 ≤ (⨆ i : Fin (m n), spectralResidual j (x n) i) :=
          (hb' n ⟨0, hm n⟩).trans
            (le_ciSup (Set.finite_range (spectralResidual j (x n))).bddAbove ⟨0, hm n⟩)
        rw [Real.dist_eq, ← hEq, hj0, sub_zero, abs_lt]
        constructor <;> linarith
      refine Metric.tendsto_atTop.mpr fun ε hε => ?_
      exact Filter.eventually_atTop.1 (hdist ε hε)
    · -- Positive case: full max extraction, transported along `hev`.
      have hpos : 0 < lam j := lt_of_le_of_ne ((hl.2 j).1) (Ne.symm hj0)
      exact (tail_array_max_tendsto hm hb' hy hl hpos).congr' hev
  -- Promote to all levels by bounded induction.
  have hall : ∀ N : ℕ, ∀ c : ℕ, c ≤ N →
      Tendsto (fun n => padRearranged (x n) c) atTop (𝓝 (lam c)) := by
    intro N
    induction N with
    | zero =>
      intro c hc
      have hc0 : c = 0 := le_antisymm hc (Nat.zero_le c)
      subst hc0
      exact hstep 0 (fun q hq => absurd hq (Nat.not_lt_zero q))
    | succ N ih =>
      intro c hc
      by_cases heq : c = N + 1
      · subst heq
        exact hstep (N + 1) (fun q hq => ih q (by omega))
      · exact ih c (by omega)
  intro j
  exact hall j j (Nat.le_refl j)

end Hurst
