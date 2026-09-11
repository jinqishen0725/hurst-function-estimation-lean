import Hurst.TailExtraction
import Hurst.SpectralMatchingSort

/-!
# Residual subtraction: the engine of the peeling induction

Fix a varying-size array `x n : Fin (m n) → ℝ` whose power sums converge to the
power sums of a limiting sequence `lam` (antitone, nonnegative, square-summable),
and assume the induction hypothesis that each *padded decreasingly rearranged*
entry of `x n` converges to the corresponding entry of `lam`.  Peeling off the
top `J` entries amounts to subtracting their power-sum contribution:

* `spectralResidual`: the residual array that zeroes out every entry whose
  descending spectral rank is `< J` (i.e. the top `J` entries);
* `resid_split`: the per-array finite identity
  `∑ resid ^ k + ∑_{c < J} (padded rearranged c) ^ k = ∑ x ^ k`;
* `residualPowerSum_tendsto`: the main result — the power sums of the residual
  converge to `∑' j, if J ≤ j then lam j ^ k else 0`;
* `residualTailPowerSum_tendsto`: the same limit phrased through
  `tailPowerSum lam J k`.
-/

open Filter Topology

namespace Hurst

/-- The residual array after peeling off the top `J` entries (i.e. every entry
whose descending spectral rank is `< J` is replaced by `0`). -/
noncomputable def spectralResidual (J : ℕ) {m : ℕ} (xv : Fin m → ℝ) (i : Fin m) : ℝ :=
  if J ≤ specDescendingRank xv i then xv i else 0

theorem spectralResidual_apply (J : ℕ) {m : ℕ} (xv : Fin m → ℝ) (i : Fin m) :
    spectralResidual J xv i = if J ≤ specDescendingRank xv i then xv i else 0 :=
  rfl

/-- The padded decreasingly rearranged array: entry `c` for `c < m`, `0` beyond.
This is exactly the shape of the peeling induction hypothesis. -/
noncomputable def padRearranged {m : ℕ} (xv : Fin m → ℝ) (c : ℕ) : ℝ :=
  if h : c < m then xv (decreasingSpectralPerm xv ⟨c, h⟩) else 0

/-- For `k ≥ 2`, square-summability of a nonnegative antitone sequence implies
`k`-th power summability: `lam j ^ k ≤ lam 0 ^ (k - 2) * lam j ^ 2`. -/
theorem summable_pow_of_square {lam : ℕ → ℝ} (hlam : Antitone lam) (hnn : ∀ j, 0 ≤ lam j)
    {k : ℕ} (hk : 2 ≤ k) (hsum : Summable (fun j => lam j ^ 2)) :
    Summable (fun j => lam j ^ k) := by
  have hle : ∀ j, lam j ^ k ≤ lam 0 ^ (k - 2) * lam j ^ 2 := by
    intro j
    have e0 : lam j ^ k = lam j ^ (k - 2) * lam j ^ 2 := by
      rw [← pow_add, Nat.sub_add_cancel hk]
    calc lam j ^ k = lam j ^ (k - 2) * lam j ^ 2 := e0
      _ ≤ lam 0 ^ (k - 2) * lam j ^ 2 :=
          mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (hnn j) (hlam (Nat.zero_le j)) (k - 2))
            (pow_nonneg (hnn j) 2)
  have hf : Summable (fun j => lam 0 ^ (k - 2) * lam j ^ 2) :=
    by simpa [smul_eq_mul] using hsum.const_smul (lam 0 ^ (k - 2))
  exact Summable.of_nonneg_of_le (fun j => pow_nonneg (hnn j) k) hle hf

/-- The series of the peeled-off (zero-padded) sequence is the shifted series. -/
theorem tsum_pow_if_eq_shift {lam : ℕ → ℝ} (hnn : ∀ j, 0 ≤ lam j) {J k : ℕ}
    (h : Summable (fun j => lam j ^ k)) :
    (∑' j : ℕ, if J ≤ j then lam j ^ k else (0:ℝ)) = ∑' d : ℕ, lam (J + d) ^ k := by
  have hsumif : Summable (fun j => if J ≤ j then lam j ^ k else (0:ℝ)) := by
    refine Summable.of_nonneg_of_le ?_ ?_ h
    · intro j
      by_cases hs : J ≤ j
      · rw [if_pos hs]; exact pow_nonneg (hnn j) k
      · rw [if_neg hs]
    · intro j
      by_cases hs : J ≤ j
      · rw [if_pos hs]
      · rw [if_neg hs]; exact pow_nonneg (hnn j) k
  have hsplit := hsumif.sum_add_tsum_nat_add J
  have h0 : (∑ c ∈ Finset.range J, if J ≤ c then lam c ^ k else (0:ℝ)) = 0 :=
    Finset.sum_eq_zero fun c hc => if_neg (by
      have := Finset.mem_range.mp hc; omega)
  have h1 : (∑' d : ℕ, if J ≤ d + J then lam (d + J) ^ k else (0:ℝ))
      = ∑' d : ℕ, lam (J + d) ^ k := by
    refine tsum_congr fun d => ?_
    rw [Nat.add_comm d J, if_pos (Nat.le_add_right J d)]
  rw [h0, zero_add, h1] at hsplit
  exact hsplit.symm

/-- **Per-array splitting identity.**  The residual power sum plus the power sum
of the (padded) top `J` rearranged entries equals the total power sum.  This is
exact, since the residual only zeroes entries of rank `< J`, and the ranks
`< J` are exactly the first `min J m` indices of the decreasing rearrangement. -/
theorem resid_split (m : ℕ) (xv : Fin m → ℝ) (J k : ℕ) (hk : k ≠ 0) :
    (∑ i : Fin m, (if J ≤ specDescendingRank xv i then xv i else (0:ℝ)) ^ k)
      + ∑ c ∈ Finset.range J, (padRearranged xv c) ^ k
      = ∑ i : Fin m, xv i ^ k := by
  have h1 : ∀ i : Fin m, (if J ≤ specDescendingRank xv i then xv i else (0:ℝ)) ^ k
      = (if J ≤ specDescendingRank xv i then xv i ^ k else (0:ℝ)) := by
    intro i
    by_cases h : J ≤ specDescendingRank xv i
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, zero_pow hk]
  have h2 : ∀ i : Fin m, (if J ≤ specDescendingRank xv i then xv i ^ k else (0:ℝ))
        + (if specDescendingRank xv i < J then xv i ^ k else (0:ℝ)) = xv i ^ k := by
    intro i
    by_cases h : J ≤ specDescendingRank xv i
    · rw [if_pos h, if_neg (by omega), add_zero]
    · rw [if_neg h, if_pos (by omega), zero_add]
  have hperm : ∀ a : Fin m,
      decreasingSpectralPerm xv ⟨specDescendingRank xv a, specDescendingRank_lt xv a⟩ = a :=
    fun a => specDescendingRank_injective xv (by
      rw [specDescendingRank_decreasingSpectralPerm, Fin.val_mk])
  -- The padded top-J sum: zero entries beyond `m n`, then reindex by the rank.
  have htop : (∑ i : Fin m, (if specDescendingRank xv i < J then xv i ^ k else (0:ℝ)))
      = ∑ c ∈ Finset.range J, (padRearranged xv c) ^ k := by
    simp only [padRearranged]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    rw [← Finset.sum_subset
      (h := Finset.filter_subset (fun c : ℕ => c < m) (Finset.range J))
      (fun c hc hmem => by
        have hc' : ¬ (c < m) := fun hlt => hmem (Finset.mem_filter.mpr ⟨hc, hlt⟩)
        rw [dif_neg hc', zero_pow hk])]
    refine Finset.sum_bij (fun a _ => specDescendingRank xv a) ?_ ?_ ?_ ?_
    · intro a ha
      have ha' := (Finset.mem_filter.mp ha).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha', specDescendingRank_lt xv a⟩
    · intro a₁ _ a₂ _ hEq
      exact specDescendingRank_injective xv hEq
    · intro b hb
      obtain ⟨hbJ, hbm⟩ := Finset.mem_filter.mp hb
      refine ⟨decreasingSpectralPerm xv ⟨b, hbm⟩, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · rw [specDescendingRank_decreasingSpectralPerm]
        exact Finset.mem_range.mp hbJ
      · rw [specDescendingRank_decreasingSpectralPerm, Fin.val_mk]
    · intro a _
      rw [dif_pos (specDescendingRank_lt xv a), hperm a]
  -- Third identity: merge the two ite-sums, then evaluate pointwise.
  have h3 : (∑ i : Fin m, (if J ≤ specDescendingRank xv i then xv i ^ k else (0:ℝ)))
        + ∑ i : Fin m, (if specDescendingRank xv i < J then xv i ^ k else (0:ℝ))
      = ∑ i : Fin m, ((if J ≤ specDescendingRank xv i then xv i ^ k else (0:ℝ))
        + (if specDescendingRank xv i < J then xv i ^ k else (0:ℝ))) :=
    Finset.sum_add_distrib.symm
  calc (∑ i : Fin m, (if J ≤ specDescendingRank xv i then xv i else (0:ℝ)) ^ k)
        + ∑ c ∈ Finset.range J, (padRearranged xv c) ^ k
      = (∑ i : Fin m, (if J ≤ specDescendingRank xv i then xv i ^ k else (0:ℝ)))
          + ∑ c ∈ Finset.range J, (padRearranged xv c) ^ k := by
        rw [Finset.sum_congr rfl fun i _ => h1 i]
    _ = (∑ i : Fin m, (if J ≤ specDescendingRank xv i then xv i ^ k else (0:ℝ)))
          + (∑ i : Fin m, (if specDescendingRank xv i < J then xv i ^ k else (0:ℝ))) := by
        rw [htop]
    _ = ∑ i : Fin m, ((if J ≤ specDescendingRank xv i then xv i ^ k else (0:ℝ))
          + (if specDescendingRank xv i < J then xv i ^ k else (0:ℝ))) := h3
    _ = ∑ i : Fin m, xv i ^ k := Finset.sum_congr rfl fun i _ => h2 i

/-- **Residual subtraction lemma.**  If the power sums of `x n` converge to those
of `lam` and every padded decreasingly rearranged entry converges to the
corresponding entry of `lam`, then the power sums of the residual array (top `J`
entries removed) converge to the power series of `lam` started at `J`. -/
theorem residualPowerSum_tendsto
    (m : ℕ → ℕ) (hm : ∀ n, 0 < m n)
    (x : ∀ n, Fin (m n) → ℝ)
    (lam : ℕ → ℝ)
    (hl : Antitone lam ∧ ∀ j, 0 ≤ lam j ∧ Summable (fun j => lam j ^ 2))
    (hp : ∀ k : ℕ, 2 ≤ k → Tendsto (fun n => ∑ i : Fin (m n), x n i ^ k) atTop
      (𝓝 (∑' j : ℕ, lam j ^ k)))
    (hip : ∀ c : ℕ, Tendsto
      (fun n => if h : c < m n then x n (decreasingSpectralPerm (x n) ⟨c, h⟩) else (0:ℝ))
      atTop (𝓝 (lam c)))
    (J : ℕ) :
    ∀ k : ℕ, 2 ≤ k → Tendsto
      (fun n => ∑ i : Fin (m n),
        (if J ≤ specDescendingRank (x n) i then x n i else (0:ℝ)) ^ k) atTop
      (𝓝 (∑' j : ℕ, if J ≤ j then lam j ^ k else (0:ℝ))) := by
  intro k hk
  have hlam := hl.1
  have hnn : ∀ j, 0 ≤ lam j := fun j => (hl.2 j).1
  have hsum : Summable (fun j => lam j ^ 2) := (hl.2 0).2
  have h2k : k ≠ 0 := by omega
  have hsumk := summable_pow_of_square hlam hnn hk hsum
  have hsplit : ∀ n : ℕ,
      (∑ i : Fin (m n), (if J ≤ specDescendingRank (x n) i then x n i else (0:ℝ)) ^ k)
        + ∑ c ∈ Finset.range J,
            (if h : c < m n then x n (decreasingSpectralPerm (x n) ⟨c, h⟩) else (0:ℝ)) ^ k
      = ∑ i : Fin (m n), x n i ^ k := fun n => resid_split (m n) (x n) J k h2k
  have htoplim : Tendsto (fun n => ∑ c ∈ Finset.range J,
      (if h : c < m n then x n (decreasingSpectralPerm (x n) ⟨c, h⟩) else (0:ℝ)) ^ k)
      atTop (𝓝 (∑ c ∈ Finset.range J, lam c ^ k)) :=
    tendsto_finsetSum _ fun c _ => Tendsto.pow (hip c) k
  have hseries : (∑' j : ℕ, lam j ^ k)
      = (∑ c ∈ Finset.range J, lam c ^ k) + ∑' d : ℕ, lam (J + d) ^ k := by
    have hs := hsumk.sum_add_tsum_nat_add J
    have hconv : (∑' d : ℕ, lam (d + J) ^ k) = (∑' d : ℕ, lam (J + d) ^ k) :=
      tsum_congr fun d => congrArg (fun z => z ^ k) (congrArg lam (Nat.add_comm d J))
    rw [← hs, hconv]
  have hlimval : (∑' j : ℕ, if J ≤ j then lam j ^ k else (0:ℝ))
      = (∑' j : ℕ, lam j ^ k) - ∑ c ∈ Finset.range J, lam c ^ k := by
    rw [tsum_pow_if_eq_shift hnn hsumk, hseries]
    ring
  have hfin : Tendsto (fun n => (∑ i : Fin (m n), x n i ^ k)
        - ∑ c ∈ Finset.range J,
            (if h : c < m n then x n (decreasingSpectralPerm (x n) ⟨c, h⟩) else (0:ℝ)) ^ k)
      atTop (𝓝 ((∑' j : ℕ, lam j ^ k) - ∑ c ∈ Finset.range J, lam c ^ k)) :=
    Tendsto.sub (hp k hk) htoplim
  have hfun : ∀ n : ℕ, (∑ i : Fin (m n), x n i ^ k)
        - ∑ c ∈ Finset.range J,
            (if h : c < m n then x n (decreasingSpectralPerm (x n) ⟨c, h⟩) else (0:ℝ)) ^ k
      = ∑ i : Fin (m n),
        (if J ≤ specDescendingRank (x n) i then x n i else (0:ℝ)) ^ k := by
    intro n
    have hsn := hsplit n
    linarith
  rw [hlimval]
  exact Tendsto.congr hfun hfin

/-- The same limit phrased through `tailPowerSum`. -/
theorem residualTailPowerSum_tendsto
    (m : ℕ → ℕ) (hm : ∀ n, 0 < m n)
    (x : ∀ n, Fin (m n) → ℝ)
    (lam : ℕ → ℝ)
    (hl : Antitone lam ∧ ∀ j, 0 ≤ lam j ∧ Summable (fun j => lam j ^ 2))
    (hp : ∀ k : ℕ, 2 ≤ k → Tendsto (fun n => ∑ i : Fin (m n), x n i ^ k) atTop
      (𝓝 (∑' j : ℕ, lam j ^ k)))
    (hip : ∀ c : ℕ, Tendsto
      (fun n => if h : c < m n then x n (decreasingSpectralPerm (x n) ⟨c, h⟩) else (0:ℝ))
      atTop (𝓝 (lam c)))
    (J k : ℕ) (hk : 2 ≤ k) :
    Tendsto (fun n => ∑ i : Fin (m n),
        (if J ≤ specDescendingRank (x n) i then x n i else (0:ℝ)) ^ k) atTop
      (𝓝 (tailPowerSum lam J k)) := by
  have hlam := hl.1
  have hnn : ∀ j, 0 ≤ lam j := fun j => (hl.2 j).1
  have hsum : Summable (fun j => lam j ^ 2) := (hl.2 0).2
  have hsumk := summable_pow_of_square hlam hnn hk hsum
  have hlimval : (∑' j : ℕ, if J ≤ j then lam j ^ k else (0:ℝ))
      = tailPowerSum lam J k := by
    show (∑' j : ℕ, if J ≤ j then lam j ^ k else (0:ℝ))
      = ∑' d : ℕ, lam (J + d) ^ k
    exact tsum_pow_if_eq_shift hnn hsumk
  rw [← hlimval]
  exact residualPowerSum_tendsto m hm x lam hl hp hip J k hk

end Hurst
