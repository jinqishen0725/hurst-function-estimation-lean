import Hurst.ShiftedWeightEnergy
import Mathlib.Analysis.Normed.Group.Tannery

noncomputable section
open Filter
open scoped Topology
namespace Hurst

def symmetricLagTerm (m : ℕ) (F : ℕ → ℕ → ℝ) (k : ℕ) : ℝ :=
  if k = 0 then ∑ i ∈ Finset.range m, F i i
  else 2 * ∑ i ∈ Finset.range (m - k), F i (i + k)

@[simp]
theorem symmetricLagTerm_eq_zero_of_le
    (m : ℕ) (F : ℕ → ℕ → ℝ) (k : ℕ) (h : m ≤ k) :
    symmetricLagTerm m F k = 0 := by
  by_cases hk : k = 0
  · subst k
    have hm : m = 0 := by omega
    simp [symmetricLagTerm, hm]
  · simp [symmetricLagTerm, hk, Nat.sub_eq_zero_of_le h]

theorem finite_symmetric_double_sum_eq_lags
    (m : ℕ) (F : ℕ → ℕ → ℝ)
    (hsym : ∀ i j, i < m → j < m → F i j = F j i) :
    (∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m, F i j) =
      ∑ k ∈ Finset.range m, symmetricLagTerm m F k := by
  classical
  let P := Finset.range m ×ˢ Finset.range m
  let D := P.filter (fun p : ℕ × ℕ => p.1 = p.2)
  let R := P.filter (fun p : ℕ × ℕ => p.1 ≠ p.2)
  let U := R.filter (fun p : ℕ × ℕ => p.1 < p.2)
  let L := R.filter (fun p : ℕ × ℕ => ¬ p.1 < p.2)
  let Q := P.filter (fun p : ℕ × ℕ => 0 < p.1 ∧ p.2 + p.1 < m)
  have hsplit :
      (∑ p ∈ P, F p.1 p.2) =
        (∑ p ∈ D, F p.1 p.2) +
          (∑ p ∈ U, F p.1 p.2) + ∑ p ∈ L, F p.1 p.2 := by
    have hDR := Finset.sum_filter_add_sum_filter_not P
      (fun p : ℕ × ℕ => p.1 = p.2) (fun p => F p.1 p.2)
    have hUL := Finset.sum_filter_add_sum_filter_not R
      (fun p : ℕ × ℕ => p.1 < p.2) (fun p => F p.1 p.2)
    simpa only [D, R, U, L, add_assoc] using hDR.symm.trans (congrArg
      (fun z => (∑ p ∈ D, F p.1 p.2) + z) hUL.symm)
  have hdiag : (∑ p ∈ D, F p.1 p.2) =
      ∑ i ∈ Finset.range m, F i i := by
    simp only [D, P, Finset.sum_filter, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro i hi
    simp [hi]
  have hlower : (∑ p ∈ L, F p.1 p.2) = ∑ p ∈ U, F p.1 p.2 := by
    let swap : ℕ × ℕ → ℕ × ℕ := fun p => (p.2, p.1)
    apply Finset.sum_bij (fun p _ => swap p)
    · intro p hp
      simp only [L, U, R, P, Finset.mem_filter, Finset.mem_product,
        Finset.mem_range] at hp ⊢
      rcases hp with ⟨⟨⟨hp1, hp2⟩, hne⟩, hnlt⟩
      exact ⟨⟨⟨hp2, hp1⟩, hne.symm⟩, lt_of_le_of_ne (le_of_not_gt hnlt) hne.symm⟩
    · intro p hp q hq he
      dsimp [swap] at he
      exact Prod.ext (congrArg Prod.snd he) (congrArg Prod.fst he)
    · intro p hp
      simp only [U, R, P, Finset.mem_filter, Finset.mem_product,
        Finset.mem_range] at hp
      refine ⟨swap p, ?_, ?_⟩
      · rcases hp with ⟨⟨⟨hp1, hp2⟩, hne⟩, hlt⟩
        simp only [L, R, P, Finset.mem_filter, Finset.mem_product,
          Finset.mem_range, swap]
        exact ⟨⟨⟨hp2, hp1⟩, hne.symm⟩, not_lt_of_ge hlt.le⟩
      · simp [swap]
    · intro p hp
      simp only [L, R, P, Finset.mem_filter, Finset.mem_product,
        Finset.mem_range] at hp
      rcases hp with ⟨⟨⟨hp1, hp2⟩, _⟩, _⟩
      dsimp [swap]
      exact hsym p.1 p.2 hp1 hp2
  have hupper : (∑ p ∈ U, F p.1 p.2) =
      ∑ p ∈ Q, F p.2 (p.2 + p.1) := by
    let lag : ℕ × ℕ → ℕ × ℕ := fun p => (p.2 - p.1, p.1)
    apply Finset.sum_bij (fun p _ => lag p)
    · intro p hp
      simp only [U, R, P, Q, Finset.mem_filter, Finset.mem_product,
        Finset.mem_range] at hp ⊢
      rcases hp with ⟨⟨⟨hp1, hp2⟩, hne⟩, hlt⟩
      dsimp [lag]
      refine ⟨⟨(Nat.sub_le _ _).trans_lt hp2, hp1⟩,
        ⟨Nat.sub_pos_of_lt hlt, ?_⟩⟩
      omega
    · intro p hp q hq he
      simp only [U, R, P, Finset.mem_filter, Finset.mem_product,
        Finset.mem_range] at hp hq
      rcases hp with ⟨⟨⟨hp1, hp2⟩, _⟩, hplt⟩
      rcases hq with ⟨⟨⟨hq1, hq2⟩, _⟩, hqlt⟩
      dsimp [lag] at he
      have he1 := congrArg Prod.fst he
      have he2 := congrArg Prod.snd he
      apply Prod.ext
      · exact he2
      · omega
    · intro p hp
      simp only [Q, P, Finset.mem_filter, Finset.mem_product,
        Finset.mem_range] at hp
      rcases hp with ⟨⟨hp1, hp2⟩, hkpos, hsum⟩
      refine ⟨(p.2, p.2 + p.1), ?_, ?_⟩
      · simp only [U, R, P, Finset.mem_filter, Finset.mem_product,
          Finset.mem_range]
        exact ⟨⟨⟨hp2, hsum⟩, by omega⟩, by omega⟩
      · dsimp [lag]
        apply Prod.ext <;> simp_all
    · intro p hp
      simp only [U, R, P, Finset.mem_filter, Finset.mem_product,
        Finset.mem_range] at hp
      rcases hp with ⟨⟨⟨_, _⟩, _⟩, hlt⟩
      dsimp [lag]
      congr 2
      omega
  have hQ : (∑ p ∈ Q, F p.2 (p.2 + p.1)) =
      ∑ k ∈ Finset.range m, if k = 0 then 0
        else ∑ i ∈ Finset.range (m - k), F i (i + k) := by
    simp only [Q, P, Finset.sum_filter, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.sum_ite]
    simp only [Finset.sum_const_zero, add_zero]
    by_cases hk0 : k = 0
    · subst k
      simp
    · simp only [hk0, if_false]
      apply Finset.sum_congr
      · ext i
        simp only [Finset.mem_filter, Finset.mem_range]
        omega
      · intro i hi
        rfl
  rw [← Finset.sum_product']
  rw [hsplit, hdiag, hlower, hupper, hQ]
  by_cases hm : m = 0
  · subst m
    simp [symmetricLagTerm]
  · simp only [symmetricLagTerm, Finset.sum_ite]
    simp [Finset.sum_filter, hm, Nat.pos_of_ne_zero hm, mul_comm]
    rw [show (∑ k ∈ Finset.range m, if k = 0 then 0
          else 2 * ∑ i ∈ Finset.range (m - k), F i (i + k)) =
        (∑ k ∈ Finset.range m, if k = 0 then 0
          else ∑ i ∈ Finset.range (m - k), F i (i + k)) +
        ∑ k ∈ Finset.range m, if k = 0 then 0
          else ∑ i ∈ Finset.range (m - k), F i (i + k) by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hk0 : k = 0 <;> simp [hk0] <;> ring]
    ring



theorem tendsto_sum_range_of_dominated_lag
    {α : Type*} {𝓕 : Filter α} (m : α → ℕ)
    (f : α → ℕ → ℝ) (g bound : ℕ → ℝ)
    (hsupport : ∀ n k, m n ≤ k → f n k = 0)
    (hpoint : ∀ k, Tendsto (fun n => f n k) 𝓕 (𝓝 (g k)))
    (hsum : Summable bound)
    (hbound : ∀ᶠ n in 𝓕, ∀ k, |f n k| ≤ bound k) :
    Tendsto (fun n => ∑ k ∈ Finset.range (m n), f n k)
      𝓕 (𝓝 (∑' k, g k)) := by
  have ht := tendsto_tsum_of_dominated_convergence hsum hpoint (by
    filter_upwards [hbound] with n hn
    intro k
    simpa only [Real.norm_eq_abs] using hn k)
  convert ht using 1
  funext n
  rw [tsum_eq_sum (s := Finset.range (m n)) (fun k hk =>
    hsupport n k (le_of_not_gt (fun h => hk (Finset.mem_range.mpr h))))]

/-- Reindex each finite symmetric double sum by lag and apply Tannery's
theorem to the resulting zero-extended lag rows. -/
theorem tendsto_symmetric_double_sum_of_dominated_lags
    {α : Type*} {𝓕 : Filter α} (m : α → ℕ)
    (F : α → ℕ → ℕ → ℝ) (g bound : ℕ → ℝ)
    (hsym : ∀ n i j, i < m n → j < m n → F n i j = F n j i)
    (hpoint : ∀ k, Tendsto
      (fun n => symmetricLagTerm (m n) (F n) k) 𝓕 (𝓝 (g k)))
    (hsum : Summable bound)
    (hbound : ∀ᶠ n in 𝓕, ∀ k,
      |symmetricLagTerm (m n) (F n) k| ≤ bound k) :
    Tendsto (fun n => ∑ i ∈ Finset.range (m n),
      ∑ j ∈ Finset.range (m n), F n i j)
      𝓕 (𝓝 (∑' k, g k)) := by
  have ht := tendsto_sum_range_of_dominated_lag m
    (fun n k => symmetricLagTerm (m n) (F n) k) g bound
    (fun n k hk => symmetricLagTerm_eq_zero_of_le (m n) (F n) k hk)
    hpoint hsum hbound
  exact ht.congr' (Filter.Eventually.of_forall fun n =>
    (finite_symmetric_double_sum_eq_lags (m n) (F n) (hsym n)).symm)

end Hurst
