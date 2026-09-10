import Mathlib

noncomputable section
open Filter
open scoped Topology

namespace Hurst

/-- Sequential compactness argument for a varying finite row: if every
subsequence and every choice of active row indices converges to the same
limit, then convergence is uniform over the active indices. -/
theorem eventually_uniform_of_subsequence_tendsto
    (m : ℕ → ℕ) (active : ∀ n, Fin (m n) → Prop)
    (x : ∀ n, Fin (m n) → ℝ) (a : ℝ)
    (hseq : ∀ (φ : ℕ → ℕ), StrictMono φ →
      ∀ (i : ∀ n, Fin (m (φ n))), (∀ n, active (φ n) (i n)) →
        Tendsto (fun n => x (φ n) (i n)) atTop (nhds a)) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ i, active n i → (abs (x n i - a) < ε) := by
  intro ε hε
  by_contra hnot
  have hfreq : ∃ᶠ n in atTop, ¬ (∀ i, active n i → (abs (x n i - a) < ε)) :=
    (not_eventually.mp hnot)
  obtain ⟨φ, hφmono, hφ⟩ := extraction_of_frequently_atTop hfreq
  have hbad : ∀ n, ∃ i : Fin (m (φ n)),
      active (φ n) i ∧ ε ≤ abs (x (φ n) i - a) := by
    intro n
    simp only [not_forall, Classical.not_imp, not_lt] at hφ
    obtain ⟨i, hi, hbad⟩ := hφ n
    exact ⟨i, hi, hbad⟩
  choose i hiActive hiBad using hbad
  have ht := hseq φ hφmono i hiActive
  have habs : Tendsto (fun n => abs (x (φ n) (i n) - a)) atTop (nhds 0) := by
    simpa only [Real.norm_eq_abs] using
      (tendsto_iff_norm_sub_tendsto_zero.mp ht)
  have hsmall : ∀ᶠ n in atTop, abs (x (φ n) (i n) - a) < ε :=
    habs.eventually (gt_mem_nhds hε)
  obtain ⟨n, hn⟩ := hsmall.exists
  exact (not_lt_of_ge (hiBad n)) hn

end Hurst
