import Hurst.FiniteProductBounds

noncomputable section
open Set
open scoped ContDiff
namespace Hurst

/-- Quantitative continuity of the finite Faà di Bruno polynomial. -/
theorem composite_derivative_difference_bound (m : ℕ) (f phi : ℝ → ℝ) (x y B D ε : ℝ)
    (hB : 1 ≤ B) (hD : 0 ≤ D) (hε : 0 ≤ ε)
    (hpx : ContDiffAt ℝ m phi (f x)) (hpy : ContDiffAt ℝ m phi (f y))
    (hfx : ContDiffAt ℝ m f x) (hfy : ContDiffAt ℝ m f y)
    (hfb : ∀ j ≤ m, |iteratedDeriv j f x| ≤ B ∧ |iteratedDeriv j f y| ≤ B)
    (hfd : ∀ j ≤ m, |iteratedDeriv j f x - iteratedDeriv j f y| ≤ D * ε)
    (hpb : ∀ j ≤ m, |iteratedDeriv j phi (f x)| ≤ B ∧ |iteratedDeriv j phi (f y)| ≤ B)
    (hpd : ∀ j ≤ m, |iteratedDeriv j phi (f x) - iteratedDeriv j phi (f y)| ≤ D * ε) :
    |iteratedDeriv m (phi ∘ f) x - iteratedDeriv m (phi ∘ f) y| ≤
      Fintype.card (OrderedFinpartition m) * ((m + 1 : ℕ) : ℝ) * D * B ^ (m + 1) * ε := by
  classical
  rw [iteratedDeriv_comp_eq_sum_orderedFinpartition hpx hfx le_rfl,
    iteratedDeriv_comp_eq_sum_orderedFinpartition hpy hfy le_rfl, ← Finset.sum_sub_distrib]
  have hterm : ∀ c : OrderedFinpartition m,
      |iteratedDeriv c.length phi (f x) * (∏ j, iteratedDeriv (c.partSize j) f x) -
        iteratedDeriv c.length phi (f y) * ∏ j, iteratedDeriv (c.partSize j) f y| ≤
          ((m + 1 : ℕ) : ℝ) * D * B ^ (m + 1) * ε := by
    intro c
    let U : Fin (c.length + 1) → ℝ := Fin.cons (iteratedDeriv c.length phi (f x)) (fun j => iteratedDeriv (c.partSize j) f x)
    let V : Fin (c.length + 1) → ℝ := Fin.cons (iteratedDeriv c.length phi (f y)) (fun j => iteratedDeriv (c.partSize j) f y)
    have hU : ∀ i, |U i| ≤ B := by
      intro i
      refine Fin.cases (hpb c.length c.length_le).1 (fun j => (hfb (c.partSize j) (c.partSize_le j)).1) i
    have hV : ∀ i, |V i| ≤ B := by
      intro i
      refine Fin.cases (hpb c.length c.length_le).2 (fun j => (hfb (c.partSize j) (c.partSize_le j)).2) i
    have hd : ∀ i, |U i - V i| ≤ D * ε := by
      intro i
      refine Fin.cases (hpd c.length c.length_le) (fun j => hfd (c.partSize j) (c.partSize_le j)) i
    have h := finite_product_difference_bound Finset.univ U V B D ε hB hD hε
      (fun i _ => hU i) (fun i _ => hV i) (fun i _ => hd i)
    simp only [U, V, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Finset.card_univ, Fintype.card_fin] at h
    apply h.trans
    have hlen : ((c.length + 1 : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.add_le_add_right c.length_le 1
    have hpow := pow_le_pow_right₀ hB (Nat.add_le_add_right c.length_le 1)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (mul_le_mul_of_nonneg_right hlen hD) hpow (pow_nonneg (by linarith) _) (by positivity)) hε
  have hs := (Finset.abs_sum_le_sum_abs _ Finset.univ).trans (Finset.sum_le_sum (fun c _ => hterm c))
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc] using hs

end Hurst
