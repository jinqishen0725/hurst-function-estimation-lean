import Hurst.HolderRegularity
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

noncomputable section
open Set
open scoped ENNReal NNReal
namespace Hurst

theorem ceil_degree_exponent (p : ℝ) (hp : 1 ≤ p) :
    Nat.ceil p - 1 ≤ Nat.floor p ∧ 0 < p - (Nat.ceil p - 1 : ℕ) ∧ p - (Nat.ceil p - 1 : ℕ) ≤ 1 := by
  rcases ceil_degree_cases p hp with ⟨he, hlt⟩ | ⟨he, hn⟩
  · rw [he]
    exact ⟨le_rfl, by linarith, by linarith [Nat.lt_floor_add_one p]⟩
  · have hnR : ((Nat.ceil p - 1 : ℕ) : ℝ) + 1 = Nat.floor p := by exact_mod_cast hn
    exact ⟨by omega, by linarith, by linarith⟩

theorem unit_distance_le_holder (x y α : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1)
    (hα : 0 < α) (hα1 : α ≤ 1) : |y - x| ≤ |y - x| ^ α := by
  by_cases he : y = x
  · subst y
    simp [Real.zero_rpow hα.ne']
  have hd : 0 < |y - x| := abs_pos.mpr (sub_ne_zero.mpr he)
  have hd1 : |y - x| ≤ 1 := abs_le.mpr ⟨by linarith [hy.1, hx.2], by linarith [hx.1, hy.2]⟩
  calc
    _ = |y - x| ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hd hd1 hα1

/-- All derivatives used by the estimator share a uniform Holder exponent. -/
theorem hurstHolder_uniform_jets (p : ℝ) (hp : 1 ≤ p) :
    ∃ C > 0, ∀ M : ℝ, 0 ≤ M → ∀ f ∈ hurstHolderClass p M,
      ∀ k ≤ Nat.ceil p - 1, ∀ x ∈ Ioo (0 : ℝ) 1,
      |iteratedDeriv k f x| ≤ C * (1 + M) ∧ ∀ y ∈ Ioo (0 : ℝ) 1,
        |iteratedDeriv k f y - iteratedDeriv k f x| ≤
          C * (1 + M) * |y - x| ^ (p - (Nat.ceil p - 1 : ℕ)) := by
  obtain ⟨B, hB, hbound⟩ := hurstHolder_uniform_derivative_bounds p hp
  obtain ⟨D, hD, hLip⟩ := hurstHolder_uniform_lower_derivative_lipschitz p hp
  obtain ⟨hm, hα, hα1⟩ := ceil_degree_exponent p hp
  refine ⟨B + D + 1, by positivity, ?_⟩
  intro M hM f hf k hk x hx
  have hMC : 0 ≤ 1 + M := by positivity
  refine ⟨(hbound M hM f hf x hx k (hk.trans hm)).trans (by nlinarith), ?_⟩
  intro y hy
  by_cases hkr : k < Nat.floor p
  · have h := (hLip M hM f hf k hkr x hx y hy).trans
      (mul_le_mul_of_nonneg_left (unit_distance_le_holder x y _ hx hy hα hα1) (show 0 ≤ D * (1 + M) by positivity))
    exact h.trans (mul_le_mul_of_nonneg_right (by nlinarith : D * (1 + M) ≤ (B + D + 1) * (1 + M)) (Real.rpow_nonneg (abs_nonneg _) _))
  · have hke : k = Nat.floor p := by omega
    have hme : Nat.ceil p - 1 = Nat.floor p := by omega
    rw [hme, hke]
    have h := hf.2.2 y hy x hx
    exact h.trans (mul_le_mul_of_nonneg_right (by nlinarith : M ≤ (B + D + 1) * (1 + M)) (Real.rpow_nonneg (abs_nonneg _) _))

theorem continuousOn_of_holder_real (f : ℝ → ℝ) (S : Set ℝ) (C α : ℝ)
    (hC : 0 ≤ C) (hα : 0 < α)
    (hf : ∀ x ∈ S, ∀ y ∈ S, |f x - f y| ≤ C * |x - y| ^ α) : ContinuousOn f S := by
  have hhold : HolderOnWith (Real.toNNReal C) (Real.toNNReal α) f S := by
    intro x hx y hy
    have h := ENNReal.ofReal_le_ofReal (hf x hx y hy)
    rw [ENNReal.ofReal_mul hC, ← ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hα.le] at h
    simpa only [edist_dist, Real.dist_eq, Real.coe_toNNReal _ hα.le, ENNReal.ofReal] using h
  exact hhold.continuousOn (Real.toNNReal_pos.mpr hα)

/-- The original class is C^m for m=ceil(p)-1, including the integer endpoint convention. -/
theorem hurstHolder_contDiff_degree (p M : ℝ) (hp : 1 ≤ p) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M) :
    ContDiffOn ℝ (Nat.ceil p - 1) f (Ioo (0 : ℝ) 1) := by
  obtain ⟨C, hC, hc⟩ := hurstHolder_uniform_jets p hp
  obtain ⟨hm, hα, hα1⟩ := ceil_degree_exponent p hp
  apply (contDiffOn_nat_iff_continuousOn_differentiableOn_deriv isOpen_Ioo.uniqueDiffOn).mpr
  constructor
  · intro k hk
    have hcont := continuousOn_of_holder_real (iteratedDeriv k f) (Ioo (0 : ℝ) 1)
      (C * (1 + M)) (p - (Nat.ceil p - 1 : ℕ)) (by positivity) hα
      (fun x hx y hy => (hc M hM f hf k hk y hy).2 x hx)
    exact hcont.congr (iteratedDerivWithin_of_isOpen (n := k) isOpen_Ioo)
  · intro k hk
    have hd : DifferentiableOn ℝ (iteratedDeriv k f) (Ioo (0 : ℝ) 1) :=
      fun x hx => (hf.2.1 k (lt_of_lt_of_le hk hm) x hx).differentiableWithinAt
    exact hd.congr (iteratedDerivWithin_of_isOpen (n := k) isOpen_Ioo)

end Hurst
