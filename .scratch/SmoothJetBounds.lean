import Hurst.SmoothTaylor

noncomputable section
open Set
namespace Hurst

/-- One common constant bounds a finite jet and its parameter Lipschitz constants. -/
theorem smooth_uniform_jet_control (phi : ℝ → ℝ)
    (hphi : ContDiffOn ℝ (⊤ : ℕ∞) phi (Ioo (0 : ℝ) 1))
    (m : ℕ) (a b : ℝ) (ha : 0 < a) (hb : b < 1) :
    ∃ C ≥ 1, ∀ j ≤ m, (∀ h ∈ Icc a b, |iteratedDeriv j phi h| ≤ C) ∧
      ∀ h ∈ Icc a b, ∀ k ∈ Icc a b, |iteratedDeriv j phi k - iteratedDeriv j phi h| ≤ C * |k - h| := by
  classical
  choose D hD hd using (fun j : Fin (m + 2) => smooth_uniform_iteratedDeriv_bound phi hphi a b ha hb j.val)
  let C := 1 + ∑ j, D j
  have hsum : ∀ j, D j ≤ C := by
    intro j
    have he := Finset.single_le_sum (s := Finset.univ) (fun i _ => hD i) (Finset.mem_univ j)
    dsimp [C]
    linarith
  have hC : 1 ≤ C := by dsimp [C]; have he := Finset.sum_nonneg (s := Finset.univ) (fun j _ => hD j); linarith
  refine ⟨C, hC, ?_⟩
  intro j hj
  have hbound : ∀ h ∈ Icc a b, |iteratedDeriv j phi h| ≤ C :=
    fun h hh => (hd ⟨j, by omega⟩ h hh).trans (hsum _)
  refine ⟨hbound, ?_⟩
  intro h hh k hk
  have hderiv : ∀ u ∈ Icc a b, HasDerivAt (iteratedDeriv j phi) (iteratedDeriv (j + 1) phi u) u := by
    intro u hu
    simpa only [iteratedDeriv_succ] using
      (smooth_differentiable_iteratedDeriv phi hphi j u ⟨ha.trans_le hu.1, hu.2.trans_lt hb⟩).hasDerivAt
  have hbnd : ∀ u ∈ Icc a b, ‖iteratedDeriv (j + 1) phi u‖ ≤ C := by
    intro u hu
    rw [Real.norm_eq_abs]
    exact (hd ⟨j + 1, by omega⟩ u hu).trans (hsum _)
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u hu => (hderiv u hu).hasDerivWithinAt) hbnd (convex_Icc a b) hh hk
  simpa only [Real.norm_eq_abs] using h

end Hurst
