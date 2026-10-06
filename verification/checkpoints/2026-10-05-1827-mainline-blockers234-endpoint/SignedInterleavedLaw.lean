import Hurst.P3SignedMatching
import Hurst.SpectralPermutation

/-!
# Separate positive/negative sorting preserves the Gaussian spectral law

Decode an interleaved row into sign and rank, undo the two sorting
permutations, then swap the two slots at each original index when its
coefficient is negative. This gives an actual permutation of the original
row padded with zeros. It works for empty rows and repeated eigenvalues.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Hurst

private def signedParityEquiv (m : ℕ) : Fin (2 * m) ≃ Fin 2 × Fin m where
  toFun i := (⟨i.val % 2, Nat.mod_lt _ (by omega)⟩,
    ⟨i.val / 2, by have := i.isLt; omega⟩)
  invFun p := ⟨2 * p.2.val + p.1.val, by have := p.1.isLt; have := p.2.isLt; omega⟩
  left_inv i := by apply Fin.ext; simp only; omega
  right_inv p := by
    apply Prod.ext <;> apply Fin.ext <;> simp only
    · have := p.1.isLt; omega
    · have := p.1.isLt; omega

private def signedSlotSwap {m : ℕ} (c : Fin m → ℝ) : Fin 2 × Fin m ≃ Fin 2 × Fin m :=
  Equiv.prodCongrLeft fun j =>
    if 0 ≤ c j then Equiv.refl (Fin 2) else Equiv.swap (0 : Fin 2) 1

private theorem zeroPaddedRow_signedSlotSwap {m : ℕ} (c : Fin m → ℝ)
    (b : Fin 2) (j : Fin m) :
    zeroPaddedRow c (finProdFinEquiv (signedSlotSwap c (b, j))) =
      if b = 0 then max (c j) 0 else -max (-c j) 0 := by
  have hj : j.val < m := j.isLt
  have hjm : ¬ j.val + m < m := by omega
  fin_cases b <;> by_cases h : 0 ≤ c j
  · simp [signedSlotSwap, Equiv.prodCongrLeft, finProdFinEquiv, zeroPaddedRow,
      h, hj, max_eq_left h]
  · have hc : c j ≤ 0 := le_of_not_ge h
    simp [signedSlotSwap, Equiv.prodCongrLeft, finProdFinEquiv, zeroPaddedRow,
      h, hjm, max_eq_right hc]
  · have hn : -c j ≤ 0 := neg_nonpos.mpr h
    simp [signedSlotSwap, Equiv.prodCongrLeft, finProdFinEquiv, zeroPaddedRow,
      h, hjm, max_eq_right hn]
  · have hn : 0 ≤ -c j := neg_nonneg.mpr (le_of_not_ge h)
    simp [signedSlotSwap, Equiv.prodCongrLeft, finProdFinEquiv, zeroPaddedRow,
      h, hj, max_eq_left hn]

/-- The sign-aware permutation includes all multiplicities and the extra zeros. -/
def signedInterleavedPerm {m : ℕ} (c : Fin m → ℝ) : Equiv.Perm (Fin (2 * m)) :=
  (signedParityEquiv m).trans
    ((Equiv.prodCongrRight fun b : Fin 2 =>
      if b = 0 then decreasingSpectralPerm (signedPosPart c)
      else decreasingSpectralPerm (signedAbsNegPart c)).trans
      ((signedSlotSwap c).trans finProdFinEquiv))

theorem signedInterleavedRow_eq_zeroPadded_permute {m : ℕ} (c : Fin m → ℝ) :
    signedInterleavedRow c = zeroPaddedRow c ∘ signedInterleavedPerm c := by
  funext i
  have hj : i.val / 2 < m := by have := i.isLt; omega
  let j : Fin m := ⟨i.val / 2, hj⟩
  let b : Fin 2 := ⟨i.val % 2, Nat.mod_lt _ (by omega)⟩
  change signedInterleavedRow c i = zeroPaddedRow c
    (finProdFinEquiv (signedSlotSwap c
      (b, (if b = 0 then decreasingSpectralPerm (signedPosPart c)
        else decreasingSpectralPerm (signedAbsNegPart c)) j)))
  rw [zeroPaddedRow_signedSlotSwap]
  by_cases hi : i.val % 2 = 0
  · have hb : b = 0 := Fin.ext hi
    simp only [hb, if_pos rfl]
    rw [signedInterleavedRow, dif_pos hi, padRearranged_of_lt _ hj]
    rfl
  · have hb : b ≠ 0 := fun h => hi (congrArg Fin.val h)
    simp only [if_neg hb]
    rw [signedInterleavedRow, dif_neg hi, padRearranged_of_lt _ hj]
    rfl

/-- Separately sorting positive and negative coefficients and interleaving
them preserves the law of the original centered Gaussian quadratic sum. -/
theorem signedInterleavedRow_identDistrib {m : ℕ} (c : Fin m → ℝ) :
    IdentDistrib (centeredSpectralSquares (signedInterleavedRow c))
      (centeredSpectralSquares c)
      (stdGaussian (EuclideanSpace ℝ (Fin (2 * m))))
      (stdGaussian (EuclideanSpace ℝ (Fin m))) := by
  rw [signedInterleavedRow_eq_zeroPadded_permute]
  exact (centeredSpectralSquares_permute_identDistrib
    (signedInterleavedPerm c) (zeroPaddedRow c)).symm.trans (zeroPadding_identDistrib c)

end Hurst
