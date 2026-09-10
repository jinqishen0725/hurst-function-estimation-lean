import Hurst.PaddedFeatureRow

noncomputable section
open Filter
namespace Hurst

/-- Extend a polynomial row by evaluating a prescribed polynomial profile on
the new right-end coordinates.  Unlike zero padding, this satisfies the B&S
uniform profile condition even when the profile does not vanish at `1`. -/
def paddedPolynomialRow {m : ℕ} (P : Fin m → Polynomial ℝ)
    (Φ : ℝ → Polynomial ℝ) (d : ℕ) (i : Fin (m + d)) : Polynomial ℝ :=
  if hi : i.val < m then P ⟨i.val, hi⟩
  else Φ (((i.val : ℝ) + 1) / (m + d : ℝ))

@[simp] theorem paddedPolynomialRow_castAdd {m : ℕ}
    (P : Fin m → Polynomial ℝ) (Φ : ℝ → Polynomial ℝ)
    (d : ℕ) (i : Fin m) :
    paddedPolynomialRow P Φ d (Fin.castAdd d i) = P i := by
  simp [paddedPolynomialRow]

@[simp] theorem paddedPolynomialRow_natAdd {m : ℕ}
    (P : Fin m → Polynomial ℝ) (Φ : ℝ → Polynomial ℝ)
    (d : ℕ) (i : Fin d) :
    paddedPolynomialRow P Φ d (Fin.natAdd m i) =
      Φ ((((m + i.val : ℕ) : ℝ) + 1) / (m + d : ℝ)) := by
  simp [paddedPolynomialRow]

/-- Exact target/filler decomposition of an exact-size B&S row. -/
theorem paddedPolynomialRow_sum {m : ℕ}
    (P : Fin m → Polynomial ℝ) (Φ : ℝ → Polynomial ℝ)
    (d : ℕ) (X : Fin (m + d) → ℝ) :
    (∑ i, (paddedPolynomialRow P Φ d i).eval (X i)) =
      (∑ i : Fin m, (P i).eval (X (Fin.castAdd d i))) +
      ∑ i : Fin d,
        (Φ ((((m + i.val : ℕ) : ℝ) + 1) / (m + d : ℝ))).eval
          (X (Fin.natAdd m i)) := by
  rw [Fin.sum_univ_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [paddedPolynomialRow_castAdd]
  · apply Finset.sum_congr rfl
    intro i _
    rw [paddedPolynomialRow_natAdd]

/-- The normalized padded statistic is the normalized target block plus a
right-end filler remainder, with the same exact-row normalization. -/
theorem paddedPolynomialRow_normalized_sum {m : ℕ}
    (P : Fin m → Polynomial ℝ) (Φ : ℝ → Polynomial ℝ)
    (d : ℕ) (X : Fin (m + d) → ℝ) :
    (Real.sqrt (m + d : ℝ))⁻¹ *
        ∑ i, (paddedPolynomialRow P Φ d i).eval (X i) =
      (Real.sqrt (m + d : ℝ))⁻¹ *
          ∑ i : Fin m, (P i).eval (X (Fin.castAdd d i)) +
      (Real.sqrt (m + d : ℝ))⁻¹ *
          ∑ i : Fin d,
            (Φ ((((m + i.val : ℕ) : ℝ) + 1) / (m + d : ℝ))).eval
              (X (Fin.natAdd m i)) := by
  rw [paddedPolynomialRow_sum, mul_add]

/-- With no holes, padding is definitionally the original row after the
canonical `Fin (m+0) ≃ Fin m` cast. -/
theorem paddedPolynomialRow_zero {m : ℕ}
    (P : Fin m → Polynomial ℝ) (Φ : ℝ → Polynomial ℝ)
    (i : Fin (m + 0)) :
    paddedPolynomialRow P Φ 0 i = P (Fin.cast (Nat.add_zero m) i) := by
  simp [paddedPolynomialRow]

end Hurst
