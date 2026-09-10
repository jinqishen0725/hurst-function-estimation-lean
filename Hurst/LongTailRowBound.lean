import Hurst.FiniteRowCutoff

noncomputable section
namespace Hurst

/-- Dividing a scaled tail estimate by the positive power converts it to a
uniform decay estimate beyond an integer cutoff. -/
theorem scaled_tail_error_to_cutoff_decay
    (R : ℕ) (x psi c F r : ℝ)
    (hx : ((R + 1 : ℕ) : ℝ) ≤ x) (hpsi : 0 ≤ psi)
    (hc : 0 ≤ c) (hF : 0 ≤ F)
    (htail : |x ^ psi * r - c| ≤ F) :
    |r| ≤ (F + c) * (((R + 1 : ℕ) : ℝ) ^ (-psi)) := by
  have hRpos : (0 : ℝ) < ((R + 1 : ℕ) : ℝ) := by positivity
  have hxpos : 0 < x := hRpos.trans_le hx
  have hxpow : 0 < x ^ psi := Real.rpow_pos_of_pos hxpos _
  have hnum : |x ^ psi * r| ≤ F + c := by
    calc
      |x ^ psi * r| = |(x ^ psi * r - c) + c| := by congr 1 <;> ring
      _ ≤ |x ^ psi * r - c| + |c| := abs_add_le _ _
      _ ≤ F + c := by rw [abs_of_nonneg hc]; exact add_le_add htail le_rfl
  have hpow : ((R + 1 : ℕ) : ℝ) ^ psi ≤ x ^ psi :=
    Real.rpow_le_rpow hRpos.le hx hpsi
  have hpowInv : (x ^ psi)⁻¹ ≤
      (((R + 1 : ℕ) : ℝ) ^ psi)⁻¹ :=
    (inv_le_inv₀ hxpow (Real.rpow_pos_of_pos hRpos _)).2 hpow
  have hfactor : |r| = (x ^ psi)⁻¹ * |x ^ psi * r| := by
    rw [abs_mul, abs_of_pos hxpow]
    field_simp [hxpow.ne']
  rw [hfactor]
  calc
    (x ^ psi)⁻¹ * |x ^ psi * r| ≤
        (x ^ psi)⁻¹ * (F + c) :=
      mul_le_mul_of_nonneg_left hnum (inv_nonneg.mpr hxpow.le)
    _ ≤ (((R + 1 : ℕ) : ℝ) ^ psi)⁻¹ * (F + c) :=
      mul_le_mul_of_nonneg_right hpowInv (add_nonneg hF hc)
    _ = (F + c) * (((R + 1 : ℕ) : ℝ) ^ (-psi)) := by
      rw [Real.rpow_neg hRpos.le]
      ring

/-- A correlation row with a scaled power-law tail has a finite cutoff
bound.  This isolates the deterministic estimate needed by the long-memory
second-moment argument. -/
theorem finite_correlation_square_row_le_scaled_tail
    {m : ℕ} (R : ℕ) (psi c F : ℝ)
    (hpsi : 0 ≤ psi) (hc : 0 ≤ c) (hF : 0 ≤ F)
    (r : Fin m → Fin m → ℝ) (i : Fin m)
    (hone : ∀ j, |r i j| ≤ 1)
    (htail : ∀ j, R < Nat.dist j.val i.val →
      |((Nat.dist j.val i.val : ℕ) : ℝ) ^ psi * r i j - c| ≤ F) :
    (∑ j : Fin m, r i j ^ 2) ≤
      (2 * (R : ℝ) + 1) + (m : ℝ) *
        ((F + c) * (((R + 1 : ℕ) : ℝ) ^ (-psi))) ^ 2 := by
  apply finite_correlation_square_row_le_cutoff R
    ((F + c) * (((R + 1 : ℕ) : ℝ) ^ (-psi))) (by positivity) r i hone
  intro j hj
  apply scaled_tail_error_to_cutoff_decay R
    (Nat.dist j.val i.val : ℝ) psi c F (r i j) _ hpsi hc hF (htail j hj)
  exact_mod_cast (show R + 1 ≤ Nat.dist j.val i.val by omega)

end Hurst
