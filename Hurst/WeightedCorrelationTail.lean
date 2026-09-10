import Hurst.TruncatedCovarianceLimit

noncomputable section
namespace Hurst

theorem weighted_truncationCovariance_tail_le
    (m K M : ℕ) (N D B T : ℝ) (hN : 0 < N)
    (hD : 0 ≤ D) (hB : 0 ≤ B) (hT : 0 ≤ T)
    (w : Fin m → ℝ) (corr : Fin m → Fin m → ℝ)
    (hwmax : ∀ i, |w i| ≤ D / N)
    (hwmass : ∑ i, |w i| ≤ B)
    (hcorr : ∀ i j, |corr i j| ≤ 1)
    (htail : ∀ i, ∑ j,
      (if K < Nat.dist j.val i.val then corr i j ^ 2 else 0) ≤ T) :
    N * |∑ i, ∑ j, if K < Nat.dist j.val i.val then
      w i * w j * gaussianLogTruncationCovariance M (corr i j) else 0| ≤
      D * B * (∑ k ∈ Finset.range M, gaussianLogHermiteCoefficient k ^ 2) * T := by
  let E : ℝ := ∑ k ∈ Finset.range M, gaussianLogHermiteCoefficient k ^ 2
  have hE : 0 ≤ E := Finset.sum_nonneg (fun k _ => sq_nonneg _)
  have hsum : |∑ i, ∑ j, if K < Nat.dist j.val i.val then
      w i * w j * gaussianLogTruncationCovariance M (corr i j) else 0| ≤
      ∑ i, |w i| * (D / N) * E * T := by
    calc
      _ ≤ ∑ i, |∑ j, if K < Nat.dist j.val i.val then
          w i * w j * gaussianLogTruncationCovariance M (corr i j) else 0| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, if K < Nat.dist j.val i.val then
          |w i| * (D / N) * E * corr i j ^ 2 else 0 := by
        apply Finset.sum_le_sum
        intro i _
        calc
          _ ≤ ∑ j, |if K < Nat.dist j.val i.val then
              w i * w j * gaussianLogTruncationCovariance M (corr i j) else 0| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ _ := by
            apply Finset.sum_le_sum
            intro j _
            by_cases hj : K < Nat.dist j.val i.val
            · simp only [hj, if_true, abs_mul]
              have hc := gaussianLogTruncationCovariance_abs_le_square M (corr i j) (hcorr i j)
              calc
                |w i| * |w j| * |gaussianLogTruncationCovariance M (corr i j)| ≤
                    |w i| * (D / N) * |gaussianLogTruncationCovariance M (corr i j)| := by
                  exact mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left (hwmax j) (abs_nonneg _)) (abs_nonneg _)
                _ ≤ |w i| * (D / N) * (E * corr i j ^ 2) := by
                  have hc' : |gaussianLogTruncationCovariance M (corr i j)| ≤
                      E * corr i j ^ 2 := by
                    simpa only [E, mul_comm, sq_abs] using hc
                  exact mul_le_mul_of_nonneg_left hc'
                    (mul_nonneg (abs_nonneg _) (div_nonneg hD hN.le))
                _ = |w i| * (D / N) * E * corr i j ^ 2 := by ring
            · simp [hj]
      _ ≤ ∑ i, |w i| * (D / N) * E * T := by
        apply Finset.sum_le_sum
        intro i _
        have hi := htail i
        calc
          (∑ j, if K < Nat.dist j.val i.val then
              |w i| * (D / N) * E * corr i j ^ 2 else 0) =
              ∑ j, (|w i| * (D / N) * E) *
                (if K < Nat.dist j.val i.val then corr i j ^ 2 else 0) := by
            apply Finset.sum_congr rfl
            intro j _
            by_cases hj : K < Nat.dist j.val i.val <;> simp [hj]
          _ =
              (|w i| * (D / N) * E) *
                (∑ j, if K < Nat.dist j.val i.val then corr i j ^ 2 else 0) := by
            symm
            simpa only [sq_abs] using
              (Finset.mul_sum Finset.univ
                (fun j : Fin m => if K < Nat.dist j.val i.val then corr i j ^ 2 else 0)
                (|w i| * (D / N) * E))
          _ ≤ (|w i| * (D / N) * E) * T := by
            gcongr
          _ = _ := by ring
  have hscaled := mul_le_mul_of_nonneg_left hsum hN.le
  calc
    N * |∑ i, ∑ j, if K < Nat.dist j.val i.val then
        w i * w j * gaussianLogTruncationCovariance M (corr i j) else 0| ≤
        N * (∑ i, |w i| * (D / N) * E * T) := hscaled
    _ = D * (∑ i, |w i|) * E * T := by
      have hf : (∑ i, |w i| * (D / N) * E * T) =
          (∑ i, |w i|) * (D / N) * E * T := by
        simp only [← Finset.sum_mul]
      rw [hf]
      field_simp
    _ ≤ D * B * E * T := by
      gcongr
    _ = _ := rfl

end Hurst
