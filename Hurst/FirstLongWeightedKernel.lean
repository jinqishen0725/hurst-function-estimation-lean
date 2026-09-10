import Hurst.FirstLongRieszEnergy

noncomputable section
open Set Filter
open scoped Topology
namespace Hurst

/-- Multiplying the rows of two mesh kernels by nearby bounded weights preserves
Hilbert--Schmidt closeness.  This is the deterministic algebra behind the
signed equivalent-kernel step; no positivity of either weight is used. -/
theorem realScaleMeshEnergy_left_weight_sub_le {m : ℕ}
    (S : ℝ) (A B : Fin m → Fin m → ℝ) (u v : Fin m → ℝ)
    (U e : ℝ)
    (hu : ∀ i, |u i| ≤ U) (huv : ∀ i, |u i - v i| ≤ e) :
    realScaleMeshEnergy S (fun i j => u i * A i j - v i * B i j) ≤
      2 * U ^ 2 * realScaleMeshEnergy S (fun i j => A i j - B i j) +
        2 * e ^ 2 * realScaleMeshEnergy S B := by
  have hterm (i j : Fin m) :
      (u i * A i j - v i * B i j) ^ 2 ≤
        2 * U ^ 2 * (A i j - B i j) ^ 2 +
          2 * e ^ 2 * B i j ^ 2 := by
    have hid : u i * A i j - v i * B i j =
        u i * (A i j - B i j) + (u i - v i) * B i j := by ring
    rw [hid]
    have hs :
        (u i * (A i j - B i j) + (u i - v i) * B i j) ^ 2 ≤
          2 * (u i * (A i j - B i j)) ^ 2 +
            2 * ((u i - v i) * B i j) ^ 2 := by
      nlinarith [sq_nonneg
        (u i * (A i j - B i j) - (u i - v i) * B i j)]
    have hu2 : (u i) ^ 2 ≤ U ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (u i)) (hu i) 2
    have huv2 : (u i - v i) ^ 2 ≤ e ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (u i - v i)) (huv i) 2
    have hmul1 := mul_le_mul_of_nonneg_right hu2 (sq_nonneg (A i j - B i j))
    have hmul2 := mul_le_mul_of_nonneg_right huv2 (sq_nonneg (B i j))
    calc
      (u i * (A i j - B i j) + (u i - v i) * B i j) ^ 2 ≤
          2 * (u i * (A i j - B i j)) ^ 2 +
            2 * ((u i - v i) * B i j) ^ 2 := hs
      _ ≤ 2 * U ^ 2 * (A i j - B i j) ^ 2 +
            2 * e ^ 2 * B i j ^ 2 := by
        simp only [mul_pow]
        nlinarith
  unfold realScaleMeshEnergy
  have hsum :
      (∑ i : Fin m, ∑ j : Fin m,
        (u i * A i j - v i * B i j) ^ 2) ≤
      ∑ i : Fin m, ∑ j : Fin m,
        (2 * U ^ 2 * (A i j - B i j) ^ 2 +
          2 * e ^ 2 * B i j ^ 2) := by
      gcongr with i hi j hj
      exact hterm i j
  have hsplit :
      (∑ i : Fin m, ∑ j : Fin m,
        (2 * U ^ 2 * (A i j - B i j) ^ 2 +
          2 * e ^ 2 * B i j ^ 2)) =
        2 * U ^ 2 * (∑ i : Fin m, ∑ j : Fin m,
          (A i j - B i j) ^ 2) +
        2 * e ^ 2 * (∑ i : Fin m, ∑ j : Fin m, B i j ^ 2) := by
    simp_rw [Finset.sum_add_distrib]
    simp_rw [← Finset.mul_sum]
  calc
    S⁻¹ ^ 2 * (∑ i : Fin m, ∑ j : Fin m,
        (u i * A i j - v i * B i j) ^ 2) ≤
      S⁻¹ ^ 2 * (∑ i : Fin m, ∑ j : Fin m,
        (2 * U ^ 2 * (A i j - B i j) ^ 2 +
          2 * e ^ 2 * B i j ^ 2)) :=
      mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ = 2 * U ^ 2 * (S⁻¹ ^ 2 * ∑ i : Fin m, ∑ j : Fin m,
          (A i j - B i j) ^ 2) +
        2 * e ^ 2 * (S⁻¹ ^ 2 * ∑ i : Fin m, ∑ j : Fin m, B i j ^ 2) := by
      rw [hsplit]
      ring

/-- Filter form of the preceding estimate.  Uniform convergence of possibly
signed row weights and bounded reference energy are enough; no square root of
the covariance operator is needed at this stage. -/
theorem realScaleMeshEnergy_left_weight_sub_tendsto_zero
    (m : ℕ → ℕ) (S : ℕ → ℝ)
    (A B : ∀ n, Fin (m n) → Fin (m n) → ℝ)
    (u v : ∀ n, Fin (m n) → ℝ) (U C : ℝ)
    (hC : 0 ≤ C)
    (hu : ∀ᶠ n in atTop, ∀ i, |u n i| ≤ U)
    (huv : ∀ eps > 0, ∀ᶠ n in atTop, ∀ i, |u n i - v n i| ≤ eps)
    (hAB : Tendsto (fun n => realScaleMeshEnergy (S n)
      (fun i j => A n i j - B n i j)) atTop (𝓝 0))
    (hB : ∀ᶠ n in atTop, realScaleMeshEnergy (S n) (B n) ≤ C) :
    Tendsto (fun n => realScaleMeshEnergy (S n)
      (fun i j => u n i * A n i j - v n i * B n i j)) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro eps heps
  let eta : ℝ := Real.sqrt (eps / (8 * (C + 1)))
  have hC1 : 0 < C + 1 := by linarith
  have heta : 0 < eta := by
    dsimp only [eta]
    positivity
  have hsmall : 2 * eta ^ 2 * C < eps / 2 := by
    have hsqrt : eta ^ 2 = eps / (8 * (C + 1)) := by
      dsimp only [eta]
      rw [Real.sq_sqrt]
      positivity
    rw [hsqrt]
    have hfrac : C / (C + 1) < 1 := by
      exact (div_lt_one hC1).2 (by linarith)
    calc
      2 * (eps / (8 * (C + 1))) * C = eps / 4 * (C / (C + 1)) := by field_simp; ring
      _ < eps / 4 * 1 := by gcongr
      _ < eps / 2 := by linarith
  have hcoef : 0 < eps / (4 * (U ^ 2 + 1)) := by positivity
  have hABevent := (Metric.tendsto_nhds.mp hAB) _ hcoef
  filter_upwards [hu, huv eta heta, hABevent, hB] with n hun huvn hABn hBn
  rw [Real.dist_eq]
  have henergy := realScaleMeshEnergy_left_weight_sub_le
    (S n) (A n) (B n) (u n) (v n) U eta hun huvn
  have hfirst : 2 * U ^ 2 * realScaleMeshEnergy (S n)
      (fun i j => A n i j - B n i j) ≤ eps / 2 := by
    rw [Real.dist_eq, sub_zero] at hABn
    have hnonneg : 0 ≤ realScaleMeshEnergy (S n)
        (fun i j => A n i j - B n i j) := by
      exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ =>
        Finset.sum_nonneg fun j _ => sq_nonneg _)
    rw [abs_of_nonneg hnonneg] at hABn
    calc
      2 * U ^ 2 * realScaleMeshEnergy (S n)
          (fun i j => A n i j - B n i j) ≤
        2 * U ^ 2 * (eps / (4 * (U ^ 2 + 1))) := by
          exact mul_le_mul_of_nonneg_left hABn.le (by positivity)
      _ ≤ eps / 2 := by
        have hden : 0 < U ^ 2 + 1 := by positivity
        have hratio : U ^ 2 / (U ^ 2 + 1) ≤ 1 := by
          exact (div_le_one hden).2 (by linarith [sq_nonneg U])
        calc
          2 * U ^ 2 * (eps / (4 * (U ^ 2 + 1))) =
              eps / 2 * (U ^ 2 / (U ^ 2 + 1)) := by field_simp; ring
          _ ≤ eps / 2 := by
            have hehalf : 0 ≤ eps / 2 := by linarith
            simpa only [mul_one] using
              mul_le_mul_of_nonneg_left hratio hehalf
  have hsecond : 2 * eta ^ 2 * realScaleMeshEnergy (S n) (B n) < eps / 2 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hBn
      (mul_nonneg (by positivity) (sq_nonneg eta))) hsmall
  have hnonneg : 0 ≤ realScaleMeshEnergy (S n)
      (fun i j => u n i * A n i j - v n i * B n i j) := by
    exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => sq_nonneg _)
  simp only [sub_zero, abs_of_nonneg hnonneg]
  linarith

end Hurst
