import Hurst.FirstLongDiagonalBand

noncomputable section
open Set Filter
open scoped Topology
namespace Hurst

/-- Squared Hilbert--Schmidt norm of a step kernel whose value on every mesh
cell `(i,j)` is `A i j`.  Each cell has area `N⁻²`. -/
def meshHilbertSchmidtEnergy {m : ℕ} (N : ℕ)
    (A : Fin m → Fin m → ℝ) : ℝ :=
  (N : ℝ)⁻¹ ^ 2 * ∑ i : Fin m, ∑ j : Fin m, A i j ^ 2

/-- The part of the squared step-kernel norm within `R` cells of the
diagonal. -/
def meshHilbertSchmidtBandEnergy {m : ℕ} (N R : ℕ)
    (A : Fin m → Fin m → ℝ) : ℝ :=
  (N : ℝ)⁻¹ ^ 2 * ∑ i : Fin m,
    ∑ j ∈ Finset.univ.filter
      (fun j : Fin m => Nat.dist j.val i.val ≤ R), A i j ^ 2

/-- The abstract mesh band energy agrees exactly with the correlation-scale
quantity used in `meshDiagonalBandEnergy`. -/
theorem meshHilbertSchmidtBandEnergy_scaled_eq {m N R : ℕ}
    (ψ : ℝ) (hn : 0 < N) (r : Fin m → Fin m → ℝ) :
    meshHilbertSchmidtBandEnergy N R
        (fun i j => (N : ℝ) ^ ψ * r i j) =
      meshDiagonalBandEnergy N R ψ r := by
  have hnR : (0 : ℝ) < N := by exact_mod_cast hn
  have hscalar : (N : ℝ)⁻¹ ^ 2 * ((N : ℝ) ^ ψ) ^ 2 =
      (N : ℝ) ^ (2 * ψ - 2) := by
    rw [show (N : ℝ)⁻¹ = (N : ℝ) ^ (-1 : ℝ) by
      rw [Real.rpow_neg_one],
      ← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_mul hnR.le, ← Real.rpow_mul hnR.le,
      ← Real.rpow_add hnR]
    congr 1
    norm_num
    ring
  unfold meshHilbertSchmidtBandEnergy meshDiagonalBandEnergy
  simp_rw [mul_pow]
  calc
    (N : ℝ)⁻¹ ^ 2 * ∑ i : Fin m, ∑ j ∈ Finset.univ.filter
        (fun j : Fin m => Nat.dist j.val i.val ≤ R),
          ((N : ℝ) ^ ψ) ^ 2 * r i j ^ 2 =
      (N : ℝ)⁻¹ ^ 2 * (((N : ℝ) ^ ψ) ^ 2 *
        ∑ i : Fin m, ∑ j ∈ Finset.univ.filter
          (fun j : Fin m => Nat.dist j.val i.val ≤ R), r i j ^ 2) := by
        congr 1
        simp only [Finset.mul_sum]
    _ = _ := by rw [← mul_assoc, hscalar]

/-- Direct near-diagonal consequence for a scaled correlation step kernel. -/
theorem meshHilbertSchmidtBandEnergy_scaled_tendsto_zero
    (m N R : ℕ → ℕ) (ψ : ℝ)
    (r : ∀ n, Fin (m n) → Fin (m n) → ℝ)
    (hN : ∀ᶠ n in atTop, 0 < N n)
    (hmN : ∀ᶠ n in atTop, m n ≤ N n)
    (hr : ∀ᶠ n in atTop, ∀ i j, |r n i j| ≤ 1)
    (hcut : Tendsto (fun n =>
      (N n : ℝ) ^ (2 * ψ - 1) * (2 * (R n : ℝ) + 1))
      atTop (𝓝 0)) :
    Tendsto (fun n => meshHilbertSchmidtBandEnergy (N n) (R n)
      (fun i j => (N n : ℝ) ^ ψ * r n i j)) atTop (𝓝 0) := by
  have ht := meshDiagonalBandEnergy_tendsto_zero m N R ψ r hN hmN hr hcut
  apply ht.congr'
  filter_upwards [hN] with n hn
  exact (meshHilbertSchmidtBandEnergy_scaled_eq ψ hn (r n)).symm

theorem meshHilbertSchmidtEnergy_eq_band_add_off {m N R : ℕ}
    (A : Fin m → Fin m → ℝ) :
    meshHilbertSchmidtEnergy N A =
      meshHilbertSchmidtBandEnergy N R A +
      (N : ℝ)⁻¹ ^ 2 * ∑ i : Fin m,
        ∑ j ∈ Finset.univ.filter
          (fun j : Fin m => ¬ Nat.dist j.val i.val ≤ R), A i j ^ 2 := by
  unfold meshHilbertSchmidtEnergy meshHilbertSchmidtBandEnergy
  have hsplit : (∑ i : Fin m, ∑ j : Fin m, A i j ^ 2) =
      (∑ i : Fin m, ∑ j ∈ Finset.univ.filter
        (fun j : Fin m => Nat.dist j.val i.val ≤ R), A i j ^ 2) +
      (∑ i : Fin m, ∑ j ∈ Finset.univ.filter
        (fun j : Fin m => ¬ Nat.dist j.val i.val ≤ R), A i j ^ 2) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    exact (Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun j : Fin m => Nat.dist j.val i.val ≤ R) (fun j => A i j ^ 2)).symm
  rw [hsplit]
  ring

/-- Near the diagonal, the squared error is bounded by twice the energy of
each kernel separately. -/
theorem meshHilbertSchmidtBandEnergy_sub_le {m N R : ℕ}
    (A B : Fin m → Fin m → ℝ) :
    meshHilbertSchmidtBandEnergy N R (fun i j => A i j - B i j) ≤
      2 * meshHilbertSchmidtBandEnergy N R A +
        2 * meshHilbertSchmidtBandEnergy N R B := by
  unfold meshHilbertSchmidtBandEnergy
  have hs : (∑ i : Fin m,
      ∑ j ∈ Finset.univ.filter
        (fun j : Fin m => Nat.dist j.val i.val ≤ R),
          (A i j - B i j) ^ 2) ≤
      2 * (∑ i : Fin m,
        ∑ j ∈ Finset.univ.filter
          (fun j : Fin m => Nat.dist j.val i.val ≤ R), A i j ^ 2) +
      2 * (∑ i : Fin m,
        ∑ j ∈ Finset.univ.filter
          (fun j : Fin m => Nat.dist j.val i.val ≤ R), B i j ^ 2) := by
    calc
      _ ≤ ∑ i : Fin m, ∑ j ∈ Finset.univ.filter
          (fun j : Fin m => Nat.dist j.val i.val ≤ R),
            (2 * A i j ^ 2 + 2 * B i j ^ 2) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        nlinarith [sq_nonneg (A i j + B i j)]
      _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hscale : 0 ≤ (N : ℝ)⁻¹ ^ 2 := sq_nonneg _
  have := mul_le_mul_of_nonneg_left hs hscale
  nlinarith

/-- Away from the diagonal, a uniform entrywise error controls the whole
mesh Hilbert--Schmidt error. -/
theorem meshHilbertSchmidt_off_le_of_uniform {m N R : ℕ}
    (hn : 0 < N) (hmN : m ≤ N) (A B : Fin m → Fin m → ℝ) (e : ℝ)
    (he : 0 ≤ e)
    (hoff : ∀ i j, R < Nat.dist j.val i.val → |A i j - B i j| ≤ e) :
    (N : ℝ)⁻¹ ^ 2 * ∑ i : Fin m,
        ∑ j ∈ Finset.univ.filter
          (fun j : Fin m => ¬ Nat.dist j.val i.val ≤ R),
            (A i j - B i j) ^ 2 ≤ e ^ 2 := by
  have hsum : (∑ i : Fin m,
      ∑ j ∈ Finset.univ.filter
        (fun j : Fin m => ¬ Nat.dist j.val i.val ≤ R),
          (A i j - B i j) ^ 2) ≤ (m : ℝ) ^ 2 * e ^ 2 := by
    calc
      _ ≤ ∑ i : Fin m, ∑ _j ∈ Finset.univ.filter
          (fun j : Fin m => ¬ Nat.dist j.val i.val ≤ R), e ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        have habs := hoff i j (lt_of_not_ge (Finset.mem_filter.mp hj).2)
        have hp := pow_le_pow_left₀ (abs_nonneg (A i j - B i j)) habs 2
        simpa only [sq_abs] using hp
      _ ≤ ∑ _i : Fin m, ∑ _j : Fin m, e ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => sq_nonneg e)
      _ = (m : ℝ) ^ 2 * e ^ 2 := by simp; ring
  have hnR : (0 : ℝ) < N := by exact_mod_cast hn
  have hmR : (m : ℝ) ≤ N := by exact_mod_cast hmN
  have hratio : (N : ℝ)⁻¹ ^ 2 * (m : ℝ) ^ 2 ≤ 1 := by
    rw [inv_pow]
    have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := sq_pos_of_pos hnR
    rw [inv_mul_eq_div]
    exact (div_le_one hN2).mpr (pow_le_pow_left₀ (by positivity) hmR 2)
  calc
    _ ≤ (N : ℝ)⁻¹ ^ 2 * ((m : ℝ) ^ 2 * e ^ 2) :=
      mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ = ((N : ℝ)⁻¹ ^ 2 * (m : ℝ) ^ 2) * e ^ 2 := by ring
    _ ≤ 1 * e ^ 2 := mul_le_mul_of_nonneg_right hratio (sq_nonneg _)
    _ = _ := one_mul _

/-- Deterministic near/off-diagonal gluing theorem for step kernels.  It is
the finite-mesh version of Hilbert--Schmidt convergence: vanishing energy of
both kernels in a shrinking diagonal band plus uniform convergence outside
that band implies convergence in mesh `L²`. -/
theorem meshHilbertSchmidtEnergy_sub_tendsto_zero
    (m N R : ℕ → ℕ)
    (A B : ∀ n, Fin (m n) → Fin (m n) → ℝ)
    (e : ℕ → ℝ)
    (hN : ∀ᶠ n in atTop, 0 < N n)
    (hmN : ∀ᶠ n in atTop, m n ≤ N n)
    (he : ∀ᶠ n in atTop, 0 ≤ e n)
    (hoff : ∀ᶠ n in atTop, ∀ i j,
      R n < Nat.dist j.val i.val → |A n i j - B n i j| ≤ e n)
    (hAnear : Tendsto (fun n =>
      meshHilbertSchmidtBandEnergy (N n) (R n) (A n)) atTop (𝓝 0))
    (hBnear : Tendsto (fun n =>
      meshHilbertSchmidtBandEnergy (N n) (R n) (B n)) atTop (𝓝 0))
    (herr : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n =>
      meshHilbertSchmidtEnergy (N n) (fun i j => A n i j - B n i j))
      atTop (𝓝 0) := by
  have hnear : Tendsto (fun n =>
      2 * meshHilbertSchmidtBandEnergy (N n) (R n) (A n) +
        2 * meshHilbertSchmidtBandEnergy (N n) (R n) (B n))
      atTop (𝓝 0) := by
    convert (hAnear.const_mul 2).add (hBnear.const_mul 2) using 1 <;> ring
  have herrsq : Tendsto (fun n => (e n) ^ 2) atTop (𝓝 0) := by
    convert herr.pow 2 using 1 <;> norm_num
  have hupper := hnear.add herrsq
  apply squeeze_zero'
  · exact Eventually.of_forall fun n => mul_nonneg (sq_nonneg _)
      (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
  · filter_upwards [hN, hmN, he, hoff] with n hn hm hen hoffn
    have hband := meshHilbertSchmidtBandEnergy_sub_le
      (N := N n) (R := R n) (A n) (B n)
    have hoffbound := meshHilbertSchmidt_off_le_of_uniform hn hm
      (R := R n) (A n) (B n) (e n) hen hoffn
    calc
      meshHilbertSchmidtEnergy (N n) (fun i j => A n i j - B n i j) =
          meshHilbertSchmidtBandEnergy (N n) (R n)
              (fun i j => A n i j - B n i j) +
            (N n : ℝ)⁻¹ ^ 2 * ∑ i : Fin (m n),
              ∑ j ∈ Finset.univ.filter
                (fun j : Fin (m n) => ¬ Nat.dist j.val i.val ≤ R n),
                  (A n i j - B n i j) ^ 2 :=
        meshHilbertSchmidtEnergy_eq_band_add_off (R := R n) _
      _ ≤ (2 * meshHilbertSchmidtBandEnergy (N n) (R n) (A n) +
          2 * meshHilbertSchmidtBandEnergy (N n) (R n) (B n)) +
          (e n) ^ 2 := add_le_add hband hoffbound
  · simpa only [zero_add] using hupper

/-- Away from the diagonal, a relative entrywise error is controlled by the
full Hilbert--Schmidt energy of the reference kernel.  This is useful for
singular power kernels, where the entries are not uniformly bounded as the
diagonal cutoff shrinks. -/
theorem meshHilbertSchmidt_off_le_of_relative {m N R : ℕ}
    (A B : Fin m → Fin m → ℝ) (e : ℝ) (he : 0 ≤ e)
    (hoff : ∀ i j, R < Nat.dist j.val i.val →
      |A i j - B i j| ≤ e * |B i j|) :
    (N : ℝ)⁻¹ ^ 2 * ∑ i : Fin m,
        ∑ j ∈ Finset.univ.filter
          (fun j : Fin m => ¬ Nat.dist j.val i.val ≤ R),
            (A i j - B i j) ^ 2 ≤
      e ^ 2 * meshHilbertSchmidtEnergy N B := by
  unfold meshHilbertSchmidtEnergy
  have hterm (i j : Fin m) (hij : R < Nat.dist j.val i.val) :
      (A i j - B i j) ^ 2 ≤ e ^ 2 * B i j ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg _) (hoff i j hij) 2
    simpa only [sq_abs, mul_pow] using h
  calc
    (N : ℝ)⁻¹ ^ 2 * ∑ i : Fin m,
        ∑ j ∈ Finset.univ.filter
          (fun j : Fin m => ¬ Nat.dist j.val i.val ≤ R),
            (A i j - B i j) ^ 2 ≤
      (N : ℝ)⁻¹ ^ 2 * ∑ i : Fin m,
        ∑ j ∈ Finset.univ.filter
          (fun j : Fin m => ¬ Nat.dist j.val i.val ≤ R),
            e ^ 2 * B i j ^ 2 := by
      gcongr with i hi j hj
      exact hterm i j (lt_of_not_ge (Finset.mem_filter.mp hj).2)
    _ ≤ (N : ℝ)⁻¹ ^ 2 * ∑ i : Fin m, ∑ j : Fin m,
          e ^ 2 * B i j ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun (j : Fin m) _ _ => mul_nonneg (sq_nonneg e) (sq_nonneg (B i j)))
    _ = e ^ 2 * ((N : ℝ)⁻¹ ^ 2 *
          ∑ i : Fin m, ∑ j : Fin m, B i j ^ 2) := by
      simp only [Finset.mul_sum]
      ring

/-- Near/off-diagonal gluing with a relative error away from the diagonal.
Only a uniform bound on the reference Hilbert--Schmidt energy is needed. -/
theorem meshHilbertSchmidtEnergy_sub_tendsto_zero_of_relative
    (m N R : ℕ → ℕ)
    (A B : ∀ n, Fin (m n) → Fin (m n) → ℝ)
    (e : ℕ → ℝ) (C : ℝ)
    (he : ∀ᶠ n in atTop, 0 ≤ e n) (hC : 0 ≤ C)
    (hoff : ∀ᶠ n in atTop, ∀ i j,
      R n < Nat.dist j.val i.val →
        |A n i j - B n i j| ≤ e n * |B n i j|)
    (hAnear : Tendsto (fun n =>
      meshHilbertSchmidtBandEnergy (N n) (R n) (A n)) atTop (𝓝 0))
    (hBnear : Tendsto (fun n =>
      meshHilbertSchmidtBandEnergy (N n) (R n) (B n)) atTop (𝓝 0))
    (hBbound : ∀ᶠ n in atTop,
      meshHilbertSchmidtEnergy (N n) (B n) ≤ C)
    (herr : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n =>
      meshHilbertSchmidtEnergy (N n) (fun i j => A n i j - B n i j))
      atTop (𝓝 0) := by
  have hnear : Tendsto (fun n =>
      2 * meshHilbertSchmidtBandEnergy (N n) (R n) (A n) +
        2 * meshHilbertSchmidtBandEnergy (N n) (R n) (B n))
      atTop (𝓝 0) := by
    convert (hAnear.const_mul 2).add (hBnear.const_mul 2) using 1 <;> ring
  have herrC : Tendsto (fun n => (e n) ^ 2 * C) atTop (𝓝 0) := by
    convert (herr.pow 2).mul_const C using 1 <;> ring
  have hupper := hnear.add herrC
  apply squeeze_zero'
  · exact Eventually.of_forall fun n => mul_nonneg (sq_nonneg _)
      (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
  · filter_upwards [he, hoff, hBbound] with n hen hoffn hBn
    have hband := meshHilbertSchmidtBandEnergy_sub_le
      (N := N n) (R := R n) (A n) (B n)
    have hoffbound := meshHilbertSchmidt_off_le_of_relative
      (N := N n) (R := R n) (A n) (B n) (e n) hen hoffn
    have hoffC : (e n) ^ 2 * meshHilbertSchmidtEnergy (N n) (B n) ≤
        (e n) ^ 2 * C := mul_le_mul_of_nonneg_left hBn (sq_nonneg _)
    calc
      meshHilbertSchmidtEnergy (N n) (fun i j => A n i j - B n i j) =
          meshHilbertSchmidtBandEnergy (N n) (R n)
              (fun i j => A n i j - B n i j) +
            (N n : ℝ)⁻¹ ^ 2 * ∑ i : Fin (m n),
              ∑ j ∈ Finset.univ.filter
                (fun j : Fin (m n) => ¬ Nat.dist j.val i.val ≤ R n),
                  (A n i j - B n i j) ^ 2 :=
        meshHilbertSchmidtEnergy_eq_band_add_off (R := R n) _
      _ ≤ (2 * meshHilbertSchmidtBandEnergy (N n) (R n) (A n) +
          2 * meshHilbertSchmidtBandEnergy (N n) (R n) (B n)) +
          (e n) ^ 2 * C := add_le_add hband (hoffbound.trans hoffC)
  · simpa only [zero_add] using hupper

end Hurst
