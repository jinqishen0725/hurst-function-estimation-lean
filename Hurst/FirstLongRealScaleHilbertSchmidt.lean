import Hurst.FirstLongDiagonalBand

noncomputable section
open Set Filter
open scoped Topology
namespace Hurst

private theorem real_scale_diagonal_band_card {m : ℕ} (R : ℕ) (i : Fin m) :
    (Finset.univ.filter
      (fun j : Fin m => Nat.dist j.val i.val ≤ R)).card ≤ 2 * R + 1 := by
  let T : Finset (Fin m) := Finset.univ.filter
    (fun j => Nat.dist j.val i.val ≤ R)
  have hc := finite_lattice_interval_card T
    ((i.val : ℝ) - R) ((i.val : ℝ) + R) (by linarith) (by
      intro j hj
      have hd : Nat.dist j.val i.val ≤ R := (Finset.mem_filter.mp hj).2
      have hleft : j.val ≤ i.val + R := by
        rcases le_total i.val j.val with hij | hji
        · rw [Nat.dist_eq_sub_of_le_right hij] at hd
          omega
        · omega
      have hright : i.val ≤ j.val + R := by
        rcases le_total j.val i.val with hji | hij
        · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le_right hji] at hd
          omega
        · omega
      have hleftR : (j.val : ℝ) ≤ i.val + R := by exact_mod_cast hleft
      have hrightR : (i.val : ℝ) ≤ j.val + R := by exact_mod_cast hright
      constructor <;> linarith)
  have hcR : (T.card : ℝ) ≤ (2 * R + 1 : ℕ) := by
    convert hc using 1 <;> push_cast <;> ring
  exact_mod_cast hcR

/-- Squared step-kernel energy with an arbitrary positive real mesh scale.
This is the correct interface for the effective local sample size `n * δ`. -/
def realScaleMeshEnergy {m : ℕ} (S : ℝ)
    (A : Fin m → Fin m → ℝ) : ℝ :=
  S⁻¹ ^ 2 * ∑ i : Fin m, ∑ j : Fin m, A i j ^ 2

def realScaleMeshBandEnergy {m : ℕ} (S : ℝ) (R : ℕ)
    (A : Fin m → Fin m → ℝ) : ℝ :=
  S⁻¹ ^ 2 * ∑ i : Fin m,
    ∑ j ∈ Finset.univ.filter
      (fun j : Fin m => Nat.dist j.val i.val ≤ R), A i j ^ 2

/-- A unit-bounded correlation matrix has a direct near-diagonal bound at a
real effective scale.  No artificial `m ≤ S` or integrality assumption is
needed. -/
theorem realScaleMeshBandEnergy_scaled_le {m R : ℕ}
    (S ψ : ℝ) (hS : 0 < S) (r : Fin m → Fin m → ℝ)
    (hr : ∀ i j, |r i j| ≤ 1) :
    realScaleMeshBandEnergy S R (fun i j => S ^ ψ * r i j) ≤
      S ^ (2 * ψ - 2) * (m : ℝ) * (2 * (R : ℝ) + 1) := by
  have hinner : ∀ i : Fin m,
      (∑ j ∈ Finset.univ.filter
        (fun j : Fin m => Nat.dist j.val i.val ≤ R), r i j ^ 2) ≤
        2 * (R : ℝ) + 1 := by
    intro i
    calc
      _ ≤ ∑ _j ∈ Finset.univ.filter
          (fun j : Fin m => Nat.dist j.val i.val ≤ R), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        have hp := pow_le_pow_left₀ (abs_nonneg (r i j)) (hr i j) 2
        simpa only [sq_abs, one_pow] using hp
      _ = ((Finset.univ.filter
          (fun j : Fin m => Nat.dist j.val i.val ≤ R)).card : ℝ) := by simp
      _ ≤ (2 * R + 1 : ℕ) := by
        exact_mod_cast real_scale_diagonal_band_card R i
      _ = _ := by push_cast; ring
  have hsum :
      (∑ i : Fin m, ∑ j ∈ Finset.univ.filter
        (fun j : Fin m => Nat.dist j.val i.val ≤ R), r i j ^ 2) ≤
        (m : ℝ) * (2 * (R : ℝ) + 1) := by
    calc
      _ ≤ ∑ _i : Fin m, (2 * (R : ℝ) + 1) :=
        Finset.sum_le_sum fun i _ => hinner i
      _ = _ := by simp; ring
  have hscalar : S⁻¹ ^ 2 * (S ^ ψ) ^ 2 = S ^ (2 * ψ - 2) := by
    rw [show S⁻¹ = S ^ (-1 : ℝ) by rw [Real.rpow_neg_one],
      ← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_mul hS.le, ← Real.rpow_mul hS.le,
      ← Real.rpow_add hS]
    congr 1
    norm_num
    ring
  unfold realScaleMeshBandEnergy
  simp_rw [mul_pow]
  calc
    S⁻¹ ^ 2 * ∑ i : Fin m, ∑ j ∈ Finset.univ.filter
        (fun j : Fin m => Nat.dist j.val i.val ≤ R),
          (S ^ ψ) ^ 2 * r i j ^ 2 =
      (S⁻¹ ^ 2 * (S ^ ψ) ^ 2) *
        (∑ i : Fin m, ∑ j ∈ Finset.univ.filter
          (fun j : Fin m => Nat.dist j.val i.val ≤ R), r i j ^ 2) := by
        simp only [Finset.mul_sum]
        ring
    _ = S ^ (2 * ψ - 2) *
        (∑ i : Fin m, ∑ j ∈ Finset.univ.filter
          (fun j : Fin m => Nat.dist j.val i.val ≤ R), r i j ^ 2) := by
        rw [hscalar]
    _ ≤ S ^ (2 * ψ - 2) *
        ((m : ℝ) * (2 * (R : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hS.le _)
    _ = _ := by ring

theorem realScaleMeshBandEnergy_scaled_tendsto_zero
    (m R : ℕ → ℕ) (S : ℕ → ℝ) (ψ : ℝ)
    (r : ∀ n, Fin (m n) → Fin (m n) → ℝ)
    (hS : ∀ᶠ n in atTop, 0 < S n)
    (hr : ∀ᶠ n in atTop, ∀ i j, |r n i j| ≤ 1)
    (hcut : Tendsto (fun n =>
      S n ^ (2 * ψ - 2) * (m n : ℝ) * (2 * (R n : ℝ) + 1))
      atTop (𝓝 0)) :
    Tendsto (fun n => realScaleMeshBandEnergy (S n) (R n)
      (fun i j => S n ^ ψ * r n i j)) atTop (𝓝 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall fun n => mul_nonneg (sq_nonneg _)
      (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
  · filter_upwards [hS, hr] with n hSn hrn
    exact realScaleMeshBandEnergy_scaled_le (S n) ψ hSn (r n) hrn
  · exact hcut

theorem realScaleMeshEnergy_eq_band_add_off {m R : ℕ}
    (S : ℝ) (A : Fin m → Fin m → ℝ) :
    realScaleMeshEnergy S A =
      realScaleMeshBandEnergy S R A +
      S⁻¹ ^ 2 * ∑ i : Fin m,
        ∑ j ∈ Finset.univ.filter
          (fun j : Fin m => ¬ Nat.dist j.val i.val ≤ R), A i j ^ 2 := by
  unfold realScaleMeshEnergy realScaleMeshBandEnergy
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

theorem realScaleMeshBandEnergy_sub_le {m R : ℕ}
    (S : ℝ) (A B : Fin m → Fin m → ℝ) :
    realScaleMeshBandEnergy S R (fun i j => A i j - B i j) ≤
      2 * realScaleMeshBandEnergy S R A +
        2 * realScaleMeshBandEnergy S R B := by
  unfold realScaleMeshBandEnergy
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
  have hscale : 0 ≤ S⁻¹ ^ 2 := sq_nonneg _
  have := mul_le_mul_of_nonneg_left hs hscale
  nlinarith

/-- Away from the diagonal, an entrywise error `e` contributes at most
`(m/S)^2 e^2`. -/
theorem realScaleMesh_off_le_of_uniform {m R : ℕ}
    (S : ℝ) (hS : 0 < S) (A B : Fin m → Fin m → ℝ) (e : ℝ)
    (he : 0 ≤ e)
    (hoff : ∀ i j, R < Nat.dist j.val i.val → |A i j - B i j| ≤ e) :
    S⁻¹ ^ 2 * ∑ i : Fin m,
        ∑ j ∈ Finset.univ.filter
          (fun j : Fin m => ¬ Nat.dist j.val i.val ≤ R),
            (A i j - B i j) ^ 2 ≤
      ((m : ℝ) / S) ^ 2 * e ^ 2 := by
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
  calc
    _ ≤ S⁻¹ ^ 2 * ((m : ℝ) ^ 2 * e ^ 2) :=
      mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ = ((m : ℝ) / S) ^ 2 * e ^ 2 := by
      field_simp [hS.ne']

/-- Relative off-diagonal errors are measured against the reference kernel
energy, so singular power kernels need no uniform entry bound. -/
theorem realScaleMesh_off_le_of_relative {m R : ℕ}
    (S : ℝ) (A B : Fin m → Fin m → ℝ) (e : ℝ) (he : 0 ≤ e)
    (hoff : ∀ i j, R < Nat.dist j.val i.val →
      |A i j - B i j| ≤ e * |B i j|) :
    S⁻¹ ^ 2 * ∑ i : Fin m,
        ∑ j ∈ Finset.univ.filter
          (fun j : Fin m => ¬ Nat.dist j.val i.val ≤ R),
            (A i j - B i j) ^ 2 ≤
      e ^ 2 * realScaleMeshEnergy S B := by
  unfold realScaleMeshEnergy
  have hterm (i j : Fin m) (hij : R < Nat.dist j.val i.val) :
      (A i j - B i j) ^ 2 ≤ e ^ 2 * B i j ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg _) (hoff i j hij) 2
    simpa only [sq_abs, mul_pow] using h
  calc
    S⁻¹ ^ 2 * ∑ i : Fin m,
        ∑ j ∈ Finset.univ.filter
          (fun j : Fin m => ¬ Nat.dist j.val i.val ≤ R),
            (A i j - B i j) ^ 2 ≤
      S⁻¹ ^ 2 * ∑ i : Fin m,
        ∑ j ∈ Finset.univ.filter
          (fun j : Fin m => ¬ Nat.dist j.val i.val ≤ R),
            e ^ 2 * B i j ^ 2 := by
      gcongr with i hi j hj
      exact hterm i j (lt_of_not_ge (Finset.mem_filter.mp hj).2)
    _ ≤ S⁻¹ ^ 2 * ∑ i : Fin m, ∑ j : Fin m,
          e ^ 2 * B i j ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun (j : Fin m) _ _ => mul_nonneg (sq_nonneg e) (sq_nonneg (B i j)))
    _ = e ^ 2 * (S⁻¹ ^ 2 *
          ∑ i : Fin m, ∑ j : Fin m, B i j ^ 2) := by
      simp only [Finset.mul_sum]
      ring

/-- Near/off-diagonal gluing at the actual effective scale.  The active-window
cardinality only has to be a bounded multiple of the effective sample size. -/
theorem realScaleMeshEnergy_sub_tendsto_zero
    (m R : ℕ → ℕ) (S : ℕ → ℝ)
    (A B : ∀ n, Fin (m n) → Fin (m n) → ℝ)
    (e : ℕ → ℝ) (C : ℝ)
    (hS : ∀ᶠ n in atTop, 0 < S n)
    (hC : 0 ≤ C)
    (hmS : ∀ᶠ n in atTop, (m n : ℝ) / S n ≤ C)
    (he : ∀ᶠ n in atTop, 0 ≤ e n)
    (hoff : ∀ᶠ n in atTop, ∀ i j,
      R n < Nat.dist j.val i.val → |A n i j - B n i j| ≤ e n)
    (hAnear : Tendsto (fun n =>
      realScaleMeshBandEnergy (S n) (R n) (A n)) atTop (𝓝 0))
    (hBnear : Tendsto (fun n =>
      realScaleMeshBandEnergy (S n) (R n) (B n)) atTop (𝓝 0))
    (herr : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n =>
      realScaleMeshEnergy (S n) (fun i j => A n i j - B n i j))
      atTop (𝓝 0) := by
  have hnear : Tendsto (fun n =>
      2 * realScaleMeshBandEnergy (S n) (R n) (A n) +
        2 * realScaleMeshBandEnergy (S n) (R n) (B n))
      atTop (𝓝 0) := by
    convert (hAnear.const_mul 2).add (hBnear.const_mul 2) using 1 <;> ring
  have herrC : Tendsto (fun n => C ^ 2 * (e n) ^ 2) atTop (𝓝 0) := by
    convert (herr.pow 2).const_mul (C ^ 2) using 1 <;> ring
  have hupper := hnear.add herrC
  apply squeeze_zero'
  · exact Eventually.of_forall fun n => mul_nonneg (sq_nonneg _)
      (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
  · filter_upwards [hS, hmS, he, hoff] with n hSn hmn hen hoffn
    have hband := realScaleMeshBandEnergy_sub_le
      (S := S n) (R := R n) (A n) (B n)
    have hoffbound := realScaleMesh_off_le_of_uniform
      (S n) hSn (R := R n) (A n) (B n) (e n) hen hoffn
    have hratio0 : 0 ≤ (m n : ℝ) / S n := div_nonneg (by positivity) hSn.le
    have hratio : ((m n : ℝ) / S n) ^ 2 ≤ C ^ 2 :=
      pow_le_pow_left₀ hratio0 hmn 2
    have hoffC : ((m n : ℝ) / S n) ^ 2 * (e n) ^ 2 ≤
        C ^ 2 * (e n) ^ 2 :=
      mul_le_mul_of_nonneg_right hratio (sq_nonneg _)
    calc
      realScaleMeshEnergy (S n) (fun i j => A n i j - B n i j) =
          realScaleMeshBandEnergy (S n) (R n)
              (fun i j => A n i j - B n i j) +
            (S n)⁻¹ ^ 2 * ∑ i : Fin (m n),
              ∑ j ∈ Finset.univ.filter
                (fun j : Fin (m n) => ¬ Nat.dist j.val i.val ≤ R n),
                  (A n i j - B n i j) ^ 2 :=
        realScaleMeshEnergy_eq_band_add_off (R := R n) _ _
      _ ≤ (2 * realScaleMeshBandEnergy (S n) (R n) (A n) +
          2 * realScaleMeshBandEnergy (S n) (R n) (B n)) +
          C ^ 2 * (e n) ^ 2 :=
        add_le_add hband (hoffbound.trans hoffC)
  · simpa only [zero_add] using hupper

/-- Real-scale gluing using a relative approximation off the diagonal. -/
theorem realScaleMeshEnergy_sub_tendsto_zero_of_relative
    (m R : ℕ → ℕ) (S : ℕ → ℝ)
    (A B : ∀ n, Fin (m n) → Fin (m n) → ℝ)
    (e : ℕ → ℝ) (C : ℝ)
    (he : ∀ᶠ n in atTop, 0 ≤ e n) (hC : 0 ≤ C)
    (hoff : ∀ᶠ n in atTop, ∀ i j,
      R n < Nat.dist j.val i.val →
        |A n i j - B n i j| ≤ e n * |B n i j|)
    (hAnear : Tendsto (fun n =>
      realScaleMeshBandEnergy (S n) (R n) (A n)) atTop (𝓝 0))
    (hBnear : Tendsto (fun n =>
      realScaleMeshBandEnergy (S n) (R n) (B n)) atTop (𝓝 0))
    (hBbound : ∀ᶠ n in atTop, realScaleMeshEnergy (S n) (B n) ≤ C)
    (herr : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n =>
      realScaleMeshEnergy (S n) (fun i j => A n i j - B n i j))
      atTop (𝓝 0) := by
  have hnear : Tendsto (fun n =>
      2 * realScaleMeshBandEnergy (S n) (R n) (A n) +
        2 * realScaleMeshBandEnergy (S n) (R n) (B n))
      atTop (𝓝 0) := by
    convert (hAnear.const_mul 2).add (hBnear.const_mul 2) using 1 <;> ring
  have herrC : Tendsto (fun n => (e n) ^ 2 * C) atTop (𝓝 0) := by
    convert (herr.pow 2).mul_const C using 1 <;> ring
  have hupper := hnear.add herrC
  apply squeeze_zero'
  · exact Eventually.of_forall fun n => mul_nonneg (sq_nonneg _)
      (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
  · filter_upwards [he, hoff, hBbound] with n hen hoffn hBn
    have hband := realScaleMeshBandEnergy_sub_le
      (S := S n) (R := R n) (A n) (B n)
    have hoffbound := realScaleMesh_off_le_of_relative
      (S n) (R := R n) (A n) (B n) (e n) hen hoffn
    have hoffC : (e n) ^ 2 * realScaleMeshEnergy (S n) (B n) ≤
        (e n) ^ 2 * C := mul_le_mul_of_nonneg_left hBn (sq_nonneg _)
    calc
      realScaleMeshEnergy (S n) (fun i j => A n i j - B n i j) =
          realScaleMeshBandEnergy (S n) (R n)
              (fun i j => A n i j - B n i j) +
            (S n)⁻¹ ^ 2 * ∑ i : Fin (m n),
              ∑ j ∈ Finset.univ.filter
                (fun j : Fin (m n) => ¬ Nat.dist j.val i.val ≤ R n),
                  (A n i j - B n i j) ^ 2 :=
        realScaleMeshEnergy_eq_band_add_off (R := R n) _ _
      _ ≤ (2 * realScaleMeshBandEnergy (S n) (R n) (A n) +
          2 * realScaleMeshBandEnergy (S n) (R n) (B n)) +
          (e n) ^ 2 * C :=
        add_le_add hband (hoffbound.trans hoffC)
  · simpa only [zero_add] using hupper

end Hurst
