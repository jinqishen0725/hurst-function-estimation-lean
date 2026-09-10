import Hurst.HolderTaylor
import Mathlib.LinearAlgebra.Vandermonde

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Hurst

theorem matrix_inverse_coefficient_bound {r : ℕ} (W : Matrix (Fin r) (Fin r) ℝ)
    (hW : IsUnit W.det) (v : Fin r → ℝ) (B : ℝ) (hB : ∀ i, |W.mulVec v i| ≤ B) (i : Fin r) :
    |v i| ≤ (∑ j, |W⁻¹ i j|) * B := by
  have he : (W⁻¹ : Matrix (Fin r) (Fin r) ℝ).mulVec (W.mulVec v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul W hW, Matrix.one_mulVec]
  rw [← he]
  change |∑ j, W⁻¹ i j * W.mulVec v j| ≤ _
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ j, |W⁻¹ i j| * B := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hB j) (abs_nonneg _)
    _ = _ := (Finset.sum_mul _ _ _).symm

def derivativeNodeStep (r : ℕ) : ℝ := 1 / (2 * (r + 1))
def derivativeNodeMatrix (r : ℕ) (ε : ℝ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ :=
  Matrix.vandermonde (fun i => ε * (i.val : ℝ) * derivativeNodeStep r)

theorem derivativeNodeMatrix_invertible (r : ℕ) (ε : ℝ) (hε : ε ≠ 0) :
    IsUnit (derivativeNodeMatrix r ε).det := by
  apply isUnit_iff_ne_zero.mpr
  apply Matrix.det_vandermonde_ne_zero_iff.mpr
  intro i j hij
  have ha : derivativeNodeStep r ≠ 0 := by unfold derivativeNodeStep; positivity
  have he : (i.val : ℝ) = j.val := mul_left_cancel₀ hε (mul_right_cancel₀ ha hij)
  exact Fin.ext (by exact_mod_cast he)

theorem derivative_nodes_in_domain (r : ℕ) (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) (i : Fin (r + 1)) :
    x + (if x ≤ 1 / 2 then 1 else -1) * (i.val : ℝ) * derivativeNodeStep r ∈ Ioo (0 : ℝ) 1 := by
  have ha : 0 < derivativeNodeStep r := by unfold derivativeNodeStep; positivity
  have hi : (i.val : ℝ) < r + 1 := by exact_mod_cast i.isLt
  have hstep : (i.val : ℝ) * derivativeNodeStep r < 1 / 2 := by
    unfold derivativeNodeStep
    rw [mul_one_div]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (r + 1))).mpr
    nlinarith
  have hn : 0 ≤ (i.val : ℝ) * derivativeNodeStep r := mul_nonneg (Nat.cast_nonneg _) ha.le
  split_ifs with h
  · constructor <;> nlinarith [hx.1, hx.2]
  · constructor <;> nlinarith [hx.1, hx.2]

theorem taylorJet_coefficient_uniform_bound (r : ℕ) :
    ∃ C > 0, ∀ f : ℝ → ℝ, ∀ M : ℝ, 0 ≤ M →
      (∀ x ∈ Ioo (0 : ℝ) 1, |f x| ≤ 1) →
      (∀ x ∈ Ioo (0 : ℝ) 1, ∀ y ∈ Ioo (0 : ℝ) 1, |f y - taylorJet r f x y| ≤ M) →
      ∀ x ∈ Ioo (0 : ℝ) 1, ∀ k : Fin (r + 1), |iteratedDeriv k.val f x| ≤ C * (1 + M) := by
  classical
  let Wp := derivativeNodeMatrix r 1
  let Wm := derivativeNodeMatrix r (-1)
  let R := 1 + (∑ i, ∑ j, |Wp⁻¹ i j|) + (∑ i, ∑ j, |Wm⁻¹ i j|)
  have hRp : 0 ≤ ∑ i, ∑ j, |Wp⁻¹ i j| := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _))
  have hRm : 0 ≤ ∑ i, ∑ j, |Wm⁻¹ i j| := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _))
  have hR : 0 < R := by dsimp [R]; linarith
  refine ⟨(r.factorial : ℝ) * R, by positivity, ?_⟩
  intro f M hM hf hrem x hx k
  let ε : ℝ := if x ≤ 1 / 2 then 1 else -1
  let W := derivativeNodeMatrix r ε
  have hε : ε ≠ 0 := by dsimp [ε]; split_ifs <;> norm_num
  have hW : IsUnit W.det := derivativeNodeMatrix_invertible r ε hε
  let v : Fin (r + 1) → ℝ := fun i => iteratedDeriv i.val f x / (i.val.factorial : ℝ)
  have hvalues : ∀ i, |W.mulVec v i| ≤ 1 + M := by
    intro i
    let y := x + ε * (i.val : ℝ) * derivativeNodeStep r
    have hy : y ∈ Ioo (0 : ℝ) 1 := derivative_nodes_in_domain r x hx i
    have he : W.mulVec v i = taylorJet r f x y := by
      unfold W derivativeNodeMatrix Matrix.mulVec dotProduct taylorJet
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Matrix.vandermonde_apply, v, y, add_sub_cancel_left]
      ring
    rw [he]
    have htri := abs_add_le (f y) (taylorJet r f x y - f y)
    have hh := hrem x hx y hy
    rw [abs_sub_comm] at hh
    have hval := hf y hy
    have hid : f y + (taylorJet r f x y - f y) = taylorJet r f x y := by ring
    rw [hid] at htri
    linarith
  have hrow : (∑ j, |W⁻¹ k j|) ≤ R := by
    have hp : (∑ j, |Wp⁻¹ k j|) ≤ ∑ i, ∑ j, |Wp⁻¹ i j| :=
      Finset.single_le_sum (f := fun i => ∑ j, |Wp⁻¹ i j|) (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _)) (Finset.mem_univ k)
    have hm : (∑ j, |Wm⁻¹ k j|) ≤ ∑ i, ∑ j, |Wm⁻¹ i j| :=
      Finset.single_le_sum (f := fun i => ∑ j, |Wm⁻¹ i j|) (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _)) (Finset.mem_univ k)
    dsimp [W, ε]
    split_ifs with h
    · change (∑ j, |Wp⁻¹ k j|) ≤ R
      dsimp [R]
      linarith
    · change (∑ j, |Wm⁻¹ k j|) ≤ R
      dsimp [R]
      linarith
  have hv : |v k| ≤ R * (1 + M) := (matrix_inverse_coefficient_bound W hW v (1 + M) hvalues k).trans
    (mul_le_mul_of_nonneg_right hrow (by positivity))
  have hfact : (k.val.factorial : ℝ) ≤ r.factorial := by exact_mod_cast Nat.factorial_le (Nat.le_of_lt_succ k.isLt)
  have hkfact : (0 : ℝ) < k.val.factorial := by positivity
  have hrecover : |iteratedDeriv k.val f x| = (k.val.factorial : ℝ) * |v k| := by
    dsimp [v]
    rw [abs_div, abs_of_pos hkfact]
    field_simp
  rw [hrecover]
  calc
    _ ≤ (r.factorial : ℝ) * (R * (1 + M)) := mul_le_mul hfact hv (abs_nonneg _) (by positivity)
    _ = _ := by ring

end Hurst
