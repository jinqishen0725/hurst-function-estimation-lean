import Hurst.FrozenEstimates

noncomputable section
open Set
namespace Hurst

def powerForwardDifference : ℕ → ℝ → ℝ → ℝ → ℝ
  | 0, p, _, x => x ^ p
  | r + 1, p, l, x => powerForwardDifference r p l (x + l) - powerForwardDifference r p l x

def powerDifferenceCoeff (r : ℕ) (p : ℝ) : ℝ := ∏ j ∈ Finset.range r, |p - j|

theorem powerDifferenceCoeff_nonneg (r : ℕ) (p : ℝ) : 0 ≤ powerDifferenceCoeff r p := by
  unfold powerDifferenceCoeff
  exact Finset.prod_nonneg (fun _ _ => abs_nonneg _)

theorem powerDifferenceCoeff_succ (r : ℕ) (p : ℝ) :
    powerDifferenceCoeff (r + 1) p = |p| * powerDifferenceCoeff r (p - 1) := by
  unfold powerDifferenceCoeff
  rw [Finset.prod_range_succ']
  simp only [Nat.cast_zero, sub_zero, Nat.cast_add, Nat.cast_one]
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  congr 1
  ring

theorem powerForwardDifference_hasDerivAt (r : ℕ) (p l x : ℝ) (hl : 0 ≤ l) (hx : 0 < x) :
    HasDerivAt (powerForwardDifference r p l) (p * powerForwardDifference r (p - 1) l x) x := by
  induction r generalizing x with
  | zero =>
    exact Real.hasDerivAt_rpow_const (Or.inl hx.ne')
  | succ r ih =>
    have h1 := (ih (x + l) (by linarith)).comp x ((hasDerivAt_id x).add_const l)
    have h2 := ih x hx
    convert! h1.sub h2 using 1
    simp only [powerForwardDifference, id_eq, mul_one]
    ring

theorem powerForwardDifference_bound (r : ℕ) (p l x : ℝ) (hp : p ≤ r)
    (hl : 0 ≤ l) (hx : 0 < x) :
    |powerForwardDifference r p l x| ≤ powerDifferenceCoeff r p * x ^ (p - r) * l ^ r := by
  induction r generalizing p x with
  | zero => simp [powerForwardDifference, powerDifferenceCoeff, abs_of_nonneg (Real.rpow_nonneg hx.le p)]
  | succ r ih =>
    have hpR : p ≤ (r : ℝ) + 1 := by exact_mod_cast hp
    have hd : ∀ u ∈ Icc x (x + l), HasDerivAt (powerForwardDifference r p l)
        (p * powerForwardDifference r (p - 1) l u) u := by
      intro u hu
      exact powerForwardDifference_hasDerivAt r p l u hl (hx.trans_le hu.1)
    have hb : ∀ u ∈ Icc x (x + l),
        ‖p * powerForwardDifference r (p - 1) l u‖ ≤
          powerDifferenceCoeff (r + 1) p * x ^ (p - (r + 1)) * l ^ r := by
      intro u hu
      have hi := ih (p - 1) u (by linarith) (hx.trans_le hu.1)
      have hp' : p - 1 - r ≤ 0 := by linarith
      have hr := Real.rpow_le_rpow_of_nonpos hx hu.1 hp'
      have hi' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr (powerDifferenceCoeff_nonneg r (p - 1))) (pow_nonneg hl r)
      have hh := mul_le_mul_of_nonneg_left (hi.trans hi') (abs_nonneg p)
      rw [Real.norm_eq_abs, abs_mul]
      apply hh.trans_eq
      rw [powerDifferenceCoeff_succ]
      rw [show p - 1 - (r : ℝ) = p - ((r : ℝ) + 1) by ring]
      ring
    have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun u hu => (hd u hu).hasDerivWithinAt) hb (convex_Icc x (x + l))
      (left_mem_Icc.mpr (by linarith)) (right_mem_Icc.mpr (by linarith))
    simp only [Real.norm_eq_abs, add_sub_cancel_left, abs_of_nonneg hl] at hm
    exact hm.trans_eq (by simp only [Nat.cast_add, Nat.cast_one, pow_succ]; ring)

theorem powerForwardDifference_four (p l x : ℝ) :
    powerForwardDifference 4 p l x =
      (x + 4 * l) ^ p - 4 * (x + 3 * l) ^ p + 6 * (x + 2 * l) ^ p - 4 * (x + l) ^ p + x ^ p := by
  simp only [powerForwardDifference]
  ring_nf

theorem powerDifferenceCoeff_four_bound (p : ℝ) (hp : 0 ≤ p) (hp2 : p ≤ 2) :
    powerDifferenceCoeff 4 p ≤ 256 := by
  have hh : ∀ j ∈ Finset.range 4, |p - j| ≤ (4 : ℝ) := by
    intro j hj
    have hj' : (j : ℝ) ≤ 3 := by exact_mod_cast (show j ≤ 3 from by have he := Finset.mem_range.mp hj; omega)
    have hj0 : (0 : ℝ) ≤ j := by positivity
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have he := Finset.prod_le_prod (s := Finset.range 4) (fun (j : ℕ) hj => abs_nonneg (p - (j : ℝ))) hh
  norm_num [powerDifferenceCoeff] at he ⊢
  exact he

theorem powerForwardDifference_four_bound (p l x : ℝ) (hp : 0 ≤ p) (hp2 : p ≤ 2)
    (hl : 0 ≤ l) (hx : 0 < x) :
    |powerForwardDifference 4 p l x| ≤ 256 * x ^ (p - 4) * l ^ 4 := by
  have he := powerForwardDifference_bound 4 p l x (by norm_num; linarith) hl hx
  have hc := powerDifferenceCoeff_four_bound p hp hp2
  exact he.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hx.le _)) (pow_nonneg hl 4))

end Hurst
