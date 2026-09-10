import Hurst.HolderRegularity

noncomputable section
open Set
namespace Hurst

theorem hurstHolder_quadratic_remainder (p : ℝ) (hp : 2 ≤ p) :
    ∃ C > 0, ∀ M : ℝ, 0 ≤ M → ∀ f ∈ hurstHolderClass p M,
      ∀ x ∈ Ioo (0 : ℝ) 1, ∀ y ∈ Ioo (0 : ℝ) 1,
        |f y - f x - (y - x) * deriv f x| ≤ C * (1 + M) * |y - x| ^ 2 := by
  obtain ⟨C, hC, hc⟩ := hurstHolder_uniform_derivative_bounds p (by linarith)
  have hp2 : 2 ≤ Nat.floor p := (Nat.le_floor_iff (by linarith : 0 ≤ p)).mpr hp
  refine ⟨C / 2, by positivity, ?_⟩
  intro M hM f hf x hx y hy
  by_cases heq : x = y
  · subst y
    simp
  obtain ⟨z, hz, he⟩ := interval_taylor_lagrange f 1
    (fun k hk u hu => hf.2.1 k (by omega) u hu) x y hx hy heq
  simp only [Fin.sum_univ_succ] at he
  norm_num [iteratedDeriv_zero, iteratedDeriv_one] at he
  have hzU : z ∈ Ioo (0 : ℝ) 1 :=
    ⟨(lt_min hx.1 hy.1).trans hz.1, hz.2.trans (max_lt hx.2 hy.2)⟩
  have hcoeff := hc M hM f hf z hzU 2 hp2
  have hR : f y - f x - (y - x) * deriv f x = iteratedDeriv 2 f z * (y - x) ^ 2 / 2 := by linarith
  rw [hR, abs_div, abs_mul, abs_of_nonneg (sq_nonneg (y - x)), abs_of_pos (by norm_num : (0 : ℝ) < 2), sq_abs]
  have hm := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg (y - x))
  nlinarith

theorem hurstHolder_second_difference_bound (p : ℝ) (hp : 2 ≤ p) :
    ∃ C > 0, ∀ M : ℝ, 0 ≤ M → ∀ f ∈ hurstHolderClass p M,
      ∀ t l : ℝ, 0 ≤ l → t ∈ Ioo (0 : ℝ) 1 → t + 2 * l ∈ Ioo (0 : ℝ) 1 →
        |f (t + 2 * l) - 2 * f (t + l) + f t| ≤ C * (1 + M) * l ^ 2 := by
  obtain ⟨C, hC, hc⟩ := hurstHolder_quadratic_remainder p hp
  refine ⟨6 * C, by positivity, ?_⟩
  intro M hM f hf t l hl ht ht2
  have ht1 : t + l ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht2.2]⟩
  have h1 := hc M hM f hf t ht (t + l) ht1
  have h2 := hc M hM f hf t ht (t + 2 * l) ht2
  rw [add_sub_cancel_left, abs_of_nonneg hl] at h1
  rw [add_sub_cancel_left, abs_of_nonneg (by positivity : 0 ≤ 2 * l)] at h2
  have he : f (t + 2 * l) - 2 * f (t + l) + f t =
      (f (t + 2 * l) - f t - (2 * l) * deriv f t) -
      2 * (f (t + l) - f t - l * deriv f t) := by ring
  rw [he]
  apply (abs_sub _ _).trans
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  nlinarith [mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 2)]

end Hurst
