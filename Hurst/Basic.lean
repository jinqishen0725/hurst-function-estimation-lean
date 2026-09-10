import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! Deterministic definitions from Sections 1--2. All results in this file are
kernel-checked; none assert existence of an mBm or an asymptotic limit. -/
noncomputable section
open scoped BigOperators
namespace Hurst

def delta (h : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ := f t - f (t + h)
def difference : ℕ → ℝ → (ℝ → ℝ) → ℝ → ℝ
  | 0, _, f => f
  | q + 1, h, f => delta h (difference q h f)

theorem difference_one (h t : ℝ) (f : ℝ → ℝ) :
    difference 1 h f t = f t - f (t + h) := rfl

theorem difference_two (h t : ℝ) (f : ℝ → ℝ) :
    difference 2 h f t = f t - 2 * f (t + h) + f (t + 2*h) := by
  simp only [difference, delta]
  rw [show t + h + h = t + 2*h by ring]
  ring

theorem difference_const (q : ℕ) (h c t : ℝ) :
    difference (q+1) h (fun _ => c) t = 0 := by
  induction q generalizing t with
  | zero => simp [difference, delta]
  | succ q ih => change difference (q+1) h (fun _ => c) t - difference (q+1) h (fun _ => c) (t+h) = 0
                 rw [ih, ih]; ring

/-- Equation (2.1), in dimension one, retaining the original double sum. -/
def g (q : ℕ) (H u h : ℝ) : ℝ :=
  -(1/2 : ℝ) * ∑ i ∈ Finset.range (q+1), ∑ j ∈ Finset.range (q+1),
    (-1 : ℝ)^(i+j) * (q.choose i : ℝ) * (q.choose j : ℝ) *
      |u + ((i : ℝ) - (j : ℝ))*h| ^ (2*H)

theorem g_one (H u h : ℝ) :
    g 1 H u h = (|u+h|^(2*H) + |u-h|^(2*H) - 2*|u|^(2*H))/2 := by
  norm_num [g, Finset.sum_range_succ, sub_eq_add_neg]
  ring

theorem g_one_zero (H h : ℝ) (hH : H ≠ 0) :
    g 1 H 0 h = |h|^(2*H) := by
  rw [g_one]
  simp [Real.zero_rpow (show (2:ℝ)*H ≠ 0 from mul_ne_zero (by norm_num) hH)]

theorem g_one_unit (H : ℝ) (hH : H ≠ 0) : g 1 H 0 1 = 1 := by
  simp [g_one_zero H 1 hH]

theorem g_zero_direction (q : ℕ) (H : ℝ) (hH : H ≠ 0) :
    g q H 0 0 = 0 := by
  simp [g, Real.zero_rpow (show (2:ℝ)*H ≠ 0 from mul_ne_zero (by norm_num) hH)]

theorem g_two_unit (H : ℝ) (hH : H ≠ 0) :
    g 2 H 0 1 = 4 - (2 : ℝ)^(2*H) := by
  norm_num [g, Finset.sum_range_succ,
    Real.zero_rpow (show (2:ℝ)*H ≠ 0 from mul_ne_zero (by norm_num) hH)]
  ring

theorem g_two_pos (H : ℝ) (hH : 0 < H) (hH1 : H < 1) :
    0 < g 2 H 0 1 := by
  rw [g_two_unit H (ne_of_gt hH)]
  have hp : (2 : ℝ)^(2*H) < (2 : ℝ)^(2 : ℝ) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  norm_num at hp
  linarith

/-- L = log n, c = log σ² + E log χ₁². -/
def G (q : ℕ) (L c H : ℝ) : ℝ := -2*H*L + c + Real.log (g q H 0 1)

theorem G_one (L c H : ℝ) (hH : H ≠ 0) : G 1 L c H = c - 2*L*H := by
  simp [G, g_one_unit H hH]; ring

/-- The midpoint grid has ONE division by n, correcting Section 2's display. -/
def grid (n : ℕ) (i : ℕ) : ℝ := ((i : ℝ) + 1/2) / n

theorem grid_mem (n i : ℕ) (hn : 0 < n) (hi : i < n) :
    grid n i ∈ Set.Ioo (0 : ℝ) 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hiR : (i : ℝ) + 1 ≤ n := by exact_mod_cast hi
  constructor
  · exact div_pos (by positivity) hnR
  · unfold grid; apply (div_lt_one hnR).mpr; linarith

/-- Diagonal normalization of (1.1) after D(H,H)=1/2. -/
theorem diagonal_covariance (v a : ℝ) : v * (1/2) * (a+a-0) = v*a := by ring

end Hurst
