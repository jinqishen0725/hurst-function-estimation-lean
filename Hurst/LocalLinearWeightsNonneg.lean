import Hurst.LocalWeights

/-!
# Sign of the degree-one local polynomial weights

This file analyzes the sign of `localPolynomialWeights 1 n q b t i`, i.e. of the
local *linear* regression weights (design functions `{1, x}`) over the truncated
kernel window `x i = (grid n i.val - t) / b`, `i : Fin (n - q)`.

**The unconditional statement "every weight is nonnegative" is FALSE**, and the
often-quoted proof sketch "w_i ≥ 0 because `|x| ≤ x ^ 2` on `|x| ≤ 1`" is wrong
(in fact `x ^ 2 ≤ |x|` there).  Local linear weights are signed in general: on a
one-sided window the outermost weight is strictly negative.  Concrete
counterexample inside the present setup: `n = 10, q = 0, b = 1/4, t = 1/20`;
the active coordinates are `x ∈ {0, 2/5, 4/5}` and, writing `c = (10 * (1/4))⁻¹`
and `K j = localKernel (2 * j / 5)`,
`μ2 - μ1 * (4/5) = c * (-4/25 * K 1) < 0` while
`μ0 * μ2 - μ1 ^ 2 = c² * (4/125 * (K 0 * K 1 + 4 * K 0 * K 2 + K 1 * K 2)) > 0`,
so the weight at `x = 4/5` is negative.

What *is* true, and proved here:

* the moment entries of the degree-one Gram matrix
  `G = localDesignGram 1 n q b t` (with kernel weights
  `w i = (n*b)⁻¹ * localKernel (x i)`, all nonnegative for `0 < n`, `0 < b`):
  `G 0 0 = ∑ w i`, `G 0 1 = G 1 0 = ∑ w i * x i`, `G 1 1 = ∑ w i * x i ^ 2`;
* the elementary moment inequalities `0 ≤ G 0 0`, `0 ≤ G 1 1`,
  `G 1 1 ≤ G 0 0`, `|G 0 1| ≤ G 0 0`;
* the determinant identity
  `G.det = 1/2 * ∑ i ∑ j w i * w j * (x j - x i) ^ 2`
  (Cauchy–Schwarz made explicit), hence `G.det ≥ 0` always, and `G.det > 0`
  whenever the window contains two distinct grid points with nonzero kernel;
* the exact closed form, valid unconditionally
  (`Ring.inverse 0 = 0`, and a singular Gram yields the zero matrix inverse):
  `localPolynomialWeights 1 n q b t i
     = w i * (G 1 1 - G 0 1 * x i) * Ring.inverse G.det`;
* the sharp sign criterion: `G 0 1 * x i ≤ G 1 1 → 0 ≤ w_i`, in particular at
  window points with `G 0 1 * x i ≤ 0` (e.g. the grid point with `x i = 0`),
  and the global corrected statement: if `G 0 1 * x i ≤ G 1 1` for every `i`
  then every degree-one weight is nonnegative.
-/

noncomputable section
open scoped BigOperators
namespace Hurst

/-! ### Entries of the degree-one Gram matrix as window moments -/

theorem localDesignGram_apply_eq (r n q : ℕ) (b t : ℝ) (j k : Fin (r + 1)) :
    localDesignGram r n q b t j k
      = ∑ i : Fin (n - q), ((n : ℝ) * b)⁻¹ * localKernel ((grid n i.val - t) / b)
          * ((grid n i.val - t) / b) ^ j.val * ((grid n i.val - t) / b) ^ k.val := by
  unfold localDesignGram designGram
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Zeroth window moment: `G 0 0 = ∑ w i`. -/
theorem localDesignGram_one_moment_zero (n q : ℕ) (b t : ℝ) :
    localDesignGram 1 n q b t (0 : Fin 2) (0 : Fin 2)
      = ∑ i : Fin (n - q), ((n : ℝ) * b)⁻¹ * localKernel ((grid n i.val - t) / b) := by
  rw [localDesignGram_apply_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  show ((n : ℝ) * b)⁻¹ * localKernel ((grid n i.val - t) / b) *
    ((grid n i.val - t) / b) ^ 0 * ((grid n i.val - t) / b) ^ 0 = _
  simp

/-- First window moment: `G 0 1 = ∑ w i * x i`. -/
theorem localDesignGram_one_moment_one (n q : ℕ) (b t : ℝ) :
    localDesignGram 1 n q b t (0 : Fin 2) (1 : Fin 2)
      = ∑ i : Fin (n - q), ((n : ℝ) * b)⁻¹ * localKernel ((grid n i.val - t) / b)
          * ((grid n i.val - t) / b) := by
  rw [localDesignGram_apply_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  show ((n : ℝ) * b)⁻¹ * localKernel ((grid n i.val - t) / b) *
    ((grid n i.val - t) / b) ^ 0 * ((grid n i.val - t) / b) ^ 1 = _
  simp only [pow_zero, pow_one]
  ring

/-- First window moment (symmetry): `G 1 0 = ∑ w i * x i`. -/
theorem localDesignGram_one_moment_one' (n q : ℕ) (b t : ℝ) :
    localDesignGram 1 n q b t (1 : Fin 2) (0 : Fin 2)
      = ∑ i : Fin (n - q), ((n : ℝ) * b)⁻¹ * localKernel ((grid n i.val - t) / b)
          * ((grid n i.val - t) / b) := by
  rw [localDesignGram_apply_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  show ((n : ℝ) * b)⁻¹ * localKernel ((grid n i.val - t) / b) *
    ((grid n i.val - t) / b) ^ 1 * ((grid n i.val - t) / b) ^ 0 = _
  simp only [pow_zero, pow_one]
  ring

/-- Second window moment: `G 1 1 = ∑ w i * x i ^ 2`. -/
theorem localDesignGram_one_moment_two (n q : ℕ) (b t : ℝ) :
    localDesignGram 1 n q b t (1 : Fin 2) (1 : Fin 2)
      = ∑ i : Fin (n - q), ((n : ℝ) * b)⁻¹ * localKernel ((grid n i.val - t) / b)
          * ((grid n i.val - t) / b) ^ 2 := by
  rw [localDesignGram_apply_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  show ((n : ℝ) * b)⁻¹ * localKernel ((grid n i.val - t) / b) *
    ((grid n i.val - t) / b) ^ 1 * ((grid n i.val - t) / b) ^ 1 = _
  simp only [pow_one]
  ring

/-! ### Positivity of the kernel weights and moment inequalities -/

/-- A grid point with nonzero kernel weight has coordinate in the open window. -/
theorem localKernel_abs_lt (x : ℝ) (h : localKernel x ≠ 0) : |x| < 1 := by
  by_contra hc
  exact h (localKernel_zero x (not_lt.mp hc))

/-- The normalized kernel weights are nonnegative. -/
theorem localLinearWindowWeight_nonneg (n q : ℕ) (b t : ℝ) (hn : 0 < n) (hb : 0 < b)
    (i : Fin (n - q)) : 0 ≤ ((n : ℝ) * b)⁻¹ * localKernel ((grid n i.val - t) / b) :=
  mul_nonneg (inv_nonneg.mpr (le_of_lt (mul_pos (by exact_mod_cast hn) hb)))
    (localKernel_nonneg _)

/-- The kernel weight at a point with nonzero kernel is positive. -/
theorem localLinearWindowWeight_pos (n q : ℕ) (b t : ℝ) (hn : 0 < n) (hb : 0 < b)
    (i : Fin (n - q)) (h : localKernel ((grid n i.val - t) / b) ≠ 0) :
    0 < ((n : ℝ) * b)⁻¹ * localKernel ((grid n i.val - t) / b) :=
  mul_pos (inv_pos.mpr (mul_pos (by exact_mod_cast hn) hb))
    (localKernel_pos _ (localKernel_abs_lt _ h))

theorem localDesignGram_one_moment_zero_nonneg (n q : ℕ) (b t : ℝ) (hn : 0 < n) (hb : 0 < b) :
    0 ≤ localDesignGram 1 n q b t (0 : Fin 2) (0 : Fin 2) := by
  rw [localDesignGram_one_moment_zero]
  exact Finset.sum_nonneg fun i _ => localLinearWindowWeight_nonneg n q b t hn hb i

theorem localDesignGram_one_moment_two_nonneg (n q : ℕ) (b t : ℝ) (hn : 0 < n) (hb : 0 < b) :
    0 ≤ localDesignGram 1 n q b t (1 : Fin 2) (1 : Fin 2) := by
  rw [localDesignGram_one_moment_two]
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (localLinearWindowWeight_nonneg n q b t hn hb i) (sq_nonneg _)

/-- Second moment bounded by the zeroth moment (`x ^ 2 ≤ 1` on the window). -/
theorem localDesignGram_one_moment_two_le_zero (n q : ℕ) (b t : ℝ) (hn : 0 < n) (hb : 0 < b) :
    localDesignGram 1 n q b t (1 : Fin 2) (1 : Fin 2)
      ≤ localDesignGram 1 n q b t (0 : Fin 2) (0 : Fin 2) := by
  rw [localDesignGram_one_moment_two, localDesignGram_one_moment_zero]
  refine Finset.sum_le_sum fun i _ => ?_
  have hW := localLinearWindowWeight_nonneg n q b t hn hb i
  by_cases h1 : 1 ≤ |(grid n i.val - t) / b|
  · rw [localKernel_zero _ h1, mul_zero, zero_mul]
  · have hx : |(grid n i.val - t) / b| ≤ 1 := (lt_of_not_ge h1).le
    have h2 : ((grid n i.val - t) / b) ^ 2 ≤ 1 := by
      have h := abs_le.mp hx
      nlinarith
    have h := mul_le_mul_of_nonneg_left h2 hW
    rwa [mul_one] at h

/-- First moment bounded by the zeroth moment in absolute value. -/
theorem localDesignGram_one_abs_moment_one_le_zero (n q : ℕ) (b t : ℝ) (hn : 0 < n) (hb : 0 < b) :
    |localDesignGram 1 n q b t (0 : Fin 2) (1 : Fin 2)|
      ≤ localDesignGram 1 n q b t (0 : Fin 2) (0 : Fin 2) := by
  have key : ∀ i : Fin (n - q),
      (-(((n : ℝ) * b)⁻¹ * localKernel ((grid n i.val - t) / b))
        ≤ ((n : ℝ) * b)⁻¹ * localKernel ((grid n i.val - t) / b) * ((grid n i.val - t) / b)) ∧
      (((n : ℝ) * b)⁻¹ * localKernel ((grid n i.val - t) / b) * ((grid n i.val - t) / b)
        ≤ ((n : ℝ) * b)⁻¹ * localKernel ((grid n i.val - t) / b)) := by
    intro i
    have hW := localLinearWindowWeight_nonneg n q b t hn hb i
    by_cases h1 : 1 ≤ |(grid n i.val - t) / b|
    · rw [localKernel_zero _ h1, mul_zero, zero_mul]
      exact ⟨by simp, by simp⟩
    · have hx : |(grid n i.val - t) / b| ≤ 1 := (lt_of_not_ge h1).le
      rcases abs_le.mp hx with ⟨hlo, hhi⟩
      constructor
      · calc -(((n : ℝ) * b)⁻¹ * localKernel ((grid n i.val - t) / b))
            = ((n : ℝ) * b)⁻¹ * localKernel ((grid n i.val - t) / b) * (-1) := by ring
          _ ≤ ((n : ℝ) * b)⁻¹ * localKernel ((grid n i.val - t) / b)
                * ((grid n i.val - t) / b) := mul_le_mul_of_nonneg_left hlo hW
      · have h := mul_le_mul_of_nonneg_left hhi hW
        rwa [mul_one] at h
  rw [localDesignGram_one_moment_one, localDesignGram_one_moment_zero, abs_le]
  constructor
  · rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun i _ => (key i).1
  · exact Finset.sum_le_sum fun i _ => (key i).2

/-! ### The determinant identity -/

/-- Cauchy–Schwarz made explicit: for nontrivial weights `w` and design
coordinates `x`, `μ0 * μ2 - μ1 ^ 2 = 1/2 * ∑ i ∑ j w i * w j * (x j - x i) ^ 2`. -/
theorem gram_det_eq_sum_sq {ι : Type*} [Fintype ι] (W : ι → ℝ) (x : ι → ℝ) :
    (∑ i : ι, W i) * ∑ i : ι, W i * x i ^ 2
        - (∑ i : ι, W i * x i) * ∑ i : ι, W i * x i
      = (1 : ℝ) / 2 * ∑ i : ι, ∑ j : ι, W i * W j * (x j - x i) ^ 2 := by
  have hsplit : ∑ i : ι, ∑ j : ι, W i * W j * (x j - x i) ^ 2
      = (∑ i : ι, ∑ j : ι, W i * W j * x j ^ 2
          + ∑ i : ι, ∑ j : ι, W i * W j * x i ^ 2)
        - ∑ i : ι, ∑ j : ι, (W i * W j * x i * x j + W i * W j * x i * x j) := by
    have point : ∀ i j : ι, W i * W j * (x j - x i) ^ 2
        = W i * W j * x j ^ 2 + W i * W j * x i ^ 2
            - (W i * W j * x i * x j + W i * W j * x i * x j) :=
      fun i j => by ring
    have hinner : ∀ i : ι, ∑ j : ι, W i * W j * (x j - x i) ^ 2
        = (∑ j : ι, W i * W j * x j ^ 2) + (∑ j : ι, W i * W j * x i ^ 2)
          - ∑ j : ι, (W i * W j * x i * x j + W i * W j * x i * x j) := by
      intro i
      rw [Finset.sum_congr rfl fun j _ => point i j,
        Finset.sum_sub_distrib
          (f := fun j : ι => W i * W j * x j ^ 2 + W i * W j * x i ^ 2)
          (g := fun j : ι => W i * W j * x i * x j + W i * W j * x i * x j),
        Finset.sum_add_distrib (f := fun j : ι => W i * W j * x j ^ 2)
          (g := fun j : ι => W i * W j * x i ^ 2)]
    rw [Finset.sum_congr rfl fun i _ => hinner i,
      Finset.sum_sub_distrib
        (f := fun i : ι => (∑ j : ι, W i * W j * x j ^ 2) + ∑ j : ι, W i * W j * x i ^ 2)
        (g := fun i : ι => ∑ j : ι,
          (W i * W j * x i * x j + W i * W j * x i * x j)),
      Finset.sum_add_distrib (f := fun i : ι => ∑ j : ι, W i * W j * x j ^ 2)
        (g := fun i : ι => ∑ j : ι, W i * W j * x i ^ 2)]
  have S1 : ∑ i : ι, ∑ j : ι, W i * W j * x j ^ 2
      = (∑ i : ι, W i) * ∑ j : ι, W j * x j ^ 2 := by
    rw [Finset.sum_mul_sum Finset.univ Finset.univ W (fun j : ι => W j * x j ^ 2)]
    have pt : ∀ i j : ι, W i * (W j * x j ^ 2) = W i * W j * x j ^ 2 := fun i j => by ring
    simp only [pt]
  have S3 : ∑ i : ι, ∑ j : ι, W i * W j * x i ^ 2
      = (∑ i : ι, W i * x i ^ 2) * ∑ j : ι, W j := by
    rw [Finset.sum_mul_sum Finset.univ Finset.univ (fun i : ι => W i * x i ^ 2) W]
    have pt : ∀ i j : ι, (W i * x i ^ 2) * W j = W i * W j * x i ^ 2 := fun i j => by ring
    simp only [pt]
  have S2 : ∑ i : ι, ∑ j : ι, (W i * W j * x i * x j + W i * W j * x i * x j)
      = (∑ i : ι, ∑ j : ι, W i * W j * x i * x j)
        + (∑ i : ι, ∑ j : ι, W i * W j * x i * x j) :=
    (Finset.sum_congr rfl fun i _ =>
      Finset.sum_add_distrib (f := fun j : ι => W i * W j * x i * x j)
        (g := fun j : ι => W i * W j * x i * x j)).trans
      (Finset.sum_add_distrib (s := Finset.univ)
        (f := fun i : ι => ∑ j : ι, W i * W j * x i * x j)
        (g := fun i : ι => ∑ j : ι, W i * W j * x i * x j))
  have S4 : (∑ i : ι, W i * x i) * ∑ i : ι, W i * x i
      = ∑ i : ι, ∑ j : ι, W i * W j * x i * x j := by
    rw [Finset.sum_mul_sum Finset.univ Finset.univ (fun i : ι => W i * x i)
      (fun j : ι => W j * x j)]
    have pt : ∀ i j : ι, (W i * x i) * (W j * x j) = W i * W j * x i * x j := fun i j => by ring
    simp only [pt]
  rw [hsplit, S1, S3, S2, S4]
  ring

/-- Determinant of the degree-one Gram matrix as half the weighted pairwise
square distances. -/
theorem localDesignGram_one_det_eq (n q : ℕ) (b t : ℝ) :
    (localDesignGram 1 n q b t).det = (1 : ℝ) / 2 * ∑ i : Fin (n - q), ∑ j : Fin (n - q),
      ((n : ℝ) * b)⁻¹ * localKernel ((grid n i.val - t) / b) *
        (((n : ℝ) * b)⁻¹ * localKernel ((grid n j.val - t) / b) *
          ((grid n j.val - t) / b - (grid n i.val - t) / b) ^ 2) := by
  rw [Matrix.det_fin_two, localDesignGram_one_moment_zero, localDesignGram_one_moment_two,
    localDesignGram_one_moment_one, localDesignGram_one_moment_one']
  rw [gram_det_eq_sum_sq
    (fun i : Fin (n - q) => ((n : ℝ) * b)⁻¹ * localKernel ((grid n i.val - t) / b))
    (fun i : Fin (n - q) => (grid n i.val - t) / b)]
  exact congrArg (fun S : ℝ => (1 : ℝ) / 2 * S)
    (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)

/-- The degree-one Gram determinant is always nonnegative. -/
theorem localDesignGram_one_det_nonneg (n q : ℕ) (b t : ℝ) (hn : 0 < n) (hb : 0 < b) :
    0 ≤ (localDesignGram 1 n q b t).det := by
  rw [localDesignGram_one_det_eq]
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_)
  exact mul_nonneg (localLinearWindowWeight_nonneg n q b t hn hb i)
    (mul_nonneg (localLinearWindowWeight_nonneg n q b t hn hb j) (sq_nonneg _))

set_option maxHeartbeats 1000000 in
/-- The degree-one Gram determinant is strictly positive as soon as the window
contains two distinct grid points with nonzero kernel. -/
theorem localDesignGram_one_det_pos (n q : ℕ) (b t : ℝ) (hn : 0 < n) (hb : 0 < b)
    (i j : Fin (n - q)) (hi : localKernel ((grid n i.val - t) / b) ≠ 0)
    (hj : localKernel ((grid n j.val - t) / b) ≠ 0)
    (hij : (grid n i.val - t) / b < (grid n j.val - t) / b) :
    0 < (localDesignGram 1 n q b t).det := by
  rw [localDesignGram_one_det_eq]
  have hpt : ∀ k l : Fin (n - q), 0 ≤ ((n : ℝ) * b)⁻¹ * localKernel ((grid n k.val - t) / b) *
      (((n : ℝ) * b)⁻¹ * localKernel ((grid n l.val - t) / b) *
        ((grid n l.val - t) / b - (grid n k.val - t) / b) ^ 2) := fun k l =>
    mul_nonneg (localLinearWindowWeight_nonneg n q b t hn hb k)
      (mul_nonneg (localLinearWindowWeight_nonneg n q b t hn hb l) (sq_nonneg _))
  have hWk : ∀ k : Fin (n - q), 0 ≤ ∑ l : Fin (n - q),
      ((n : ℝ) * b)⁻¹ * localKernel ((grid n k.val - t) / b) *
        (((n : ℝ) * b)⁻¹ * localKernel ((grid n l.val - t) / b) *
          ((grid n l.val - t) / b - (grid n k.val - t) / b) ^ 2) := fun k =>
    Finset.sum_nonneg fun l _ => hpt k l
  have hterm : 0 < (1 : ℝ) / 2 * (((n : ℝ) * b)⁻¹ * localKernel ((grid n i.val - t) / b) *
      (((n : ℝ) * b)⁻¹ * localKernel ((grid n j.val - t) / b) *
        ((grid n j.val - t) / b - (grid n i.val - t) / b) ^ 2)) := by
    refine mul_pos (by positivity) (mul_pos ?_ ?_)
    · exact localLinearWindowWeight_pos n q b t hn hb i hi
    · exact mul_pos (localLinearWindowWeight_pos n q b t hn hb j hj)
        (pow_pos (sub_pos.mpr hij) 2)
  refine hterm.trans_le (mul_le_mul_of_nonneg_left ?_ (by positivity))
  exact (Finset.single_le_sum (f := fun l : Fin (n - q) =>
      ((n : ℝ) * b)⁻¹ * localKernel ((grid n i.val - t) / b) *
        (((n : ℝ) * b)⁻¹ * localKernel ((grid n l.val - t) / b) *
          ((grid n l.val - t) / b - (grid n i.val - t) / b) ^ 2))
    (fun l _ => hpt i l) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (f := fun k : Fin (n - q) => ∑ l : Fin (n - q),
      ((n : ℝ) * b)⁻¹ * localKernel ((grid n k.val - t) / b) *
        (((n : ℝ) * b)⁻¹ * localKernel ((grid n l.val - t) / b) *
          ((grid n l.val - t) / b - (grid n k.val - t) / b) ^ 2))
    (fun k _ => hWk k) (Finset.mem_univ i))

/-! ### The exact degree-one weight formula -/

/-- Closed form of the degree-one weights, valid unconditionally: if the Gram
determinant vanishes then `Ring.inverse` kills the correction term and the
weight is `0`. -/
theorem localLinearWeight_one_form (n q : ℕ) (b t : ℝ) (i : Fin (n - q)) :
    localPolynomialWeights 1 n q b t i
      = ((n : ℝ) * b)⁻¹ * localKernel ((grid n i.val - t) / b)
        * ((localDesignGram 1 n q b t) (1 : Fin 2) (1 : Fin 2)
            - (localDesignGram 1 n q b t) (0 : Fin 2) (1 : Fin 2)
                * ((grid n i.val - t) / b))
        * Ring.inverse (localDesignGram 1 n q b t).det := by
  rw [localPolynomialWeights_formula, Fin.sum_univ_two]
  have hinv := Matrix.inv_def (localDesignGram 1 n q b t)
  have ha := Matrix.adjugate_fin_two (localDesignGram 1 n q b t)
  have e0 : (localDesignGram 1 n q b t)⁻¹ (0 : Fin 2) (0 : Fin 2)
      = Ring.inverse (localDesignGram 1 n q b t).det
          * (localDesignGram 1 n q b t) (1 : Fin 2) (1 : Fin 2) := by
    rw [hinv, ha]
    simp
  have e1 : (localDesignGram 1 n q b t)⁻¹ (0 : Fin 2) (1 : Fin 2)
      = Ring.inverse (localDesignGram 1 n q b t).det
          * -(localDesignGram 1 n q b t) (0 : Fin 2) (1 : Fin 2) := by
    rw [hinv, ha]
    simp
  rw [e0, e1]
  have hv0 : ((0 : Fin 2)).val = 0 := rfl
  have hv1 : ((1 : Fin 2)).val = 1 := rfl
  rw [hv0, hv1]
  ring

/-! ### Nonnegativity criteria -/

/-- **Sharp pointwise sign criterion** for the degree-one local linear weights:
the weight at grid point `i` is nonnegative as soon as
`μ1 * x i ≤ μ2` (i.e. `G 0 1 * x i ≤ G 1 1`).  No determinant hypothesis is
needed: a singular Gram yields zero weights. -/
theorem localLinearWeight_nonneg (n q : ℕ) (b t : ℝ) (hn : 0 < n) (hb : 0 < b)
    (i : Fin (n - q))
    (hnum : (localDesignGram 1 n q b t) (1 : Fin 2) (1 : Fin 2)
        - (localDesignGram 1 n q b t) (0 : Fin 2) (1 : Fin 2)
            * ((grid n i.val - t) / b) ≥ 0) :
    0 ≤ localPolynomialWeights 1 n q b t i := by
  have hdet : 0 ≤ (localDesignGram 1 n q b t).det :=
    localDesignGram_one_det_nonneg n q b t hn hb
  rw [localLinearWeight_one_form]
  by_cases hz : (localDesignGram 1 n q b t).det = 0
  · rw [hz, Ring.inverse_zero, mul_zero]
  · refine mul_nonneg (mul_nonneg ?_ hnum) ?_
    · exact mul_nonneg (inv_nonneg.mpr (le_of_lt (mul_pos (by exact_mod_cast hn) hb)))
        (localKernel_nonneg _)
    · rw [Ring.inverse_eq_inv]
      exact inv_nonneg.mpr (le_of_lt (lt_of_le_of_ne hdet (Ne.symm hz)))

/-- **Corrected global statement**: every degree-one weight is nonnegative
provided the window is balanced in the sense `μ1 * x i ≤ μ2` for every grid
point.  (The unconditional version is false; see the module docstring.) -/
theorem localLinearWeights_nonneg (n q : ℕ) (b t : ℝ) (hn : 0 < n) (hb : 0 < b)
    (h : ∀ i : Fin (n - q), (localDesignGram 1 n q b t) (0 : Fin 2) (1 : Fin 2)
          * ((grid n i.val - t) / b)
        ≤ (localDesignGram 1 n q b t) (1 : Fin 2) (1 : Fin 2)) :
    ∀ i : Fin (n - q), 0 ≤ localPolynomialWeights 1 n q b t i := fun i =>
  localLinearWeight_nonneg n q b t hn hb i (by linarith [h i])

/-- The weight at a grid point whose coordinate has sign opposite to `μ1`
(in particular `x i = 0`) is always nonnegative. -/
theorem localLinearWeight_nonneg_of_mul_nonpos (n q : ℕ) (b t : ℝ) (hn : 0 < n) (hb : 0 < b)
    (i : Fin (n - q)) (h : (localDesignGram 1 n q b t) (0 : Fin 2) (1 : Fin 2)
        * ((grid n i.val - t) / b) ≤ 0) :
    0 ≤ localPolynomialWeights 1 n q b t i := by
  refine localLinearWeight_nonneg n q b t hn hb i ?_
  have h2 := localDesignGram_one_moment_two_nonneg n q b t hn hb
  linarith

/-- The weight at the grid point with `x i = 0` (the evaluation point itself,
when it lies on the grid) is always nonnegative. -/
theorem localLinearWeight_nonneg_at_center (n q : ℕ) (b t : ℝ) (hn : 0 < n) (hb : 0 < b)
    (i : Fin (n - q)) (h : (grid n i.val - t) / b = 0) :
    0 ≤ localPolynomialWeights 1 n q b t i := by
  refine localLinearWeight_nonneg n q b t hn hb i ?_
  rw [h, mul_zero, sub_zero]
  exact localDesignGram_one_moment_two_nonneg n q b t hn hb

/-- Sufficient pointwise condition: `|μ1 * x i| ≤ μ2` implies a nonnegative
weight at `i`. -/
theorem localLinearWeight_nonneg_of_abs_mul_le (n q : ℕ) (b t : ℝ) (hn : 0 < n) (hb : 0 < b)
    (i : Fin (n - q))
    (h : |(localDesignGram 1 n q b t) (0 : Fin 2) (1 : Fin 2) * ((grid n i.val - t) / b)|
        ≤ (localDesignGram 1 n q b t) (1 : Fin 2) (1 : Fin 2)) :
    0 ≤ localPolynomialWeights 1 n q b t i := by
  refine localLinearWeight_nonneg n q b t hn hb i ?_
  have h2 := localDesignGram_one_moment_two_nonneg n q b t hn hb
  have hbnd := abs_le.mp h
  linarith

end Hurst
