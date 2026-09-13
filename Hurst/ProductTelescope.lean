import Mathlib

/-!
# Per-tuple product telescope

The difference of two finite products decomposed as a telescoping sum (the
difference-decomposition engine for product-level perturbation bounds):

`∏_{i<k} u i - ∏_{i<k} t i
  = ∑_{i<k} (∏_{j<i} u j) * (u i - t i) * (∏_{j=i+1}^{k-1} t j)`,

where the trailing `t`-suffix is written as `∏ j ∈ range (k - 1 - i), t (j + i + 1)`.

Induction peels the last factor: the new last summand has an empty `t`-suffix,
and every earlier summand's `t`-suffix gains exactly one factor `t n`, so the
bulk sum factors as `(∑_{i<n} _) * t n` and the induction hypothesis slots in
by pure `ring` algebra.  No analysis, no norms — the norm bookkeeping belongs
to the consumer.
-/

namespace Hurst

theorem prod_telescope {k : ℕ} (u t : ℕ → ℝ) :
    (∏ i ∈ Finset.range k, u i) - (∏ i ∈ Finset.range k, t i) =
      ∑ i ∈ Finset.range k, (∏ j ∈ Finset.range i, u j) * (u i - t i) *
        (∏ j ∈ Finset.range (k - 1 - i), t (j + i + 1)) := by
  induction k with
  | zero => simp
  | succ n ih =>
    have hlast : (∏ j ∈ Finset.range n, u j) * (u n - t n) *
        (∏ j ∈ Finset.range (n + 1 - 1 - n), t (j + n + 1))
        = (∏ j ∈ Finset.range n, u j) * (u n - t n) := by
      rw [show (n + 1 - 1 - n : ℕ) = 0 by omega, Finset.prod_range_zero, mul_one]
    have hsum : ∑ i ∈ Finset.range n,
        (∏ j ∈ Finset.range i, u j) * (u i - t i) *
          (∏ j ∈ Finset.range (n + 1 - 1 - i), t (j + i + 1))
      = (∑ i ∈ Finset.range n, (∏ j ∈ Finset.range i, u j) * (u i - t i) *
          (∏ j ∈ Finset.range (n - 1 - i), t (j + i + 1))) * t n := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hin : i < n := Finset.mem_range.mp hi
      rw [show (n + 1 - 1 - i : ℕ) = (n - 1 - i) + 1 by omega, Finset.prod_range_succ,
        show ((n - 1 - i) + i + 1 : ℕ) = n by omega]
      ring
    rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.sum_range_succ,
      hlast, hsum, ← ih]
    ring

/-- **Insertion form.** If `u` agrees with `t` on `range k` except at the pivot `s`,
then scaling the single pivot factor from `t s` to `u s` changes the product by
exactly `(u s - ρ * t s)` times the product of the untouched `t`-factors, written
with an indicator. -/
theorem prod_telescope_insert {k : ℕ} (ρ : ℝ) (u t : ℕ → ℝ) (s : ℕ) (hs : s < k)
    (hu : ∀ i ∈ Finset.range k, i ≠ s → u i = t i) :
    (∏ i ∈ Finset.range k, u i) - ρ * (∏ i ∈ Finset.range k, t i)
      = (u s - ρ * t s) * ∏ i ∈ Finset.range k, (if i = s then 1 else t i) := by
  have hEq : (∏ i ∈ Finset.range k, u i)
      = ∏ i ∈ Finset.range k, (if i = s then u i else t i) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    by_cases h : i = s
    · rw [if_pos h]
    · rw [if_neg h, hu i hi h]
  have hE : ∏ i ∈ Finset.range k, (if i = s then 1 else t i)
      = ∏ i ∈ (Finset.range k).erase s, t i := by
    conv_lhs => rw [← Finset.insert_erase (Finset.mem_range.mpr hs)]
    rw [Finset.prod_insert (f := fun i => (if i = s then (1 : ℝ) else t i))
      (Finset.notMem_erase s (Finset.range k))]
    rw [if_pos rfl, one_mul,
      Finset.prod_congr rfl (fun i hi => by rw [if_neg (Finset.mem_erase.mp hi).1])]
  have hU : (∏ i ∈ Finset.range k, (if i = s then u i else t i))
      = u s * ∏ i ∈ (Finset.range k).erase s, t i := by
    conv_lhs => rw [← Finset.insert_erase (Finset.mem_range.mpr hs)]
    rw [Finset.prod_insert (f := fun i => (if i = s then u i else t i))
      (Finset.notMem_erase s (Finset.range k))]
    rw [if_pos rfl,
      Finset.prod_congr rfl (fun i hi => by rw [if_neg (Finset.mem_erase.mp hi).1])]
  have hT : (∏ i ∈ Finset.range k, t i) = t s * ∏ i ∈ (Finset.range k).erase s, t i := by
    conv_lhs => rw [← Finset.insert_erase (Finset.mem_range.mpr hs)]
    exact Finset.prod_insert (f := t) (Finset.notMem_erase s (Finset.range k))
  rw [hEq, hU, hT, hE]
  ring

end Hurst
