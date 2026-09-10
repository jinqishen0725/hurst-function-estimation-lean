import Mathlib.Analysis.Matrix.Normed
open Matrix
example {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) :
    (∑ p ∈ (Finset.univ.product Finset.univ : Finset (n × n)), |A p.1 p.2|^2) =
    ∑ i, ∑ j, |A i j|^2 := by
  exact Finset.sum_product Finset.univ Finset.univ (fun p => |A p.1 p.2|^2)
