import Mathlib

open Filter
open scoped Topology

example (r : ℕ → ℝ) (J : ℕ) (c : ℝ) :
    (∀ δ : ℝ, 0 < δ → δ ≤ c → True) ∧ True := by
  refine ⟨fun δ hδpos hδλ => ?_, trivial⟩
  refine Classical.byContradiction fun hcon => ?_
  have hfreq0 : Filter.Frequently (fun n : ℕ => r n J < c) atTop :=
    Filter.not_eventually.mp hcon
  trivial
