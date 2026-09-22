import Hurst.HSOperatorFoundation

/-!
# Countability of orthonormal families in `HS.L2`

M1 step0 prerequisite (contract §5, "ι 可数化(可分性路线)"): in the separable Hilbert space
`HS.L2 = L²(vol)` (with `vol = volume.restrict (Icc (-1 : ℝ) 1)`), the index type of every
orthonormal family is countable.

## Route

* `SeparableSpace HS.L2` is derived *unconditionally* from mathlib's separable-measure API
  (`Mathlib/MeasureTheory/Measure/SeparableMeasure.lean`):
  `ℝ` is countably generated as a measurable space (`BorelSpace.countablyGenerated`), `vol` is
  s-finite (finite, in fact), hence `IsSeparable vol`; therefore `Lp ℝ 2 vol` is
  second-countable, hence separable.
* Distinct vectors of an orthonormal family are at distance exactly `√2`
  (`‖v i - v j‖² = ‖v i‖² - 2⟪v i, v j⟫ + ‖v j‖² = 2`).
* Hence the open balls `ball (v i) (√2 / 2)` form a pairwise-disjoint family of nonempty open
  sets, and in a separable space such a family has countable index type
  (`Pairwise.countable_of_isOpen_disjoint`).
* Re-enumeration through `ℕ` then follows from `Countable.exists_injective_nat`.

## Main results

* `HS.instSeparableSpaceL2` : `TopologicalSpace.SeparableSpace HS.L2`, no extra hypotheses.
* `HS.dist_orthonormal_eq_sqrt_two` : pairwise distance `√2` for distinct orthonormal vectors.
* `HS.countable_of_orthonormal` : `Orthonormal ℝ v → Countable ι`.
* `HS.exists_injective_to_nat` : `Orthonormal ℝ v → ∃ f : ι → ℕ, Function.Injective f`.
-/

open scoped Real
open scoped ENNReal

namespace HS

/-! ### Separability of `HS.L2` (unconditional) -/

/-- `HS.L2 = L²([-1,1])` is separable: `ℝ` carries a countably generated measurable space, the
restricted Lebesgue measure is s-finite, so mathlib's `IsSeparable`/`Lp.SecondCountableTopology`
instances apply.  No hypotheses.  (mathlib has no `Fact (p ≠ ∞)` instance for the literal
`p = 2`, so we supply it locally.) -/
instance instSeparableSpaceL2 : TopologicalSpace.SeparableSpace L2 := by
  haveI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
  infer_instance

/-! ### Pairwise distances in an orthonormal family -/

/-- Distinct members of an orthonormal family in a real inner product space are at distance
exactly `√2`. -/
theorem dist_orthonormal_eq_sqrt_two {F : Type*} [SeminormedAddCommGroup F]
    [InnerProductSpace ℝ F] {ι : Type*} (v : ι → F) (hv : Orthonormal ℝ v) {i j : ι}
    (hij : i ≠ j) : dist (v i) (v j) = Real.sqrt 2 := by
  have hsq : dist (v i) (v j) ^ 2 = 2 := by
    rw [dist_eq_norm, norm_sub_sq_real, hv.norm_eq_one i, hv.norm_eq_one j,
      hv.inner_eq_zero hij]
    ring
  symm
  exact Real.sqrt_eq_iff_eq_sq (by norm_num) dist_nonneg |>.2 hsq.symm

/-! ### Countability of the index type -/

/-- step0: separability of `HS.L2` forces every orthonormal family's index type to be
countable (pairwise distances are √2; inject into a countable family of balls). -/
theorem countable_of_orthonormal {ι : Type*} (v : ι → HS.L2) (hv : Orthonormal ℝ v) :
    Countable ι := by
  classical
  -- the balls of radius √2/2 around the (mutually √2-distant) family members are disjoint
  have hdisj : ∀ i j : ι, i ≠ j → Disjoint (Metric.ball (v i) (Real.sqrt 2 / 2))
      (Metric.ball (v j) (Real.sqrt 2 / 2)) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro x hx hxj
    rw [Metric.mem_ball] at hx hxj
    have hcon : Real.sqrt 2 < Real.sqrt 2 := by
      calc Real.sqrt 2 = dist (v i) (v j) := (dist_orthonormal_eq_sqrt_two v hv hij).symm
        _ ≤ dist (v i) x + dist x (v j) := dist_triangle (v i) x (v j)
        _ = dist x (v i) + dist x (v j) := by rw [dist_comm (v i) x]
        _ < Real.sqrt 2 / 2 + Real.sqrt 2 / 2 := add_lt_add hx hxj
        _ = Real.sqrt 2 := by ring
    exact lt_irrefl _ hcon
  have hr : 0 < Real.sqrt 2 / 2 := div_pos (Real.sqrt_pos.mpr (by norm_num)) (by norm_num)
  exact Pairwise.countable_of_isOpen_disjoint
    (s := fun i => Metric.ball (v i) (Real.sqrt 2 / 2)) (fun i j hij => hdisj i j hij)
    (fun _ => Metric.isOpen_ball) (fun i => ⟨v i, Metric.mem_ball_self hr⟩)

/-- re-enumeration: a complete orthonormal family with countable index re-indexes
through an injection into ℕ -/
theorem exists_injective_to_nat {ι : Type*} (v : ι → HS.L2) (hv : Orthonormal ℝ v) :
    ∃ f : ι → ℕ, Function.Injective f := by
  haveI := countable_of_orthonormal v hv
  exact Countable.exists_injective_nat ι

end HS
