import Mathlib

/-!
# The hyperplane `{z : Fin k → ℝ | z i = z j}` is Lebesgue-null

For distinct coordinates `i ≠ j` in `Fin k`, the set of vectors with `z i = z j` is a proper
linear subspace of `Fin k → ℝ`, hence null for the product Lebesgue measure
`volume = Measure.pi (fun _ => volume)`.  We record:

* `Hurst.HyperplaneNull.measurableSet_hyperplane` : the hyperplane is measurable;
* `Hurst.HyperplaneNull.measure_hyperplane_eq_zero` : `volume {z | z i = z j} = 0`;
* `Hurst.HyperplaneNull.measure_pi_hyperplane_eq_zero` : the same in explicit `Measure.pi` form;
* `Hurst.HyperplaneNull.measure_hyperplane_inter_eq_zero` : its intersection with any set is null;
* `Hurst.HyperplaneNull.measure_hyperplane_inter_cube_eq_zero` : the version inside the cube
  `∏ _, Icc (-1 : ℝ) 1`;
* null-measurability companions.
-/

namespace Hurst.HyperplaneNull

open MeasureTheory Set

variable {k : ℕ}

/-- The linear functional `z ↦ z i - z j` whose kernel is the hyperplane `{z | z i = z j}`. -/
noncomputable def hyperplaneLinearMap (i j : Fin k) : (Fin k → ℝ) →ₗ[ℝ] ℝ where
  toFun z := z i - z j
  map_add' x y := by simp only [Pi.add_apply]; ring
  map_smul' c x := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- The hyperplane `{z | z i = z j}` as a linear subspace: the kernel of `z ↦ z i - z j`. -/
noncomputable def hyperplaneSubmodule (i j : Fin k) : Submodule ℝ (Fin k → ℝ) :=
  LinearMap.ker (hyperplaneLinearMap i j)

theorem mem_hyperplaneSubmodule {i j : Fin k} {z : Fin k → ℝ} :
    z ∈ hyperplaneSubmodule i j ↔ z i = z j := by
  simp [hyperplaneSubmodule, hyperplaneLinearMap, LinearMap.mem_ker, sub_eq_zero]

theorem coe_hyperplaneSubmodule (i j : Fin k) :
    (hyperplaneSubmodule i j : Set (Fin k → ℝ)) = {z : Fin k → ℝ | z i = z j} := by
  ext z
  exact mem_hyperplaneSubmodule

/-- The hyperplane is a proper subspace when `i ≠ j`. -/
theorem hyperplaneSubmodule_ne_top {i j : Fin k} (hij : i ≠ j) :
    hyperplaneSubmodule i j ≠ ⊤ := by
  intro h
  have hmem : (Function.update (fun _ : Fin k => (0 : ℝ)) i (1 : ℝ)) ∈ hyperplaneSubmodule i j := by
    rw [h]
    exact Submodule.mem_top
  rw [mem_hyperplaneSubmodule] at hmem
  simp only [Function.update_self, Function.update_of_ne (Ne.symm hij)] at hmem
  exact one_ne_zero hmem

/-- The hyperplane `{z | z i = z j}` is Lebesgue-null in `Fin k → ℝ`. -/
theorem measure_hyperplane_eq_zero {i j : Fin k} (hij : i ≠ j) :
    volume {z : Fin k → ℝ | z i = z j} = 0 := by
  rw [← coe_hyperplaneSubmodule]
  exact Measure.addHaar_submodule volume _ (hyperplaneSubmodule_ne_top hij)

/-- The hyperplane is null, stated in explicit `Measure.pi` form. -/
theorem measure_pi_hyperplane_eq_zero {i j : Fin k} (hij : i ≠ j) :
    Measure.pi (fun _ => (volume : Measure ℝ)) {z : Fin k → ℝ | z i = z j} = 0 :=
  measure_hyperplane_eq_zero hij

/-- The hyperplane is measurable. -/
theorem measurableSet_hyperplane (i j : Fin k) :
    MeasurableSet {z : Fin k → ℝ | z i = z j} := by
  have hset : {z : Fin k → ℝ | z i = z j} = (fun z => z i - z j) ⁻¹' {(0 : ℝ)} := by
    ext z
    simp [sub_eq_zero]
  rw [hset]
  exact (measurable_pi_apply i).sub (measurable_pi_apply j) (measurableSet_singleton (0 : ℝ))

/-- The hyperplane is null-measurable. -/
theorem nullMeasurableSet_hyperplane {i j : Fin k} (hij : i ≠ j) :
    NullMeasurableSet {z : Fin k → ℝ | z i = z j} volume :=
  NullMeasurableSet.of_null (measure_hyperplane_eq_zero hij)

/-- The hyperplane intersected with *any* set is null. -/
theorem measure_hyperplane_inter_eq_zero {i j : Fin k} (hij : i ≠ j) (s : Set (Fin k → ℝ)) :
    volume ({z : Fin k → ℝ | z i = z j} ∩ s) = 0 :=
  measure_mono_null inter_subset_left (measure_hyperplane_eq_zero hij)

/-- The hyperplane intersected with any set is null, in explicit `Measure.pi` form. -/
theorem measure_pi_hyperplane_inter_eq_zero {i j : Fin k} (hij : i ≠ j) (s : Set (Fin k → ℝ)) :
    Measure.pi (fun _ => (volume : Measure ℝ)) ({z : Fin k → ℝ | z i = z j} ∩ s) = 0 :=
  measure_hyperplane_inter_eq_zero hij s

/-- The part of the hyperplane inside the cube `∏ _, Icc (-1, 1)` is null. -/
theorem measure_hyperplane_inter_cube_eq_zero {i j : Fin k} (hij : i ≠ j) :
    volume ({z : Fin k → ℝ | z i = z j} ∩ pi univ (fun _ => Icc (-1 : ℝ) 1)) = 0 :=
  measure_hyperplane_inter_eq_zero hij _

/-- The part of the hyperplane inside the cube `∏ _, Icc (-1, 1)` is null,
in explicit `Measure.pi` form. -/
theorem measure_pi_hyperplane_inter_cube_eq_zero {i j : Fin k} (hij : i ≠ j) :
    Measure.pi (fun _ => (volume : Measure ℝ))
        ({z : Fin k → ℝ | z i = z j} ∩ pi univ (fun _ => Icc (-1 : ℝ) 1)) = 0 :=
  measure_hyperplane_inter_eq_zero hij _

/-- The intersection of the hyperplane with the cube `∏ _, Icc (-1, 1)` is measurable
(friendlier `Icc` class: both factors are measurable, so `MeasurableSet.inter` applies). -/
theorem measurableSet_hyperplane_inter_cube (i j : Fin k) :
    MeasurableSet ({z : Fin k → ℝ | z i = z j} ∩ pi univ (fun _ => Icc (-1 : ℝ) 1)) := by
  refine (measurableSet_hyperplane i j).inter ?_
  rw [measurableSet_pi Set.countable_univ]
  exact Or.inl fun _ _ => measurableSet_Icc

/-- The intersection of the hyperplane with the cube `∏ _, Icc (-1, 1)` is null-measurable. -/
theorem nullMeasurableSet_hyperplane_inter_cube {i j : Fin k} (hij : i ≠ j) :
    NullMeasurableSet ({z : Fin k → ℝ | z i = z j} ∩ pi univ (fun _ => Icc (-1 : ℝ) 1)) volume :=
  NullMeasurableSet.of_null (measure_hyperplane_inter_cube_eq_zero hij)

end Hurst.HyperplaneNull
