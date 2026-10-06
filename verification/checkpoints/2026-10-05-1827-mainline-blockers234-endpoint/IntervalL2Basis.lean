import Hurst.CountableEigenfamily

/-!
# A natural-number indexed Hilbert basis of `L²([-1,1])`

Positive-length pairwise disjoint intervals give an infinite orthonormal family
of normalized indicators. Extend that family to a Hilbert basis, use separability
to make its index countable, and reindex the (necessarily infinite) basis by ℕ.
No basis or infinite-dimensionality hypothesis is imposed on the model.
-/

open MeasureTheory Measure Set
open scoped Real ENNReal

noncomputable section
namespace HS

private def basisInterval (n : ℕ) : Set ℝ := Ioo (1 / ((n : ℝ) + 2)) (1 / ((n : ℝ) + 1))

private theorem basisInterval_subset (n : ℕ) : basisInterval n ⊆ I := by
  intro x hx
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have ha : 0 < 1 / ((n : ℝ) + 2) := by positivity
  have hb : 1 / ((n : ℝ) + 1) ≤ 1 := by
    apply (div_le_one (by positivity)).2
    linarith
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

private theorem basisInterval_volume_pos (n : ℕ) : 0 < vol (basisInterval n) := by
  change 0 < (volume.restrict I) (basisInterval n)
  rw [Measure.restrict_apply (show MeasurableSet (basisInterval n) from measurableSet_Ioo),
    Set.inter_eq_left.mpr (basisInterval_subset n)]
  change 0 < volume (Ioo (1 / ((n : ℝ) + 2)) (1 / ((n : ℝ) + 1)))
  rw [Real.volume_Ioo]
  apply ENNReal.ofReal_pos.mpr
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have h : 1 / ((n : ℝ) + 2) < 1 / ((n : ℝ) + 1) := by
    exact one_div_lt_one_div_of_lt (by positivity) (by linarith)
  linarith

private theorem basisInterval_disjoint : Pairwise (fun i j => Disjoint (basisInterval i) (basisInterval j)) := by
  intro i j hij
  wlog hij' : i < j generalizing i j
  · exact (@this j i hij.symm (Nat.lt_of_le_of_ne (Nat.le_of_not_gt hij') hij.symm)).symm
  rw [Set.disjoint_left]
  intro x hxi hxj
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg _
  have hijR : (i : ℝ) + 2 ≤ (j : ℝ) + 1 := by
    exact_mod_cast (show i + 2 ≤ j + 1 by omega)
  have hbound : 1 / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 2) :=
    one_div_le_one_div_of_le (by positivity) hijR
  exact (not_lt_of_ge hbound) (hxj.2.trans' hxi.1)

private def intervalIndicator (n : ℕ) : L2 :=
  indicatorConstLp 2 (show MeasurableSet (basisInterval n) from measurableSet_Ioo)
    (measure_ne_top vol _) (1 : ℝ)

private theorem intervalIndicator_norm_pos (n : ℕ) : 0 < ‖intervalIndicator n‖ := by
  rw [intervalIndicator, norm_indicatorConstLp (by norm_num) (by norm_num)]
  simp only [norm_one, one_mul]
  exact Real.rpow_pos_of_pos
    (ENNReal.toReal_pos (ne_of_gt (basisInterval_volume_pos n)) (measure_ne_top vol _)) _

private theorem intervalIndicator_inner_zero {i j : ℕ} (hij : i ≠ j) :
    inner ℝ (intervalIndicator i) (intervalIndicator j) = 0 := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [indicatorConstLp_coeFn (p := 2) (μ := vol)
      (hs := show MeasurableSet (basisInterval i) from measurableSet_Ioo)
      (hμs := measure_ne_top vol _) (c := (1 : ℝ)),
    indicatorConstLp_coeFn (p := 2) (μ := vol)
      (hs := show MeasurableSet (basisInterval j) from measurableSet_Ioo)
      (hμs := measure_ne_top vol _) (c := (1 : ℝ))] with x hi hj
  change intervalIndicator i x = _ at hi
  change intervalIndicator j x = _ at hj
  rw [hi, hj]
  by_cases hxi : x ∈ basisInterval i
  · have hxj : x ∉ basisInterval j := fun hxj =>
      Set.disjoint_left.mp (basisInterval_disjoint hij) hxi hxj
    simp [hxi, hxj]
  · simp [hxi]

/-- A genuinely infinite orthonormal sequence, built from disjoint interval indicators. -/
theorem exists_orthonormal_nat_L2 : ∃ v : ℕ → L2, Orthonormal ℝ v := by
  let v : ℕ → L2 := fun n => ‖intervalIndicator n‖⁻¹ • intervalIndicator n
  refine ⟨v, ?_, ?_⟩
  · intro n
    change ‖‖intervalIndicator n‖⁻¹ • intervalIndicator n‖ = 1
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀]
    exact ne_of_gt (intervalIndicator_norm_pos n)
  · intro i j hij
    change inner ℝ (‖intervalIndicator i‖⁻¹ • intervalIndicator i)
      (‖intervalIndicator j‖⁻¹ • intervalIndicator j) = 0
    simp [inner_smul_left, inner_smul_right, intervalIndicator_inner_zero hij]

/-- A complete orthonormal basis indexed by ℕ exists without any model assumptions. -/
theorem nonempty_hilbertBasis_nat_L2 : Nonempty (HilbertBasis ℕ ℝ L2) := by
  classical
  obtain ⟨v, hv⟩ := exists_orthonormal_nat_L2
  obtain ⟨w, b, hvw, _hb⟩ := hv.toSubtypeRange.exists_hilbertBasis_extension
  haveI : Countable w := countable_of_orthonormal b b.orthonormal
  have hw : w.Infinite := Set.infinite_of_injective_forall_mem hv.linearIndependent.injective
    (fun n => hvw (Set.mem_range_self n))
  haveI : Infinite w := hw.to_subtype
  let q : ℕ ≃ w := Classical.choice (inferInstance : Nonempty (ℕ ≃ w))
  refine ⟨HilbertBasis.mk (b.orthonormal.comp q q.injective) ?_⟩
  have hrange : Set.range (fun n => b (q n)) = Set.range b := by
    exact q.surjective.range_comp b
  simpa only [Function.comp_def, hrange, b.dense_span] using
    (le_refl (⊤ : Submodule ℝ L2))

/-- One fixed basis for internal analytic constructions. -/
def intervalL2Basis : HilbertBasis ℕ ℝ L2 :=
  Classical.choice nonempty_hilbertBasis_nat_L2

end HS
