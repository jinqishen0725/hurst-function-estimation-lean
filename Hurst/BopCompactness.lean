import Mathlib
import Hurst.PositiveSquareRoot

/-!
# Compactness of the positive square root and of the model `B = S ∘ M_omega ∘ S`

M1-D2 gap 1 (the B-side input consumed by `HS.hBridge_clm` /
`HS.exists_diag_enumeration_clm`): the spectral square root `HS.sqrtOp` of the
unweighted Riesz operator is a **compact** operator, and so is the model
`HS.Bop = S ∘ M_omega ∘ S`.

Route (no `hconst`-type premise anywhere; the only input beyond the landed
M1-B signatures is the square-summability `∑' κ i ^ 2` already carried by
`exists_nonneg_eigenfamily`):

* the coefficient family `√κ` of `sqrtOp` vanishes at infinity (its
  above-threshold level sets are finite, by `∑' κ²`-summability);
* finitely-supported truncations of the spectral operator have finite-dimen-
  sional range (duality: `⟪S_N x, y⟫ = specPair c_N x y = 0` off the span),
  hence are compact (`isCompactOperator_of_locallyCompactSpace_rng` on the
  range + `IsCompactOperator.comp_clm`);
* `‖S − S_N‖ ≤ sup_{i≥N-coefficients} √κ i → 0` (operator-form Cauchy–Schwarz
  `abs_specPair_le` + `norm_specOperator_le`), so `sqrtOp` is the operator-norm
  limit of compact operators (`isCompactOperator_of_tendsto`);
* `B = S ∘L (M_omega ∘L S)` is compact by `IsCompactOperator.clm_comp`
  (compact composed with a continuous linear map, applied second).
-/

open MeasureTheory
open scoped Real

noncomputable section

namespace HS

variable {ι : Type} {v : ι → L2}

/-! ### Block A: above-threshold level sets of a square-summable nonnegative family -/

/-- A nonnegative square-summable real family is arbitrarily small off a finite
set: `{i | ε ≤ g i}` is finite for every `ε > 0`. -/
private theorem setFinite_above_threshold {g : ι → ℝ} (hg : ∀ i, 0 ≤ g i)
    (hgs : Summable (fun i => g i ^ 2)) {ε : ℝ} (hε : 0 < ε) :
    {i : ι | ε ≤ g i}.Finite := by
  by_contra hinf
  -- name the total to keep the tsum notation from absorbing the arithmetic
  set hB : ℝ := ∑' i, g i ^ 2 with hBdef
  have hB0 : (0:ℝ) ≤ hB := by
    rw [hBdef]
    exact tsum_nonneg fun i => sq_nonneg (g i)
  obtain ⟨N, hNgt⟩ : ∃ N : ℕ, hB / ε ^ 2 + 1 < (N : ℝ) := exists_nat_gt _
  obtain ⟨t, hts, htc⟩ := Set.Infinite.exists_subset_card_eq hinf N
  have hsum : ∑ i ∈ t, g i ^ 2 ≤ hB :=
    Summable.sum_le_tsum t (fun i _ => sq_nonneg (g i)) hgs
  have hge : ∀ i ∈ t, ε ^ 2 ≤ g i ^ 2 := by
    intro i hi
    have hle : ε ≤ g i := hts hi
    nlinarith [hg i, hle]
  have hcard : (N:ℝ) * ε ^ 2 ≤ ∑ i ∈ t, g i ^ 2 := by
    have h0 : (∑ i ∈ t, ε ^ 2) ≤ ∑ i ∈ t, g i ^ 2 := Finset.sum_le_sum hge
    rw [Finset.sum_const, nsmul_eq_mul, htc] at h0
    exact h0
  have hε2 : (0:ℝ) < ε ^ 2 := by positivity
  have hkey : hB + ε ^ 2 < (N:ℝ) * ε ^ 2 := by
    have hscal : (hB / ε ^ 2 + 1) * ε ^ 2 < (N:ℝ) * ε ^ 2 :=
      mul_lt_mul_of_pos_right hNgt hε2
    have hexp : (hB / ε ^ 2 + 1) * ε ^ 2 = hB + ε ^ 2 := by
      rw [add_mul, div_mul_cancel₀ hB (ne_of_gt hε2), one_mul]
    rw [hexp] at hscal
    exact hscal
  have hfinal : hB + ε ^ 2 ≤ hB := (le_of_lt hkey).trans (le_trans hcard hsum)
  exact absurd hfinal (by linarith)

/-! ### Block B: finitely-supported spectral operators are compact -/

/-- A spectral operator with finitely-supported coefficient family has
finite-dimensional range: `⟪S x, y⟫ = specPair c x y = 0` for `y` orthogonal to
the span of the (finitely many) `v i` with `c i ≠ 0`. -/
private theorem specOperator_mem_span_of_finite_support {c : ι → ℝ} {C : ℝ}
    (hc : ∀ i, |c i| ≤ C) (hC0 : 0 ≤ C) (hv : Orthonormal ℝ v)
    (hs : {i : ι | c i ≠ 0}.Finite) (x : L2) :
    specOperator hc hC0 hv x ∈ Submodule.span ℝ (v '' {i : ι | c i ≠ 0}) := by
  classical
  set E : Submodule ℝ L2 := Submodule.span ℝ (v '' {i : ι | c i ≠ 0}) with hEdef
  haveI : FiniteDimensional ℝ E := FiniteDimensional.span_of_finite ℝ (hs.image v)
  have h1 : specOperator hc hC0 hv x ∈ Eᗮᗮ := by
    refine (Submodule.mem_orthogonal' (K := Eᗮ) (specOperator hc hC0 hv x)).mpr fun w hw => ?_
    rw [specOperator_apply, inner_specOperatorFun hc hC0 hv, specPair]
    have hterm : ∀ i, c i * inner ℝ (v i) x * inner ℝ (v i) w = 0 := by
      intro i
      by_cases hi : c i = 0
      · simp [hi]
      · have hvi : v i ∈ E := Submodule.subset_span (Set.mem_image_of_mem v hi)
        have h0 := (Submodule.mem_orthogonal (K := E) w).mp hw (v i) hvi
        rw [h0]
        ring
    exact Eq.trans (tsum_congr hterm) (by simp)
  rw [Submodule.orthogonal_orthogonal (K := E)] at h1
  exact h1

/-- **Finitely-supported spectral operators are compact**: the operator factors
through its finite-dimensional range (`isCompactOperator_of_locallyCompactSpace_rng`
+ `IsCompactOperator.comp_clm`). -/
private theorem isCompactOperator_specOperator_of_finite_support {c : ι → ℝ} {C : ℝ}
    (hc : ∀ i, |c i| ≤ C) (hC0 : 0 ≤ C) (hv : Orthonormal ℝ v)
    (hs : {i : ι | c i ≠ 0}.Finite) :
    IsCompactOperator (specOperator hc hC0 hv) := by
  classical
  set E : Submodule ℝ L2 := Submodule.span ℝ (v '' {i : ι | c i ≠ 0}) with hEdef
  haveI : FiniteDimensional ℝ E := FiniteDimensional.span_of_finite ℝ (hs.image v)
  have hmem : ∀ x : L2, specOperator hc hC0 hv x ∈ E :=
    specOperator_mem_span_of_finite_support hc hC0 hv hs
  -- the corestriction to `E` is a continuous linear map
  obtain ⟨K, hKapp⟩ : ∃ K : L2 →L[ℝ] E, ∀ x, (K x : L2) = specOperator hc hC0 hv x :=
    ⟨LinearMap.mkContinuous
      (LinearMap.codRestrict E (specOperator hc hC0 hv).toLinearMap hmem)
      ‖specOperator hc hC0 hv‖ (fun x => by
        rw [Submodule.coe_norm, LinearMap.codRestrict_apply]
        exact ContinuousLinearMap.le_opNorm _ _), fun x => rfl⟩
  have hcomp : specOperator hc hC0 hv = E.subtypeL.comp K := by
    refine ContinuousLinearMap.ext fun x => ?_
    rw [ContinuousLinearMap.comp_apply]
    exact (hKapp x).symm
  rw [hcomp]
  exact (isCompactOperator_of_locallyCompactSpace_rng E.subtypeL).comp_clm K

/-! ### Block C: truncations approximate the spectral operator in norm -/

/-- If two bounded coefficient families differ pointwise by at most `δ`, the
corresponding spectral operators differ in operator norm by at most `δ`
(operator-form Cauchy–Schwarz `abs_specPair_le` + `norm_specOperator_le`). -/
private theorem norm_specOperator_sub_of_bound {c₀ c₁ : ι → ℝ} {bnd δ : ℝ}
    (hb0 : ∀ i, |c₀ i| ≤ bnd) (hb1 : ∀ i, |c₁ i| ≤ bnd) (hC0 : 0 ≤ bnd)
    (hv : Orthonormal ℝ v) (hδ : 0 ≤ δ) (hδb : ∀ i, |c₁ i - c₀ i| ≤ δ) :
    ‖specOperator hb1 hC0 hv - specOperator hb0 hC0 hv‖ ≤ δ := by
  have hEq : specOperator hb1 hC0 hv - specOperator hb0 hC0 hv
      = specOperator hδb hδ hv := by
    refine ContinuousLinearMap.ext fun x => eq_of_forall_inner_eq fun y => ?_
    rw [sub_apply, inner_sub_left, inner_specOperator hb1 hC0 hv x y,
      inner_specOperator hb0 hC0 hv x y, inner_specOperator hδb hδ hv x y]
    refine Eq.trans (((summable_specPair hb1 hC0 hv x y).hasSum.sub
      (summable_specPair hb0 hC0 hv x y).hasSum).tsum_eq.symm) ?_
    refine tsum_congr fun i => ?_
    ring
  rw [hEq]
  exact norm_specOperator_le hδb hδ hv

/-! ### Block D: compactness of the positive square root -/

/-- **The positive square root is compact** (M1-D2 gap 1, first half): the
spectral square root of `T`, with eigen-coefficients `√κ` where `∑' κ i ^ 2 < ∞`,
is a compact operator.  Route: finitely-supported truncations (compact by
finite-dimensional range) converge to it in operator norm at rate `1/(n+1)`
(the squared-threshold level sets of `κ` are finite), and
`isCompactOperator_of_tendsto` closes.  **No `hconst`-type premise.** -/
theorem sqrtOp_isCompactOperator {T : L2 →L[ℝ] L2} {κ : ι → ℝ}
    (hv : Orthonormal ℝ v) (he : ∀ i, T (v i) = κ i • v i) (hκ0 : ∀ i, 0 ≤ κ i)
    (hκ : Summable (fun i => κ i ^ 2)) :
    IsCompactOperator (sqrtOp hv he hκ0) := by
  classical
  have hS : sqrtOp hv he hκ0 = specOperator (c := fun i => Real.sqrt (κ i))
      (fun i => sqrt_kappa_le hv he hκ0 i) (Real.sqrt_nonneg ‖T‖) hv := rfl
  rw [hS]
  have hb0 : ∀ i, |Real.sqrt (κ i)| ≤ Real.sqrt ‖T‖ := fun i => sqrt_kappa_le hv he hκ0 i
  have hC0 : (0:ℝ) ≤ Real.sqrt ‖T‖ := Real.sqrt_nonneg ‖T‖
  -- per level n: the truncation below the 1/(n+1)-coefficient level
  have hper : ∀ n : ℕ, ∃ S : L2 →L[ℝ] L2,
      (‖S - specOperator (c := fun i => Real.sqrt (κ i)) hb0 hC0 hv‖
        ≤ (1:ℝ)/((n:ℝ)+1)) ∧ IsCompactOperator S := by
    intro n
    have hsn : {i : ι | ((1:ℝ)/((n:ℝ)+1)) ^ 2 ≤ κ i}.Finite :=
      setFinite_above_threshold hκ0 hκ (by positivity)
    set s : Finset ι := hsn.toFinset with hsdef
    refine ⟨specOperator
      (c := fun i => if i ∈ s then Real.sqrt (κ i) else 0)
      (fun i => by
        by_cases hi : i ∈ s
        · simpa [hi] using hb0 i
        · rw [if_neg hi]; simpa using hC0) hC0 hv, ?_, ?_⟩
    · refine norm_specOperator_sub_of_bound hb0
        (fun i => by
          by_cases hi : i ∈ s
          · simpa [hi] using hb0 i
          · rw [if_neg hi]; simpa using hC0) hC0 hv (by positivity) ?_
      intro i
      by_cases hi : i ∈ s
      · rw [if_pos hi, sub_self, abs_zero]
        exact div_nonneg zero_le_one (by positivity)
      · have hmem : ¬(((1:ℝ)/((n:ℝ)+1)) ^ 2 ≤ κ i) := by
          simpa [hsdef, Finset.mem_coe, Set.mem_setOf_eq] using hi
        have hκlt : κ i < ((1:ℝ)/((n:ℝ)+1)) ^ 2 := lt_of_not_ge hmem
        have hsqrt : Real.sqrt (κ i) < (1:ℝ)/((n:ℝ)+1) := by
          have h := Real.sqrt_lt_sqrt (hκ0 i) hκlt
          rwa [Real.sqrt_sq (by positivity)] at h
        rw [if_neg hi, zero_sub, abs_neg, abs_of_nonneg (Real.sqrt_nonneg _)]
        exact le_of_lt hsqrt
    · refine isCompactOperator_specOperator_of_finite_support
        (fun i => by
          by_cases hi : i ∈ s
          · simpa [hi] using hb0 i
          · rw [if_neg hi]; simpa using hC0) hC0 hv ?_
      refine Set.Finite.subset (Finset.finite_toSet s) fun i hi => ?_
      by_cases him : i ∈ s
      · exact Finset.mem_coe.mpr him
      · simp [him] at hi
  have hmain : ∃ SN : ℕ → (L2 →L[ℝ] L2),
      (∀ n, ‖SN n - specOperator (c := fun i => Real.sqrt (κ i)) hb0 hC0 hv‖
        ≤ (1:ℝ)/((n:ℝ)+1)) ∧ ∀ n, IsCompactOperator (SN n) :=
    ⟨fun n => (hper n).choose, fun n => (hper n).choose_spec.1,
      fun n => (hper n).choose_spec.2⟩
  obtain ⟨SN, hnorm, hcomp⟩ := hmain
  refine isCompactOperator_of_tendsto (ι := ℕ) (l := Filter.atTop)
    (F := fun n => SN n) (f := specOperator (c := fun i => Real.sqrt (κ i)) hb0 hC0 hv) ?_
    (Filter.Eventually.of_forall hcomp)
  rw [Metric.tendsto_atTop]
  intro ε hε
  refine ⟨Nat.ceil (1/ε), fun n hn => ?_⟩
  rw [dist_eq_norm]
  have hcast : ((Nat.ceil (1/ε) : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hge : (1:ℝ)/ε + 1 ≤ (n:ℝ) + 1 := by linarith [Nat.le_ceil (1/ε)]
  have hlt : (1:ℝ)/((n:ℝ)+1) < ε := by
    rw [div_lt_iff₀ (by positivity : (0:ℝ) < (n:ℝ) + 1)]
    have hmul : ε * ((1:ℝ)/ε + 1) ≤ ε * ((n:ℝ) + 1) := mul_le_mul_of_nonneg_left hge hε.le
    have hkey : ε * ((1:ℝ)/ε + 1) = 1 + ε := by field_simp
    nlinarith [hε, hmul, hkey]
  exact lt_of_le_of_lt (hnorm n) hlt

/-! ### Block E: compactness of the model `B = S ∘ M_omega ∘ S` -/

/-- **The model `B = S ∘ M_omega ∘ S` is compact** (M1-D2 gap 1, second half):
compactness of the square root transports through composition with the bounded
multiplication operator (`IsCompactOperator.clm_comp`). -/
theorem Bop_isCompactOperator {T : L2 →L[ℝ] L2} {κ : ι → ℝ}
    (hv : Orthonormal ℝ v) (he : ∀ i, T (v i) = κ i • v i) (hκ0 : ∀ i, 0 ≤ κ i)
    (hκ : Summable (fun i => κ i ^ 2))
    (omega : ℝ → ℝ) (hm : Measurable omega) {MR : ℝ}
    (hess : ∀ᵐ x ∂vol, |omega x| ≤ MR) :
    IsCompactOperator (Bop hv he hκ0 omega hm hess) := by
  have hBdef : Bop hv he hκ0 omega hm hess
      = (sqrtOp hv he hκ0).comp ((mulOperator omega hm hess).comp (sqrtOp hv he hκ0)) := rfl
  rw [hBdef]
  exact (sqrtOp_isCompactOperator hv he hκ0 hκ).comp_clm
    ((mulOperator omega hm hess).comp (sqrtOp hv he hκ0))

end HS

