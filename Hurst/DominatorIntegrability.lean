import Hurst.ContinuumCutoffAssembly
import Hurst.TwoFactorShiftBound

/-!
# Integrability of the continuum cutoff dominator

This file discharges the integrability hypothesis `hdom` of
`Hurst.continuumCutoffRemoval_of_integrable_dominator`
(`Hurst.ContinuumCutoffAssembly`) from explicit uniform one- and two-factor shift bounds.

The dominator `continuumCutoffDominator k psi c omega` is the product over the cycle of
vertex factors (cube indicator times `|omega|` times `|c|`) and edge factors
`|z i - z (finCyclicSucc i)|^(-psi)`.  Writing the pi-integral as an iterated integral
(peeling the first coordinate to the *inner* integral, `lintegral_pi_cons`), the first
coordinate of the cycle carries two edges and is bounded by the two-factor shift bound
`hν2`, while the remaining open chain is bounded inductively by the one-factor shift
bound `hν1` (`chainOC_lintegral_le`).  The result is the explicit finite bound

`∫⁻ z, dominator z ≤ ofReal (2 * |c| * B * (|c| * B * ν₂) * (|c| * B * ν₁)^(k-2))`,

hence the dominator is integrable (`continuumCutoffDominator_integrable`).
-/

open scoped ENNReal
open Set MeasureTheory Filter

namespace Hurst

noncomputable section

/-! ### Measurability of real powers and finite products -/

lemma measurable_rpow_of_nonneg {α : Type*} [MeasurableSpace α] {f : α → ℝ}
    (hf : Measurable f) (hpos : ∀ x, 0 ≤ f x) (r : ℝ) : Measurable (fun x => f x ^ r) := by
  have hfun : (fun x : α => f x ^ r)
      = fun x => if f x = 0 then (if r = 0 then (1 : ℝ) else 0)
          else Real.exp (Real.log (f x) * r) := by
    funext x
    rw [Real.rpow_def_of_nonneg (hpos x) r]
  rw [hfun]
  refine Measurable.ite (hf (measurableSet_singleton (0 : ℝ))) measurable_const ?_
  exact Real.measurable_exp.comp ((Real.measurable_log.comp hf).mul measurable_const)

lemma measurable_eval_apply {ι α : Type*} [MeasurableSpace α] (i : ι) :
    Measurable (fun f : ι → α => f i) := by
  have h := Measurable.eval (a := i) (g := (id : (ι → α) → (ι → α)))
    (measurable_id (α := ι → α))
  exact h

lemma measurable_abs_rpow (r : ℝ) (y : ℝ) :
    Measurable (fun x : ℝ => |x - y| ^ r) :=
  measurable_rpow_of_nonneg ((measurable_id.sub measurable_const).abs)
    (fun x => abs_nonneg _) r

lemma measurable_finset_prod_real {ι : Type*} {s : Finset ι} {f : ι → ℝ → ℝ}
    (h : ∀ i ∈ s, Measurable (f i)) : Measurable (fun a => ∏ i ∈ s, f i a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using measurable_const
  | insert i s hi ih =>
      simp only [Finset.prod_insert hi]
      exact (h i (Finset.mem_insert_self i s)).mul
        (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

lemma measurable_finset_prod_ennreal {ι : Type*} {s : Finset ι} {f : ι → ℝ → ℝ≥0∞}
    (h : ∀ i ∈ s, Measurable (f i)) : Measurable (fun a => ∏ i ∈ s, f i a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using measurable_const
  | insert i s hi ih =>
      simp only [Finset.prod_insert hi]
      exact (h i (Finset.mem_insert_self i s)).mul
        (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

lemma ofReal_finset_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ) (h : ∀ i ∈ s, 0 ≤ f i) :
    ENNReal.ofReal (∏ i ∈ s, f i) = ∏ i ∈ s, ENNReal.ofReal (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi]
      have hprod := Finset.prod_nonneg (fun j hj => h j (Finset.mem_insert_of_mem hj))
      calc ENNReal.ofReal (f i * ∏ j ∈ s, f j)
          = ENNReal.ofReal (f i) * ENNReal.ofReal (∏ j ∈ s, f j) :=
            ENNReal.ofReal_mul (h i (Finset.mem_insert_self i s))
        _ = ∏ j ∈ insert i s, ENNReal.ofReal (f j) := by
            simp only [Finset.prod_insert hi, ← ih fun j hj => h j (Finset.mem_insert_of_mem hj)]

/-! ### One-dimensional vertex and edge factors -/

/-- The cube indicator as an extended-real function. -/
def cubeInd (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) x)

/-- The vertex factor of the dominator: cube indicator times `|omega|` times `|c|`. -/
def domVert (c : ℝ) (omega : ℝ → ℝ) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) x * |omega x| * |c|)

/-- The edge factor of the dominator: `|x - y|^(-psi)`. -/
def domEdge (psi : ℝ) (x y : ℝ) : ℝ≥0∞ := ENNReal.ofReal (|x - y| ^ (-psi))

lemma measurable_cubeInd : Measurable cubeInd :=
  ENNReal.measurable_ofReal.comp (measurable_const.indicator measurableSet_Icc)

lemma measurable_domVert (c : ℝ) (omega : ℝ → ℝ) (homega : Measurable omega) :
    Measurable (domVert c omega) :=
  ENNReal.measurable_ofReal.comp
    (((measurable_const.indicator measurableSet_Icc).mul homega.abs).mul measurable_const)

lemma measurable_domEdge (psi : ℝ) (y : ℝ) : Measurable (fun x => domEdge psi x y) :=
  ENNReal.measurable_ofReal.comp (measurable_abs_rpow (-psi) y)

lemma measurable_domEdge₂ (psi : ℝ) :
    Measurable (fun p : ℝ × ℝ => domEdge psi p.1 p.2) := by
  have habs : Measurable (fun p : ℝ × ℝ => |p.1 - p.2|) :=
    (measurable_fst.sub measurable_snd).abs
  exact ENNReal.measurable_ofReal.comp
    (measurable_rpow_of_nonneg habs (fun p => abs_nonneg _) (-psi))

lemma domVert_mul_domEdge_eq (psi c : ℝ) (omega : ℝ → ℝ) (x y : ℝ) :
    domVert c omega x * domEdge psi x y
      = ENNReal.ofReal ((Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) x * |omega x| * |c| *
          |x - y| ^ (-psi)) := by
  have h1 : 0 ≤ (Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) x * |omega x| * |c| :=
    mul_nonneg (mul_nonneg
      (indicator_nonneg (fun _ _ => (zero_le_one : (0 : ℝ) ≤ 1)) x)
      (abs_nonneg (omega x))) (abs_nonneg c)
  have h2 : 0 ≤ |x - y| ^ (-psi) := Real.rpow_nonneg (abs_nonneg (x - y)) (-psi)
  unfold domVert domEdge
  rw [← ENNReal.ofReal_mul h1]

lemma domVert_le_of_bound (c B : ℝ) (omega : ℝ → ℝ)
    (hB : ∀ z ∈ Icc (-1 : ℝ) 1, |omega z| ≤ B) (x : ℝ) :
    domVert c omega x ≤ ENNReal.ofReal (|c| * B) * cubeInd x := by
  by_cases hx : x ∈ Icc (-1 : ℝ) 1
  · unfold domVert cubeInd
    simp only [Set.indicator_of_mem hx, one_mul, ENNReal.ofReal_one, mul_one]
    have hle : |omega x| * |c| ≤ |c| * B := by
      have h0 : |omega x| * |c| ≤ B * |c| :=
        mul_le_mul_of_nonneg_right (hB x hx) (abs_nonneg c)
      rw [mul_comm B] at h0
      exact h0
    exact ENNReal.ofReal_le_ofReal hle
  · unfold domVert cubeInd
    simp [Set.indicator_of_notMem hx]

lemma cubeInd_mul_domEdge_eq (psi : ℝ) (x a : ℝ) :
    cubeInd x * domEdge psi x a
      = ENNReal.ofReal ((Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) x * |x - a| ^ (-psi)) := by
  unfold cubeInd domEdge
  by_cases hx : x ∈ Icc (-1 : ℝ) 1
  · simp only [Set.indicator_of_mem hx, one_mul]
    rw [ENNReal.ofReal_one, one_mul]
  · simp [Set.indicator_of_notMem hx]

lemma cubeInd_mul_domEdge_domEdge_eq (psi : ℝ) (x a b : ℝ) :
    cubeInd x * domEdge psi x a * domEdge psi x b
      = ENNReal.ofReal ((Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) x *
          |x - a| ^ (-psi) * |x - b| ^ (-psi)) := by
  unfold cubeInd domEdge
  by_cases hx : x ∈ Icc (-1 : ℝ) 1
  · simp only [Set.indicator_of_mem hx, one_mul]
    rw [ENNReal.ofReal_one, one_mul]
    exact (ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg (x - a)) (-psi))).symm
  · simp [Set.indicator_of_notMem hx]

/-! ### The singular one-factor integrability -/

/-- Integrability of the cube-indicated Riesz factor `|x - a|^(-r)` for `0 < r < 1`. -/
lemma integrable_ind_rpow_gen (r : ℝ) (hr1 : 0 < r) (hr2 : r < 1) (a : ℝ) :
    Integrable
      ((Icc (-1 : ℝ) 1).indicator (fun x : ℝ => |x - a| ^ (-r))) (volume : Measure ℝ) := by
  have h := intervalIntegrable_abs_sub_rpow hr2 a (-2) 2
  have hset : IntegrableOn (fun x : ℝ => |x - a| ^ (-r)) (Icc (-1 : ℝ) 1)
      (volume : Measure ℝ) :=
    (intervalIntegrable_iff.mp h).mono (by
      intro x hx
      simp only [Set.mem_Icc] at hx
      simp only [Set.mem_uIoc, min_eq_left (by norm_num : (-2 : ℝ) ≤ 2),
        max_eq_right (by norm_num : (-2 : ℝ) ≤ 2)]
      exact Or.inl ⟨by linarith, by linarith⟩) le_rfl
  exact (integrable_indicator_iff measurableSet_Icc).mpr hset

/-! ### The indicator bridge from Bochner integrals to lintegrals -/

/-- Bridge: a bound on the Bochner integral of `g` over the cube gives a bound on the
lintegral of the cube-indicated `ofReal (g)`. -/
lemma ind_mul_eq_indicator (g : ℝ → ℝ) (x : ℝ) :
    (Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) x * g x
      = (Icc (-1 : ℝ) 1).indicator g x := by
  by_cases hx : x ∈ Icc (-1 : ℝ) 1
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_notMem hx]

lemma indicator_lintegral_le {g : ℝ → ℝ} (hgnn : ∀ x, 0 ≤ g x)
    (hf : Integrable ((Icc (-1 : ℝ) 1).indicator g) (volume : Measure ℝ))
    (ν : ℝ) (hν : ∫ x in Icc (-1 : ℝ) 1, g x ≤ ν) :
    ∫⁻ x : ℝ, ENNReal.ofReal ((Icc (-1 : ℝ) 1).indicator g x) ≤ ENNReal.ofReal ν := by
  have hfnn : ∀ x : ℝ, 0 ≤ (Icc (-1 : ℝ) 1).indicator g x := by
    intro x
    by_cases hx : x ∈ Icc (-1 : ℝ) 1
    · rw [← ind_mul_eq_indicator g x, Set.indicator_of_mem hx, one_mul]
    · rw [← ind_mul_eq_indicator g x, Set.indicator_of_notMem hx, zero_mul]
  rw [← ofReal_integral_eq_lintegral_ofReal hf (Filter.Eventually.of_forall hfnn)]
  refine ENNReal.ofReal_le_ofReal ?_
  have heq : ∫ x, (Icc (-1 : ℝ) 1).indicator g x = ∫ x in Icc (-1 : ℝ) 1, g x :=
    integral_indicator measurableSet_Icc
  rw [heq]
  exact hν

/-! ### One- and two-factor shift bounds for the inner integrals -/

/-- One-factor shift bound: vertex times one edge. -/
lemma vertexEdge_lintegral_le (psi c B ν₁ : ℝ) (omega : ℝ → ℝ)
    (hpsi1 : 0 < psi) (hpsi2 : 2 * psi < 1)
    (hB : ∀ z ∈ Icc (-1 : ℝ) 1, |omega z| ≤ B)
    (hν1 : ∀ a : ℝ, ∫ x in Icc (-1 : ℝ) 1, |x - a| ^ (-psi) ≤ ν₁)
    (hνpos : 0 ≤ ν₁)
    (a : ℝ) :
    ∫⁻ x : ℝ, domVert c omega x * domEdge psi x a ∂volume
      ≤ ENNReal.ofReal (|c| * B * ν₁) := by
  have hBpos : 0 ≤ B := le_trans (abs_nonneg _) (hB 0 (by simp))
  have hpoint : ∀ x : ℝ, domVert c omega x * domEdge psi x a
      ≤ ENNReal.ofReal (|c| * B) *
        ENNReal.ofReal ((Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) x *
          |x - a| ^ (-psi)) := by
    intro x
    calc domVert c omega x * domEdge psi x a
        ≤ ENNReal.ofReal (|c| * B) * cubeInd x * domEdge psi x a := by
          gcongr
          exact domVert_le_of_bound c B omega hB x
      _ = ENNReal.ofReal (|c| * B) * (cubeInd x * domEdge psi x a) := mul_assoc _ _ _
      _ = ENNReal.ofReal (|c| * B) *
            ENNReal.ofReal ((Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) x *
              |x - a| ^ (-psi)) := by rw [cubeInd_mul_domEdge_eq]
  refine le_trans (lintegral_mono hpoint) ?_
  rw [lintegral_const_mul' (ENNReal.ofReal (|c| * B)) _ ENNReal.ofReal_ne_top]
  have hintform : ∫⁻ x : ℝ, ENNReal.ofReal ((Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) x *
      |x - a| ^ (-psi)) ∂volume
      = ∫⁻ x : ℝ, ENNReal.ofReal ((Icc (-1 : ℝ) 1).indicator (fun y : ℝ => |y - a| ^ (-psi)) x)
          ∂volume := by
    refine lintegral_congr (fun x => ?_)
    rw [ind_mul_eq_indicator (fun y : ℝ => |y - a| ^ (-psi)) x]
  rw [hintform]
  calc ENNReal.ofReal (|c| * B)
        * ∫⁻ x : ℝ, ENNReal.ofReal ((Icc (-1 : ℝ) 1).indicator (fun y : ℝ => |y - a| ^ (-psi)) x) ∂volume
      ≤ ENNReal.ofReal (|c| * B) * ENNReal.ofReal ν₁ := by
        gcongr
        exact indicator_lintegral_le (fun x => Real.rpow_nonneg (abs_nonneg (x - a)) (-psi))
          (integrable_ind_rpow_gen psi hpsi1 (by linarith : psi < 1) a) ν₁ (hν1 a)
    _ = ENNReal.ofReal (|c| * B * ν₁) :=
            (ENNReal.ofReal_mul (mul_nonneg (abs_nonneg c) hBpos)).symm

/-- Two-factor shift bound: vertex times two edges. -/
lemma vertexEdgeEdge_lintegral_le (psi c B ν₂ : ℝ) (omega : ℝ → ℝ)
    (hpsi1 : 0 < psi) (hpsi2 : 2 * psi < 1)
    (hB : ∀ z ∈ Icc (-1 : ℝ) 1, |omega z| ≤ B)
    (hν2 : ∀ a b : ℝ, ∫ x in Icc (-1 : ℝ) 1, |x - a| ^ (-psi) * |x - b| ^ (-psi) ≤ ν₂)
    (hνpos : 0 ≤ ν₂)
    (a b : ℝ) :
    ∫⁻ x : ℝ, domVert c omega x * domEdge psi x a * domEdge psi x b ∂volume
      ≤ ENNReal.ofReal (|c| * B * ν₂) := by
  have hBpos : 0 ≤ B := le_trans (abs_nonneg _) (hB 0 (by simp))
  have hint2 : Integrable
      ((Icc (-1 : ℝ) 1).indicator
        (fun x : ℝ => |x - a| ^ (-psi) * |x - b| ^ (-psi))) (volume : Measure ℝ) := by
    have h1 := integrable_ind_rpow_gen (2 * psi) (by linarith : 0 < 2 * psi)
      (by linarith : 2 * psi < 1) a
    have h2 := integrable_ind_rpow_gen (2 * psi) (by linarith : 0 < 2 * psi)
      (by linarith : 2 * psi < 1) b
    refine Integrable.mono' (h1.add h2) ?_ ?_
    · exact (Measurable.indicator
        ((measurable_abs_rpow (-psi) a).mul (measurable_abs_rpow (-psi) b))
        measurableSet_Icc).aestronglyMeasurable
    · filter_upwards with x
      by_cases hx : x ∈ Icc (-1 : ℝ) 1
      · show ‖((Icc (-1 : ℝ) 1).indicator
            (fun y : ℝ => |y - a| ^ (-psi) * |y - b| ^ (-psi)) x)‖ ≤
            ((Icc (-1 : ℝ) 1).indicator (fun y : ℝ => |y - a| ^ (-(2 * psi))) x +
              (Icc (-1 : ℝ) 1).indicator (fun y : ℝ => |y - b| ^ (-(2 * psi))) x)
        have hu2 : |x - a| ^ (-(2 * psi))
            = |x - a| ^ (-psi) * |x - a| ^ (-psi) := by
          rw [show (-(2 * psi)) = (-psi) + (-psi) from by ring,
            Real.rpow_add' (abs_nonneg (x - a)) (by linarith)]
        have hv2 : |x - b| ^ (-(2 * psi))
            = |x - b| ^ (-psi) * |x - b| ^ (-psi) := by
          rw [show (-(2 * psi)) = (-psi) + (-psi) from by ring,
            Real.rpow_add' (abs_nonneg (x - b)) (by linarith)]
        rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Set.indicator_of_mem hx,
          Real.norm_eq_abs, abs_of_nonneg
            (mul_nonneg (Real.rpow_nonneg (abs_nonneg (x - a)) (-psi))
              (Real.rpow_nonneg (abs_nonneg (x - b)) (-psi))), hu2, hv2]
        nlinarith [sq_nonneg (|x - a| ^ (-psi) - |x - b| ^ (-psi))]
      · show ‖((Icc (-1 : ℝ) 1).indicator
            (fun y : ℝ => |y - a| ^ (-psi) * |y - b| ^ (-psi)) x)‖ ≤
            ((Icc (-1 : ℝ) 1).indicator (fun y : ℝ => |y - a| ^ (-(2 * psi))) x +
              (Icc (-1 : ℝ) 1).indicator (fun y : ℝ => |y - b| ^ (-(2 * psi))) x)
        rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
        simp
  have hpoint : ∀ x : ℝ, domVert c omega x * domEdge psi x a * domEdge psi x b
      ≤ ENNReal.ofReal (|c| * B) *
        ENNReal.ofReal ((Icc (-1 : ℝ) 1).indicator
          (fun y : ℝ => |y - a| ^ (-psi) * |y - b| ^ (-psi)) x) := by
    intro x
    calc domVert c omega x * domEdge psi x a * domEdge psi x b
        ≤ (ENNReal.ofReal (|c| * B) * cubeInd x) * (domEdge psi x a * domEdge psi x b) := by
          rw [mul_assoc]
          exact mul_le_mul (domVert_le_of_bound c B omega hB x)
            (le_refl (domEdge psi x a * domEdge psi x b))
            (mul_nonneg (by positivity) (by positivity)) (by positivity)
      _ = ENNReal.ofReal (|c| * B) * (cubeInd x * domEdge psi x a * domEdge psi x b) := by ring
      _ = ENNReal.ofReal (|c| * B) * ENNReal.ofReal
            ((Icc (-1 : ℝ) 1).indicator (fun y : ℝ => |y - a| ^ (-psi) * |y - b| ^ (-psi)) x) := by
          rw [cubeInd_mul_domEdge_domEdge_eq]
  refine le_trans (lintegral_mono hpoint) ?_
  rw [lintegral_const_mul' (ENNReal.ofReal (|c| * B)) _ ENNReal.ofReal_ne_top]
  have hintform : ∀ x : ℝ, ENNReal.ofReal ((Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) x *
      |x - a| ^ (-psi) * |x - b| ^ (-psi))
      = ENNReal.ofReal ((Icc (-1 : ℝ) 1).indicator
          (fun y : ℝ => |y - a| ^ (-psi) * |y - b| ^ (-psi)) x) := by
    intro x
    rw [mul_assoc, ind_mul_eq_indicator (fun y : ℝ => |y - a| ^ (-psi) * |y - b| ^ (-psi)) x]
  have hintform2 : ∫⁻ x : ℝ, ENNReal.ofReal ((Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) x *
      |x - a| ^ (-psi) * |x - b| ^ (-psi)) ∂volume
      = ∫⁻ x : ℝ, ENNReal.ofReal ((Icc (-1 : ℝ) 1).indicator
          (fun y : ℝ => |y - a| ^ (-psi) * |y - b| ^ (-psi)) x) ∂volume :=
    lintegral_congr (fun x => hintform x)
  rw [hintform2]
  calc ENNReal.ofReal (|c| * B)
        * ∫⁻ x : ℝ, ENNReal.ofReal ((Icc (-1 : ℝ) 1).indicator
            (fun y : ℝ => |y - a| ^ (-psi) * |y - b| ^ (-psi)) x) ∂volume
      ≤ ENNReal.ofReal ν₂ :=
        indicator_lintegral_le
          (fun x => mul_nonneg (Real.rpow_nonneg (abs_nonneg (x - a)) (-psi))
            (Real.rpow_nonneg (abs_nonneg (x - b)) (-psi)))
          hint2 ν₂ (hν2 a b)
    _ ≤ ENNReal.ofReal (|c| * B) * ENNReal.ofReal ν₂ := by
        gcongr
    _ = ENNReal.ofReal (|c| * B * ν₂) :=
            (ENNReal.ofReal_mul (mul_nonneg (abs_nonneg c) hBpos)).symm

/-- Vertex-only bound over the whole line (uses the cube indicator). -/
lemma vertex_lintegral_le (c B : ℝ) (omega : ℝ → ℝ)
    (hB : ∀ z ∈ Icc (-1 : ℝ) 1, |omega z| ≤ B) :
    ∫⁻ x : ℝ, domVert c omega x ∂volume ≤ ENNReal.ofReal (2 * |c| * B) := by
  have hBpos : 0 ≤ B := le_trans (abs_nonneg _) (hB 0 (by simp))
  refine le_trans (lintegral_mono (fun x => domVert_le_of_bound c B omega hB x)) ?_
  rw [lintegral_const_mul (ENNReal.ofReal (|c| * B)) measurable_cubeInd]
  have hgnn1 : ∀ x : ℝ, 0 ≤ (1 : ℝ) := fun _ => le_of_lt (by norm_num)
  have hf1 : Integrable ((Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)))
      (volume : Measure ℝ) := (integrable_const (1 : ℝ)).indicator measurableSet_Icc
  have hci : ∫⁻ x : ℝ, cubeInd x ∂volume = ENNReal.ofReal 2 := by
    have h := indicator_lintegral_le (g := fun _ : ℝ => (1 : ℝ)) hgnn1 hf1 2 (by norm_num)
    simpa [cubeInd] using h
  rw [hci]
  have h2c : (2 : ℝ) * (|c| * B) = |c| * B * 2 := by ring
  rw [← ENNReal.ofReal_mul (mul_nonneg (abs_nonneg c) hBpos), h2c]
  exact le_refl _

/-! ### Peeling the first coordinate of a pi-integral to the inner integral -/

lemma lintegral_pi_cons {n : ℕ} {G : (Fin (n+1) → ℝ) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ u : Fin (n+1) → ℝ, G u ∂(Measure.pi fun _ : Fin (n+1) => (volume : Measure ℝ))
      = ∫⁻ t : Fin n → ℝ, ∫⁻ x : ℝ, G (Fin.cons x t) ∂volume
          ∂(Measure.pi fun _ : Fin n => (volume : Measure ℝ)) := by
  have hmp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => (volume : Measure ℝ)) 0).symm
  rw [← hmp.lintegral_comp_emb
    (MeasurableEquiv.measurableEmbedding
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm) G]
  rw [lintegral_prod_symm'
    (f := fun p : ℝ × (Fin n → ℝ) =>
      G ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm p))
    (hG.comp (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm.measurable)]
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_zero]
  exact rfl

/-! ### The open chain -/

/-- The open-chain integrand on `n+1` vertices: vertex factors on all coordinates and
edge factors on consecutive pairs. -/
def chainOC (psi c : ℝ) (omega : ℝ → ℝ) (n : ℕ) (t : Fin (n+1) → ℝ) : ℝ≥0∞ :=
  (∏ j : Fin (n+1), domVert c omega (t j)) *
  (∏ j : Fin n, domEdge psi (t j) (t j.succ))

lemma chainOC_cons (psi c : ℝ) (omega : ℝ → ℝ) (n : ℕ) (x : ℝ) (t : Fin (n+1) → ℝ) :
    chainOC psi c omega (n+1) (Fin.cons x t)
      = domVert c omega x * domEdge psi x (t 0) * chainOC psi c omega n t := by
  unfold chainOC
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring

lemma measurable_chainOC (psi c : ℝ) (omega : ℝ → ℝ) (homega : Measurable omega) (n : ℕ) :
    Measurable (chainOC psi c omega n) := by
  have hvb : ∀ j : Fin (n+1), Measurable
      (fun t : Fin (n+1) → ℝ => domVert c omega (t j)) := fun j =>
    (measurable_domVert c omega homega).comp (measurable_eval_apply j)
  have hee : ∀ j : Fin n, Measurable
      (fun t : Fin (n+1) → ℝ => domEdge psi (t (Fin.castSucc j)) (t (Fin.succ j))) := fun j =>
    (measurable_domEdge₂ psi).comp
      ((measurable_eval_apply (Fin.castSucc j)).prodMk
        (measurable_eval_apply (Fin.succ j)))
  unfold chainOC
  exact (measurable_finset_prod_ennreal (fun j _ => hvb j)).mul
    (measurable_finset_prod_ennreal (fun j _ => hee j))

lemma chainOC_lintegral_le (psi c B ν₁ : ℝ) (omega : ℝ → ℝ)
    (hpsi1 : 0 < psi) (hpsi2 : 2 * psi < 1)
    (hB : ∀ z ∈ Icc (-1 : ℝ) 1, |omega z| ≤ B)
    (hν1 : ∀ a : ℝ, ∫ x in Icc (-1 : ℝ) 1, |x - a| ^ (-psi) ≤ ν₁)
    (hνpos : 0 ≤ ν₁) (homega : Measurable omega) (n : ℕ) :
    ∫⁻ t : Fin (n+1) → ℝ, chainOC psi c omega n t
        ∂(Measure.pi fun _ : Fin (n+1) => (volume : Measure ℝ))
      ≤ ENNReal.ofReal (2 * |c| * B) * ENNReal.ofReal (|c| * B * ν₁) ^ n := by
  induction n with
  | zero =>
      rw [lintegral_pi_cons (G := chainOC psi c omega 0)
        (measurable_chainOC psi c omega homega 0)]
      have hcons : ∀ (t : Fin 0 → ℝ) (x : ℝ),
          chainOC psi c omega 0 (Fin.cons x t) = domVert c omega x := by
        intro t x
        simp [chainOC]
      simp only [hcons]
      have hvolume : (Measure.pi fun _ : Fin 0 => (volume : Measure ℝ))
          = Measure.dirac (Fin.elim0) :=
        MeasureTheory.Measure.volume_pi_eq_dirac (x := Fin.elim0)
      rw [hvolume, lintegral_dirac]
      exact vertex_lintegral_le c B omega hB
  | succ n ih =>
      rw [lintegral_pi_cons (G := chainOC psi c omega (n+1))
        (measurable_chainOC psi c omega homega (n+1))]
      rw [chainOC_cons]
      have hmeas2 : ∀ t : Fin (n+1) → ℝ, Measurable
          (fun x : ℝ => domVert c omega x * domEdge psi x (t 0)) := fun t =>
        (measurable_domVert c omega homega).mul (measurable_domEdge psi (t 0))
      have hstep : ∀ t : Fin (n+1) → ℝ,
          ∫⁻ x : ℝ, domVert c omega x * domEdge psi x (t 0) * chainOC psi c omega n t ∂volume
            ≤ ENNReal.ofReal (|c| * B * ν₁) * chainOC psi c omega n t := by
        intro t
        rw [← lintegral_const_mul (chainOC psi c omega n t) (hmeas2 t)]
        exact (mul_comm _ _) ▸
          mul_le_mul_of_nonneg_left
            (vertexEdge_lintegral_le psi c B ν₁ omega hpsi1 hpsi2 hB hν1 hνpos (t 0))
            (le_of_eq rfl)
      refine le_trans (lintegral_mono hstep) ?_
      rw [lintegral_const_mul (ENNReal.ofReal (|c| * B * ν₁))
        (measurable_chainOC psi c omega homega n)]
      calc ENNReal.ofReal (|c| * B * ν₁)
            * ∫⁻ t : Fin (n+1) → ℝ, chainOC psi c omega n t
                ∂(Measure.pi fun _ : Fin (n+1) => (volume : Measure ℝ))
          ≤ ENNReal.ofReal (|c| * B * ν₁)
              * (ENNReal.ofReal (2 * |c| * B) * ENNReal.ofReal (|c| * B * ν₁) ^ n) :=
            mul_le_mul_of_nonneg_left ih (le_of_eq rfl)
      _ = ENNReal.ofReal (2 * |c| * B) * ENNReal.ofReal (|c| * B * ν₁) ^ (n + 1) := by
            rw [pow_succ]
            ring

/-! ### The dominator, peeled -/

set_option maxHeartbeats 1000000 in
lemma dominator_cons (psi c : ℝ) (omega : ℝ → ℝ) (n : ℕ) (x : ℝ) (t : Fin (n+1) → ℝ) :
    ENNReal.ofReal (continuumCutoffDominator (n+2) psi c omega (Fin.cons x t))
      = domVert c omega x * domEdge psi x (t 0) * domEdge psi (t (Fin.last n)) x *
        chainOC psi c omega (n+1) t := by
  have hprod : ENNReal.ofReal (continuumCutoffDominator (n+2) psi c omega (Fin.cons x t))
      = ∏ i : Fin (n+2), ENNReal.ofReal
          ((Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) (Fin.cons x t i) *
            |omega (Fin.cons x t i)| * |c| *
            |Fin.cons x t i - Fin.cons x t (finCyclicSucc i)| ^ (-psi)) := by
    show ENNReal.ofReal (∏ i : Fin (n+2),
        (Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) (Fin.cons x t i) *
          |omega (Fin.cons x t i)| * |c| *
          |Fin.cons x t i - Fin.cons x t (finCyclicSucc i)| ^ (-psi)) = _
    exact ofReal_finset_prod _ _ (fun i _ => by positivity)
  rw [hprod]
  have hterm : ∀ i : Fin (n+2),
      ENNReal.ofReal ((Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) (Fin.cons x t i) *
        |omega (Fin.cons x t i)| * |c| *
        |Fin.cons x t i - Fin.cons x t (finCyclicSucc i)| ^ (-psi))
      = domVert c omega (Fin.cons x t i) *
        domEdge psi (Fin.cons x t i) (Fin.cons x t (finCyclicSucc i)) :=
    fun i => domVert_mul_domEdge_eq psi c omega _ _
  rw [Finset.prod_congr rfl (fun i _ => hterm i), Finset.prod_mul_distrib,
    Fin.prod_univ_succ, Fin.prod_univ_succ]
  have hcyc0 : finCyclicSucc (0 : Fin (n+2)) = (1 : Fin (n+2)) := by
    simp only [finCyclicSucc]
    exact Fin.ext (by simp; omega)
  have hlast : finCyclicSucc (Fin.succ (Fin.last n)) = (0 : Fin (n+2)) := by
    simp only [finCyclicSucc, Fin.val_succ, Fin.val_last]
    exact Fin.ext (by omega)
  have hmid : ∀ j : Fin n,
      Fin.cons x t (finCyclicSucc (Fin.succ (Fin.castSucc j))) = t (Fin.succ j) := by
    intro j
    have hc : finCyclicSucc (Fin.succ (Fin.castSucc j))
        = (Fin.succ (Fin.succ j) : Fin (n+1)) := by
      simp only [finCyclicSucc, Fin.val_succ, Fin.val_castSucc]
      exact Fin.ext (by simp; omega)
    rw [hc, Fin.cons_succ x t (Fin.succ j)]
  rw [hcyc0, Fin.cons_zero, Fin.cons_succ x t (0 : Fin (n+1))]
  rw [Fin.prod_univ_castSucc]
  have hcast1 : ∀ j : Fin n, Fin.cons x t (Fin.castSucc j) = t j := fun j =>
    congrArg t (Fin.ext rfl)
  have hlastc : Fin.cons x t (finCyclicSucc (Fin.succ (Fin.last n))) = x := by
    rw [hlast, Fin.cons_zero]
  simp only [hmid, hcast1, hlastc]
  ring

/-- Measurability of the dominator. -/
lemma measurable_dominator (k : ℕ) (psi c : ℝ) (omega : ℝ → ℝ) (homega : Measurable omega) :
    Measurable (continuumCutoffDominator k psi c omega) := by
  show Measurable (fun z => ∏ i : Fin k,
    (Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) (z i) *
      |omega (z i)| * |c| * |z i - z (finCyclicSucc i)| ^ (-psi))
  have hev : ∀ i : Fin k, Measurable (fun z : Fin k → ℝ => z i) := fun i =>
    measurable_eval_apply i
  exact measurable_finset_prod_real (fun i _ =>
    (((measurable_const.indicator measurableSet_Icc).comp (hev i)).mul
      (homega.abs.comp (hev i))).mul
      (measurable_rpow_of_nonneg ((hev i).sub (hev (finCyclicSucc i))).abs
        (fun z => abs_nonneg _) (-psi)))

/-- The explicit finite bound for the dominator's pi-lintegral. -/
set_option maxHeartbeats 1000000 in
theorem continuumCutoffDominator_lintegral_le (k : ℕ) (psi c : ℝ) (omega : ℝ → ℝ)
    (B_omega ν₁ ν₂ : ℝ) (hk : 2 ≤ k)
    (hpsi1 : 0 < psi) (hpsi2 : 2 * psi < 1)
    (homega_meas : Measurable omega)
    (hB : ∀ z ∈ Icc (-1 : ℝ) 1, |omega z| ≤ B_omega)
    (hν1 : ∀ a : ℝ, ∫ x in Icc (-1 : ℝ) 1, |x - a| ^ (-psi) ≤ ν₁)
    (hν2 : ∀ a b : ℝ, ∫ x in Icc (-1 : ℝ) 1, |x - a| ^ (-psi) * |x - b| ^ (-psi) ≤ ν₂)
    (hνpos : 0 ≤ ν₁ ∧ 0 ≤ ν₂) :
    ∫⁻ z, ENNReal.ofReal (continuumCutoffDominator k psi c omega z)
        ∂(volume : Measure (Fin k → ℝ))
      ≤ ENNReal.ofReal
          (2 * |c| * B_omega * (|c| * B_omega * ν₂) * (|c| * B_omega * ν₁) ^ (k - 2)) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
  rw [volume_pi]
  rw [lintegral_pi_cons
    (G := fun z => ENNReal.ofReal (continuumCutoffDominator (n+2) psi c omega z))
    (ENNReal.measurable_ofReal.comp (measurable_dominator (n+2) psi c omega homega_meas))]
  rw [dominator_cons]
  have hmeasfun : ∀ t : Fin (n+1) → ℝ, Measurable
      (fun x : ℝ => domVert c omega x * domEdge psi x (t 0) * domEdge psi x (t (Fin.last n))) :=
    fun t => (measurable_domVert c omega homega_meas).mul
      ((measurable_domEdge psi (t 0)).mul (measurable_domEdge psi (t (Fin.last n))))
  have hinner : ∀ t : Fin (n+1) → ℝ,
      ∫⁻ x : ℝ, domVert c omega x * domEdge psi x (t 0) * domEdge psi x (t (Fin.last n)) ∂volume
        ≤ ENNReal.ofReal (|c| * B_omega * ν₂) * chainOC psi c omega (n+1) t := by
    intro t
    rw [← lintegral_const_mul (chainOC psi c omega (n+1) t) (hmeasfun t)]
    calc (∫⁻ x : ℝ, domVert c omega x * domEdge psi x (t 0) * domEdge psi x (t (Fin.last n)) ∂volume)
        * chainOC psi c omega (n+1) t
        = chainOC psi c omega (n+1) t * ∫⁻ x : ℝ,
            domVert c omega x * domEdge psi x (t 0) * domEdge psi x (t (Fin.last n)) ∂volume :=
          mul_comm _ _
      _ ≤ chainOC psi c omega (n+1) t * ENNReal.ofReal (|c| * B_omega * ν₂) :=
          mul_le_mul_of_nonneg_left
            (vertexEdgeEdge_lintegral_le psi c B_omega ν₂ omega hpsi1 hpsi2 hB hν2 hνpos.2
              (t 0) (t (Fin.last n))) (by positivity)
      _ = ENNReal.ofReal (|c| * B_omega * ν₂) * chainOC psi c omega (n+1) t := mul_comm _ _
  refine le_trans (lintegral_mono hinner) ?_
  rw [lintegral_const_mul (ENNReal.ofReal (|c| * B_omega * ν₂))
    (measurable_chainOC psi c omega homega_meas (n+1))]
  have hchain := chainOC_lintegral_le psi c B_omega ν₁ omega hpsi1 hpsi2 hB hν1 hνpos.1
    homega_meas n
  have hBpos : 0 ≤ B_omega := le_trans (abs_nonneg _) (hB 0 (by simp))
  calc ENNReal.ofReal (|c| * B_omega * ν₂)
        * ∫⁻ t : Fin (n+1) → ℝ, chainOC psi c omega (n+1) t
            ∂(Measure.pi fun _ : Fin (n+1) => (volume : Measure ℝ))
      ≤ ENNReal.ofReal (|c| * B_omega * ν₂)
          * (ENNReal.ofReal (2 * |c| * B_omega) * ENNReal.ofReal (|c| * B_omega * ν₁) ^ n) :=
        mul_le_mul_of_nonneg_left hchain (le_of_eq rfl)
    _ = ENNReal.ofReal
          (2 * |c| * B_omega * (|c| * B_omega * ν₂) * (|c| * B_omega * ν₁) ^ (n + 2 - 2)) := by
        rw [pow_succ, ← ENNReal.ofReal_mul
          (mul_nonneg (mul_nonneg (abs_nonneg c) hBpos) hνpos.2)
          (mul_nonneg (by nlinarith) (mul_nonneg (mul_nonneg (abs_nonneg c) hBpos) hνpos.1)),
          ← ENNReal.ofReal_mul (by nlinarith) (by nlinarith), ← pow_succ']
        congr 2
        ring

/-- **Integrability of the continuum cutoff dominator.** -/
theorem continuumCutoffDominator_integrable
    (k : ℕ) (psi c : ℝ) (omega : ℝ → ℝ) (B_omega ν₁ ν₂ : ℝ)
    (hk : 2 ≤ k) (hpsi1 : 0 < psi) (hpsi2 : 2 * psi < 1)
    (homega_meas : Measurable omega)
    (homegaB : ∀ z ∈ Icc (-1 : ℝ) 1, |omega z| ≤ B_omega)
    (hν1 : ∀ a : ℝ, ∫ x in Icc (-1 : ℝ) 1, |x - a| ^ (-psi) ≤ ν₁)
    (hν2 : ∀ a b : ℝ, ∫ x in Icc (-1 : ℝ) 1, |x - a| ^ (-psi) * |x - b| ^ (-psi) ≤ ν₂)
    (hνpos : 0 ≤ ν₁ ∧ 0 ≤ ν₂) :
    Integrable (continuumCutoffDominator k psi c omega) (volume : Measure (Fin k → ℝ)) := by
  have hbound := continuumCutoffDominator_lintegral_le k psi c omega B_omega ν₁ ν₂ hk hpsi1
    hpsi2 homega_meas homegaB hν1 hν2 hνpos
  have hnonneg : ∀ z, 0 ≤ continuumCutoffDominator k psi c omega z := by
    intro z
    unfold continuumCutoffDominator
    exact Finset.prod_nonneg (fun i _ => by positivity)
  refine ⟨?_, (measurable_dominator k psi c omega homega_meas).aestronglyMeasurable⟩
  have heq : ∫⁻ z, ‖continuumCutoffDominator k psi c omega z‖₊
        ∂(volume : Measure (Fin k → ℝ))
      = ∫⁻ z, ENNReal.ofReal (continuumCutoffDominator k psi c omega z)
          ∂(volume : Measure (Fin k → ℝ)) := by
    refine lintegral_congr (fun z => ?_)
    rw [Real.nnnorm_of_nonneg (hnonneg z), ENNReal.coe_toNNReal]
  show (∫⁻ z, ‖continuumCutoffDominator k psi c omega z‖₊
      ∂(volume : Measure (Fin k → ℝ)) ≠ ∞)
  rw [heq, hbound]
  exact ENNReal.ofReal_ne_top

end
end Hurst

section checks
open scoped ENNReal
#check @ENNReal.ofReal_mul
#check @ENNReal.ofReal_le_ofReal
#check @ENNReal.ofReal_ne_top
#check @Set.indicator_nonneg
#check @mul_le_mul_of_nonneg_right
#check @intervalIntegral.intervalIntegrable_rpow'
#check @intervalIntegrable_iff
#check @Measurable.eval
#check @Fin.insertNth_zero'
#check @Fin.prod_univ_castSucc
#check @Measurable.prod_mk
#check @set_integral_const
#check @Real.volume_Icc
#check @MeasureTheory.Integrable.mono'
#check @ofReal_integral_eq_lintegral_ofReal
#check @Measurable.ite
#check @measurePreserving_piFinSuccAbove
#check @lintegral_prod_symm'
#check @lintegral_const_mul
#check @lintegral_const_mul'
#check @Set.mem_uIoc
#check @Real.nnnorm_of_nonneg
#check @ENNReal.coe_toNNReal
#check @integrable_indicator_iff
#check @Measurable.indicator
end checks
