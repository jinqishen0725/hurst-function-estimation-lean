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

lemma measurable_finset_prod_real {ι α : Type*} [MeasurableSpace α] {s : Finset ι}
    {f : ι → α → ℝ} (h : ∀ i ∈ s, Measurable (f i)) :
    Measurable (fun a => ∏ i ∈ s, f i a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using measurable_const
  | insert i s hi ih =>
      simp only [Finset.prod_insert hi]
      exact (h i (Finset.mem_insert_self i s)).mul
        (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

lemma measurable_finset_prod_ennreal {ι α : Type*} [MeasurableSpace α] {s : Finset ι}
    {f : ι → α → ℝ≥0∞} (h : ∀ i ∈ s, Measurable (f i)) :
    Measurable (fun a => ∏ i ∈ s, f i a) := by
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
      rw [Finset.prod_insert hi, Finset.prod_insert hi,
        ENNReal.ofReal_mul (h i (Finset.mem_insert_self i s)),
        ← ih (fun j hj => h j (Finset.mem_insert_of_mem hj))]

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

lemma domEdge_symm (psi : ℝ) (a b : ℝ) : domEdge psi a b = domEdge psi b a := by
  unfold domEdge
  rw [abs_sub_comm]

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
      = ENNReal.ofReal ((Icc (-1 : ℝ) 1).indicator
          (fun y : ℝ => |y - a| ^ (-psi) * |y - b| ^ (-psi)) x) := by
  unfold cubeInd domEdge
  by_cases hx : x ∈ Icc (-1 : ℝ) 1
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx,
      ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg (x - a)) (-psi)),
      ENNReal.ofReal_one, one_mul]
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
    · rw [Set.indicator_of_mem hx]
      exact hgnn x
    · rw [Set.indicator_of_notMem hx]
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
  calc ENNReal.ofReal (|c| * B)
        * ∫⁻ x : ℝ, ENNReal.ofReal ((Icc (-1 : ℝ) 1).indicator
            (fun y : ℝ => |y - a| ^ (-psi) * |y - b| ^ (-psi)) x) ∂volume
      ≤ ENNReal.ofReal (|c| * B) * ENNReal.ofReal ν₂ := by
          gcongr
          exact indicator_lintegral_le
            (fun x => mul_nonneg (Real.rpow_nonneg (abs_nonneg (x - a)) (-psi))
              (Real.rpow_nonneg (abs_nonneg (x - b)) (-psi)))
            hint2 ν₂ (hν2 a b)
    _ = ENNReal.ofReal (|c| * B * ν₂) :=
            (ENNReal.ofReal_mul (mul_nonneg (abs_nonneg c) hBpos)).symm

/-- Vertex-only bound over the whole line (uses the cube indicator). -/
lemma vertex_lintegral_le (c B : ℝ) (omega : ℝ → ℝ)
    (hB : ∀ z ∈ Icc (-1 : ℝ) 1, |omega z| ≤ B) :
    ∫⁻ x : ℝ, domVert c omega x ∂volume ≤ ENNReal.ofReal (2 * |c| * B) := by
  have hBpos : 0 ≤ B := le_trans (abs_nonneg _) (hB 0 (by simp))
  refine le_trans (lintegral_mono (fun x => domVert_le_of_bound c B omega hB x)) ?_
  rw [lintegral_const_mul (ENNReal.ofReal (|c| * B)) measurable_cubeInd]
  have hci : ∫⁻ x : ℝ, cubeInd x ∂volume = ENNReal.ofReal 2 := by
    have hcube : cubeInd = (Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ≥0∞)) := by
      funext x
      by_cases hx : x ∈ Icc (-1 : ℝ) 1
      · simp [cubeInd, hx]
      · simp [cubeInd, hx]
    rw [hcube, lintegral_indicator_const measurableSet_Icc, Real.volume_Icc]
    norm_num
  rw [hci, ← ENNReal.ofReal_mul (mul_nonneg (abs_nonneg c) hBpos)]
  exact le_of_eq (congrArg ENNReal.ofReal (by ring))

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
  (∏ j : Fin n, domEdge psi (t (Fin.castSucc j)) (t (Fin.succ j)))

lemma chainOC_cons (psi c : ℝ) (omega : ℝ → ℝ) (n : ℕ) (x : ℝ) (t : Fin (n+1) → ℝ)
    (u : Fin (n+2) → ℝ) (hu0 : u 0 = x) (hu : ∀ i : Fin (n+1), u i.succ = t i) :
    chainOC psi c omega (n+1) u
      = domVert c omega x * domEdge psi x (t 0) * chainOC psi c omega n t := by
  unfold chainOC
  have hv : ∏ j : Fin (n+2), domVert c omega (u j)
      = domVert c omega x * ∏ j : Fin (n+1), domVert c omega (t j) := by
    rw [Fin.prod_univ_succ, hu0]
    simp only [hu]
  have he : ∏ j : Fin (n+1), domEdge psi (u (Fin.castSucc j)) (u (Fin.succ j))
      = domEdge psi x (t 0) * ∏ j : Fin n, domEdge psi (t (Fin.castSucc j)) (t (Fin.succ j)) := by
    rw [Fin.prod_univ_succ]
    simp only [hu0, hu, ← Fin.succ_castSucc, Fin.castSucc_zero]
  rw [hv, he]
  ring

lemma measurable_chainOC (psi c : ℝ) (omega : ℝ → ℝ) (homega : Measurable omega) (n : ℕ) :
    Measurable (chainOC psi c omega n) := by
  unfold chainOC
  exact (measurable_finset_prod_ennreal
      (f := fun (j : Fin (n+1)) (t : Fin (n+1) → ℝ) => domVert c omega (t j))
      fun j _ => (measurable_domVert c omega homega).comp (measurable_eval_apply j)).mul
    (measurable_finset_prod_ennreal
      (f := fun (j : Fin n) (t : Fin (n+1) → ℝ) =>
        domEdge psi (t (Fin.castSucc j)) (t (Fin.succ j)))
      fun j _ => (measurable_domEdge₂ psi).comp
        ((measurable_eval_apply (Fin.castSucc j)).prodMk
          (measurable_eval_apply (Fin.succ j))))

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
      simpa using vertex_lintegral_le c B omega hB
  | succ n ih =>
      rw [lintegral_pi_cons (G := chainOC psi c omega (n+1))
        (measurable_chainOC psi c omega homega (n+1))]
      have hcons : ∀ (t' : Fin (n+1) → ℝ) (x : ℝ),
          chainOC psi c omega (n+1) (Fin.cons x t')
            = domVert c omega x * domEdge psi x (t' 0) * chainOC psi c omega n t' := fun t' x =>
        chainOC_cons psi c omega n x t' (Fin.cons x t')
          (show (Fin.cons x t' : Fin (n+2) → ℝ) (0 : Fin (n+2)) = x by simp) (fun i => by simp)
      simp only [hcons]
      have hmeas2 : ∀ t : Fin (n+1) → ℝ, Measurable
          (fun x : ℝ => domVert c omega x * domEdge psi x (t 0)) := fun t =>
        (measurable_domVert c omega homega).mul (measurable_domEdge psi (t 0))
      have hstep : ∀ t : Fin (n+1) → ℝ,
          ∫⁻ x : ℝ, domVert c omega x * domEdge psi x (t 0) * chainOC psi c omega n t ∂volume
            ≤ ENNReal.ofReal (|c| * B * ν₁) * chainOC psi c omega n t := by
        intro t
        rw [lintegral_mul_const _ (hmeas2 t)]
        exact mul_le_mul_of_nonneg_right
          (vertexEdge_lintegral_le psi c B ν₁ omega hpsi1 hpsi2 hB hν1 hνpos (t 0))
          zero_le
      refine le_trans (lintegral_mono hstep) ?_
      rw [lintegral_const_mul (ENNReal.ofReal (|c| * B * ν₁))
        (measurable_chainOC psi c omega homega n)]
      calc ENNReal.ofReal (|c| * B * ν₁)
            * ∫⁻ t : Fin (n+1) → ℝ, chainOC psi c omega n t
                ∂(Measure.pi fun _ : Fin (n+1) => (volume : Measure ℝ))
          ≤ ENNReal.ofReal (|c| * B * ν₁)
              * (ENNReal.ofReal (2 * |c| * B) * ENNReal.ofReal (|c| * B * ν₁) ^ n) :=
            mul_le_mul_of_nonneg_left ih zero_le
      _ = ENNReal.ofReal (2 * |c| * B) * ENNReal.ofReal (|c| * B * ν₁) ^ (n + 1) := by
            rw [pow_succ]
            ring

/-! ### The dominator, peeled -/

set_option maxHeartbeats 1000000 in
lemma dominator_cons (psi c : ℝ) (omega : ℝ → ℝ) (n : ℕ) (x : ℝ) (t : Fin (n+1) → ℝ)
    (u : Fin (n+2) → ℝ) (hu0 : u 0 = x) (hu : ∀ i : Fin (n+1), u i.succ = t i) :
    ENNReal.ofReal (continuumCutoffDominator (n+2) psi c omega u)
      = domVert c omega x * domEdge psi x (t 0) * domEdge psi (t (Fin.last n)) x *
        chainOC psi c omega n t := by
  have hcyc0 : finCyclicSucc (0 : Fin (n+2)) = Fin.succ (0 : Fin (n+1)) := by
    have h1 : (0 : Fin (n+2)).val + 1 < n + 2 := by simp only [Fin.val_zero]; omega
    simp only [finCyclicSucc, dif_pos h1]
    exact Fin.ext rfl
  have hlast : finCyclicSucc (Fin.succ (Fin.last n)) = (0 : Fin (n+2)) := by
    have h1 : ¬ ((Fin.succ (Fin.last n)).val + 1 < n + 2) := by
      simp only [Fin.val_succ, Fin.val_last]
      omega
    simp only [finCyclicSucc, dif_neg h1]
    exact Fin.ext rfl
  have hmid : ∀ j : Fin n,
      finCyclicSucc (Fin.succ (Fin.castSucc j)) = Fin.succ (Fin.succ j) := by
    intro j
    have hv : (Fin.succ (Fin.castSucc j)).val = j.val + 1 := by
      simp [Fin.val_succ, Fin.val_castSucc]
    have h2 : (Fin.succ (Fin.castSucc j)).val + 1 < n + 2 := by rw [hv]; omega
    simp only [finCyclicSucc, dif_pos h2]
    exact Fin.ext rfl
  have hprod : ENNReal.ofReal (continuumCutoffDominator (n+2) psi c omega u)
      = ∏ i : Fin (n+2), ENNReal.ofReal
          ((Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) (u i) *
            (|omega (u i)| * |c| * |u i - u (finCyclicSucc i)| ^ (-psi))) := by
    show ENNReal.ofReal (∏ i : Fin (n+2),
        (Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) (u i) *
          (|omega (u i)| * |c| * |u i - u (finCyclicSucc i)| ^ (-psi))) = _
    exact ofReal_finset_prod Finset.univ _ (fun i _ =>
      mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
        (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg c))
          (Real.rpow_nonneg (abs_nonneg _) (-psi))))
  rw [hprod]
  have hterm : ∀ i : Fin (n+2),
      ENNReal.ofReal ((Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) (u i) *
        (|omega (u i)| * |c| * |u i - u (finCyclicSucc i)| ^ (-psi)))
      = domVert c omega (u i) * domEdge psi (u i) (u (finCyclicSucc i)) := by
    intro i
    unfold domVert domEdge
    rw [← ENNReal.ofReal_mul (mul_nonneg
      (mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (abs_nonneg _))
      (abs_nonneg c))]
    congr 1
    ring
  rw [Finset.prod_congr rfl (fun i _ => hterm i), Finset.prod_mul_distrib]
  have hv : ∏ i : Fin (n+2), domVert c omega (u i)
      = domVert c omega x * ∏ j : Fin (n+1), domVert c omega (t j) := by
    rw [Fin.prod_univ_succ, hu0]
    simp only [hu]
  have he : ∏ i : Fin (n+2), domEdge psi (u i) (u (finCyclicSucc i))
      = domEdge psi x (t 0) * ((∏ j : Fin n, domEdge psi (t (Fin.castSucc j)) (t (Fin.succ j)))
          * domEdge psi (t (Fin.last n)) x) := by
    rw [Fin.prod_univ_succ, hcyc0, Fin.prod_univ_castSucc]
    simp only [hcyc0, hlast, hmid, hu0, hu]
  rw [hv, he]
  unfold chainOC
  ring

/-- Measurability of the dominator. -/
lemma measurable_dominator (k : ℕ) (psi c : ℝ) (omega : ℝ → ℝ) (homega : Measurable omega) :
    Measurable (continuumCutoffDominator k psi c omega) := by
  show Measurable (fun z : Fin k → ℝ => ∏ i : Fin k,
    (Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) (z i) *
      (|omega (z i)| * |c| * |z i - z (finCyclicSucc i)| ^ (-psi)))
  have hev : ∀ i : Fin k, Measurable (fun z : Fin k → ℝ => z i) := fun i =>
    measurable_eval_apply i
  exact measurable_finset_prod_real
    (f := fun (i : Fin k) (z : Fin k → ℝ) =>
      (Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) (z i) *
        (|omega (z i)| * |c| * |z i - z (finCyclicSucc i)| ^ (-psi)))
    (fun i _ => ((measurable_const.indicator measurableSet_Icc).comp (hev i)).mul
      (((homega.abs.comp (hev i)).mul measurable_const).mul
        (measurable_rpow_of_nonneg ((hev i).sub (hev (finCyclicSucc i))).abs
          (fun z => abs_nonneg _) (-psi))))

set_option maxHeartbeats 1000000 in
/-- The explicit finite bound for the dominator's pi-lintegral. -/
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
  have hdom : ∀ (t' : Fin (n+1) → ℝ) (x : ℝ),
      ENNReal.ofReal (continuumCutoffDominator (n+2) psi c omega (Fin.cons x t'))
        = domVert c omega x * domEdge psi x (t' 0) * domEdge psi (t' (Fin.last n)) x *
          chainOC psi c omega n t' := fun t' x =>
    dominator_cons psi c omega n x t' (Fin.cons x t')
      (show (Fin.cons x t' : Fin (n+2) → ℝ) (0 : Fin (n+2)) = x by simp) (fun i => by simp)
  simp only [hdom]
  have hmeasfun : ∀ t : Fin (n+1) → ℝ, Measurable
      (fun x : ℝ => domVert c omega x * domEdge psi x (t 0) * domEdge psi x (t (Fin.last n))) :=
    fun t => ((measurable_domVert c omega homega_meas).mul
      (measurable_domEdge psi (t 0))).mul (measurable_domEdge psi (t (Fin.last n)))
  have hinner : ∀ t : Fin (n+1) → ℝ,
      ∫⁻ x : ℝ, domVert c omega x * domEdge psi x (t 0)
          * domEdge psi (t (Fin.last n)) x * chainOC psi c omega n t ∂volume
        ≤ ENNReal.ofReal (|c| * B_omega * ν₂) * chainOC psi c omega n t := by
    intro t
    have heq : ∀ x : ℝ, domVert c omega x * domEdge psi x (t 0)
          * domEdge psi (t (Fin.last n)) x * chainOC psi c omega n t
        = domVert c omega x * domEdge psi x (t 0) * domEdge psi x (t (Fin.last n))
          * chainOC psi c omega n t := by
      intro x
      rw [domEdge_symm psi (t (Fin.last n)) x]
    simp only [heq]
    rw [lintegral_mul_const _ (hmeasfun t)]
    exact mul_le_mul_of_nonneg_right
      (vertexEdgeEdge_lintegral_le psi c B_omega ν₂ omega hpsi1 hpsi2 hB hν2 hνpos.2
        (t 0) (t (Fin.last n))) zero_le
  refine le_trans (lintegral_mono hinner) ?_
  rw [lintegral_const_mul (ENNReal.ofReal (|c| * B_omega * ν₂))
    (measurable_chainOC psi c omega homega_meas n)]
  have hchain := chainOC_lintegral_le psi c B_omega ν₁ omega hpsi1 hpsi2 hB hν1 hνpos.1
    homega_meas n
  have hBpos : 0 ≤ B_omega := le_trans (abs_nonneg _) (hB 0 (by simp))
  have hE1 : 0 ≤ |c| * B_omega * ν₁ := mul_nonneg (mul_nonneg (abs_nonneg c) hBpos) hνpos.1
  have hE2 : 0 ≤ |c| * B_omega * ν₂ := mul_nonneg (mul_nonneg (abs_nonneg c) hBpos) hνpos.2
  have hexp : (n + 2 - 2 : ℕ) = n := by omega
  calc ENNReal.ofReal (|c| * B_omega * ν₂)
        * ∫⁻ t : Fin (n+1) → ℝ, chainOC psi c omega n t
            ∂(Measure.pi fun _ : Fin (n+1) => (volume : Measure ℝ))
      ≤ ENNReal.ofReal (|c| * B_omega * ν₂)
          * (ENNReal.ofReal (2 * |c| * B_omega) * ENNReal.ofReal (|c| * B_omega * ν₁) ^ n) :=
        mul_le_mul_of_nonneg_left hchain zero_le
    _ = ENNReal.ofReal
          (2 * |c| * B_omega * (|c| * B_omega * ν₂) * (|c| * B_omega * ν₁) ^ (n + 2 - 2)) := by
        rw [hexp, ← ENNReal.ofReal_pow hE1,
          ← mul_assoc (ENNReal.ofReal (|c| * B_omega * ν₂))
            (ENNReal.ofReal (2 * |c| * B_omega))
            (ENNReal.ofReal ((|c| * B_omega * ν₁) ^ n)),
          ← ENNReal.ofReal_mul hE2,
          ← ENNReal.ofReal_mul (mul_nonneg hE2
            (mul_nonneg (by norm_num : (0:ℝ) ≤ 2 * |c|) hBpos))]
        congr 1
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
    show 0 ≤ ∏ i : Fin k,
      (Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) (z i) *
        (|omega (z i)| * |c| * |z i - z (finCyclicSucc i)| ^ (-psi))
    exact Finset.prod_nonneg (fun i _ =>
      mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) (z i))
        (mul_nonneg (mul_nonneg (abs_nonneg (omega (z i))) (abs_nonneg c))
          (Real.rpow_nonneg (abs_nonneg (z i - z (finCyclicSucc i))) (-psi))))
  refine ⟨(measurable_dominator k psi c omega homega_meas).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hnonneg)]
  refine lt_of_le_of_lt hbound ?_
  exact ENNReal.ofReal_lt_top

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
#check @hasFiniteIntegral_iff_ofReal
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
