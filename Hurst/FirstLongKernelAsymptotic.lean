import Hurst.FrozenLagCorrelation
import Mathlib.Analysis.Calculus.LHopital

noncomputable section
open Set Filter
open scoped Topology
namespace Hurst

private def centeredRpowSecondDifference (α u : ℝ) : ℝ :=
  (1 + u) ^ α + (1 - u) ^ α - 2

private def centeredRpowSecondDifferenceDeriv (α u : ℝ) : ℝ :=
  α * (1 + u) ^ (α - 1) - α * (1 - u) ^ (α - 1)

private def centeredRpowSecondDifferenceSecondDeriv (α u : ℝ) : ℝ :=
  α * (α - 1) * ((1 + u) ^ (α - 2) + (1 - u) ^ (α - 2))

private theorem centeredRpowSecondDifference_hasDerivAt (α u : ℝ)
    (hu : |u| < 1) :
    HasDerivAt (centeredRpowSecondDifference α)
      (centeredRpowSecondDifferenceDeriv α u) u := by
  have hp : 0 < 1 + u := by rw [abs_lt] at hu; linarith
  have hm : 0 < 1 - u := by rw [abs_lt] at hu; linarith
  unfold centeredRpowSecondDifference centeredRpowSecondDifferenceDeriv
  convert (((Real.hasDerivAt_rpow_const (p := α) (Or.inl hp.ne')).comp u
      ((hasDerivAt_const u 1).add (hasDerivAt_id u))).add
    ((Real.hasDerivAt_rpow_const (p := α) (Or.inl hm.ne')).comp u
      ((hasDerivAt_const u 1).sub (hasDerivAt_id u)))).sub_const 2 using 1 <;>
    first | rfl | ring | (simp only [one_mul, mul_one, id_eq]; ring)

private theorem centeredRpowSecondDifferenceDeriv_hasDerivAt (α u : ℝ)
    (hu : |u| < 1) :
    HasDerivAt (centeredRpowSecondDifferenceDeriv α)
      (centeredRpowSecondDifferenceSecondDeriv α u) u := by
  have hp : 0 < 1 + u := by rw [abs_lt] at hu; linarith
  have hm : 0 < 1 - u := by rw [abs_lt] at hu; linarith
  unfold centeredRpowSecondDifferenceDeriv centeredRpowSecondDifferenceSecondDeriv
  convert ((hasDerivAt_const u α).mul
      ((Real.hasDerivAt_rpow_const (p := α - 1) (Or.inl hp.ne')).comp u
        ((hasDerivAt_const u 1).add (hasDerivAt_id u)))).sub
    ((hasDerivAt_const u α).mul
      ((Real.hasDerivAt_rpow_const (p := α - 1) (Or.inl hm.ne')).comp u
        ((hasDerivAt_const u 1).sub (hasDerivAt_id u)))) using 1 <;>
    first | rfl | ring | (simp only [one_mul, mul_one, id_eq]; ring)

/-- The symmetric second difference of `x ↦ x^α`, divided by the square of
the step, converges to its second derivative at one. -/
theorem centered_rpow_second_difference_div_sq_tendsto (α : ℝ) :
    Tendsto (fun u : ℝ => centeredRpowSecondDifference α u / u ^ 2)
      (𝓝[>] 0) (𝓝 (α * (α - 1))) := by
  have hsmall : ∀ᶠ u : ℝ in 𝓝[>] 0, |u| < 1 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with u hu
    rw [abs_of_pos hu.1]
    exact hu.2
  have hF' : ∀ᶠ u : ℝ in 𝓝[>] 0,
      HasDerivAt (centeredRpowSecondDifference α)
        (centeredRpowSecondDifferenceDeriv α u) u :=
    hsmall.mono (fun u hu => centeredRpowSecondDifference_hasDerivAt α u hu)
  have hD' : ∀ᶠ u : ℝ in 𝓝[>] 0,
      HasDerivAt (centeredRpowSecondDifferenceDeriv α)
        (centeredRpowSecondDifferenceSecondDeriv α u) u :=
    hsmall.mono (fun u hu => centeredRpowSecondDifferenceDeriv_hasDerivAt α u hu)
  have hsq' : ∀ᶠ u : ℝ in 𝓝[>] 0,
      HasDerivAt (fun z : ℝ => z ^ 2) (2 * u) u := by
    exact Eventually.of_forall (fun u => by
      simpa using (hasDerivAt_pow 2 u))
  have hlin' : ∀ᶠ u : ℝ in 𝓝[>] 0,
      HasDerivAt (fun z : ℝ => 2 * z) 2 u := by
    exact Eventually.of_forall (fun u => by
      simpa using (hasDerivAt_const_mul (x := u) (2 : ℝ)))
  have h2u : ∀ᶠ u : ℝ in 𝓝[>] 0, 2 * u ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact mul_ne_zero (by norm_num) hu.ne'
  have htwo : ∀ᶠ _u : ℝ in 𝓝[>] 0, (2 : ℝ) ≠ 0 :=
    Eventually.of_forall (fun _ => by norm_num)
  have hF0 : Tendsto (centeredRpowSecondDifference α) (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt (centeredRpowSecondDifference α) 0 := by
      unfold centeredRpowSecondDifference
      exact ((((continuousAt_const.add continuousAt_id).rpow_const
        (Or.inl (by norm_num))).add
        ((continuousAt_const.sub continuousAt_id).rpow_const
          (Or.inl (by norm_num)))).sub continuousAt_const)
    change Tendsto (centeredRpowSecondDifference α)
      (𝓝 0 ⊓ 𝓟 (Ioi 0)) (𝓝 0)
    convert hc.tendsto.mono_left inf_le_left using 1 <;>
      norm_num [centeredRpowSecondDifference]
  have hF'0 : Tendsto (centeredRpowSecondDifferenceDeriv α) (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt (centeredRpowSecondDifferenceDeriv α) 0 := by
      unfold centeredRpowSecondDifferenceDeriv
      exact ((continuousAt_const.mul
        ((continuousAt_const.add continuousAt_id).rpow_const
          (Or.inl (by norm_num)))).sub
        (continuousAt_const.mul
          ((continuousAt_const.sub continuousAt_id).rpow_const
            (Or.inl (by norm_num)))))
    change Tendsto (centeredRpowSecondDifferenceDeriv α)
      (𝓝 0 ⊓ 𝓟 (Ioi 0)) (𝓝 0)
    convert hc.tendsto.mono_left inf_le_left using 1 <;>
      norm_num [centeredRpowSecondDifferenceDeriv]
  have hsq0 : Tendsto (fun u : ℝ => u ^ 2) (𝓝[>] 0) (𝓝 0) := by
    change Tendsto (fun u : ℝ => u ^ 2) (𝓝 0 ⊓ 𝓟 (Ioi 0)) (𝓝 0)
    simpa using ((tendsto_id : Tendsto (fun u : ℝ => u) (𝓝 0) (𝓝 0)).pow 2).mono_left inf_le_left
  have hlin0 : Tendsto (fun u : ℝ => 2 * u) (𝓝[>] 0) (𝓝 0) := by
    change Tendsto (fun u : ℝ => 2 * u) (𝓝 0 ⊓ 𝓟 (Ioi 0)) (𝓝 0)
    simpa using ((tendsto_const_nhds.mul tendsto_id :
      Tendsto (fun u : ℝ => 2 * u) (𝓝 0) (𝓝 (2 * 0)))).mono_left inf_le_left
  have hsecond : Tendsto
      (fun u : ℝ => centeredRpowSecondDifferenceSecondDeriv α u / 2)
      (𝓝[>] 0) (𝓝 (α * (α - 1))) := by
    have hc : ContinuousAt (centeredRpowSecondDifferenceSecondDeriv α) 0 := by
      unfold centeredRpowSecondDifferenceSecondDeriv
      exact (continuousAt_const.mul continuousAt_const).mul
        (((continuousAt_const.add continuousAt_id).rpow_const
          (Or.inl (by norm_num))).add
          ((continuousAt_const.sub continuousAt_id).rpow_const
            (Or.inl (by norm_num))))
    have ht : Tendsto
        (fun u : ℝ => centeredRpowSecondDifferenceSecondDeriv α u / 2)
        (𝓝 0 ⊓ 𝓟 (Ioi 0))
        (𝓝 (centeredRpowSecondDifferenceSecondDeriv α 0 / 2)) :=
      (hc.tendsto.mono_left inf_le_left).div_const 2
    change Tendsto
      (fun u : ℝ => centeredRpowSecondDifferenceSecondDeriv α u / 2)
      (𝓝 0 ⊓ 𝓟 (Ioi 0)) (𝓝 (α * (α - 1)))
    convert ht using 1 <;> norm_num [centeredRpowSecondDifferenceSecondDeriv] <;> ring
  have hfirst : Tendsto
      (fun u : ℝ => centeredRpowSecondDifferenceDeriv α u / (2 * u))
      (𝓝[>] 0) (𝓝 (α * (α - 1))) :=
    HasDerivAt.lhopital_zero_nhdsGT hD' hlin' htwo hF'0 hlin0 hsecond
  exact HasDerivAt.lhopital_zero_nhdsGT hF' hsq' h2u hF0 hsq0 hfirst

/-- The frozen first-increment correlation has the exact long-memory tail
constant `h(2h-1)`.  This is the off-diagonal kernel limit used by the q=1
step-kernel construction. -/
theorem firstIncrementLagCorrelation_scaled_tendsto (h : ℝ)
    (hh : 0 < h) (hh1 : h < 1) :
    Tendsto (fun x : ℝ => x ^ (2 - 2 * h) * firstIncrementLagCorrelation h x)
      atTop (𝓝 (h * (2 * h - 1))) := by
  have hinv : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨tendsto_inv_atTop_zero, ?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact inv_pos.mpr hx
  have hcore := (centered_rpow_second_difference_div_sq_tendsto (2 * h)).comp
    hinv
  have ht := hcore.div_const 2
  have heq : ∀ᶠ x : ℝ in atTop,
      x ^ (2 - 2 * h) * firstIncrementLagCorrelation h x =
        (centeredRpowSecondDifference (2 * h) x⁻¹ / x⁻¹ ^ 2) / 2 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx0 : 0 < x := zero_lt_one.trans hx
    have hxm : 0 < x - 1 := sub_pos.mpr hx
    have hxp : 0 < x + 1 := by linarith
    have eplus : (x + 1) ^ (2 * h) =
        x ^ (2 * h) * (1 + x⁻¹) ^ (2 * h) := by
      rw [← Real.mul_rpow hx0.le (by positivity : 0 ≤ 1 + x⁻¹)]
      congr 1
      field_simp
    have eminus : (x - 1) ^ (2 * h) =
        x ^ (2 * h) * (1 - x⁻¹) ^ (2 * h) := by
      rw [← Real.mul_rpow hx0.le (by
        rw [sub_nonneg]
        exact (inv_le_one₀ hx0).mpr hx.le)]
      congr 1
      field_simp
    have hpow : x ^ (2 - 2 * h) * x ^ (2 * h) = x ^ (2 : ℝ) := by
      rw [← Real.rpow_add hx0]
      congr 1
      ring
    unfold firstIncrementLagCorrelation centeredRpowSecondDifference
    rw [abs_of_pos hxp, abs_of_pos hxm, abs_of_pos hx0, eplus, eminus]
    rw [show
      x ^ (2 * h) * (1 + x⁻¹) ^ (2 * h) +
          x ^ (2 * h) * (1 - x⁻¹) ^ (2 * h) -
          2 * x ^ (2 * h) =
        x ^ (2 * h) *
          ((1 + x⁻¹) ^ (2 * h) + (1 - x⁻¹) ^ (2 * h) - 2) by ring]
    have hxne : x ≠ 0 := hx0.ne'
    calc
      _ = (x ^ (2 - 2 * h) * x ^ (2 * h)) *
          ((1 + x⁻¹) ^ (2 * h) + (1 - x⁻¹) ^ (2 * h) - 2) / 2 := by ring
      _ = x ^ (2 : ℝ) *
          ((1 + x⁻¹) ^ (2 * h) + (1 - x⁻¹) ^ (2 * h) - 2) / 2 := by rw [hpow]
      _ = _ := by
        rw [Real.rpow_two]
        field_simp
  have ht' := ht.congr' (Filter.EventuallyEq.symm heq)
  convert ht' using 1 <;> ring

/-- Pointwise off-diagonal step-kernel limit.  If `N` is the number of grid
cells in the local window, then the entry at rescaled distance `d` converges
to the Riesz kernel with coefficient `h(2h-1)`. -/
theorem firstIncrementLagCorrelation_stepKernel_tendsto
    (h d : ℝ) (hh : 0 < h) (hh1 : h < 1) (hd : 0 < d)
    (N : ℕ → ℝ) (hN : Tendsto N atTop atTop) :
    Tendsto (fun n => N n ^ (2 - 2 * h) *
      firstIncrementLagCorrelation h (N n * d)) atTop
      (𝓝 (h * (2 * h - 1) * d ^ (-(2 - 2 * h)))) := by
  have hNd : Tendsto (fun n => N n * d) atTop atTop :=
    hN.atTop_mul_const hd
  have hscaled := (firstIncrementLagCorrelation_scaled_tendsto h hh hh1).comp hNd
  have ht := hscaled.const_mul (d ^ (-(2 - 2 * h)))
  have heq : ∀ᶠ n : ℕ in atTop,
      d ^ (-(2 - 2 * h)) *
          ((N n * d) ^ (2 - 2 * h) *
            firstIncrementLagCorrelation h (N n * d)) =
        N n ^ (2 - 2 * h) *
          firstIncrementLagCorrelation h (N n * d) := by
    filter_upwards [hN.eventually_gt_atTop 0] with n hn
    have hcancel : d ^ (-(2 - 2 * h)) * d ^ (2 - 2 * h) = 1 := by
      rw [← Real.rpow_add hd]
      simp
    rw [Real.mul_rpow hn.le hd.le]
    calc
      _ = (d ^ (-(2 - 2 * h)) * d ^ (2 - 2 * h)) *
          (N n ^ (2 - 2 * h) *
            firstIncrementLagCorrelation h (N n * d)) := by ring
      _ = _ := by rw [hcancel, one_mul]
  have ht' := ht.congr' heq
  convert ht' using 1 <;> ring

end Hurst
