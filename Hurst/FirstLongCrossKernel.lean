import Hurst.FirstLongKernelAsymptotic
import Hurst.FrozenCrossLagCorrelation
import Hurst.CorrelationLimit
import Hurst.Analytic
import Mathlib.Analysis.Calculus.Taylor

noncomputable section
open Set Filter
open scoped Topology
namespace Hurst

private theorem rpow_taylor_one (α u : ℝ) (hu : 0 < u) (_hu1 : u < 1) :
    ∃ ξ ∈ Ioo 1 (1 + u),
      (1 + u) ^ α - (1 + α * u) =
        (α * (α - 1) * ξ ^ (α - 2)) * u ^ 2 / 2 := by
  have hpos : ∀ z ∈ uIcc (1 : ℝ) (1 + u), z ≠ 0 := by
    intro z hz
    rw [uIcc_of_le (by linarith)] at hz
    exact (zero_lt_one.trans_le hz.1).ne'
  have hcd : ContDiffOn ℝ 2 (fun z : ℝ => z ^ α)
      (uIcc (1 : ℝ) (1 + u)) :=
    contDiffOn_id.rpow_const_of_ne hpos
  obtain ⟨ξ, hξ, hrem⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (show (1 : ℝ) ≠ 1 + u by linarith) hcd
  refine ⟨ξ, ?_, ?_⟩
  · simpa [uIoo, min_eq_left (by linarith : (1 : ℝ) ≤ 1 + u),
      max_eq_right (by linarith : (1 : ℝ) ≤ 1 + u)] using hξ
  have htaylor : taylorWithinEval (fun z : ℝ => z ^ α) 1
      (uIcc (1 : ℝ) (1 + u)) 1 (1 + u) = 1 + α * u := by
    rw [show (1 : ℕ) = 0 + 1 by omega, taylorWithinEval_succ,
      taylor_within_zero_eval, iteratedDerivWithin_one]
    have hunique : UniqueDiffWithinAt ℝ (uIcc (1 : ℝ) (1 + u)) 1 :=
      (uniqueDiffOn_Icc (by
        change min (1 : ℝ) (1 + u) < max 1 (1 + u)
        rw [min_eq_left (by linarith), max_eq_right (by linarith)]
        linarith)).uniqueDiffWithinAt (by
          constructor <;>
            simp [min_eq_left (by linarith : (1 : ℝ) ≤ 1 + u),
              max_eq_right (by linarith : (1 : ℝ) ≤ 1 + u), hu.le])
    rw [(Real.hasDerivAt_rpow_const (p := α) (Or.inl one_ne_zero)).hasDerivWithinAt.derivWithin hunique]
    norm_num
    ring
  rw [htaylor] at hrem
  rw [hrem]
  have hsecond : deriv (deriv (fun z : ℝ => z ^ α)) ξ =
      α * (α - 1) * ξ ^ (α - 2) := by
    rw [Real.deriv_rpow_const']
    rw [deriv_const_mul_field, Real.deriv_rpow_const]
    ring
  rw [show (2 : ℕ) = 1 + 1 by omega, iteratedDeriv_succ,
    iteratedDeriv_one]
  rw [hsecond]
  norm_num

private theorem rpow_taylor_one_sub (α u : ℝ) (hu : 0 < u) (hu1 : u < 1) :
    ∃ ξ ∈ Ioo (1 - u) 1,
      (1 - u) ^ α - (1 - α * u) =
        (α * (α - 1) * ξ ^ (α - 2)) * u ^ 2 / 2 := by
  have hpos : ∀ z ∈ uIcc (1 : ℝ) (1 - u), z ≠ 0 := by
    intro z hz
    rw [uIcc_of_ge (by linarith)] at hz
    exact (by linarith [hz.1] : 0 < z).ne'
  have hcd : ContDiffOn ℝ 2 (fun z : ℝ => z ^ α)
      (uIcc (1 : ℝ) (1 - u)) :=
    contDiffOn_id.rpow_const_of_ne hpos
  obtain ⟨ξ, hξ, hrem⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (show (1 : ℝ) ≠ 1 - u by linarith) hcd
  refine ⟨ξ, ?_, ?_⟩
  · simpa [uIoo, min_eq_right (by linarith : 1 - u ≤ (1 : ℝ)),
      max_eq_left (by linarith : 1 - u ≤ (1 : ℝ))] using hξ
  have htaylor : taylorWithinEval (fun z : ℝ => z ^ α) 1
      (uIcc (1 : ℝ) (1 - u)) 1 (1 - u) = 1 - α * u := by
    rw [show (1 : ℕ) = 0 + 1 by omega, taylorWithinEval_succ,
      taylor_within_zero_eval, iteratedDerivWithin_one]
    have hunique : UniqueDiffWithinAt ℝ (uIcc (1 : ℝ) (1 - u)) 1 :=
      (uniqueDiffOn_Icc (by
        change min (1 : ℝ) (1 - u) < max 1 (1 - u)
        rw [min_eq_right (by linarith), max_eq_left (by linarith)]
        linarith)).uniqueDiffWithinAt (by
          constructor <;>
            simp [min_eq_right (by linarith : 1 - u ≤ (1 : ℝ)),
              max_eq_left (by linarith : 1 - u ≤ (1 : ℝ)), hu.le])
    rw [(Real.hasDerivAt_rpow_const (p := α) (Or.inl one_ne_zero)).hasDerivWithinAt.derivWithin hunique]
    norm_num
    ring
  rw [htaylor] at hrem
  rw [hrem]
  have hsecond : deriv (deriv (fun z : ℝ => z ^ α)) ξ =
      α * (α - 1) * ξ ^ (α - 2) := by
    rw [Real.deriv_rpow_const']
    rw [deriv_const_mul_field, Real.deriv_rpow_const]
    ring
  rw [show (2 : ℕ) = 1 + 1 by omega, iteratedDeriv_succ,
    iteratedDeriv_one]
  rw [hsecond]
  norm_num

def centeredCrossRpowQuotient (α u : ℝ) : ℝ :=
  ((1 + u) ^ α + (1 - u) ^ α - 2) / u ^ 2

/-- Joint version of the symmetric second-difference limit.  The exponent may
vary with the mesh; no `|αₙ-α| log N` side condition is needed after factoring
out the long-lag power. -/
theorem centeredCrossRpowQuotient_joint_tendsto
    (α : ℝ) (A U : ℕ → ℝ)
    (hA : Tendsto A atTop (𝓝 α))
    (hU : Tendsto U atTop (𝓝 0))
    (hUpos : ∀ᶠ n in atTop, 0 < U n)
    (hUone : ∀ᶠ n in atTop, U n < 1) :
    Tendsto (fun n => centeredCrossRpowQuotient (A n) (U n))
      atTop (𝓝 (α * (α - 1))) := by
  classical
  let good := fun n => 0 < U n ∧ U n < 1
  let xp := fun n => if hn : good n then
    Classical.choose (rpow_taylor_one (A n) (U n) hn.1 hn.2) else 1
  let xm := fun n => if hn : good n then
    Classical.choose (rpow_taylor_one_sub (A n) (U n) hn.1 hn.2) else 1
  have hxp_mem : ∀ᶠ n in atTop, xp n ∈ Ioo 1 (1 + U n) := by
    filter_upwards [hUpos, hUone] with n hpos hone
    dsimp [xp, good]
    rw [dif_pos ⟨hpos, hone⟩]
    exact (Classical.choose_spec
      (rpow_taylor_one (A n) (U n) hpos hone)).1
  have hxm_mem : ∀ᶠ n in atTop, xm n ∈ Ioo (1 - U n) 1 := by
    filter_upwards [hUpos, hUone] with n hpos hone
    dsimp [xm, good]
    rw [dif_pos ⟨hpos, hone⟩]
    exact (Classical.choose_spec
      (rpow_taylor_one_sub (A n) (U n) hpos hone)).1
  have hxp : Tendsto xp atTop (𝓝 1) := by
    apply tendsto_of_abs_sub_le_zero xp (fun _ => 1) U 1
      tendsto_const_nhds hU (hUpos.mono fun _ hn => hn.le)
    filter_upwards [hxp_mem] with n hn
    rw [abs_of_nonneg (sub_nonneg.mpr hn.1.le)]
    linarith [hn.2]
  have hxm : Tendsto xm atTop (𝓝 1) := by
    apply tendsto_of_abs_sub_le_zero xm (fun _ => 1) U 1
      tendsto_const_nhds hU (hUpos.mono fun _ hn => hn.le)
    filter_upwards [hxm_mem] with n hn
    rw [abs_of_nonpos (sub_nonpos.mpr hn.2.le)]
    linarith [hn.1]
  let G := fun z : ℝ × ℝ => z.1 * (z.1 - 1) * z.2 ^ (z.1 - 2)
  have hG : ContinuousAt G (α, 1) := by
    dsimp [G]
    exact (continuousAt_fst.mul (continuousAt_fst.sub continuousAt_const)).mul
      (continuousAt_snd.rpow
        (continuousAt_fst.sub continuousAt_const) (Or.inl one_ne_zero))
  have hgp : Tendsto (fun n => G (A n, xp n)) atTop
      (𝓝 (α * (α - 1))) := by
    simpa [G, Function.comp_def] using
      hG.tendsto.comp (hA.prodMk_nhds hxp)
  have hgm : Tendsto (fun n => G (A n, xm n)) atTop
      (𝓝 (α * (α - 1))) := by
    simpa [G, Function.comp_def] using
      hG.tendsto.comp (hA.prodMk_nhds hxm)
  have havg := (hgp.add hgm).div_const 2
  have heq : ∀ᶠ n in atTop,
      centeredCrossRpowQuotient (A n) (U n) =
        (G (A n, xp n) + G (A n, xm n)) / 2 := by
    filter_upwards [hUpos, hUone] with n hpos hone
    have hp := (Classical.choose_spec
      (rpow_taylor_one (A n) (U n) hpos hone)).2
    have hm := (Classical.choose_spec
      (rpow_taylor_one_sub (A n) (U n) hpos hone)).2
    have hxpe : xp n = Classical.choose
        (rpow_taylor_one (A n) (U n) hpos hone) := by
      dsimp [xp, good]
      rw [dif_pos ⟨hpos, hone⟩]
    have hxme : xm n = Classical.choose
        (rpow_taylor_one_sub (A n) (U n) hpos hone) := by
      dsimp [xm, good]
      rw [dif_pos ⟨hpos, hone⟩]
    rw [← hxpe] at hp
    rw [← hxme] at hm
    dsimp [centeredCrossRpowQuotient, G]
    have hne : U n ≠ 0 := hpos.ne'
    rw [show
      (1 + U n) ^ A n + (1 - U n) ^ A n - 2 =
        ((1 + U n) ^ A n - (1 + A n * U n)) +
        ((1 - U n) ^ A n - (1 - A n * U n)) by ring,
      hp, hm]
    field_simp
  have havg' := havg.congr' (Filter.EventuallyEq.symm heq)
  convert havg' using 1 <;> ring

/-- The normalization coefficient in the cross-parameter covariance tends to
`1/2` when both parameters freeze at the same interior Hurst value. -/
theorem firstIncrementCrossCoefficient_tendsto
    (h : ℝ) (hh : 0 < h) (hh1 : h < 1)
    (H K : ℕ → ℝ)
    (hH : Tendsto H atTop (𝓝 h))
    (hK : Tendsto K atTop (𝓝 h)) :
    Tendsto (fun n =>
      harmonizableD ((H n + K n) / 2) ^ 2 /
        (2 * harmonizableD (H n) * harmonizableD (K n)))
      atTop (𝓝 (1 / 2 : ℝ)) := by
  have hDh : ContinuousAt harmonizableD h :=
    harmonizableD_continuousOn.continuousAt (Ioo_mem_nhds hh hh1)
  have hmid : Tendsto (fun n => (H n + K n) / 2) atTop (𝓝 h) := by
    convert (hH.add hK).div_const 2 using 1 <;> ring
  have hDmid : Tendsto (fun n => harmonizableD ((H n + K n) / 2))
      atTop (𝓝 (harmonizableD h)) := hDh.tendsto.comp hmid
  have hDH : Tendsto (fun n => harmonizableD (H n))
      atTop (𝓝 (harmonizableD h)) := hDh.tendsto.comp hH
  have hDK : Tendsto (fun n => harmonizableD (K n))
      atTop (𝓝 (harmonizableD h)) := hDh.tendsto.comp hK
  have hDne : harmonizableD h ≠ 0 :=
    (harmonizableD_pos h hh hh1).ne'
  have htwo : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2) :=
    tendsto_const_nhds
  have hden : Tendsto
      (fun n => 2 * harmonizableD (H n) * harmonizableD (K n))
      atTop (𝓝 (2 * harmonizableD h * harmonizableD h)) :=
    (htwo.mul hDH).mul hDK
  have ht := (hDmid.pow 2).div hden
    (mul_ne_zero (mul_ne_zero (by norm_num) hDne) hDne)
  have ht' : Tendsto (fun n =>
      harmonizableD ((H n + K n) / 2) ^ 2 /
        (2 * harmonizableD (H n) * harmonizableD (K n)))
      atTop (𝓝 (harmonizableD h ^ 2 /
        (2 * harmonizableD h * harmonizableD h))) := by
    change Tendsto
      ((fun n => harmonizableD ((H n + K n) / 2) ^ 2) /
        fun n => 2 * harmonizableD (H n) * harmonizableD (K n))
      atTop (𝓝 (harmonizableD h ^ 2 /
        (2 * harmonizableD h * harmonizableD h)))
    exact ht
  rw [show (1 / 2 : ℝ) = harmonizableD h ^ 2 /
      (2 * harmonizableD h * harmonizableD h) by field_simp [hDne]]
  exact ht'

/-- Frozen cross-parameter long-lag limit.  The logarithmic side condition is
exactly what is needed to remove the power mismatch caused by the varying
exponent `Hₙ + Kₙ`. -/
theorem firstIncrementCrossLagCorrelation_scaled_joint_tendsto
    (h : ℝ) (hh : 0 < h) (hh1 : h < 1)
    (H K X : ℕ → ℝ)
    (hH : Tendsto H atTop (𝓝 h))
    (hK : Tendsto K atTop (𝓝 h))
    (hX : Tendsto X atTop atTop)
    (hlog : Tendsto (fun n =>
      (H n + K n - 2 * h) * Real.log (X n)) atTop (𝓝 0)) :
    Tendsto (fun n => X n ^ (2 - 2 * h) *
      firstIncrementCrossLagCorrelation (H n) (K n) (X n))
      atTop (𝓝 (h * (2 * h - 1))) := by
  have hcoef := firstIncrementCrossCoefficient_tendsto h hh hh1 H K hH hK
  have hinv : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨tendsto_inv_atTop_zero, ?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact inv_pos.mpr hx
  have hUwithin : Tendsto (fun n => (X n)⁻¹) atTop (𝓝[>] 0) :=
    hinv.comp hX
  have hU : Tendsto (fun n => (X n)⁻¹) atTop (𝓝 0) :=
    tendsto_nhdsWithin_iff.mp hUwithin |>.1
  have hUpos : ∀ᶠ n in atTop, 0 < (X n)⁻¹ :=
    (tendsto_nhdsWithin_iff.mp hUwithin).2
  have hUone : ∀ᶠ n in atTop, (X n)⁻¹ < 1 := by
    filter_upwards [hX.eventually_gt_atTop 1] with n hn
    exact (inv_lt_one₀ (by linarith)).mpr hn
  have hquot := centeredCrossRpowQuotient_joint_tendsto (2 * h)
    (fun n => H n + K n) (fun n => (X n)⁻¹)
    (by convert hH.add hK using 1 <;> ring) hU hUpos hUone
  have hexp : Tendsto (fun n => Real.exp
      ((H n + K n - 2 * h) * Real.log (X n)))
      atTop (𝓝 1) := by
    change Tendsto (Real.exp ∘ fun n =>
      (H n + K n - 2 * h) * Real.log (X n)) atTop (𝓝 1)
    simpa only [Real.exp_zero] using
      Real.continuous_exp.continuousAt.tendsto.comp hlog
  have hcorr : Tendsto (fun n => X n ^ (H n + K n - 2 * h))
      atTop (𝓝 1) := by
    apply hexp.congr'
    filter_upwards [hX.eventually_gt_atTop 0] with n hn
    rw [Real.rpow_def_of_pos hn]
    congr 1
    ring
  have hprod := (hcoef.mul hcorr).mul hquot
  have heq : ∀ᶠ n in atTop,
      X n ^ (2 - 2 * h) *
          firstIncrementCrossLagCorrelation (H n) (K n) (X n) =
        (harmonizableD ((H n + K n) / 2) ^ 2 /
            (2 * harmonizableD (H n) * harmonizableD (K n))) *
          X n ^ (H n + K n - 2 * h) *
          centeredCrossRpowQuotient (H n + K n) (X n)⁻¹ := by
    filter_upwards [hX.eventually_gt_atTop 1] with n hn
    have hx0 : 0 < X n := by linarith
    have hxm : 0 < X n - 1 := sub_pos.mpr hn
    have hxp : 0 < X n + 1 := by linarith
    have eplus : (X n + 1) ^ (H n + K n) =
        X n ^ (H n + K n) *
          (1 + (X n)⁻¹) ^ (H n + K n) := by
      rw [← Real.mul_rpow hx0.le (by positivity : 0 ≤ 1 + (X n)⁻¹)]
      congr 1
      field_simp
    have eminus : (X n - 1) ^ (H n + K n) =
        X n ^ (H n + K n) *
          (1 - (X n)⁻¹) ^ (H n + K n) := by
      rw [← Real.mul_rpow hx0.le (by
        rw [sub_nonneg]
        exact (inv_le_one₀ hx0).mpr hn.le)]
      congr 1
      field_simp
    have hpowers : X n ^ (2 - 2 * h) * X n ^ (H n + K n) =
        X n ^ (H n + K n - 2 * h) * X n ^ (2 : ℝ) := by
      rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
      congr 1
      ring
    unfold firstIncrementCrossLagCorrelation centeredCrossRpowQuotient
    rw [abs_of_pos hxp, abs_of_pos hxm, abs_of_pos hx0, eplus, eminus]
    rw [show
      X n ^ (H n + K n) * (1 + (X n)⁻¹) ^ (H n + K n) +
          X n ^ (H n + K n) * (1 - (X n)⁻¹) ^ (H n + K n) -
          2 * X n ^ (H n + K n) =
        X n ^ (H n + K n) *
          ((1 + (X n)⁻¹) ^ (H n + K n) +
            (1 - (X n)⁻¹) ^ (H n + K n) - 2) by ring]
    rw [show X n ^ (2 - 2 * h) *
        (harmonizableD ((H n + K n) / 2) ^ 2 /
          (2 * harmonizableD (H n) * harmonizableD (K n)) *
          (X n ^ (H n + K n) *
            ((1 + (X n)⁻¹) ^ (H n + K n) +
              (1 - (X n)⁻¹) ^ (H n + K n) - 2))) =
      (harmonizableD ((H n + K n) / 2) ^ 2 /
          (2 * harmonizableD (H n) * harmonizableD (K n))) *
        (X n ^ (2 - 2 * h) * X n ^ (H n + K n)) *
        ((1 + (X n)⁻¹) ^ (H n + K n) +
          (1 - (X n)⁻¹) ^ (H n + K n) - 2) by ring,
      hpowers, Real.rpow_two]
    field_simp [hx0.ne']
    <;> ring
  have hprod' := hprod.congr' (Filter.EventuallyEq.symm heq)
  convert hprod' using 1 <;> ring

/-- Off-diagonal cross-parameter step-kernel limit.  This is the form used on
two local grid cells at a fixed positive rescaled separation `d`: the lag is
`Nₙ d`, while the two cell parameters may both vary toward `h`. -/
theorem firstIncrementCrossLagCorrelation_stepKernel_joint_tendsto
    (h d : ℝ) (hh : 0 < h) (hh1 : h < 1) (hd : 0 < d)
    (H K N : ℕ → ℝ)
    (hH : Tendsto H atTop (𝓝 h))
    (hK : Tendsto K atTop (𝓝 h))
    (hN : Tendsto N atTop atTop)
    (hrate : Tendsto (fun n =>
      (H n + K n - 2 * h) * Real.log (N n)) atTop (𝓝 0)) :
    Tendsto (fun n => N n ^ (2 - 2 * h) *
      firstIncrementCrossLagCorrelation (H n) (K n) (N n * d))
      atTop (𝓝 (h * (2 * h - 1) * d ^ (-(2 - 2 * h)))) := by
  have hdelta : Tendsto (fun n => H n + K n - 2 * h) atTop (𝓝 0) := by
    convert (hH.add hK).sub tendsto_const_nhds using 1 <;> ring
  have hconst : Tendsto (fun n =>
      (H n + K n - 2 * h) * Real.log d) atTop (𝓝 0) := by
    convert hdelta.mul_const (Real.log d) using 1 <;> ring
  have hlogNd : Tendsto (fun n =>
      (H n + K n - 2 * h) * Real.log (N n * d)) atTop (𝓝 0) := by
    have hsum := hrate.add hconst
    have heq : (fun n =>
        (H n + K n - 2 * h) * Real.log (N n) +
          (H n + K n - 2 * h) * Real.log d) =ᶠ[atTop]
        (fun n => (H n + K n - 2 * h) * Real.log (N n * d)) := by
      filter_upwards [hN.eventually_gt_atTop 0] with n hn
      rw [Real.log_mul hn.ne' hd.ne']
      ring
    simpa only [zero_add] using hsum.congr' heq
  have hNd : Tendsto (fun n => N n * d) atTop atTop :=
    hN.atTop_mul_const hd
  have hscaled := firstIncrementCrossLagCorrelation_scaled_joint_tendsto
    h hh hh1 H K (fun n => N n * d) hH hK hNd hlogNd
  have ht := hscaled.const_mul (d ^ (-(2 - 2 * h)))
  have heq : ∀ᶠ n in atTop,
      d ^ (-(2 - 2 * h)) *
          ((N n * d) ^ (2 - 2 * h) *
            firstIncrementCrossLagCorrelation (H n) (K n) (N n * d)) =
        N n ^ (2 - 2 * h) *
          firstIncrementCrossLagCorrelation (H n) (K n) (N n * d) := by
    filter_upwards [hN.eventually_gt_atTop 0] with n hn
    have hcancel : d ^ (-(2 - 2 * h)) * d ^ (2 - 2 * h) = 1 := by
      rw [← Real.rpow_add hd]
      simp
    rw [Real.mul_rpow hn.le hd.le]
    calc
      _ = (d ^ (-(2 - 2 * h)) * d ^ (2 - 2 * h)) *
          (N n ^ (2 - 2 * h) *
            firstIncrementCrossLagCorrelation (H n) (K n) (N n * d)) := by
          ring
      _ = _ := by rw [hcancel, one_mul]
  have ht' := ht.congr' heq
  convert ht' using 1 <;> ring

end Hurst
