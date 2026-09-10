import Hurst.FirstLongCrossKernel

noncomputable section
open Set MeasureTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

/-- Scale-free covariance of two normalized first increments with respective
positive stride multipliers `d` and `e`; `x` is the displacement of their left
endpoints in units of the base mesh. -/
def firstIncrementTwoStrideCrossLagCorrelation
    (h k d e x : ℝ) : ℝ :=
  d ^ (-h) * e ^ (-k) * harmonizableCovCoeff h k *
    (|x + e| ^ (h + k) + |x - d| ^ (h + k) -
      |x + e - d| ^ (h + k) - |x| ^ (h + k))

/-- Exact unequal-stride frozen covariance formula. -/
theorem normalizedFrozenIncrement_two_stride_cross_lag
    (h k : Ioo (0 : ℝ) 1) (s ell d e x : ℝ)
    (hell : 0 < ell) (hd : 0 < d) (he : 0 < e) :
    ⟪normalizedFrozenIncrement h s (d * ell),
      normalizedFrozenIncrement k (s + x * ell) (e * ell)⟫ =
      firstIncrementTwoStrideCrossLagCorrelation h k d e x := by
  unfold normalizedFrozenIncrement
  rw [real_inner_smul_left, real_inner_smul_right]
  let c := harmonizableCovCoeff (h : ℝ) k
  have hraw :
      ⟪harmonizableFeature h (s + d * ell) - harmonizableFeature h s,
        harmonizableFeature k (s + x * ell + e * ell) -
          harmonizableFeature k (s + x * ell)⟫ =
        c * ell ^ ((h : ℝ) + k) *
          (|x + e| ^ ((h : ℝ) + k) + |x - d| ^ ((h : ℝ) + k) -
            |x + e - d| ^ ((h : ℝ) + k) - |x| ^ ((h : ℝ) + k)) := by
    simp only [inner_sub_left, inner_sub_right,
      harmonizableFeature_inner_formula]
    have h1 : |s + d * ell - (s + x * ell + e * ell)| =
        ell * |x + e - d| := by
      rw [show s + d * ell - (s + x * ell + e * ell) =
          -(x + e - d) * ell by ring,
        abs_mul, abs_neg, abs_of_pos hell]
      ring
    have h2 : |s + d * ell - (s + x * ell)| = ell * |x - d| := by
      rw [show s + d * ell - (s + x * ell) = -(x - d) * ell by ring,
        abs_mul, abs_neg, abs_of_pos hell]
      ring
    have h3 : |s - (s + x * ell + e * ell)| = ell * |x + e| := by
      rw [show s - (s + x * ell + e * ell) = -(x + e) * ell by ring,
        abs_mul, abs_neg, abs_of_pos hell]
      ring
    have h4 : |s - (s + x * ell)| = ell * |x| := by
      rw [show s - (s + x * ell) = -x * ell by ring,
        abs_mul, abs_neg, abs_of_pos hell]
      ring
    rw [h1, h2, h3, h4]
    simp_rw [Real.mul_rpow hell.le (abs_nonneg _)]
    change _ = c * ell ^ ((h : ℝ) + k) * _
    dsimp only [c, harmonizableCovCoeff]
    ring
  rw [hraw]
  have hdell : 0 < d * ell := mul_pos hd hell
  have heell : 0 < e * ell := mul_pos he hell
  have hsplitd : (d * ell) ^ (-(h : ℝ)) =
      d ^ (-(h : ℝ)) * ell ^ (-(h : ℝ)) :=
    Real.mul_rpow hd.le hell.le
  have hsplite : (e * ell) ^ (-(k : ℝ)) =
      e ^ (-(k : ℝ)) * ell ^ (-(k : ℝ)) :=
    Real.mul_rpow he.le hell.le
  rw [hsplitd, hsplite]
  have hcancel : ell ^ (-(h : ℝ)) *
      (ell ^ (-(k : ℝ)) * ell ^ ((h : ℝ) + k)) = 1 := by
    rw [← Real.rpow_add hell, ← Real.rpow_add hell]
    convert Real.rpow_zero ell using 1
    congr 1
    ring
  unfold firstIncrementTwoStrideCrossLagCorrelation
  rw [← show harmonizableD (((h : ℝ) + k) / 2) ^ 2 /
      (2 * harmonizableD h * harmonizableD k) =
        harmonizableCovCoeff h k by rfl]
  calc
    d ^ (-(h : ℝ)) * ell ^ (-(h : ℝ)) *
        (e ^ (-(k : ℝ)) * ell ^ (-(k : ℝ)) *
          (harmonizableCovCoeff (h : ℝ) k * ell ^ ((h : ℝ) + k) *
            (|x + e| ^ ((h : ℝ) + k) + |x - d| ^ ((h : ℝ) + k) -
              |x + e - d| ^ ((h : ℝ) + k) - |x| ^ ((h : ℝ) + k)))) =
      d ^ (-(h : ℝ)) * e ^ (-(k : ℝ)) *
        (ell ^ (-(h : ℝ)) *
          (ell ^ (-(k : ℝ)) * ell ^ ((h : ℝ) + k))) *
        harmonizableCovCoeff (h : ℝ) k *
          (|x + e| ^ ((h : ℝ) + k) + |x - d| ^ ((h : ℝ) + k) -
            |x + e - d| ^ ((h : ℝ) + k) - |x| ^ ((h : ℝ) + k)) := by ring
    _ = _ := by simp only [hcancel, one_mul, mul_one]; rfl

/-- The unit-stride specialization agrees with the previously used symmetric
cross-lag correlation. -/
theorem firstIncrementTwoStrideCrossLagCorrelation_one_one
    (h k x : ℝ) :
    firstIncrementTwoStrideCrossLagCorrelation h k 1 1 x =
      firstIncrementCrossLagCorrelation h k x := by
  unfold firstIncrementTwoStrideCrossLagCorrelation
  unfold firstIncrementCrossLagCorrelation harmonizableCovCoeff
  simp only [Real.one_rpow, one_mul]
  ring_nf

theorem firstIncrementTwoStrideCrossLagCorrelation_one_two
    (h k x : ℝ) :
    firstIncrementTwoStrideCrossLagCorrelation h k 1 2 x =
      2 ^ (-k) * (firstIncrementCrossLagCorrelation h k x +
        firstIncrementCrossLagCorrelation h k (x + 1)) := by
  unfold firstIncrementTwoStrideCrossLagCorrelation
  unfold firstIncrementCrossLagCorrelation harmonizableCovCoeff
  simp only [Real.one_rpow, one_mul]
  ring

theorem firstIncrementTwoStrideCrossLagCorrelation_two_one
    (h k x : ℝ) :
    firstIncrementTwoStrideCrossLagCorrelation h k 2 1 x =
      2 ^ (-h) * (firstIncrementCrossLagCorrelation h k x +
        firstIncrementCrossLagCorrelation h k (x - 1)) := by
  unfold firstIncrementTwoStrideCrossLagCorrelation
  unfold firstIncrementCrossLagCorrelation harmonizableCovCoeff
  simp only [Real.one_rpow]
  rw [show |x - 1 + 1| = |x| by congr 1 <;> ring,
    show |x - 1 - 1| = |x - 2| by congr 1 <;> ring]
  ring

theorem firstIncrementTwoStrideCrossLagCorrelation_two_two
    (h k x : ℝ) :
    firstIncrementTwoStrideCrossLagCorrelation h k 2 2 x =
      2 ^ (-h) * 2 ^ (-k) *
        (firstIncrementCrossLagCorrelation h k (x - 1) +
          2 * firstIncrementCrossLagCorrelation h k x +
          firstIncrementCrossLagCorrelation h k (x + 1)) := by
  unfold firstIncrementTwoStrideCrossLagCorrelation
  unfold firstIncrementCrossLagCorrelation harmonizableCovCoeff
  rw [show |x - 1 + 1| = |x| by congr 1 <;> ring,
    show |x - 1 - 1| = |x - 2| by congr 1 <;> ring]
  ring

private theorem rpow_shift_ratio_tendsto_one
    (X : ℕ → ℝ) (hX : Tendsto X atTop atTop) (s psi : ℝ) :
    Tendsto (fun n => X n ^ psi / (X n + s) ^ psi) atTop (𝓝 1) := by
  have hXs : Tendsto (fun n => X n + s) atTop atTop :=
    tendsto_atTop_add_const_right atTop s hX
  have hinv : Tendsto (fun n => (X n + s)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hXs
  have hratio : Tendsto (fun n => X n / (X n + s)) atTop (𝓝 1) := by
    have ht : Tendsto (fun n => (1 : ℝ) - s * (X n + s)⁻¹)
        atTop (𝓝 1) := by
      simpa only [mul_zero, sub_zero] using
        tendsto_const_nhds.sub (tendsto_const_nhds.mul hinv)
    apply ht.congr'
    filter_upwards [hXs.eventually_gt_atTop 0] with n hn
    field_simp [hn.ne']
    <;> ring
  have hpow : Tendsto (fun n => (X n / (X n + s)) ^ psi)
      atTop (𝓝 1) := by
    have hc : ContinuousAt (fun x : ℝ => x ^ psi) 1 :=
      continuousAt_id.rpow continuousAt_const (Or.inl one_ne_zero)
    change Tendsto ((fun x : ℝ => x ^ psi) ∘
      fun n => X n / (X n + s)) atTop (𝓝 1)
    simpa only [Real.one_rpow] using hc.tendsto.comp hratio
  apply hpow.congr'
  filter_upwards [hX.eventually_gt_atTop (max 0 (-s) + 1)] with n hn
  have hx : 0 < X n := lt_of_le_of_lt (le_max_left _ _) (lt_trans (lt_add_one _) hn)
  have hxs : 0 < X n + s := by
    have hneg : -s ≤ max 0 (-s) := le_max_right _ _
    linarith
  rw [Real.div_rpow hx.le hxs.le]

private theorem cross_log_rate_shift
    (H K X : ℕ → ℝ)
    (h0 s : ℝ)
    (hH : Tendsto H atTop (𝓝 h0))
    (hK : Tendsto K atTop (𝓝 h0))
    (hX : Tendsto X atTop atTop)
    (hrate : Tendsto (fun n =>
      (H n + K n - 2 * h0) * Real.log (X n)) atTop (𝓝 0)) :
    Tendsto (fun n =>
      (H n + K n - 2 * h0) * Real.log (X n + s)) atTop (𝓝 0) := by
  have hbeta : Tendsto (fun n => H n + K n - 2 * h0) atTop (𝓝 0) := by
    convert (hH.add hK).sub tendsto_const_nhds using 1 <;> ring
  have hratio := rpow_shift_ratio_tendsto_one X hX s 1
  have hratio' : Tendsto (fun n => X n / (X n + s)) atTop (𝓝 1) := by
    simpa only [Real.rpow_one] using hratio
  have hlogratio : Tendsto (fun n => Real.log (X n / (X n + s)))
      atTop (𝓝 0) := by
    change Tendsto (Real.log ∘ fun n => X n / (X n + s)) atTop (𝓝 0)
    simpa only [Real.log_one] using
      (Real.continuousAt_log one_ne_zero).tendsto.comp hratio'
  have hsmall := hbeta.mul hlogratio
  have hdecomp : (fun n =>
      (H n + K n - 2 * h0) * Real.log (X n + s)) =ᶠ[atTop]
      (fun n => (H n + K n - 2 * h0) * Real.log (X n) -
        (H n + K n - 2 * h0) * Real.log (X n / (X n + s))) := by
    filter_upwards [hX.eventually_gt_atTop (max 0 (-s) + 1)] with n hn
    have hx : 0 < X n := lt_of_le_of_lt (le_max_left _ _) (lt_trans (lt_add_one _) hn)
    have hxs : 0 < X n + s := by
      have hneg : -s ≤ max 0 (-s) := le_max_right _ _
      linarith
    rw [Real.log_div hx.ne' hxs.ne']
    ring
  simpa only [zero_mul, sub_zero] using
    (hrate.sub hsmall).congr' hdecomp.symm

/-- Shifting the integer lag by a fixed amount does not change the scaled
long-memory cross-correlation limit. -/
theorem firstIncrementCrossLagCorrelation_shifted_scaled_joint_tendsto
    (h s : ℝ) (hh : 0 < h) (hh1 : h < 1)
    (H K X : ℕ → ℝ)
    (hH : Tendsto H atTop (𝓝 h))
    (hK : Tendsto K atTop (𝓝 h))
    (hX : Tendsto X atTop atTop)
    (hrate : Tendsto (fun n =>
      (H n + K n - 2 * h) * Real.log (X n)) atTop (𝓝 0)) :
    Tendsto (fun n => X n ^ (2 - 2 * h) *
      firstIncrementCrossLagCorrelation (H n) (K n) (X n + s))
      atTop (𝓝 (h * (2 * h - 1))) := by
  have hXs : Tendsto (fun n => X n + s) atTop atTop :=
    tendsto_atTop_add_const_right atTop s hX
  have hrate' := cross_log_rate_shift H K X h s hH hK hX hrate
  have hbase := firstIncrementCrossLagCorrelation_scaled_joint_tendsto
    h hh hh1 H K (fun n => X n + s) hH hK hXs hrate'
  have hratio := rpow_shift_ratio_tendsto_one X hX s (2 - 2 * h)
  have hprod := hratio.mul hbase
  have heq : (fun n => X n ^ (2 - 2 * h) *
      firstIncrementCrossLagCorrelation (H n) (K n) (X n + s)) =ᶠ[atTop]
      (fun n => X n ^ (2 - 2 * h) / (X n + s) ^ (2 - 2 * h) *
        ((X n + s) ^ (2 - 2 * h) *
          firstIncrementCrossLagCorrelation (H n) (K n) (X n + s))) := by
    filter_upwards [hX.eventually_gt_atTop (max 0 (-s) + 1)] with n hn
    have hxs : 0 < X n + s := by
      have hneg : -s ≤ max 0 (-s) := le_max_right _ _
      linarith
    field_simp [Real.rpow_pos_of_pos hxs (2 - 2 * h) |>.ne']
  simpa only [one_mul] using hprod.congr' heq.symm

def firstLongTwoStrideConstant (h d e : ℝ) : ℝ :=
  d ^ (-h) * e ^ (-h) * (d * e) * (h * (2 * h - 1))

theorem firstLongTwoStrideConstant_one_one (h : ℝ) :
    firstLongTwoStrideConstant h 1 1 = h * (2 * h - 1) := by
  simp [firstLongTwoStrideConstant]

theorem firstLongTwoStrideConstant_one_two (h : ℝ) :
    firstLongTwoStrideConstant h 1 2 =
      (2 : ℝ) ^ (1 - h) * (h * (2 * h - 1)) := by
  unfold firstLongTwoStrideConstant
  simp only [Real.one_rpow, one_mul]
  have hp : (2 : ℝ) ^ (-h) * (2 : ℝ) = (2 : ℝ) ^ (1 - h) := by
    calc
      _ = (2 : ℝ) ^ (-h) * (2 : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = (2 : ℝ) ^ (-h + 1) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      _ = _ := by congr 1 <;> ring
  rw [hp]

theorem firstLongTwoStrideConstant_two_one (h : ℝ) :
    firstLongTwoStrideConstant h 2 1 =
      (2 : ℝ) ^ (1 - h) * (h * (2 * h - 1)) := by
  unfold firstLongTwoStrideConstant
  simp only [Real.one_rpow, mul_one]
  have hp : (2 : ℝ) ^ (-h) * (2 : ℝ) = (2 : ℝ) ^ (1 - h) := by
    calc
      _ = (2 : ℝ) ^ (-h) * (2 : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = (2 : ℝ) ^ (-h + 1) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      _ = _ := by congr 1 <;> ring
  rw [hp]

theorem firstLongTwoStrideConstant_two_two (h : ℝ) :
    firstLongTwoStrideConstant h 2 2 =
      (2 : ℝ) ^ (2 - 2 * h) * (h * (2 * h - 1)) := by
  unfold firstLongTwoStrideConstant
  rw [show (2 : ℝ) * 2 = 2 ^ (2 : ℝ) by norm_num,
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

/-- The four cross-kernel constants form the rank-one two-scale pilot matrix.
Writing `ψ = 2 - 2h`, its scale vector is `(1, 2^(ψ/2))`; in particular the
second quadratic component is scaled by `2^ψ`. -/
theorem firstLongTwoStrideConstant_pilot_matrix (h ψ : ℝ)
    (hψ : ψ = 2 - 2 * h) :
    let c := h * (2 * h - 1)
    firstLongTwoStrideConstant h 1 1 = c ∧
      firstLongTwoStrideConstant h 1 2 = (2 : ℝ) ^ (ψ / 2) * c ∧
      firstLongTwoStrideConstant h 2 1 = (2 : ℝ) ^ (ψ / 2) * c ∧
      firstLongTwoStrideConstant h 2 2 = (2 : ℝ) ^ ψ * c := by
  dsimp only
  rw [firstLongTwoStrideConstant_one_one,
    firstLongTwoStrideConstant_one_two,
    firstLongTwoStrideConstant_two_one,
    firstLongTwoStrideConstant_two_two]
  subst ψ
  constructor
  · rfl
  constructor
  · congr 2
    ring
  constructor
  · congr 2
    ring
  · rfl

/-- The stride-two normalization factor is Lipschitz on the nonnegative Hurst
range.  This is the coefficient estimate needed in the uniform cross-tail
argument. -/
theorem two_rpow_neg_lipschitz (h k : ℝ) (hh : 0 ≤ h) (hk : 0 ≤ k) :
    |(2 : ℝ) ^ (-h) - (2 : ℝ) ^ (-k)| ≤ Real.log 2 * |h - k| := by
  have hlog : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hm := (convex_Ici (0 : ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun x : ℝ => (2 : ℝ) ^ (-x))
    (f' := fun x : ℝ => Real.log 2 * (-1) * (2 : ℝ) ^ (-x))
    (C := Real.log 2)
    (fun x hx =>
      ((hasDerivAt_id x).neg.const_rpow (by norm_num : (0 : ℝ) < 2)).hasDerivWithinAt)
    (fun x hx => by
      rw [Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_nonneg hlog, abs_neg, abs_one,
        abs_of_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-x)),
        mul_one]
      have hp : (2 : ℝ) ^ (-x) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (neg_nonpos.mpr hx)
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hp hlog)
    hk hh
  simpa only [Real.norm_eq_abs] using hm

/-- Joint unequal-stride tail limit for the only two strides used by the q=1
pilot. -/
theorem firstIncrementTwoStride_scaled_joint_tendsto
    (h d e : ℝ) (hh : 0 < h) (hh1 : h < 1)
    (hd : d = 1 ∨ d = 2) (he : e = 1 ∨ e = 2)
    (H K X : ℕ → ℝ)
    (hH : Tendsto H atTop (𝓝 h))
    (hK : Tendsto K atTop (𝓝 h))
    (hX : Tendsto X atTop atTop)
    (hrate : Tendsto (fun n =>
      (H n + K n - 2 * h) * Real.log (X n)) atTop (𝓝 0)) :
    Tendsto (fun n => X n ^ (2 - 2 * h) *
      firstIncrementTwoStrideCrossLagCorrelation (H n) (K n) d e (X n))
      atTop (𝓝 (firstLongTwoStrideConstant h d e)) := by
  let c := h * (2 * h - 1)
  have hzero : Tendsto (fun n => X n ^ (2 - 2 * h) *
      firstIncrementCrossLagCorrelation (H n) (K n) (X n))
      atTop (𝓝 (h * (2 * h - 1))) := by
    simpa only [add_zero] using
      firstIncrementCrossLagCorrelation_shifted_scaled_joint_tendsto
        h 0 hh hh1 H K X hH hK hX hrate
  have hplus := firstIncrementCrossLagCorrelation_shifted_scaled_joint_tendsto
    h 1 hh hh1 H K X hH hK hX hrate
  have hminus := firstIncrementCrossLagCorrelation_shifted_scaled_joint_tendsto
    h (-1) hh hh1 H K X hH hK hX hrate
  rcases hd with rfl | rfl <;> rcases he with rfl | rfl
  · simpa only [firstIncrementTwoStrideCrossLagCorrelation_one_one,
      firstLongTwoStrideConstant, Real.one_rpow, one_mul, add_zero] using hzero
  · have hcoef : Tendsto (fun n => (2 : ℝ) ^ (-K n)) atTop
        (𝓝 ((2 : ℝ) ^ (-h))) := by
      exact (Real.continuousAt_const_rpow (by norm_num : (2 : ℝ) ≠ 0)).tendsto.comp
        hK.neg
    have hsum := hzero.add hplus
    have hp := hcoef.mul hsum
    convert hp using 1
    · funext n
      rw [firstIncrementTwoStrideCrossLagCorrelation_one_two]
      ring
    · dsimp only [c, firstLongTwoStrideConstant]
      simp only [Real.one_rpow, one_mul]
      ring
  · have hcoef : Tendsto (fun n => (2 : ℝ) ^ (-H n)) atTop
        (𝓝 ((2 : ℝ) ^ (-h))) := by
      exact (Real.continuousAt_const_rpow (by norm_num : (2 : ℝ) ≠ 0)).tendsto.comp
        hH.neg
    have hsum := hzero.add hminus
    have hp := hcoef.mul hsum
    convert hp using 1
    · funext n
      rw [firstIncrementTwoStrideCrossLagCorrelation_two_one]
      ring
    · dsimp only [c, firstLongTwoStrideConstant]
      simp only [Real.one_rpow, one_mul, mul_one]
      ring
  · have hcoefH : Tendsto (fun n => (2 : ℝ) ^ (-H n)) atTop
        (𝓝 ((2 : ℝ) ^ (-h))) := by
      exact (Real.continuousAt_const_rpow (by norm_num : (2 : ℝ) ≠ 0)).tendsto.comp
        hH.neg
    have hcoefK : Tendsto (fun n => (2 : ℝ) ^ (-K n)) atTop
        (𝓝 ((2 : ℝ) ^ (-h))) := by
      exact (Real.continuousAt_const_rpow (by norm_num : (2 : ℝ) ≠ 0)).tendsto.comp
        hK.neg
    have hsum := (hminus.add (hzero.const_mul 2)).add hplus
    have hp := (hcoefH.mul hcoefK).mul hsum
    convert hp using 1
    · funext n
      rw [firstIncrementTwoStrideCrossLagCorrelation_two_two]
      ring
    · dsimp only [c, firstLongTwoStrideConstant]
      ring

/-- Reversing the two increments reverses the lag and exchanges the strides
and Hurst parameters. -/
theorem firstIncrementTwoStrideCrossLagCorrelation_swap
    (h k d e x : ℝ) :
    firstIncrementTwoStrideCrossLagCorrelation h k d e x =
      firstIncrementTwoStrideCrossLagCorrelation k h e d (-x) := by
  unfold firstIncrementTwoStrideCrossLagCorrelation harmonizableCovCoeff
  rw [show (h + k) / 2 = (k + h) / 2 by ring,
    show h + k = k + h by ring]
  simp only [abs_neg]
  rw [show |-x + d| = |x - d| by rw [← abs_neg]; congr 1 <;> ring,
    show |-x - e| = |x + e| by rw [← abs_neg]; congr 1 <;> ring,
    show |-x + d - e| = |x + e - d| by rw [← abs_neg]; congr 1 <;> ring]
  ring

end Hurst
