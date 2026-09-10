import Hurst.SpectralRegularity

/-! A common spectral bound independent of time and Hurst parameter on compact ranges. -/
noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped Topology ENNReal RealInnerProductSpace
namespace Hurst

def spectralMajorant (a b x : ℝ) : ℝ :=
  min (|x| ^ (1 - 2 * b)) (|x| ^ (-1 - 2 * a))

theorem spectralMajorant_nonneg (a b x : ℝ) : 0 ≤ spectralMajorant a b x :=
  le_min (Real.rpow_nonneg (abs_nonneg _) _) (Real.rpow_nonneg (abs_nonneg _) _)

theorem spectralMajorant_log_weight_integrable (a b : ℝ) (ha : 0 < a) (hb : b < 1)
    (k : ℕ) : Integrable (fun x => (Real.log |x|) ^ k * spectralMajorant a b x) volume := by
  have hm : AEStronglyMeasurable
      (fun x => (Real.log |x|) ^ k * spectralMajorant a b x) volume := by
    apply Measurable.aestronglyMeasurable
    unfold spectralMajorant
    fun_prop
  have hnear : (spectralMajorant a b) =O[𝓝[>] 0]
      (fun x : ℝ => x ^ (1 - 2 * b)) := by
    apply IsBigO.of_bound 1
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxpos : 0 < x := hx
    rw [Real.norm_eq_abs, abs_of_nonneg (spectralMajorant_nonneg a b x),
      Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hxpos.le _), one_mul]
    simpa only [spectralMajorant, abs_of_pos hxpos] using
      (min_le_left (x ^ (1 - 2 * b)) (x ^ (-1 - 2 * a)))
  have hfar : (spectralMajorant a b) =O[atTop]
      (fun x : ℝ => x ^ (-1 - 2 * a)) := by
    apply IsBigO.of_bound 1
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hxpos : 0 < x := hx
    rw [Real.norm_eq_abs, abs_of_nonneg (spectralMajorant_nonneg a b x),
      Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hxpos.le _), one_mul]
    simpa only [spectralMajorant, abs_of_pos hxpos] using
      (min_le_right (x ^ (1 - 2 * b)) (x ^ (-1 - 2 * a)))
  have hlnear : (fun x : ℝ => (Real.log |x|) ^ k) =O[𝓝[>] 0]
      (fun x => x ^ (b - 1)) := by
    apply IsBigO.of_norm_left
    simpa only [Real.rpow_natCast, norm_pow, Real.norm_eq_abs, Real.log_abs] using
      (isLittleO_abs_log_rpow_rpow_nhdsGT_zero (k : ℝ) (by linarith : b - 1 < 0)).isBigO
  have hlfar : (fun x : ℝ => (Real.log |x|) ^ k) =O[atTop]
      (fun x => x ^ a) := by
    simpa only [Real.rpow_natCast, Real.log_abs] using
      (isLittleO_log_rpow_rpow_atTop (k : ℝ) ha).isBigO
  have hpos : IntegrableOn
      (fun x => (Real.log |x|) ^ k * spectralMajorant a b x) (Ioi 0) := by
    rw [integrableOn_Ioi_iff_integrableAtFilter_atTop_nhdsWithin]
    refine ⟨?_, ?_, ?_⟩
    · have hb : (fun x => (Real.log |x|) ^ k * spectralMajorant a b x) =O[atTop]
          (fun x : ℝ => x ^ (-1 - a)) := by
        apply (hlfar.mul hfar).congr' (EventuallyEq.refl _ _) ?_
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
        rw [← Real.rpow_add hx]
        congr 1
        ring
      apply hb.integrableAtFilter hm.stronglyMeasurableAtFilter
      exact ⟨Ioi 1, Ioi_mem_atTop 1,
        integrableOn_Ioi_rpow_of_lt (by linarith : -1 - a < -1) (by norm_num)⟩
    · have hb : (fun x => (Real.log |x|) ^ k * spectralMajorant a b x) =O[𝓝[>] 0]
          (fun x : ℝ => x ^ (-b)) := by
        apply (hlnear.mul hnear).congr' (EventuallyEq.refl _ _) ?_
        filter_upwards [self_mem_nhdsWithin] with x hx
        rw [← Real.rpow_add hx]
        congr 1
        ring
      apply hb.integrableAtFilter hm.stronglyMeasurableAtFilter
      exact ⟨Ioo 0 1, Ioo_mem_nhdsGT (by norm_num),
        (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1)).mpr
          (by linarith : -1 < -b)⟩
    · apply ContinuousOn.locallyIntegrableOn _ measurableSet_Ioi
      intro x hx
      have hx0 : x ≠ 0 := ne_of_gt hx
      have hc : ContinuousAt (spectralMajorant a b) x := by
        unfold spectralMajorant
        exact (continuous_abs.continuousAt.rpow_const (Or.inl (abs_ne_zero.mpr hx0))).min
          (continuous_abs.continuousAt.rpow_const (Or.inl (abs_ne_zero.mpr hx0)))
      exact (((Real.continuousAt_log (abs_ne_zero.mpr hx0)).comp continuous_abs.continuousAt).pow k
        |>.mul hc).continuousWithinAt
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  refine ⟨?_, hpos⟩
  rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
    (Homeomorph.neg ℝ).measurableEmbedding]
  simpa only [Function.comp_def, spectralMajorant, abs_neg, neg_preimage,
    neg_Iio, neg_zero] using hpos

theorem rawHarmonizable_norm_sq_abs (h t x : ℝ) :
    ‖rawHarmonizable h t |x|‖ ^ 2 = ‖rawHarmonizable h t x‖ ^ 2 := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg hx, rawHarmonizable_norm_sq_even]

/-- A uniform bound for all |t| ≤ 1 and a ≤ h ≤ b, with a > 0 and b < 1. -/
theorem rawHarmonizable_norm_sq_uniform (a b h t x : ℝ) (ha : 0 < a) (hb : b < 1)
    (hah : a ≤ h) (hhb : h ≤ b) (ht : |t| ≤ 1) :
    ‖rawHarmonizable h t x‖ ^ 2 ≤ 4 * spectralMajorant a b x := by
  by_cases hx : x = 0
  · subst x
    simpa only [rawHarmonizable, mul_zero, Complex.ofReal_zero, Complex.exp_zero,
      sub_self, zero_div, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (spectralMajorant_nonneg a b 0)
  have hx0 : 0 < |x| := abs_pos.mpr hx
  have he : -1 - 2 * a ≤ 1 - 2 * b := by linarith
  rw [← rawHarmonizable_norm_sq_abs]
  rcases le_total |x| 1 with hx1 | hx1
  · have hr := Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (by linarith : 1 - 2 * b ≤ 1 - 2 * h)
    have hmin := Real.rpow_le_rpow_of_exponent_ge hx0 hx1 he
    rw [spectralMajorant, min_eq_left hmin]
    have hts : t ^ 2 ≤ 1 := by nlinarith [sq_abs t, abs_nonneg t]
    calc
      _ ≤ t ^ 2 * |x| ^ (1 - 2 * h) := rawHarmonizable_norm_sq_near h t |x| hx0
      _ ≤ 1 * |x| ^ (1 - 2 * b) := mul_le_mul hts hr (Real.rpow_nonneg hx0.le _) (by norm_num)
      _ ≤ 4 * |x| ^ (1 - 2 * b) := by nlinarith [Real.rpow_nonneg hx0.le (1 - 2 * b)]
  · have hr := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith : -1 - 2 * h ≤ -1 - 2 * a)
    have hmin := Real.rpow_le_rpow_of_exponent_le hx1 he
    rw [spectralMajorant, min_eq_right hmin]
    exact (rawHarmonizable_norm_sq_far h t |x| hx0).trans (mul_le_mul_of_nonneg_left hr (by norm_num))

def spectralEnvelope (a b x : ℝ) : ℝ := Real.sqrt (spectralMajorant a b x)

theorem spectralEnvelope_memLp (a b : ℝ) (ha : 0 < a) (hb : b < 1) :
    MemLp (spectralEnvelope a b) 2 volume := by
  apply (memLp_two_iff_integrable_sq (by unfold spectralEnvelope spectralMajorant; fun_prop)).mpr
  have hi := spectralMajorant_log_weight_integrable a b ha hb 0
  simpa only [spectralEnvelope, Real.sq_sqrt (spectralMajorant_nonneg a b _), pow_zero, one_mul] using hi

theorem spectralLogEnvelope_memLp (a b : ℝ) (ha : 0 < a) (hb : b < 1) :
    MemLp (fun x => |Real.log (|x|)| * spectralEnvelope a b x) 2 volume := by
  apply (memLp_two_iff_integrable_sq (by unfold spectralEnvelope spectralMajorant; fun_prop)).mpr
  have hi := spectralMajorant_log_weight_integrable a b ha hb 2
  simpa only [spectralEnvelope, mul_pow, sq_abs,
    Real.sq_sqrt (spectralMajorant_nonneg a b _)] using hi

theorem rawHarmonizable_norm_uniform (a b h t x : ℝ) (ha : 0 < a) (hb : b < 1)
    (hah : a ≤ h) (hhb : h ≤ b) (ht : |t| ≤ 1) :
    ‖rawHarmonizable h t x‖ ≤ 2 * spectralEnvelope a b x := by
  have hs := rawHarmonizable_norm_sq_uniform a b h t x ha hb hah hhb ht
  have he := Real.sq_sqrt (spectralMajorant_nonneg a b x)
  have hp := Real.sqrt_nonneg (spectralMajorant a b x)
  unfold spectralEnvelope
  nlinarith [norm_nonneg (rawHarmonizable h t x)]

theorem rawHarmonizable_hasDerivAt (h t x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun u => rawHarmonizable u t x)
      (-Real.log |x| • rawHarmonizable h t x) h := by
  have hd := (((hasDerivAt_id h).add_const (1 / 2 : ℝ)).neg).const_rpow (abs_pos.mpr hx)
  simp only [id_eq, Pi.neg_apply] at hd
  have he := hd.smul_const (Complex.exp (Complex.I * (t * x : ℝ)) - 1)
  convert! he using 1
  · ext u
    rw [rawHarmonizable_smul, Real.rpow_neg (abs_nonneg x)]
  · rw [rawHarmonizable_smul, Real.rpow_neg (abs_nonneg x), smul_smul]
    congr 1
    ring

/-- Uniform pointwise parameter control, ready to pass through L². -/
theorem rawHarmonizable_parameter_bound (a b h k t x : ℝ) (ha : 0 < a) (hb : b < 1)
    (hh : h ∈ Icc a b) (hk : k ∈ Icc a b) (ht : |t| ≤ 1) (hx : x ≠ 0) :
    ‖rawHarmonizable h t x - rawHarmonizable k t x‖ ≤
      (2 * (|Real.log (|x|)| * spectralEnvelope a b x)) * |h - k| := by
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u hu => (rawHarmonizable_hasDerivAt u t x hx).hasDerivWithinAt)
    (fun u hu => show ‖-Real.log |x| • rawHarmonizable u t x‖ ≤
      2 * (|Real.log (|x|)| * spectralEnvelope a b x) from by
        rw [norm_smul, Real.norm_eq_abs, abs_neg]
        have hn := mul_le_mul_of_nonneg_left
          (rawHarmonizable_norm_uniform a b u t x ha hb hu.1 hu.2 ht) (abs_nonneg (Real.log |x|))
        simpa only [mul_left_comm, mul_assoc] using hn)
    (convex_Icc a b) hk hh
  simpa only [Real.norm_eq_abs] using hmvt

def rawHarmonizableFeature (h : Ioo (0 : ℝ) 1) (t : ℝ) : Lp ℂ 2 (volume : Measure ℝ) :=
  (rawHarmonizable_memLp h t h.property.1 h.property.2).toLp _

theorem rawHarmonizableFeature_ae (h : Ioo (0 : ℝ) 1) (t : ℝ) :
    rawHarmonizableFeature h t =ᵐ[volume] rawHarmonizable h t := MemLp.coeFn_toLp _

/-- Both L² bounds use constants independent of h, k, and time. -/
theorem rawHarmonizableFeature_uniform_control (a b : ℝ) (ha : 0 < a) (hb : b < 1) :
    ∃ M ≥ 0, ∃ L ≥ 0,
      (∀ h : Ioo (0 : ℝ) 1, (h : ℝ) ∈ Icc a b → ∀ t, |t| ≤ 1 →
        ‖rawHarmonizableFeature h t‖ ≤ M) ∧
      (∀ h k : Ioo (0 : ℝ) 1, (h : ℝ) ∈ Icc a b → (k : ℝ) ∈ Icc a b →
        ∀ t, |t| ≤ 1 → ‖rawHarmonizableFeature h t - rawHarmonizableFeature k t‖ ≤
          L * |(h : ℝ) - k|) := by
  let e : Lp ℝ 2 (volume : Measure ℝ) := (spectralEnvelope_memLp a b ha hb).toLp _
  let d : Lp ℝ 2 (volume : Measure ℝ) := (spectralLogEnvelope_memLp a b ha hb).toLp _
  have he : e =ᵐ[volume] spectralEnvelope a b := MemLp.coeFn_toLp _
  have hd : d =ᵐ[volume] (fun x => |Real.log (|x|)| * spectralEnvelope a b x) := MemLp.coeFn_toLp _
  refine ⟨2 * ‖e‖, by positivity, 2 * ‖d‖, by positivity, ?_, ?_⟩
  · intro h hh t ht
    apply Lp.norm_le_mul_norm_of_ae_le_mul (g := e)
    filter_upwards [rawHarmonizableFeature_ae h t, he] with x hx hy
    rw [hx, hy, Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ spectralEnvelope a b x from Real.sqrt_nonneg _)]
    exact rawHarmonizable_norm_uniform a b h t x ha hb hh.1 hh.2 ht
  · intro h k hh hk t ht
    have hn : ‖rawHarmonizableFeature h t - rawHarmonizableFeature k t‖ ≤
        (2 * |(h : ℝ) - k|) * ‖d‖ := by
      apply Lp.norm_le_mul_norm_of_ae_le_mul (g := d)
      filter_upwards [Lp.coeFn_sub (rawHarmonizableFeature h t) (rawHarmonizableFeature k t),
        rawHarmonizableFeature_ae h t, rawHarmonizableFeature_ae k t, hd,
        volume.ae_ne (0 : ℝ)] with x hsub hx hy hz hx0
      rw [hsub, Pi.sub_apply, hx, hy, hz, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (abs_nonneg _) (show 0 ≤ spectralEnvelope a b x from Real.sqrt_nonneg _))]
      have hp := rawHarmonizable_parameter_bound a b h k t x ha hb hh hk ht hx0
      calc
        _ ≤ (2 * (|Real.log (|x|)| * spectralEnvelope a b x)) * |(h : ℝ) - k| := hp
        _ = _ := by ring
    calc
      _ ≤ (2 * |(h : ℝ) - k|) * ‖d‖ := hn
      _ = _ := by ring

theorem harmonizableFeature_eq_normalized_raw (h : Ioo (0 : ℝ) 1) (t : ℝ) :
    harmonizableFeature h t = (Real.sqrt 2 * harmonizableD h)⁻¹ • rawHarmonizableFeature h t := by
  apply Lp.ext
  filter_upwards [harmonizableFeature_ae h t, rawHarmonizableFeature_ae h t,
    Lp.coeFn_smul (Real.sqrt 2 * harmonizableD h)⁻¹ (rawHarmonizableFeature h t)] with x hx hy hz
  rw [hx, hz, Pi.smul_apply, hy]
  rfl

def harmonizableNormalizer (h : ℝ) : ℝ := (Real.sqrt 2 * harmonizableD h)⁻¹

def harmonizableNormalizerSlope (h : ℝ) : ℝ :=
  -(Real.sqrt 2 * harmonizableDSlope h) / (Real.sqrt 2 * harmonizableD h) ^ 2

theorem harmonizableNormalizer_hasDerivAt (h : ℝ) (hh : 0 < h) (hh1 : h < 1) :
    HasDerivAt harmonizableNormalizer (harmonizableNormalizerSlope h) h := by
  exact ((harmonizableD_hasDerivAt h hh hh1).const_mul (Real.sqrt 2)).inv
    (mul_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (by norm_num))) (harmonizableD_pos h hh hh1).ne')

theorem harmonizableNormalizer_uniform_control (a b : ℝ) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) :
    ∃ M ≥ 0, ∃ L ≥ 0,
      (∀ h ∈ Icc a b, |harmonizableNormalizer h| ≤ M) ∧
      (∀ h ∈ Icc a b, ∀ k ∈ Icc a b,
        |harmonizableNormalizer h - harmonizableNormalizer k| ≤ L * |h - k|) := by
  have hn : ∀ h ∈ Ioo (0 : ℝ) 1, Real.sqrt 2 * harmonizableD h ≠ 0 := by
    intro h hh
    exact mul_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))
      (harmonizableD_pos h hh.1 hh.2).ne'
  have hc : ContinuousOn harmonizableNormalizer (Ioo 0 1) :=
    (continuousOn_const.mul harmonizableD_continuousOn).inv₀ hn
  have hdc : ContinuousOn harmonizableNormalizerSlope (Ioo 0 1) :=
    (continuousOn_const.mul harmonizableDSlope_continuousOn).neg.div
      ((continuousOn_const.mul harmonizableD_continuousOn).pow 2) (fun h hh => pow_ne_zero 2 (hn h hh))
  have hsub : Icc a b ⊆ Ioo (0 : ℝ) 1 := fun h hh => ⟨ha.trans_le hh.1, hh.2.trans_lt hb⟩
  obtain ⟨u, hu, hum⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab) (hc.norm.mono hsub)
  obtain ⟨v, hv, hvm⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab) (hdc.norm.mono hsub)
  refine ⟨‖harmonizableNormalizer u‖, norm_nonneg _, ‖harmonizableNormalizerSlope v‖,
    norm_nonneg _, ?_, ?_⟩
  · intro h hh
    simpa only [Real.norm_eq_abs, Set.mem_setOf_eq] using hum hh
  · intro h hh k hk
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun x hx => (harmonizableNormalizer_hasDerivAt x (hsub hx).1 (hsub hx).2).hasDerivWithinAt)
      (fun x hx => hvm hx) (convex_Icc a b) hk hh
    simpa only [Real.norm_eq_abs] using hmvt

/-- The actual normalized spectral feature has a uniform L² parameter bound for |t| ≤ 1. -/
theorem harmonizableFeature_uniform_parameter_lipschitz (a b : ℝ)
    (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) :
    ∃ C ≥ 0, ∀ h k : Ioo (0 : ℝ) 1, (h : ℝ) ∈ Icc a b → (k : ℝ) ∈ Icc a b →
      ∀ t, |t| ≤ 1 → ‖harmonizableFeature h t - harmonizableFeature k t‖ ≤ C * |(h : ℝ) - k| := by
  obtain ⟨M, hM, L, hL, hnorm, hlip⟩ := rawHarmonizableFeature_uniform_control a b ha hb
  obtain ⟨N, hN, K, hK, hcnorm, hclip⟩ := harmonizableNormalizer_uniform_control a b ha hb hab
  refine ⟨N * L + K * M, by positivity, ?_⟩
  intro h k hh hk t ht
  rw [harmonizableFeature_eq_normalized_raw, harmonizableFeature_eq_normalized_raw]
  change ‖harmonizableNormalizer h • rawHarmonizableFeature h t -
      harmonizableNormalizer k • rawHarmonizableFeature k t‖ ≤ _
  have he : harmonizableNormalizer h • rawHarmonizableFeature h t -
      harmonizableNormalizer k • rawHarmonizableFeature k t =
      harmonizableNormalizer h • (rawHarmonizableFeature h t - rawHarmonizableFeature k t) +
        (harmonizableNormalizer h - harmonizableNormalizer k) • rawHarmonizableFeature k t := by module
  rw [he]
  calc
    _ ≤ ‖harmonizableNormalizer h • (rawHarmonizableFeature h t - rawHarmonizableFeature k t)‖ +
        ‖(harmonizableNormalizer h - harmonizableNormalizer k) • rawHarmonizableFeature k t‖ := norm_add_le _ _
    _ = |harmonizableNormalizer h| * ‖rawHarmonizableFeature h t - rawHarmonizableFeature k t‖ +
        |harmonizableNormalizer h - harmonizableNormalizer k| * ‖rawHarmonizableFeature k t‖ := by
      simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ N * (L * |(h : ℝ) - k|) + (K * |(h : ℝ) - k|) * M :=
      add_le_add (mul_le_mul (hcnorm h hh) (hlip h k hh hk t ht) (norm_nonneg _) hN)
        (mul_le_mul (hclip h hh k hk) (hnorm k hk t ht) (norm_nonneg _)
          (mul_nonneg hK (abs_nonneg _)))
    _ = _ := by ring

end Hurst
