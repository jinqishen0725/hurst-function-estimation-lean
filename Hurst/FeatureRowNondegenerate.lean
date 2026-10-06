import Hurst.VaryingIncrement
import Hurst.FirstStrideGrid
import Hurst.ActualQuadratureConfluence

/-!
# Feature-row nondegeneracy: the harmonizable increments never vanish

This file resolves the `hane` data premise of the full-chain endpoints at the
spectral level.  The feature-row coefficient sum is, by
`Hurst.FirstStrideGrid.gridStrideFirst_feature_identity`, a positive scalar
`ℓ ^ h` (`ℓ = 1 / n > 0`) times the harmonizable first-stride increment
`gridStrideFirstActual`, so `hane` reduces to the nonvanishing of

`normalizedVaryingIncrement h k s ℓ = ℓ ^ (-h) • (feat k (s+ℓ) - feat h s)`.

## Math first (the route-A contract; deviations are written back below)

**Claim.**  For all `h k ∈ Ioo 0 1`, `s ∈ ℝ`, `ℓ > 0`:
`normalizedVaryingIncrement h k s ℓ ≠ 0`.

Since the scalar `ℓ ^ (-h) ≠ 0`, this is `feat k (s+ℓ) ≠ feat h v` with
`v := s`, `u := s + ℓ`, `u - v = ℓ ≠ 0`.

*Degenerate cases.*  `‖feat h t‖² = |t| ^ (2h)` (Harmonizable), so
`feat h 0 = 0`; if `v = 0` the norm is `u ^ (2k) = ℓ ^ (2k) > 0`; if
`u = 0` (i.e. `s = -ℓ`) the norm is `|v| ^ (2h) = ℓ ^ (2h) > 0`.

*Main case (`u ≠ 0`, `v ≠ 0`).*  The squared distance has the a.e. pointwise
representation (`harmonizableFeature_sub_norm_sq`)

`‖feat k u - feat h v‖² = ∫ x, ‖ĝ_k(u,x) - ĝ_h(v,x)‖² dx`,

with `ĝ_h(t,x) = (√2 · D_h)⁻¹ (e^{itx} - 1) / x^{h+1/2}` the a.e.
representative.  Suppose it vanished.  The integrand is then zero a.e.;
`ĝ_k(u,·) - ĝ_h(v,·)` is continuous on `(0, ∞)`, so a.e.-zero forces
`F ≡ 0` on `(0, ∞)` (`continuousOn_Ioi_ae_zero`).

Evaluating the identity `α_k x^{-k-1/2}(e^{iux}-1) = α_h x^{-h-1/2}(e^{ivx}-1)`
(where `α_h := (√2 D_h)⁻¹ ≠ 0`) at `x_u := 2π/|u|`, where `e^{iu x_u} = 1`
(`u x_u = ±2π`), gives `e^{iv x_u} = 1`, hence `v = n |u|` with `n ∈ ℤ`
(`Complex.exp_eq_one_iff`); symmetrically `u = m |v|` with `m ∈ ℤ`.  Taking
absolute values, `|v| = |n| |u| ≥ |u|` and `|u| ≥ |v|` (`|n|, |m| ≥ 1` since
`n, m ≠ 0`), so `|v| = |u|`, `|n| = |m| = 1`, and `v = ±u`.  `v = u`
contradicts `ℓ ≠ 0`; for `v = -u` the identity reads
`α_k x^{-k-1/2}(e^{iux}-1) = α_h x^{-h-1/2}(e^{-iux}-1)`.  Taking moduli at
`x₀ := π/|u|` and `x₁ := π/(2|u|)` (where `|e^{iux}-1| = 2` resp. `√2 ≠ 0`,
and the `±u` exponents have equal moduli by the cosine formula) and dividing
gives `2^{h-k} = 1`, hence `h = k` (`log 2 ≠ 0`).  Then the pointwise identity
becomes `e^{iux} - 1 = e^{-iux} - 1` at `x₁`, i.e. `e^{±πi/2} = e^{∓πi/2}`,
i.e. `I = -I` — contradiction.  ∎

**Deviation from the task-book sketch**: the amplitude-ratio phrase
"`|ξ|^{h-k} ≠ 1` on a positive-measure set" of the sketch corresponds to the
`v = -u` sub-case only; the general first step is the integer-multiple
argument above (the sketch's `h = k` branch is subsumed).  No case of the
claim was refuted; route A is fully landed.

**Consequences.**  `gridStrideFirstActual n d H i ≠ 0` for `0 < d` and any
`H : Fin n → Ioo 0 1` (grid application: `s = grid n i ≥ 0` may be zero — the
degenerate case — and `u = s + d/n > 0`), and the endpoint's `hane` premise
discharges verbatim through `gridStrideFirst_feature_identity` with the
positive scalar `((1:ℝ)/n) ^ (H (strideFirstLeft n 1 i₀))`.
-/

set_option maxHeartbeats 1200000

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Complex
open scoped Topology RealInnerProductSpace ENNReal
namespace Hurst

/-! ## The a.e. pointwise representation of the squared distance -/

/-- The a.e. representative of a difference of harmonizable features. -/
theorem harmonizableFeature_sub_ae (h k : Ioo (0 : ℝ) 1) (v u : ℝ) :
    (harmonizableFeature k u - harmonizableFeature h v : Lp ℂ 2 volume) =ᵐ[volume]
      (normalizedHarmonizable k u - normalizedHarmonizable h v) :=
  Lp.coeFn_sub _ _ |>.trans ((harmonizableFeature_ae k u).sub (harmonizableFeature_ae h v))

/-- The squared distance of two (possibly different-parameter) harmonizable
features is the integral of the pointwise squared distance of the a.e.
representatives. -/
theorem harmonizableFeature_sub_norm_sq (h k : Ioo (0 : ℝ) 1) (v u : ℝ) :
    ‖harmonizableFeature k u - harmonizableFeature h v‖ ^ 2
      = ∫ x, ‖normalizedHarmonizable k u x - normalizedHarmonizable h v x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [harmonizableFeature_sub_ae h k v u] with x hx
  rw [hx, Pi.sub_apply, real_inner_self_eq_norm_sq]

/-! ## A.e.-zero plus continuity forces zero -/

/-- A ℂ-valued function that is a.e. zero and continuous on the positive
half-line is zero there. -/
theorem continuousOn_Ioi_ae_zero {g : ℝ → ℂ} (hcont : ContinuousOn g (Ioi (0 : ℝ)))
    (hae : g =ᵐ[volume] fun _ => (0 : ℂ)) : ∀ x ∈ Ioi (0 : ℝ), g x = 0 := by
  intro x hx
  by_contra hne
  have hx0 : (0 : ℝ) < ‖g x‖ := norm_pos_iff.mpr hne
  have hcat : ContinuousAt g x := hcont.continuousAt (Ioi_mem_nhds hx)
  obtain ⟨δ, hδpos, hδball⟩ := Metric.eventually_nhds_iff_ball.mp
    (hcat.eventually (Metric.ball_mem_nhds (g x) (half_pos hx0)))
  have hIoo : Ioo (x - δ) (x + δ) ≤ {y : ℝ | g y ≠ 0} := by
    intro y hy hzy
    have hdist : dist y x < δ := by
      rw [Real.dist_eq, abs_lt]
      exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have hbd : ‖g y - g x‖ < ‖g x‖ / 2 := by
      simpa only [dist_eq_norm] using hδball y (Metric.mem_ball.mpr hdist)
    rw [hzy, zero_sub, norm_neg] at hbd
    linarith [norm_nonneg (g x)]
  have hnull : volume {y : ℝ | g y ≠ 0} = 0 :=
    ae_iff.mp hae
  exact absurd (measure_mono_null hIoo hnull) (by
    have hvol : (0 : ℝ≥0∞) < volume (Ioo (x - δ) (x + δ)) := by
      rw [Real.volume_Ioo, ENNReal.ofReal_pos]
      linarith
    exact hvol.ne')

/-! ## Continuity of the representative and exponential values -/

/-- The raw harmonizable feature is continuous on the positive half-line. -/
theorem continuousOn_rawHarmonizable (h : Ioo (0 : ℝ) 1) (t : ℝ) :
    ContinuousOn (rawHarmonizable h t) (Ioi (0 : ℝ)) := by
  have hpow : ContinuousOn (fun x : ℝ => (x : ℝ) ^ ((h : ℝ) + 1 / 2)) (Ioi (0 : ℝ)) :=
    continuousOn_id.rpow_const
      (fun x _ => Or.inr (show (0 : ℝ) ≤ (h : ℝ) + 1 / 2 by linarith [h.property.1]))
  have hnum : ContinuousOn (fun x : ℝ => Complex.exp (Complex.I * (t * x : ℝ)) - 1)
      (Ioi (0 : ℝ)) := Continuous.continuousOn (by fun_prop)
  have hden : ContinuousOn
      (fun x : ℝ => (((x : ℝ) ^ ((h : ℝ) + 1 / 2) : ℝ) : ℂ)) (Ioi (0 : ℝ)) :=
    Complex.continuous_ofReal.comp_continuousOn hpow
  have hdennz : ∀ x ∈ Ioi (0 : ℝ),
      (((x : ℝ) ^ ((h : ℝ) + 1 / 2) : ℝ) : ℂ) ≠ 0 := by
    intro x hx
    exact Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hx _).ne'
  refine ContinuousOn.congr (hnum.div hden hdennz) ?_
  intro x hx
  simp only [rawHarmonizable, Pi.div_apply,
    abs_of_pos (show (0 : ℝ) < x from hx)]

/-- The normalized representative is continuous on the positive half-line. -/
theorem continuousOn_normalizedHarmonizable (h : Ioo (0 : ℝ) 1) (t : ℝ) :
    ContinuousOn (normalizedHarmonizable h t) (Ioi (0 : ℝ)) := by
  show ContinuousOn (fun x => normalizedHarmonizable h t x) (Ioi (0 : ℝ))
  simp only [normalizedHarmonizable, Pi.smul_apply, Complex.real_smul]
  exact continuousOn_const.mul (continuousOn_rawHarmonizable h t)

/-- The squared modulus of `e^{iθ} - 1`. -/
theorem norm_exp_I_mul_sub_one (θ : ℝ) :
    ‖Complex.exp (Complex.I * θ) - 1‖ ^ 2 = (2 : ℝ) - 2 * Real.cos θ := by
  have h := exponential_increment_inner θ θ
  rw [real_inner_self_eq_norm_sq] at h
  rw [sub_self, Real.cos_zero] at h
  linarith

/-! ## Exponential values at the sampling points -/

/-- `e^{2πi} = 1` in the `I * ↑r` shape. -/
private theorem exp_I_mul_two_pi_pos : Complex.exp (Complex.I * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
  rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_two_pi, Real.sin_two_pi]
  simp

/-- `e^{πi} = -1` in the `I * ↑r` shape. -/
private theorem exp_I_mul_pi_pos : Complex.exp (Complex.I * ((Real.pi : ℝ) : ℂ)) = -1 := by
  rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi, Real.sin_pi]
  simp

/-- `e^{πi/2} = i` in the `I * ↑r` shape. -/
private theorem exp_I_mul_pi_half_pos :
    Complex.exp (Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) = Complex.I := by
  rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

/-- `e^{±2πi} = 1` in the `I * ↑r` shape. -/
private theorem exp_I_mul_two_pi {r : ℝ} (hr : r = 2 * Real.pi ∨ r = -(2 * Real.pi)) :
    Complex.exp (Complex.I * (r : ℂ)) = 1 := by
  rcases hr with hr | hr
  · rw [hr]
    exact exp_I_mul_two_pi_pos
  · rw [hr, Complex.ofReal_neg,
      show Complex.I * -(↑(2 * Real.pi)) = -(Complex.I * ((2 * Real.pi : ℝ) : ℂ)) by ring,
      Complex.exp_neg, exp_I_mul_two_pi_pos]
    norm_num

/-- `e^{±πi} = -1` in the `I * ↑r` shape. -/
private theorem exp_I_mul_pi {r : ℝ} (hr : r = Real.pi ∨ r = -(Real.pi)) :
    Complex.exp (Complex.I * (r : ℂ)) = -1 := by
  rcases hr with hr | hr
  · rw [hr]
    exact exp_I_mul_pi_pos
  · rw [hr, Complex.ofReal_neg,
      show Complex.I * -(↑Real.pi) = -(Complex.I * ((Real.pi : ℝ) : ℂ)) by ring,
      Complex.exp_neg, exp_I_mul_pi_pos]
    norm_num

/-- `e^{-πi/2} = -i` in the `I * ↑r` shape. -/
private theorem exp_I_mul_pi_half_neg :
    Complex.exp (Complex.I * ((-(Real.pi / 2) : ℝ) : ℂ)) = -(Complex.I) := by
  rw [show (Complex.I * ((-(Real.pi / 2) : ℝ) : ℂ))
      = -(Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) from by
    rw [Complex.ofReal_neg]; ring, Complex.exp_neg, exp_I_mul_pi_half_pos,
    Complex.inv_I]

/-- `e^{±πi/2} = ±i` in the `I * ↑r` shape. -/
private theorem exp_I_mul_pi_half {r : ℝ} (hr : r = Real.pi / 2 ∨ r = -(Real.pi / 2)) :
    Complex.exp (Complex.I * (r : ℂ)) = Complex.I ∨
      Complex.exp (Complex.I * (r : ℂ)) = -(Complex.I) := by
  rcases hr with hr | hr
  · left
    rw [hr]
    exact exp_I_mul_pi_half_pos
  · right
    rw [hr]
    exact exp_I_mul_pi_half_neg

/-! ## The main nonvanishing lemma -/

/-- **The harmonizable varying increment never vanishes** (route A, all
parameters): for `h k ∈ Ioo 0 1`, `s ∈ ℝ`, `ℓ > 0`,
`normalizedVaryingIncrement h k s ℓ ≠ 0`.  This is the spectral-resolution
input that discharges the `hane` data premise; see the file header for the
full contract. -/
theorem normalizedVaryingIncrement_ne_zero (h k : Ioo (0 : ℝ) 1) (s ℓ : ℝ) (hℓ : 0 < ℓ) :
    normalizedVaryingIncrement h k s ℓ ≠ 0 := by
  intro hz
  have hsub : harmonizableFeature k (s + ℓ) - harmonizableFeature h s = 0 := by
    rw [normalizedVaryingIncrement, smul_eq_zero] at hz
    rcases hz with h0 | h0
    · exact absurd h0 (Real.rpow_pos_of_pos hℓ _).ne'
    · exact h0
  by_cases hu0 : s + ℓ = 0
  · -- `feat k u = feat k 0 = 0`, so `feat h s = 0`, but `‖feat h s‖² = ℓ^{2h} > 0`
    rw [hu0] at hsub
    have hk0 : harmonizableFeature k (0 : ℝ) = 0 := by
      have hq := harmonizableFeature_norm_sq k 0
      rw [abs_zero, Real.zero_rpow
        (by linarith [k.property.1] : (2 * (k : ℝ)) ≠ 0)] at hq
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hq)
    rw [hk0, zero_sub] at hsub
    have hzs : harmonizableFeature h s = 0 := neg_eq_zero.mp hsub
    have h1 := harmonizableFeature_norm_sq h s
    rw [hzs, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      abs_eq_neg_self.mpr (show (s : ℝ) ≤ 0 by linarith),
      show (-(s : ℝ)) = ℓ from by linarith] at h1
    exact absurd h1.symm (Real.rpow_pos_of_pos hℓ _).ne'
  by_cases hsv : s = 0
  · -- `feat h v = feat h 0 = 0`, so `feat k u = 0`, but `‖feat k u‖² = ℓ^{2k} > 0`
    rw [hsv] at hsub
    have hh0 : harmonizableFeature h (0 : ℝ) = 0 := by
      have hq := harmonizableFeature_norm_sq h 0
      rw [abs_zero, Real.zero_rpow
        (by linarith [h.property.1] : (2 * (h : ℝ)) ≠ 0)] at hq
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hq)
    rw [hh0, sub_zero] at hsub
    have h1 := harmonizableFeature_norm_sq k (s + ℓ)
    rw [hsv] at h1
    rw [hsub, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at h1
    refine absurd h1.symm (Real.rpow_pos_of_pos (abs_pos.mpr ?_) _).ne'
    simpa using ne_of_gt hℓ
  -- main case: both points nonzero, `u - v = ℓ ≠ 0`
  have huNE : s + ℓ ≠ 0 := hu0
  have hsNE : s ≠ 0 := hsv
  set u := s + ℓ with hudef
  -- integral zero, then a.e. zero of the ℂ-difference, then everywhere zero
  have hint : ∫ x,
      ‖normalizedHarmonizable k u x - normalizedHarmonizable h s x‖ ^ 2 = 0 := by
    rw [← harmonizableFeature_sub_norm_sq h k s u, hsub, norm_zero]
    norm_num
  have hI1 : Integrable (fun x : ℝ => ‖normalizedHarmonizable k u x‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm
      ((Measurable.const_smul (rawHarmonizable_measurable k u) _).aestronglyMeasurable)).mp
      (normalizedHarmonizable_memLp k u k.property.1 k.property.2)
  have hI2 : Integrable (fun x : ℝ => ‖normalizedHarmonizable h s x‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm
      ((Measurable.const_smul (rawHarmonizable_measurable h s) _).aestronglyMeasurable)).mp
      (normalizedHarmonizable_memLp h s h.property.1 h.property.2)
  have hint2 : Integrable (fun x : ℝ =>
      ‖normalizedHarmonizable k u x - normalizedHarmonizable h s x‖ ^ 2) volume := by
    have hdom : Integrable (fun x : ℝ =>
        2 * ‖normalizedHarmonizable k u x‖ ^ 2
          + 2 * ‖normalizedHarmonizable h s x‖ ^ 2) volume :=
      (hI1.const_mul 2).add (hI2.const_mul 2)
    refine hdom.mono' ?_ ?_
    · exact (((Measurable.const_smul (rawHarmonizable_measurable k u) _).sub
        (Measurable.const_smul (rawHarmonizable_measurable h s) _)).norm.pow_const 2
        |>.aestronglyMeasurable)
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h1 := norm_sub_le (normalizedHarmonizable k u x) (normalizedHarmonizable h s x)
      have h2 := mul_self_le_mul_self (norm_nonneg _) h1
      nlinarith [sq_nonneg (‖normalizedHarmonizable k u x‖
        - ‖normalizedHarmonizable h s x‖)]
  have hae : (fun x : ℝ =>
      normalizedHarmonizable k u x - normalizedHarmonizable h s x)
      =ᵐ[volume] fun _ => (0 : ℂ) := by
    have hsq : (fun x : ℝ =>
        ‖normalizedHarmonizable k u x - normalizedHarmonizable h s x‖ ^ 2)
        =ᵐ[volume] fun _ => (0 : ℝ) :=
      (integral_eq_zero_iff_of_nonneg
        (f := fun x : ℝ => ‖normalizedHarmonizable k u x - normalizedHarmonizable h s x‖ ^ 2)
        (fun x => pow_nonneg (norm_nonneg _) 2) hint2).mp hint
    filter_upwards [hsq] with x hx
    refine norm_eq_zero.mp ?_
    nlinarith [norm_nonneg (normalizedHarmonizable k u x - normalizedHarmonizable h s x),
      hx]
  have hF0 : ∀ x ∈ Ioi (0 : ℝ),
      normalizedHarmonizable k u x - normalizedHarmonizable h s x = 0 :=
    continuousOn_Ioi_ae_zero
      ((continuousOn_normalizedHarmonizable k u).sub
        (continuousOn_normalizedHarmonizable h s)) hae
  -- the pointwise coefficient form of the vanishing identity
  have hpt : ∀ (t : Ioo (0 : ℝ) 1) (w x : ℝ), normalizedHarmonizable t w x
      = Complex.ofReal ((Real.sqrt 2 * harmonizableD t)⁻¹) * rawHarmonizable t w x := by
    intro t w x
    simp only [normalizedHarmonizable, Pi.smul_apply, Complex.real_smul]
  have hαpos : ∀ t : Ioo (0 : ℝ) 1, (0 : ℝ) < (Real.sqrt 2 * harmonizableD t)⁻¹ := by
    intro t
    exact inv_pos.mpr (mul_pos (Real.sqrt_pos.mpr (by norm_num))
      (harmonizableD_pos t t.property.1 t.property.2))
  have hαne : ∀ t : Ioo (0 : ℝ) 1,
      Complex.ofReal ((Real.sqrt 2 * harmonizableD t)⁻¹) ≠ 0 :=
    fun t => Complex.ofReal_ne_zero.mpr (inv_ne_zero (mul_ne_zero
      (by norm_num : (Real.sqrt 2 : ℝ) ≠ 0)
      (harmonizableD_pos t t.property.1 t.property.2).ne'))
  have hraw_eq_zero_of_exp {x w : ℝ} (hx : 0 < x) (t : Ioo (0 : ℝ) 1)
      (hex : Complex.exp (Complex.I * (w * x : ℝ)) = 1) :
      rawHarmonizable t w x = 0 := by
    simp only [rawHarmonizable, hex, sub_self, zero_div]
  have hexp_eq_one_of_raw {x w : ℝ} (hx : 0 < x) (t : Ioo (0 : ℝ) 1)
      (hraw : rawHarmonizable t w x = 0) :
      Complex.exp (Complex.I * (w * x : ℝ)) = 1 := by
    rw [rawHarmonizable, div_eq_zero_iff] at hraw
    rcases hraw with h0 | h0
    · exact sub_eq_zero.mp h0
    · exact absurd h0 (Complex.ofReal_ne_zero.mpr
        (Real.rpow_pos_of_pos (abs_pos.mpr (ne_of_gt hx)) _).ne')
  have hraw_norm {t : Ioo (0 : ℝ) 1} {w x : ℝ} {E : ℂ} (hx : 0 < x)
      (hE : Complex.exp (Complex.I * (w * x : ℝ)) = E) :
      ‖rawHarmonizable t w x‖ = ‖E - 1‖ / (x ^ ((t : ℝ) + 1 / 2)) := by
    rw [rawHarmonizable, abs_of_pos hx, hE, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx.le _)]
  -- evaluation at `x_u = 2π/|u|`: `s` is an integer multiple of `|u|`
  have hxupos : (0:ℝ) < 2 * Real.pi / |u| := by
    apply div_pos _ (abs_pos.mpr huNE)
    positivity
  have hFu := hF0 _ hxupos
  rw [hpt k u, hpt h s] at hFu
  have hexpu : Complex.exp (Complex.I * ((s * (2 * Real.pi / |u|) : ℝ) : ℂ)) = 1 := by
    have h0 : rawHarmonizable k u (2 * Real.pi / |u|) = 0 := by
      refine hraw_eq_zero_of_exp hxupos k ?_
      rcases abs_cases u with habs | habs
      · rw [habs.1, mul_div_cancel₀ _ (ne_of_gt (lt_of_le_of_ne habs.2 (Ne.symm huNE)))]
        exact exp_I_mul_two_pi (Or.inl rfl)
      · rw [habs.1, show (u : ℝ) * (2 * Real.pi / -u) = -(2 * Real.pi) by
          field_simp [huNE]]
        exact exp_I_mul_two_pi (Or.inr rfl)
    rw [h0, mul_zero, zero_sub, neg_eq_zero, mul_eq_zero] at hFu
    rcases hFu with h0' | hraws
    · exact absurd (Complex.ofReal_eq_zero.mp h0') (inv_ne_zero
        (mul_ne_zero (by norm_num : (Real.sqrt 2 : ℝ) ≠ 0)
          (harmonizableD_pos h h.property.1 h.property.2).ne'))
    · exact hexp_eq_one_of_raw hxupos h hraws
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexpu
  have hreal1 : (((s * (2 * Real.pi / |u|) : ℝ) : ℂ))
      = (((n * (2 * Real.pi) : ℝ) : ℂ)) := by
    refine mul_left_cancel₀ Complex.I_ne_zero ?_
    rw [hn]
    push_cast
    ring
  have hs_mult : (s : ℝ) = (n : ℝ) * |u| := by
    have hc := Complex.ofReal_inj.mp hreal1
    have habsU : |u| ≠ 0 := abs_ne_zero.mpr huNE
    have h2pi : (2 * Real.pi : ℝ) ≠ 0 := by linarith [Real.pi_pos]
    have hc2 : (s : ℝ) * (2 * Real.pi) = ((n : ℝ) * |u|) * (2 * Real.pi) := by
      have h1 := congrArg (fun z : ℝ => z * |u|) hc
      rw [mul_assoc, div_mul_cancel₀ _ habsU] at h1
      ring_nf at h1 ⊢
      exact h1
    exact mul_right_cancel₀ h2pi hc2
  -- evaluation at `x_v = 2π/|s|`: `u` is an integer multiple of `|s|`
  have hxvpos : (0:ℝ) < 2 * Real.pi / |s| := by
    apply div_pos _ (abs_pos.mpr hsNE)
    positivity
  have hFv := hF0 _ hxvpos
  rw [hpt k u, hpt h s] at hFv
  have hexpv : Complex.exp (Complex.I * ((u * (2 * Real.pi / |s|) : ℝ) : ℂ)) = 1 := by
    have h0 : rawHarmonizable h s (2 * Real.pi / |s|) = 0 := by
      refine hraw_eq_zero_of_exp hxvpos h ?_
      rcases abs_cases (s:ℝ) with habs | habs
      · rw [habs.1, mul_div_cancel₀ _ (ne_of_gt (lt_of_le_of_ne habs.2 (Ne.symm hsNE)))]
        exact exp_I_mul_two_pi (Or.inl rfl)
      · rw [habs.1, show (s : ℝ) * (2 * Real.pi / -s) = -(2 * Real.pi) by
          field_simp [hsNE]]
        exact exp_I_mul_two_pi (Or.inr rfl)
    rw [h0, mul_zero, sub_zero] at hFv
    rcases mul_eq_zero.mp hFv with h0' | hraws
    · exact absurd (Complex.ofReal_eq_zero.mp h0') (inv_ne_zero
        (mul_ne_zero (by norm_num : (Real.sqrt 2 : ℝ) ≠ 0)
          (harmonizableD_pos k k.property.1 k.property.2).ne'))
    · exact hexp_eq_one_of_raw hxvpos k hraws
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp hexpv
  have hreal2 : (((u * (2 * Real.pi / |s|) : ℝ) : ℂ))
      = (((m * (2 * Real.pi) : ℝ) : ℂ)) := by
    refine mul_left_cancel₀ Complex.I_ne_zero ?_
    rw [hm]
    push_cast
    ring
  have hu_mult : u = (m : ℝ) * |s| := by
    have hc := Complex.ofReal_inj.mp hreal2
    have habsS : |s| ≠ 0 := abs_ne_zero.mpr hsNE
    have h2pi : (2 * Real.pi : ℝ) ≠ 0 := by linarith [Real.pi_pos]
    have hc2 : u * (2 * Real.pi) = ((m : ℝ) * |s|) * (2 * Real.pi) := by
      have h1 := congrArg (fun z : ℝ => z * |s|) hc
      rw [mul_assoc, div_mul_cancel₀ _ habsS] at h1
      ring_nf at h1 ⊢
      exact h1
    exact mul_right_cancel₀ h2pi hc2
  -- `|s| = |u|`, hence both integer factors are ±1, hence `s = -u`
  have habs1 : |(s : ℝ)| = |(n : ℝ)| * |u| := by
    rw [hs_mult, abs_mul, abs_of_pos (abs_pos.mpr huNE)]
  have habs2 : |u| = |(m : ℝ)| * |s| := by
    rw [hu_mult, abs_mul, abs_of_pos (abs_pos.mpr hsNE)]
  have hge1 : (1 : ℝ) ≤ |(n : ℝ)| := by
    have hn0 : n ≠ 0 := by
      rintro rfl
      have hs0 : (s : ℝ) = 0 := by rw [hs_mult]; simp
      exact hsNE hs0
    have := Int.one_le_abs hn0
    exact_mod_cast this
  have hge2 : (1 : ℝ) ≤ |(m : ℝ)| := by
    have hm0 : m ≠ 0 := by
      rintro rfl
      have hu0' : u = 0 := by rw [hu_mult]; simp
      exact huNE hu0'
    have := Int.one_le_abs hm0
    exact_mod_cast this
  have hEq : |(s : ℝ)| = |u| := by
    have h1 : |u| ≤ |(s : ℝ)| := by rw [habs1]; nlinarith [abs_nonneg u, hge1]
    have h2 : |(s : ℝ)| ≤ |u| := by rw [habs2]; nlinarith [abs_nonneg s, hge2]
    exact le_antisymm h2 h1
  have honen : |(n : ℝ)| = 1 := by
    have huu : |(n : ℝ)| * |u| = |u| := by rw [← habs1, hEq]
    exact mul_right_cancel₀ (abs_ne_zero.mpr huNE) (by rw [one_mul]; exact huu)
  have honem : |(m : ℝ)| = 1 := by
    have huu : |(m : ℝ)| * |s| = |s| := by rw [← habs2, ← hEq]
    exact mul_right_cancel₀ (abs_ne_zero.mpr hsNE) (by rw [one_mul]; exact huu)
  have hsu : (s : ℝ) = -u := by
    rcases abs_eq (by norm_num : (0 : ℝ) ≤ 1) |>.mp honen with h1 | h1
    · rcases abs_eq (by norm_num : (0 : ℝ) ≤ 1) |>.mp honem with h2 | h2
      · -- n = 1, m = 1: s = |u|, u = |s| = |u| ⟹ s = u contra
        exfalso
        rw [h1, one_mul] at hs_mult
        rw [h2, one_mul, hEq] at hu_mult
        exact hℓ.ne (by linarith [hs_mult, hu_mult, hudef])
      · -- n = 1, m = -1: s = |u|, u = -|s| = -|u| ⟹ s = -u
        rw [h1, one_mul] at hs_mult
        rw [h2, neg_mul, one_mul, hEq] at hu_mult
        linarith [hs_mult, hu_mult]
    · rcases abs_eq (by norm_num : (0 : ℝ) ≤ 1) |>.mp honem with h2 | h2
      · -- n = -1, m = 1: s = -|u|, u = |s| = |u| ⟹ s = -u
        rw [h1, neg_mul, one_mul] at hs_mult
        rw [h2, one_mul, hEq] at hu_mult
        linarith [hs_mult, hu_mult]
      · -- n = -1, m = -1: s = -|u|, u = -|s| = -|u| ⟹ s = u contra
        exfalso
        rw [h1, neg_mul, one_mul] at hs_mult
        rw [h2, neg_mul, one_mul, hEq] at hu_mult
        exact hℓ.ne (by linarith [hs_mult, hu_mult, hudef])
  -- the ±u-symmetric pointwise identity
  have hFid : ∀ x ∈ Ioi (0 : ℝ),
      Complex.ofReal ((Real.sqrt 2 * harmonizableD k)⁻¹) * rawHarmonizable k u x
        = Complex.ofReal ((Real.sqrt 2 * harmonizableD h)⁻¹)
            * rawHarmonizable h (-u) x := by
    intro x hx
    have hthis := hF0 x hx
    rw [hpt k u, hpt h s, hsu] at hthis
    exact sub_eq_zero.mp hthis
  -- the norm balance at `x₀ = π/|u|` and `x₁ = π/(2|u|)`
  have hx0pos : (0:ℝ) < Real.pi / |u| := by
    apply div_pos _ (abs_pos.mpr huNE)
    positivity
  have hx1pos : (0:ℝ) < Real.pi / (2 * |u|) := by
    apply div_pos _ (by positivity)
    positivity
  have hE0a : Complex.exp (Complex.I * ((u * (Real.pi / |u|) : ℝ) : ℂ)) = -1 := by
    rcases abs_cases u with habs | habs
    · rw [habs.1, mul_div_cancel₀ _ (ne_of_gt (lt_of_le_of_ne habs.2 (Ne.symm huNE)))]
      exact exp_I_mul_pi (Or.inl rfl)
    · rw [habs.1, show (u : ℝ) * (Real.pi / -u) = -(Real.pi) by field_simp [huNE]]
      exact exp_I_mul_pi (Or.inr rfl)
  have hE0b : Complex.exp (Complex.I * (((-u) * (Real.pi / |u|) : ℝ) : ℂ)) = -1 := by
    rw [show ((-u) * (Real.pi / |u|) : ℝ) = -(u * (Real.pi / |u|)) by ring,
      Complex.ofReal_neg,
      show Complex.I * -(↑(u * (Real.pi / |u|)))
        = -(Complex.I * ((u * (Real.pi / |u|) : ℝ) : ℂ)) by ring,
      Complex.exp_neg, hE0a]
    norm_num
  have hE1a : Complex.exp (Complex.I * ((u * (Real.pi / (2 * |u|)) : ℝ) : ℂ)) = Complex.I ∨
      Complex.exp (Complex.I * ((u * (Real.pi / (2 * |u|)) : ℝ) : ℂ)) = -(Complex.I) := by
    rcases abs_cases u with habs | habs
    · rw [habs.1]
      rw [show (u : ℝ) * (Real.pi / (2 * u)) = Real.pi / 2 by field_simp [huNE]]
      exact exp_I_mul_pi_half (Or.inl rfl)
    · rw [habs.1]
      rw [show (u : ℝ) * (Real.pi / (2 * -u)) = -(Real.pi / 2) by field_simp [huNE]]
      exact exp_I_mul_pi_half (Or.inr rfl)
  have hE1b : Complex.exp (Complex.I * (((-u) * (Real.pi / (2 * |u|)) : ℝ) : ℂ)) = Complex.I ∨
      Complex.exp (Complex.I * (((-u) * (Real.pi / (2 * |u|)) : ℝ) : ℂ)) = -(Complex.I) := by
    rcases abs_cases u with habs | habs
    · rw [habs.1]
      rw [show ((-u) * (Real.pi / (2 * u) : ℝ)) = -(Real.pi / 2) by field_simp [huNE]]
      exact Or.inr exp_I_mul_pi_half_neg
    · rw [habs.1]
      rw [show ((-u) * (Real.pi / (2 * -u) : ℝ)) = Real.pi / 2 by field_simp [huNE]]
      exact Or.inl exp_I_mul_pi_half_pos
  have hN2 : ‖((-1 : ℂ) - 1)‖ = 2 := by
    have hq : ((-1 : ℂ) - 1) = (((-2 : ℝ) : ℂ)) := by norm_num
    rw [hq, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos (by norm_num)]
  have hNsqrt2 (E : ℂ) (hE : E = Complex.I ∨ E = -(Complex.I)) :
      ‖E - 1‖ = Real.sqrt 2 := by
    rw [← Real.sqrt_sq (norm_nonneg _)]
    rcases hE with hE | hE
    · rw [hE, ← exp_I_mul_pi_half_pos, norm_exp_I_mul_sub_one, Real.cos_pi_div_two]
      norm_num
    · rw [hE, ← exp_I_mul_pi_half_neg, norm_exp_I_mul_sub_one, Real.cos_neg,
        Real.cos_pi_div_two]
      norm_num
  -- the raw-norm values at the two sampling points
  have hrawN0a : ‖rawHarmonizable k u (Real.pi / |u|)‖
      = 2 / ((Real.pi / |u|) ^ ((k : ℝ) + 1 / 2)) := by
    rw [hraw_norm hx0pos hE0a, hN2]
  have hrawN0b : ‖rawHarmonizable h (-u) (Real.pi / |u|)‖
      = 2 / ((Real.pi / |u|) ^ ((h : ℝ) + 1 / 2)) := by
    rw [hraw_norm hx0pos hE0b, hN2]
  have hrawN1a : ‖rawHarmonizable k u (Real.pi / (2 * |u|))‖
      = Real.sqrt 2 / ((Real.pi / (2 * |u|)) ^ ((k : ℝ) + 1 / 2)) := by
    rcases hE1a with hE | hE
    · rw [hraw_norm hx1pos hE, hNsqrt2 _ (Or.inl rfl)]
    · rw [hraw_norm hx1pos hE, hNsqrt2 _ (Or.inr rfl)]
  have hrawN1b : ‖rawHarmonizable h (-u) (Real.pi / (2 * |u|))‖
      = Real.sqrt 2 / ((Real.pi / (2 * |u|)) ^ ((h : ℝ) + 1 / 2)) := by
    rcases hE1b with hE | hE
    · rw [hraw_norm hx1pos hE, hNsqrt2 _ (Or.inl rfl)]
    · rw [hraw_norm hx1pos hE, hNsqrt2 _ (Or.inr rfl)]
  -- the balanced identities (cross-multiplied monomial form)
  have hbal0 : ((Real.sqrt 2 * harmonizableD k)⁻¹ : ℝ)
      * ((Real.pi / |u|) ^ ((h : ℝ) + 1 / 2))
    = ((Real.sqrt 2 * harmonizableD h)⁻¹ : ℝ)
      * ((Real.pi / |u|) ^ ((k : ℝ) + 1 / 2)) := by
    have hnorm := congrArg norm (hFid _ hx0pos)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hαpos k),
      hrawN0a, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hαpos h),
      hrawN0b] at hnorm
    field_simp [(Real.rpow_pos_of_pos hx0pos _).ne',
      (harmonizableD_pos k k.property.1 k.property.2).ne',
      (harmonizableD_pos h h.property.1 h.property.2).ne'] at hnorm ⊢
    ring_nf at hnorm ⊢
    linarith
  have hbal1 : ((Real.sqrt 2 * harmonizableD k)⁻¹ : ℝ)
      * ((Real.pi / (2 * |u|)) ^ ((h : ℝ) + 1 / 2))
    = ((Real.sqrt 2 * harmonizableD h)⁻¹ : ℝ)
      * ((Real.pi / (2 * |u|)) ^ ((k : ℝ) + 1 / 2)) := by
    have hnorm := congrArg norm (hFid _ hx1pos)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hαpos k),
      hrawN1a, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hαpos h),
      hrawN1b] at hnorm
    field_simp [(Real.rpow_pos_of_pos hx1pos _).ne',
      (harmonizableD_pos k k.property.1 k.property.2).ne',
      (harmonizableD_pos h h.property.1 h.property.2).ne'] at hnorm ⊢
    ring_nf at hnorm ⊢
    linarith
  -- the exponents agree: `2^{h-k} = 1`, hence `h = k`
  have hYk : ((Real.pi / |u|) ^ (((h : ℝ) + 1 / 2) - ((k : ℝ) + 1 / 2))) ≠ 0 :=
    (Real.rpow_pos_of_pos hx0pos _).ne'
  have hA : ((Real.sqrt 2 * harmonizableD k)⁻¹ : ℝ)
      * ((Real.pi / |u|) ^ (((h : ℝ) + 1 / 2) - ((k : ℝ) + 1 / 2)))
      = ((Real.sqrt 2 * harmonizableD h)⁻¹ : ℝ) := by
    rw [Real.rpow_sub hx0pos, mul_div_assoc', div_eq_iff
      ((Real.rpow_pos_of_pos hx0pos ((k : ℝ) + 1 / 2)).ne')]
    exact hbal0
  have hB : ((Real.sqrt 2 * harmonizableD k)⁻¹ : ℝ)
      * ((Real.pi / (2 * |u|)) ^ (((h : ℝ) + 1 / 2) - ((k : ℝ) + 1 / 2)))
      = ((Real.sqrt 2 * harmonizableD h)⁻¹ : ℝ) := by
    rw [Real.rpow_sub hx1pos, mul_div_assoc', div_eq_iff
      ((Real.rpow_pos_of_pos hx1pos ((k : ℝ) + 1 / 2)).ne')]
    exact hbal1
  have hxy : (Real.pi / |u|) = 2 * (Real.pi / (2 * |u|)) := by field_simp
  have hcanc : ((Real.pi / |u|) ^ (((h : ℝ) + 1 / 2) - ((k : ℝ) + 1 / 2)))
      = ((Real.pi / (2 * |u|)) ^ (((h : ℝ) + 1 / 2) - ((k : ℝ) + 1 / 2))) := by
    refine mul_left_cancel₀ (hαpos k).ne' ?_
    rw [hA, hB]
  have h2pow : (2 : ℝ) ^ (((h : ℝ) + 1 / 2) - ((k : ℝ) + 1 / 2)) = 1 := by
    have h2e : (2 : ℝ) ^ (((h : ℝ) + 1 / 2) - ((k : ℝ) + 1 / 2))
        * ((Real.pi / (2 * |u|)) ^ (((h : ℝ) + 1 / 2) - ((k : ℝ) + 1 / 2)))
      = ((Real.pi / (2 * |u|)) ^ (((h : ℝ) + 1 / 2) - ((k : ℝ) + 1 / 2))) := by
      rw [← Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by positivity), ← hxy, hcanc]
    exact mul_right_cancel₀ (Real.rpow_pos_of_pos hx1pos _).ne'
      (show 2 ^ (((h : ℝ) + 1 / 2) - ((k : ℝ) + 1 / 2))
          * ((Real.pi / (2 * |u|)) ^ (((h : ℝ) + 1 / 2) - ((k : ℝ) + 1 / 2)))
        = 1 * ((Real.pi / (2 * |u|)) ^ (((h : ℝ) + 1 / 2) - ((k : ℝ) + 1 / 2))) from by
        rw [one_mul]; exact h2e)
  have hkeq : ((h : ℝ) + 1 / 2) - ((k : ℝ) + 1 / 2) = 0 := by
    have hlog := Real.log_rpow (by norm_num : (0:ℝ) < 2)
      (((h : ℝ) + 1 / 2) - ((k : ℝ) + 1 / 2))
    rw [h2pow, Real.log_one] at hlog
    rcases mul_eq_zero.mp hlog.symm with h0 | h0
    · exact h0
    · exact absurd h0 (Real.log_pos (by norm_num : (1:ℝ) < 2)).ne'
  have hcoef : Complex.ofReal ((Real.sqrt 2 * harmonizableD k)⁻¹)
      = Complex.ofReal ((Real.sqrt 2 * harmonizableD h)⁻¹) := by
    have hkh : (k : ℝ) = (h : ℝ) := by linarith [hkeq]
    rw [show harmonizableD k = harmonizableD h from by rw [hkh]]
  -- final contradiction: at `x₁` the two exponentials are `±I` and `∓I`
  have hfinal := hFid _ hx1pos
  rw [hcoef] at hfinal
  have hraws := mul_left_cancel₀ (hαne h) hfinal
  rw [rawHarmonizable, rawHarmonizable] at hraws
  rw [show ((k : ℝ) + 1 / 2) = ((h : ℝ) + 1 / 2) from by linarith [hkeq]] at hraws
  have habsx : |Real.pi / (2 * |u|)| = Real.pi / (2 * |u|) := abs_of_pos hx1pos
  rw [habsx] at hraws
  have hDne : (Complex.ofReal
      ((Real.pi / (2 * |u|)) ^ ((h : ℝ) + 1 / 2))) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hx1pos _).ne'
  have hmul := congrArg (fun z : ℂ => z *
      (Complex.ofReal ((Real.pi / (2 * |u|)) ^ ((h : ℝ) + 1 / 2)))) hraws
  rw [div_mul_cancel₀ _ hDne, div_mul_cancel₀ _ hDne] at hmul
  rw [show ((-u) * (Real.pi / (2 * |u|)) : ℝ) = -(u * (Real.pi / (2 * |u|))) by ring,
    Complex.ofReal_neg,
    show Complex.I * -(↑(u * (Real.pi / (2 * |u|))))
      = -(Complex.I * ((u * (Real.pi / (2 * |u|)) : ℝ) : ℂ)) by ring,
    Complex.exp_neg] at hmul
  rcases hE1a with hEv | hEv
  · rw [hEv, Complex.inv_I] at hmul
    have him := (Complex.ext_iff.mp hmul).2
    norm_num at him
  · rw [hEv, ← neg_inv, Complex.inv_I, neg_neg] at hmul
    have him := (Complex.ext_iff.mp hmul).2
    norm_num at him

/-! ## The grid application and the `hane` discharge -/

/-- **The grid first-stride increment never vanishes** — for every `n`, every
`0 < d`, EVERY parameter field `H : Fin n → Ioo 0 1` (no Hölder or midpoint
structure), and every stride index: `gridStrideFirstActual n d H i ≠ 0`.
This is strictly stronger than the endpoint's `hane` (which fixes
`H = midpointSampleHurst f hf.1 n` and `d = 1` at the active indices). -/
theorem gridStrideFirstActual_ne_zero (n d : ℕ) (hn : 0 < n) (hd : 0 < d)
    (H : Fin n → Ioo (0 : ℝ) 1) (i : Fin (n - d)) :
    gridStrideFirstActual n d H i ≠ 0 := by
  have hℓ : (0 : ℝ) < (d : ℝ) / n := div_pos (by exact_mod_cast hd) (by exact_mod_cast hn)
  exact normalizedVaryingIncrement_ne_zero (H (strideFirstLeft n d i))
    (H (strideFirstRight n d i)) (grid n i.val) ((d : ℝ) / n) hℓ

/-- **The `hane` data premise, discharged internally.**  The feature-row
coefficient sum equals the positive scalar `((1:ℝ)/n) ^ (H left)` times the
never-vanishing increment (`gridStrideFirst_feature_identity`), hence is
nonzero for every active index — for every parameter field, in particular the
midpoint sample of any `f` in the Hölder class. -/
theorem actualQ1_hane_discharged (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M)
    (n : ℕ) (hn : 0 < n) (δ t : ℝ)
    (k : Fin (localWeightActiveSet n 1 δ t).card) :
    ∑ i, actualQ1Coeff n δ t k i •
      actualQ1Obs f n (midpointSampleHurst f hf.1 n) i ≠ 0 := by
  set i₀ := localWeightActiveIndex n 1 δ t k with hi₀
  have hstep : gridStrideFirstActual n 1 (midpointSampleHurst f hf.1 n) i₀ ≠ 0 :=
    gridStrideFirstActual_ne_zero n 1 hn (by norm_num)
      (midpointSampleHurst f hf.1 n) i₀
  have hid := gridStrideFirst_feature_identity n 1 hn (by norm_num)
    (midpointSampleHurst f hf.1 n) i₀
  unfold actualQ1Coeff actualQ1Obs
  rw [hid]
  exact smul_ne_zero
    (Real.rpow_pos_of_pos (div_pos (by norm_num) (by exact_mod_cast hn))
      (midpointSampleHurst f hf.1 n (strideFirstLeft n 1 i₀))).ne' hstep

/-- The `hane` premise in the exact ∀-n shape consumed by the endpoints:
discharged for every `n` (vacuous at `n = 0`) and every active index. -/
theorem actualQ1_hane_all (f : ℝ → ℝ) (hf : f ∈ hurstHolderClass p M) (δ t : ℝ) :
    ∀ (n : ℕ) (k : Fin (localWeightActiveSet n 1 δ t).card),
      ∑ i, actualQ1Coeff n δ t k i •
        actualQ1Obs f n (midpointSampleHurst f hf.1 n) i ≠ 0 := by
  intro n k
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hcard : (localWeightActiveSet 0 1 δ t).card = 0 := by
      simp [localWeightActiveSet]
    rw [hcard] at k
    exact k.elim0
  · exact actualQ1_hane_discharged f hf n hn δ t k

end Hurst
