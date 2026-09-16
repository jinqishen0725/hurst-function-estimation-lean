import Hurst.HSOperatorLayer4

/-!
# Positivity of the uniform-ω Riesz operator (kernel-PSD reduction)

Builds the hPos clause at the uniform-`ω` form of the Riesz kernel
`K_R(x,y) = ω(x)·c·|x-y|^(-ψ)` (the landed `HS.rieszKernel` of
`Hurst.HSOperatorLayer2`, whose `ω`-factor is a ROW multiplier `ω(x)`,
so the kernel is asymmetric in general; for uniform `ω` it is a multiple of
the symmetric distance kernel).

## Main results

* `laplace_rpow_neg` — **the banked Gamma–Laplace identity**: for `0 < b`,
  `0 < ψ`, `b^(-ψ) = (1/Γ(ψ)) ∫₀^∞ u^(ψ-1) e^(-u·b) du`, from mathlib's
  `integral_rpow_mul_exp_neg_mul_rpow` (`Mathlib/MeasureTheory/Integral/Gamma.lean`).
* `diag_null_vol2` — the diagonal `{p | p.1 = p.2}` is `vol2`-null (Fubini on
  sections).
* `KernelPSD_congr` — pointwise-equal kernels have the same quadratic form.
* `kernelPSD_rpow_dist_of_poisson` — **the PSD reduction**: for `0 < ψ < 1`,
  `c ≥ 0`, `KernelPSD (fun p => c·|x-y|^(-ψ))` follows from
  (i) `hpoisson : ∀ u > 0, KernelPSD (fun p => exp (-(u·|x-y|)))` — the
  classical Cauchy/Poisson-kernel fact (`e^(-u|x|)` is the characteristic
  function of the centered Cauchy law of scale `u`; PSD of `φ(x-y)` from a
  characteristic function `φ` is pure Fubini, no Fourier inversion needed);
  and (ii) `hint` — absolute integrability of the triple integrand
  `u^(ψ-1) e^(-u|x-y|) f(x) f(y)` over `Ioi 0 × Icc×Icc` (true by the Schur
  test: `sup_x ∫_{-1}^1 |x-y|^(-ψ) dy ≤ 2·2^(1-ψ)/(1-ψ) < ∞` for `ψ < 1`;
  not discharged here).  The proof: Laplace representation of the kernel
  pointwise off the diagonal, Fubini (`MeasureTheory.integral_prod`,
  `MeasureTheory.integral_prod_swap`), and positivity of each Poisson slice
  from `hpoisson`.
* `kernelPSD_riesz_uniform` — the mission statement: `KernelPSD` of the landed
  `HS.rieszKernel ψ c ω` under the uniform-`ω` hypothesis
  (`(Icc (-1) 1).indicator ω` constant — the symmetric-kernel condition of
  layer 2's `TOp_riesz_selfAdjoint`), conditional on (i)+(ii).
* `eigenvalue_nonneg_riesz_uniform` — the hPos clause: every eigenvalue of the
  uniform-`ω` Riesz operator is nonnegative, via layer 4's landed bridge
  `eigenvalue_nonneg_of_kernelPSD`.

## Honest status

* The deduction chain (Laplace identity → Fubini → slice positivity → PSD,
  and PSD → eigenvalues ≥ 0) is fully machine-checked.
* Two certificates remain open, both classical:
  (a) `hpoisson`: PSD of `e^(-u|x-y|)`.  Mathlib v4.31 has the Cauchy
  distribution (`Probability/Distributions/Cauchy.lean`: `cauchyPDFReal`,
  `cauchyMeasure`) but **no** Cauchy characteristic function, so the CF route
  (`∫∫ e^(-u|x-y|) f f = ∫ |∫ e^(-iuy) f|² dν_u ≥ 0`) cannot yet be discharged
  from mathlib.
  (b) `hint`: the Schur-test integrability bound (elementary calculus).
* Accordingly the positivity verdict at the uniform-`ω` form is:
  **reduced to (a)+(b), both isolated as explicit hypotheses** — the general
  (non-uniform-`ω`) row-weighted kernel stays open (genuinely asymmetric
  kernel; PSD can fail).
-/

open MeasureTheory Measure Real Set
open scoped Real

noncomputable section

namespace HS

/-! ### The banked Gamma–Laplace identity -/

/-- **Gamma–Laplace representation**: for `0 < b` and `0 < ψ`,
`b^(-ψ) = (1/Γ(ψ)) ∫₀^∞ u^(ψ-1) e^(-u·b) du`. -/
theorem laplace_rpow_neg {b : ℝ} (hb : 0 < b) {ψ : ℝ} (hψ : 0 < ψ) :
    b ^ (-ψ) = 1 / Real.Gamma ψ * ∫ u in Ioi (0 : ℝ), u ^ (ψ - 1) * exp (-(u * b)) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := ψ - 1) (b := b) one_pos
    (by linarith) hb
  simp only [Real.rpow_one] at h
  have key : ∀ u : ℝ, (-b) * u = -(u * b) := fun u => by ring
  simp only [key] at h
  rw [show (-(ψ - 1 + 1) / 1 : ℝ) = -ψ by ring,
    show ((ψ - 1 + 1) / 1 : ℝ) = ψ by ring, show (1 : ℝ) / 1 = 1 by norm_num] at h
  have hΓ : 0 < Real.Gamma ψ := Real.Gamma_pos_of_pos hψ
  rw [h]
  field_simp

/-! ### Diagonal nullity -/

/-- The diagonal of the square has `vol2`-measure zero (Fubini on sections:
the `x`-section of the diagonal is the singleton `{x}`, which `vol` kills). -/
theorem diag_null_vol2 : vol2 {p : ℝ × ℝ | p.1 = p.2} = 0 := by
  have hseteq : {p : ℝ × ℝ | p.1 = p.2} = {p : ℝ × ℝ | p.1 - p.2 = 0} := by
    ext p; simp [sub_eq_zero]
  rw [hseteq]
  have hmeas : MeasurableSet {p : ℝ × ℝ | p.1 - p.2 = 0} :=
    (isClosed_eq (continuous_fst.sub continuous_snd) continuous_const).measurableSet
  have hsec : ∀ x : ℝ, vol ((Prod.mk x) ⁻¹' {p : ℝ × ℝ | p.1 - p.2 = 0}) = 0 := by
    intro x
    have hsec' : (Prod.mk x) ⁻¹' {p : ℝ × ℝ | p.1 - p.2 = 0} = {x} := by
      ext y; simp [sub_eq_zero]
    rw [hsec', Measure.restrict_apply (measurableSet_singleton x), Set.inter_comm]
    exact le_antisymm ((measure_mono (Set.inter_subset_right)).trans
      Real.volume_singleton.le) (by simp)
  refine le_antisymm ?_ (by simp)
  calc vol2 {p : ℝ × ℝ | p.1 - p.2 = 0}
      ≤ ∫⁻ x : ℝ, vol ((Prod.mk x) ⁻¹' {p : ℝ × ℝ | p.1 - p.2 = 0}) ∂vol :=
      Measure.prod_apply_le hmeas
    _ ≤ 0 := by
        rw [← lintegral_zero]
        refine lintegral_mono fun x => ?_
        rw [hsec x]

/-- Off the diagonal, a.e. on the square. -/
theorem ae_ne_diag : ∀ᵐ p : ℝ × ℝ ∂vol2, p.1 ≠ p.2 := by
  rw [ae_iff]
  have h : {p : ℝ × ℝ | ¬(p.1 ≠ p.2)} = {p : ℝ × ℝ | p.1 = p.2} := by
    ext p; simp
  rw [h]
  exact diag_null_vol2

/-! ### Kernel congruence -/

/-- Pointwise-equal kernels have the same quadratic form. -/
theorem KernelPSD_congr {K L : ℝ × ℝ → ℝ} (h : ∀ p : ℝ × ℝ, K p = L p)
    (hK : KernelPSD K) : KernelPSD L := by
  intro f
  rw [show kpair L f f = kpair K f f from by
    show ∫ p : ℝ × ℝ, L p * (⇑f) p.2 * (⇑f) p.1 ∂vol2
      = ∫ p : ℝ × ℝ, K p * (⇑f) p.2 * (⇑f) p.1 ∂vol2
    exact integral_congr_ae (Filter.Eventually.of_forall fun p => by
      simp only []; rw [h p])]
  exact hK f

/-! ### The PSD reduction (mixture of Poisson slices) -/

set_option maxHeartbeats 1000000 in
/-- **The PSD reduction**: the distance-power kernel `c·|x-y|^(-ψ)` on the
square has nonnegative quadratic form, given (i) PSD of every Poisson slice
`e^(-u|x-y|)` and (ii) absolute integrability of the triple integrand
(Schur test).  The deduction is fully checked. -/
theorem kernelPSD_rpow_dist_of_poisson {ψ c : ℝ} (hψ : 0 < ψ) (_hψ1 : ψ < 1) (hc : 0 ≤ c)
    (hpoisson : ∀ u > 0, KernelPSD (fun p : ℝ × ℝ => exp (-(u * |p.1 - p.2|))))
    (hint : ∀ f : L2, Integrable
      (fun q : (ℝ × ℝ) × ℝ =>
        q.2 ^ (ψ - 1) * (exp (-(q.2 * |q.1.1 - q.1.2|)) * (⇑f) q.1.2 * (⇑f) q.1.1))
      (vol2.prod (volume.restrict (Ioi (0 : ℝ))))) :
    KernelPSD (fun p : ℝ × ℝ => c * |p.1 - p.2| ^ (-ψ)) := by
  intro f
  have hΓ : 0 < Real.Gamma ψ := Real.Gamma_pos_of_pos hψ
  set ν : Measure ℝ := volume.restrict (Ioi (0 : ℝ)) with hν
  have hJi : Integrable
      (fun q : (ℝ × ℝ) × ℝ =>
        q.2 ^ (ψ - 1) * (exp (-(q.2 * |q.1.1 - q.1.2|)) * (⇑f) q.1.2 * (⇑f) q.1.1))
      (vol2.prod ν) := hint f
  have hJi' : Integrable
      (fun q : (ℝ × ℝ) × ℝ =>
        c / Real.Gamma ψ * (q.2 ^ (ψ - 1) *
          (exp (-(q.2 * |q.1.1 - q.1.2|)) * (⇑f) q.1.2 * (⇑f) q.1.1)))
      (vol2.prod ν) := hJi.const_mul (c / Real.Gamma ψ)
  have hswap : Integrable
      (fun z : ℝ × (ℝ × ℝ) =>
        (fun q : (ℝ × ℝ) × ℝ =>
          c / Real.Gamma ψ * (q.2 ^ (ψ - 1) *
            (exp (-(q.2 * |q.1.1 - q.1.2|)) * (⇑f) q.1.2 * (⇑f) q.1.1)))
          z.swap)
      (ν.prod vol2) := by
    have key := MeasurePreserving.integrable_comp_of_integrable
      (measurePreserving_swap (μ := ν) (ν := vol.prod vol)) hJi'
    exact key
  have hint_sec : ∀ u : ℝ, ∫ p : ℝ × ℝ,
      (c / Real.Gamma ψ) * (u ^ (ψ - 1) * (exp (-(u * |p.1 - p.2|)) * (⇑f) p.2 * (⇑f) p.1)) ∂vol2
      = (c / Real.Gamma ψ) * (u ^ (ψ - 1) * kpair (fun p : ℝ × ℝ => exp (-(u * |p.1 - p.2|))) f f) := by
    intro u
    rw [integral_const_mul (r := c / Real.Gamma ψ), integral_const_mul (r := u ^ (ψ - 1))]
    rfl
  have hstep1 : kpair (fun p : ℝ × ℝ => c * |p.1 - p.2| ^ (-ψ)) f f
      = ∫ z : (ℝ × ℝ) × ℝ,
        (c / Real.Gamma ψ) * (z.2 ^ (ψ - 1) *
          (exp (-(z.2 * |z.1.1 - z.1.2|)) * (⇑f) z.1.2 * (⇑f) z.1.1))
        ∂(vol2.prod ν) := by
    have href : kpair (fun p : ℝ × ℝ => c * |p.1 - p.2| ^ (-ψ)) f f
        = ∫ p : ℝ × ℝ, c * |p.1 - p.2| ^ (-ψ) * (⇑f) p.2 * (⇑f) p.1 ∂vol2 := rfl
    rw [href]
    have hae : ∀ᵐ p : ℝ × ℝ ∂vol2,
        c * |p.1 - p.2| ^ (-ψ) * (⇑f) p.2 * (⇑f) p.1
        = ∫ u : ℝ, (c / Real.Gamma ψ) * (u ^ (ψ - 1) *
            (exp (-(u * |p.1 - p.2|)) * (⇑f) p.2 * (⇑f) p.1)) ∂ν := by
      filter_upwards [ae_ne_diag] with p hp
      have habs : 0 < |p.1 - p.2| := abs_pos.mpr (sub_ne_zero.mpr hp)
      have hI : ∫ u : ℝ, u ^ (ψ - 1) * exp (-(u * |p.1 - p.2|)) ∂ν
          = Real.Gamma ψ * |p.1 - p.2| ^ (-ψ) := by
        rw [hν]
        have hL := laplace_rpow_neg habs hψ
        rw [hL]
        field_simp
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        simp only []
        rw [mul_comm u (|p.1 - p.2|)]
      have hpt : ∀ u : ℝ, u ^ (ψ - 1) *
            (exp (-(u * |p.1 - p.2|)) * (⇑f) p.2 * (⇑f) p.1)
          = ((⇑f) p.2 * (⇑f) p.1) * (u ^ (ψ - 1) * exp (-(u * |p.1 - p.2|))) := fun u => by ring
      rw [integral_const_mul (r := c / Real.Gamma ψ),
        integral_congr_ae (Filter.Eventually.of_forall hpt),
        integral_const_mul (r := (⇑f) p.2 * (⇑f) p.1), hI]
      field_simp [hΓ.ne']
    rw [integral_congr_ae hae, ← integral_prod (fun q : (ℝ × ℝ) × ℝ =>
      c / Real.Gamma ψ * (q.2 ^ (ψ - 1) *
        (exp (-(q.2 * |q.1.1 - q.1.2|)) * (⇑f) q.1.2 * (⇑f) q.1.1))) hJi']
  rw [hstep1, ← integral_prod_swap (fun q : (ℝ × ℝ) × ℝ =>
    c / Real.Gamma ψ * (q.2 ^ (ψ - 1) *
      (exp (-(q.2 * |q.1.1 - q.1.2|)) * (⇑f) q.1.2 * (⇑f) q.1.1)))]
  rw [integral_prod (fun z : ℝ × (ℝ × ℝ) =>
    (fun q : (ℝ × ℝ) × ℝ =>
      c / Real.Gamma ψ * (q.2 ^ (ψ - 1) *
        (exp (-(q.2 * |q.1.1 - q.1.2|)) * (⇑f) q.1.2 * (⇑f) q.1.1))) z.swap) hswap]
  show 0 ≤ ∫ x : ℝ, ∫ p : ℝ × ℝ,
    (c / Real.Gamma ψ) * (x ^ (ψ - 1) *
      (exp (-(x * |p.1 - p.2|)) * (⇑f) p.2 * (⇑f) p.1)) ∂vol2
    ∂ν
  simp only [hint_sec]
  show 0 ≤ ∫ u : ℝ, (c / Real.Gamma ψ) *
    (u ^ (ψ - 1) * kpair (fun p : ℝ × ℝ => exp (-(u * |p.1 - p.2|))) f f)
    ∂(volume.restrict (Ioi (0 : ℝ)))
  refine setIntegral_nonneg measurableSet_Ioi (fun u hu => ?_)
  exact mul_nonneg (div_nonneg hc hΓ.le)
    (mul_nonneg (le_of_lt (Real.rpow_pos_of_pos hu _)) (hpoisson u hu f))

/-! ### The uniform-ω Riesz kernel -/

/-- **Mission statement**: the uniform-`ω` Riesz kernel has nonnegative
quadratic form, conditional on the Poisson-slice PSD certificate `hpoisson`
and the Schur integrability certificate `hint`. -/
theorem kernelPSD_riesz_uniform {ψ c : ℝ} (hψ : 0 < ψ) (hψ1 : ψ < 1) (hc : 0 ≤ c)
    {omega : ℝ → ℝ}
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y)
    (hw : 0 ≤ (I : Set ℝ).indicator omega 0)
    (hpoisson : ∀ u > 0, KernelPSD (fun p : ℝ × ℝ => exp (-(u * |p.1 - p.2|))))
    (hint : ∀ f : L2, Integrable
      (fun q : (ℝ × ℝ) × ℝ =>
        q.2 ^ (ψ - 1) * (exp (-(q.2 * |q.1.1 - q.1.2|)) * (⇑f) q.1.2 * (⇑f) q.1.1))
      (vol2.prod (volume.restrict (Ioi (0 : ℝ))))) :
    KernelPSD (rieszKernel ψ c omega) := by
  refine KernelPSD_congr (fun p => ?_)
    (kernelPSD_rpow_dist_of_poisson hψ hψ1 (mul_nonneg hw hc) hpoisson hint)
  show (I : Set ℝ).indicator omega 0 * c * |p.1 - p.2| ^ (-ψ)
      = rieszKernel ψ c omega p
  rw [rieszKernel_apply, hconst p.1 0]

/-- **The hPos clause**: every eigenvalue of the uniform-`ω` Riesz operator is
nonnegative (conditional on the two certificates), via the landed
`eigenvalue_nonneg_of_kernelPSD` bridge. -/
theorem eigenvalue_nonneg_riesz_uniform {ψ c : ℝ} {omega : ℝ → ℝ} {M : ℝ}
    (hψ : 0 < ψ) (hψ1 : ψ < 1) (hc : 0 ≤ c)
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-ψ)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ M)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * ψ)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y)
    (hw : 0 ≤ (I : Set ℝ).indicator omega 0)
    (hpoisson : ∀ u > 0, KernelPSD (fun p : ℝ × ℝ => exp (-(u * |p.1 - p.2|))))
    (hint : ∀ f : L2, Integrable
      (fun q : (ℝ × ℝ) × ℝ =>
        q.2 ^ (ψ - 1) * (exp (-(q.2 * |q.1.1 - q.1.2|)) * (⇑f) q.1.2 * (⇑f) q.1.1))
      (vol2.prod (volume.restrict (Ioi (0 : ℝ)))))
    {μ : ℝ}
    (hμ : Module.End.HasEigenvalue
      ((TOp (rieszKernel ψ c omega) (hsKernel_rieszKernel hpow homega hbdd hg) :
        L2 →ₗ[ℝ] L2)) μ) :
    0 ≤ μ :=
  eigenvalue_nonneg_of_kernelPSD
    (hK := hsKernel_rieszKernel hpow homega hbdd hg)
    (kernelPSD_riesz_uniform hψ hψ1 hc hconst hw hpoisson hint) hμ

end HS

end
