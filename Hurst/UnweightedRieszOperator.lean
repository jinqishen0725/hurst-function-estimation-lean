import Hurst.RieszSectionBounds
import Hurst.GeneralKHasSumFinal
import Hurst.RieszCompactEnumeration
import Hurst.CauchyKernelPSD
import Hurst.RieszOperatorPositivity
import Hurst.EigenFamilySplice

/-!
# The unweighted Riesz kernel operator (M1-A)

Foundation of the `hconst`-elimination milestone: the spectral object is built from the
**unweighted** symmetric kernel `K(x,y) = c·|x-y|^(-ψ)` (`HS.unweightedRieszKernel`),
whose symmetry gives self-adjointness with NO weight condition.  (The weighted operator
`B = K^(1/2) W K^(1/2)` of 22:W6 / 23:A4-A6 is built on top of this by M1-B/M1-D.)

## Main results (frozen interface of `milestone1_hconst_elimination_math_spec.md` §2)

* `unweightedRieszKernel`, `unweightedRieszKernel_symm` — the kernel and its symmetry
  (`|x-y| = |y-x|`; this is where `hconst` is eliminated).
* `hsKernel_unweightedRieszKernel` — the kernel is Hilbert–Schmidt for `0 ≤ ψ`, `2ψ < 1`
  (uniform section bound `fract_section_bound` ⇒ `∫∫ K² < ∞`).
* `isSymmetric_TOp_unweightedRiesz` — the kernel operator is a symmetric endomorphism
  (no weight hypothesis at all).
* `isCompactOperator_TOp_unweightedRiesz` — HS ⇒ compact (mesh-approximation route of
  `isCompactOperator_TOp_riesz`, which never used the weight).
* `inner_TOp_unweightedRiesz_nonneg` — **A5**: nonnegativity of the quadratic form via
  the Gamma–Laplace representation `|x-y|^(-ψ) = Γ(ψ)^{-1} ∫₀^∞ s^{ψ-1} e^{-s|x-y|} ds`
  (`laplace_rpow_neg`) mixed with the landed PSD certificate `kernelPSD_exp_dist`
  (`e^{-u|x-y|}` is PSD).  The Schur-test absolute integrability of the triple integrand
  is discharged here (`integrable_laplace_integrand`) from `fract_section_bound`.
* `exists_nonneg_eigenfamily` — complete orthonormal eigenfamily with `κ ≥ 0` and
  `Summable κ²` (splice of `exists_complete_eigenfamily_of_symmetric` + positivity +
  `hsNorm_sq_eq_tsum_eigenvalue_sq_of_orthonormal_complete`).

## DECLARED DEVIATION from the frozen §2 signatures

The two positivity-flavored theorems carry one extra hypothesis

```
hc : 0 ≤ c
```

(`inner_TOp_unweightedRiesz_nonneg`, `exists_nonneg_eigenfamily`).  It is mathematically
necessary: the quadratic form scales by `c`, so for `c < 0` the nonnegativity conclusions
are FALSE (eigenvalues of the operator are `c`-times those of the PSD distance kernel).
The landed `HS.kernelPSD_rpow_dist_of_poisson` already requires `0 ≤ c`.  In the actual
model `c = h·(2h-1) > 0` for `h > 1/2`, so the hypothesis is satisfiable.  (Same kind of
declared amendment as the `hpsi0 : 0 ≤ psi` of `Hurst.RieszSectionBounds`.)  All other
signatures match the frozen §2 interface verbatim.
-/

open MeasureTheory Measure Real Set Filter Submodule
open scoped Real

noncomputable section

namespace HS

/-! ### The frozen kernel definition and its symmetry -/

/-- The unweighted Riesz kernel `K(x, y) = c·|x - y|^(-ψ)` — symmetric in `(x, y)`;
this symmetry (not any weight condition) is what makes the operator self-adjoint and
eliminates the unsatisfiable `hconst` premise of the weighted line. -/
def unweightedRieszKernel (psi c : ℝ) : ℝ × ℝ → ℝ :=
  fun p => c * |p.1 - p.2| ^ (-psi)

theorem unweightedRieszKernel_apply (psi c x y : ℝ) :
    unweightedRieszKernel psi c (x, y) = c * |x - y| ^ (-psi) := rfl

theorem unweightedRieszKernel_apply_swap (psi c x y : ℝ) :
    unweightedRieszKernel psi c (y, x) = c * |y - x| ^ (-psi) := rfl

/-- **Symmetry of the unweighted kernel** (`|x - y| = |y - x|`) — the hconst-elimination
step. -/
theorem unweightedRieszKernel_symm (psi c x y : ℝ) :
    unweightedRieszKernel psi c (x, y) = unweightedRieszKernel psi c (y, x) := by
  rw [unweightedRieszKernel_apply, unweightedRieszKernel_apply_swap, abs_sub_comm]

/-- Measurability of the kernel (from the landed `measurable_abs_sub_rpow`). -/
theorem measurable_unweightedRieszKernel (psi c : ℝ) :
    Measurable (unweightedRieszKernel psi c) :=
  (measurable_const.mul (measurable_abs_sub_rpow (r := psi)))

/-! ### Section bounds for the distance power against the carrier measure -/

/-- The squared-distance-power identity `(r ^ (-ψ))² = r ^ (-2ψ)`. -/
private theorem abs_sub_rpow_sq' {r psi : ℝ} (hr : 0 ≤ r) :
    (r ^ (-psi)) ^ 2 = r ^ (-(2 * psi)) := by
  rw [← Real.rpow_natCast (r ^ (-psi)) 2, ← Real.rpow_mul hr,
    show (2:ℝ) * psi = psi * 2 from by ring, ← neg_mul]
  norm_num

/-- Single-variable integrability of the distance power against the carrier measure
(from the landed interval-integrability of `Hurst.TwoFactorShiftBound`). -/
private theorem integrable_abs_sub_vol {p : ℝ} (hp : p < 1) (y : ℝ) :
    MeasureTheory.Integrable (fun x : ℝ => |x - y| ^ (-p)) vol := by
  have hint := Hurst.intervalIntegrable_abs_sub_rpow hp y (-2 : ℝ) 2
  have h3 : MeasureTheory.IntegrableOn (fun x : ℝ => |x - y| ^ (-p))
      (Set.Ioc (-2 : ℝ) 2) MeasureTheory.volume := by
    have h4 := intervalIntegrable_iff.mp hint
    rwa [Set.uIoc_of_le (by norm_num)] at h4
  exact h3.mono_set (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)

/-- Uniform section bound (real form): `∫ |x - y|^(-s) dvol ≤ 2 + 2/(1-s)` for
`0 ≤ s < 1`, uniform in `y`. -/
theorem integral_abs_sub_vol_le {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (y : ℝ) :
    ∫ x : ℝ, |x - y| ^ (-s) ∂vol ≤ 2 + 2 / (1 - s) := by
  have hae : (fun x : ℝ => |x - y| ^ (-s))
      =ᵐ[vol] (fun x : ℝ => (I : Set ℝ).indicator (fun a : ℝ => |a - y| ^ (-s)) x) := by
    filter_upwards [MeasureTheory.ae_restrict_mem
      (measurableSet_Icc : MeasurableSet (I : Set ℝ))] with x hx
    rw [Set.indicator_of_mem hx]
  rw [MeasureTheory.integral_congr_ae hae]
  exact fract_section_bound hs0 hs1 y

/-- Bridge: for a nonneg a.e.-measurable real function with finite real integral, the
ℓ-integral of its `ofReal` is the `ofReal` of the real integral. -/
private theorem lintegral_ofReal_eq {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {g : α → ℝ}
    (hnn : ∀ᵐ a ∂μ, 0 ≤ g a) (hAESM : AEStronglyMeasurable g μ)
    (hfin : MeasureTheory.Integrable g μ) :
    ∫⁻ a, ENNReal.ofReal (g a) ∂μ = ENNReal.ofReal (∫ a, g a ∂μ) := by
  have h1 := MeasureTheory.integral_eq_lintegral_of_nonneg_ae hnn hAESM
  have hLne : (∫⁻ a, ENNReal.ofReal (g a) ∂μ) ≠ ⊤ := by
    intro hT
    have hle := lintegral_ofReal_le_lintegral_enorm (μ := μ) g
    rw [hT] at hle
    exact lt_irrefl (⊤ : ENNReal) (hle.trans_lt hfin.hasFiniteIntegral)
  calc ∫⁻ a, ENNReal.ofReal (g a) ∂μ
      = ENNReal.ofReal (∫⁻ a, ENNReal.ofReal (g a) ∂μ).toReal := by
        rw [ENNReal.ofReal_toReal hLne]
    _ = ENNReal.ofReal (∫ a, g a ∂μ) := by rw [h1]

/-- The ℓ-integral of the distance power over the carrier measure equals the `ofReal`
of the real integral. -/
private theorem lintegral_ofReal_abs_sub_vol_eq {s : ℝ} (hs1 : s < 1) (y : ℝ) :
    (∫⁻ x : ℝ, ENNReal.ofReal (|x - y| ^ (-s)) ∂vol)
      = ENNReal.ofReal (∫ x : ℝ, |x - y| ^ (-s) ∂vol) :=
  lintegral_ofReal_eq (Eventually.of_forall fun x => Real.rpow_nonneg (abs_nonneg (x - y)) (-s))
    ((measurable_abs_sub_rpow (r := s)).comp
        (measurable_id.prodMk measurable_const) |>.aestronglyMeasurable)
    (integrable_abs_sub_vol hs1 y)

/-- Uniform section bound (ℓ form). -/
private theorem lintegral_abs_sub_vol_le {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (y : ℝ) :
    ∫⁻ x : ℝ, ENNReal.ofReal (|x - y| ^ (-s)) ∂vol
      ≤ ENNReal.ofReal (2 + 2 / (1 - s)) := by
  rw [lintegral_ofReal_abs_sub_vol_eq hs1 y]
  exact ENNReal.ofReal_le_ofReal (integral_abs_sub_vol_le hs0 hs1 y)

/-! ### Square-integrability of the distance power on the square -/

/-- **Square-integrability**: `|x - y|^(-s)` is integrable on the unit square for
`0 ≤ s < 1` (uniform section bound + Tonelli).  At `s = 2ψ` this is exactly the standing
hypothesis `hg` of `Hurst.HSOperatorLayer2.hsKernel_rieszKernel`, now discharged
unconditionally within the capstone window `0 ≤ ψ, 2ψ < 1`. -/
theorem integrable_abs_sub_rpow_vol2 {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-s)) vol2 := by
  rcases eq_or_lt_of_le hs0 with h0 | hs0
  · subst h0
    have heq : (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-(0:ℝ))) = fun _ => (1:ℝ) := by
      funext p; simp
    rw [heq]
    exact integrable_const (1:ℝ)
  have hAESM : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-s)) vol2 :=
    (measurable_abs_sub_rpow (r := s)).aestronglyMeasurable
  refine ⟨hAESM, ?_⟩
  have hbound : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (|p.1 - p.2| ^ (-s)) ∂vol2) < ⊤ := by
    have hmeas : AEMeasurable
        (fun p : ℝ × ℝ => ENNReal.ofReal (|p.1 - p.2| ^ (-s))) vol2 :=
      Measurable.comp_aemeasurable (g := fun x : ℝ => ENNReal.ofReal x)
        ENNReal.continuous_ofReal.measurable hAESM.aemeasurable
    have houter : (∫⁻ a : ℝ, ENNReal.ofReal (2 + 2 / (1 - s)) ∂vol)
        = ENNReal.ofReal (2 + 2 / (1 - s)) * ENNReal.ofReal 2 := by
      rw [lintegral_const]
      congr 1
      rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Icc]
      norm_num
    rw [lintegral_prod _ hmeas]
    calc ∫⁻ a : ℝ, ∫⁻ b : ℝ, ENNReal.ofReal (|a - b| ^ (-s)) ∂vol ∂vol
        ≤ ∫⁻ a : ℝ, ∫⁻ b : ℝ, ENNReal.ofReal (|b - a| ^ (-s)) ∂vol ∂vol := by
          refine lintegral_mono fun a => ?_
          exact (lintegral_congr_ae
            (Eventually.of_forall fun b => by rw [abs_sub_comm a b])).le
      _ ≤ ∫⁻ a : ℝ, ENNReal.ofReal (2 + 2 / (1 - s)) ∂vol :=
          lintegral_mono fun a => lintegral_abs_sub_vol_le hs0.le hs1 a
      _ = ENNReal.ofReal (2 + 2 / (1 - s)) * ENNReal.ofReal 2 := houter
      _ ≤ ENNReal.ofReal (2 * (2 + 2 / (1 - s))) := by
          have hC : (0:ℝ) ≤ 2 + 2 / (1 - s) := by
            have h1s : (0:ℝ) < 1 - s := by linarith
            exact le_of_lt (add_pos (by norm_num) (div_pos (by norm_num) h1s))
          have h1 : ENNReal.ofReal ((2 + 2 / (1 - s)) * 2)
              = ENNReal.ofReal (2 + 2 / (1 - s)) * ENNReal.ofReal 2 :=
            ENNReal.ofReal_mul hC
          rw [← h1]
          exact ENNReal.ofReal_le_ofReal (by linarith)
      _ < ⊤ := ENNReal.ofReal_lt_top
  rw [MeasureTheory.hasFiniteIntegral_def]
  have henorm : ∀ p : ℝ × ℝ, ‖(fun p : ℝ × ℝ => |p.1 - p.2| ^ (-s)) p‖ₑ
      = ENNReal.ofReal (|p.1 - p.2| ^ (-s)) := by
    intro p
    rw [← ofReal_norm, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg (p.1 - p.2)) (-s))]
  rw [lintegral_congr_ae (Eventually.of_forall henorm)]
  exact hbound

/-! ### The frozen interface (kernel, symmetry, compactness) -/

/-- **Frozen §2**: the unweighted Riesz kernel is a Hilbert–Schmidt kernel for
`0 ≤ psi` and `2 * psi < 1` (the squared section bound via
`integrable_abs_sub_rpow_vol2` at `s = 2ψ`). -/
theorem hsKernel_unweightedRieszKernel {psi c : ℝ} (hpsi0 : 0 ≤ psi) (hpsi2 : 2 * psi < 1) :
    HSKernel (unweightedRieszKernel psi c) := by
  have hsq : ∀ p : ℝ × ℝ,
      unweightedRieszKernel psi c p ^ 2 = c ^ 2 * |p.1 - p.2| ^ (-(2 * psi)) := by
    intro p
    rw [unweightedRieszKernel_apply, mul_pow, abs_sub_rpow_sq' (abs_nonneg (p.1 - p.2))]
  have hint := integrable_abs_sub_rpow_vol2 (s := 2 * psi) (by linarith) hpsi2
  have hK2 : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => unweightedRieszKernel psi c p ^ 2) vol2 :=
    (hint.const_mul (c ^ 2)).congr
      (Eventually.of_forall fun p => (hsq p).symm)
  exact memLp_two_of_aemeasurable (measurable_unweightedRieszKernel psi c).aestronglyMeasurable
    hK2

/-- **Frozen §2**: the unweighted Riesz kernel operator is a symmetric endomorphism of
`L²` — from the pointwise symmetry of the kernel, with NO weight condition. -/
theorem isSymmetric_TOp_unweightedRiesz {psi c : ℝ} (hpsi0 : 0 ≤ psi) (hpsi2 : 2 * psi < 1) :
    (↑(TOp (unweightedRieszKernel psi c)
        (hsKernel_unweightedRieszKernel hpsi0 hpsi2)) : L2 →ₗ[ℝ] L2).IsSymmetric :=
  isSymmetric_TOp_of_symmetric_kernel (fun p => by
    rw [unweightedRieszKernel_apply, show p.swap = (p.2, p.1) from rfl,
      unweightedRieszKernel_apply, abs_sub_comm])

/-- `hsNorm` is invariant under swapping the order of subtraction. -/
private theorem hsNorm_sub_comm' (A B : ℝ × ℝ → ℝ) :
    hsNorm (A - B) = hsNorm (fun p => B p - A p) := by
  rw [hsNorm_def, hsNorm_def]
  refine congrArg Real.sqrt ?_
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  show (A - B) p ^ 2 = (B p - A p) ^ 2
  simp only [Pi.sub_apply]
  ring

set_option maxHeartbeats 1000000 in
/-- **Frozen §2**: the unweighted Riesz kernel operator is compact — operator-norm
approximation by bounded-continuous kernels (`exists_continuous_approx`) and the
compact-limit bridge (`isCompactOperator_TOp_limit`); the route of
`isCompactOperator_TOp_riesz` without any weight input. -/
theorem isCompactOperator_TOp_unweightedRiesz {psi c : ℝ} (hpsi0 : 0 ≤ psi)
    (hpsi2 : 2 * psi < 1) :
    IsCompactOperator (TOp (unweightedRieszKernel psi c)
      (hsKernel_unweightedRieszKernel hpsi0 hpsi2)) := by
  classical
  have hall : ∀ n : ℕ, ∃ g : ℝ × ℝ → ℝ, Continuous g ∧
      HSKernel g ∧ hsNorm (fun p => unweightedRieszKernel psi c p - g p) ≤ 1 / ((n:ℝ) + 1) :=
    fun n => exists_continuous_approx (hsKernel_unweightedRieszKernel hpsi0 hpsi2)
      (by positivity)
  choose g hgc hgm hgn using hall
  have hTc : ∀ n : ℕ, IsCompactOperator (TOp (g n) (hgm n)) := fun n =>
    continuous_kernel_compact (hgm n) (hgc n)
  have hTn : ∀ n : ℕ, ‖TOp (g n) (hgm n) - TOp (unweightedRieszKernel psi c)
      (hsKernel_unweightedRieszKernel hpsi0 hpsi2)‖ ≤ 1 / ((n:ℝ) + 1) := by
    intro n
    calc ‖TOp (g n) (hgm n) - TOp (unweightedRieszKernel psi c)
          (hsKernel_unweightedRieszKernel hpsi0 hpsi2)‖
        ≤ hsNorm (g n - unweightedRieszKernel psi c) :=
          TOp_norm_diff_le (hgm n) (hsKernel_unweightedRieszKernel hpsi0 hpsi2)
      _ = hsNorm (fun p => unweightedRieszKernel psi c p - g n p) := hsNorm_sub_comm' _ _
      _ ≤ 1 / ((n:ℝ) + 1) := hgn n
  exact isCompactOperator_TOp_limit (hsKernel_unweightedRieszKernel hpsi0 hpsi2)
    (fun n => TOp (g n) (hgm n)) hTc hTn

/-! ### Positivity (A5): the Gamma–Laplace mixture of exp-kernel PSD slices -/

/-- File-local form of `ENNReal.ofReal_mul` (hypothesis on the first factor). -/
private theorem ofReal_mul_eq {a c : ℝ} (h : 0 ≤ a) :
    ENNReal.ofReal (a * c) = ENNReal.ofReal a * ENNReal.ofReal c := ENNReal.ofReal_mul h

/-- The inner Gamma–Laplace ℓ-identity: for `ψ > 0` and `d > 0`,
`∫⁻ s, ofReal(s^{ψ-1} e^{-s·d}) ∂ν = ofReal(Γ(ψ)·d^{-ψ})` where
`ν = volume.restrict (Ioi 0)`. -/
private theorem lintegral_laplace_eq {psi d : ℝ} (hpsi : 0 < psi) (hd : 0 < d) :
    (∫⁻ s : ℝ, ENNReal.ofReal (s ^ (psi - 1) * exp (-(s * d)))
        ∂(volume.restrict (Ioi (0 : ℝ))))
      = ENNReal.ofReal (Real.Gamma psi * d ^ (-psi)) := by
  have hΓ : 0 < Real.Gamma psi := Real.Gamma_pos_of_pos hpsi
  have hrpow : ContinuousOn (fun s : ℝ => s ^ (psi - 1)) (Ioi (0:ℝ)) := by
    intro x hx
    exact (ContinuousAt.rpow_const (p := psi - 1) continuousAt_id
      (Or.inl (ne_of_gt hx))).continuousWithinAt
  have hcont : ContinuousOn (fun s : ℝ => s ^ (psi - 1) * exp (-(s * d))) (Ioi (0:ℝ)) :=
    hrpow.mul (Real.continuous_exp.comp
      (Continuous.neg (continuous_id.mul continuous_const))).continuousOn
  have hAESM : AEStronglyMeasurable (fun s : ℝ => s ^ (psi - 1) * exp (-(s * d)))
      (volume.restrict (Ioi (0 : ℝ))) := hcont.aestronglyMeasurable measurableSet_Ioi
  have hnn : ∀ᵐ s ∂(volume.restrict (Ioi (0:ℝ))), 0 ≤ s ^ (psi - 1) * exp (-(s * d)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with s hs
    exact mul_nonneg (Real.rpow_nonneg (Set.mem_Ioi.mp hs).le (psi - 1)) (exp_nonneg _)
  have h1 := MeasureTheory.integral_eq_lintegral_of_nonneg_ae hnn hAESM
  have hval : (∫ s : ℝ, s ^ (psi - 1) * exp (-(s * d)) ∂(volume.restrict (Ioi (0:ℝ))))
      = Real.Gamma psi * d ^ (-psi) := by
    have hcongr : ∀ s : ℝ, s ^ (psi - 1) * exp (-(s * d))
        = s ^ (psi - 1) * exp (-(d * s)) := fun s => by rw [mul_comm d s]
    rw [MeasureTheory.integral_congr_ae (Eventually.of_forall hcongr),
      laplace_rpow_neg hd hpsi]
    field_simp [hΓ.ne']
  have hLne : (∫⁻ s : ℝ, ENNReal.ofReal (s ^ (psi - 1) * exp (-(s * d)))
      ∂(volume.restrict (Ioi (0:ℝ)))) ≠ ⊤ := by
    intro hT
    rw [hT, ENNReal.toReal_top] at h1
    rw [hval] at h1
    exact absurd h1 (ne_of_gt (mul_pos hΓ (Real.rpow_pos_of_pos hd _)))
  calc ∫⁻ s : ℝ, ENNReal.ofReal (s ^ (psi - 1) * exp (-(s * d)))
        ∂(volume.restrict (Ioi (0 : ℝ)))
      = ENNReal.ofReal (∫⁻ s : ℝ, ENNReal.ofReal (s ^ (psi - 1) * exp (-(s * d)))
          ∂(volume.restrict (Ioi (0 : ℝ)))).toReal := by
        rw [ENNReal.ofReal_toReal hLne]
    _ = ENNReal.ofReal (∫ s : ℝ, s ^ (psi - 1) * exp (-(s * d))
          ∂(volume.restrict (Ioi (0 : ℝ)))) := by rw [h1]
    _ = ENNReal.ofReal (Real.Gamma psi * d ^ (-psi)) := by rw [hval]

/-- **Schur direction bound** (the `p.2`-factor): `∫∫ ofReal(|x-y|^{-ψ}|f(y)|²)
≤ ofReal((2 + 2/(1-ψ))·‖f‖²)` — Tonelli with the `f`-factor in the outer variable, then
the uniform section bound. -/
private theorem lintegral_schur_dir {psi : ℝ} (hpsi0 : 0 < psi) (hpsi1 : psi < 1) (f : L2) :
    (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (|p.1 - p.2| ^ (-psi) * |(⇑f) p.2| ^ 2) ∂vol2)
      ≤ ENNReal.ofReal ((2 + 2 / (1 - psi)) * ‖f‖ ^ 2) := by
  have hC0 : (0:ℝ) ≤ 2 + 2 / (1 - psi) := by
    have h1s : (0:ℝ) < 1 - psi := by linarith
    exact le_of_lt (add_pos (by norm_num) (div_pos (by norm_num) h1s))
  have hfsq : AEStronglyMeasurable (fun y : ℝ => |(⇑f) y| ^ 2) vol := by
    have h0 : AEStronglyMeasurable (fun y : ℝ => (⇑f) y * (⇑f) y) vol :=
      (MeasureTheory.Lp.aestronglyMeasurable f).mul (MeasureTheory.Lp.aestronglyMeasurable f)
    have hpt : (fun y : ℝ => (⇑f) y * (⇑f) y) = (fun y : ℝ => |(⇑f) y| ^ 2) := by
      funext y
      exact (pow_two _).symm.trans (sq_abs _).symm
    rw [hpt] at h0
    exact h0
  have hfinabs : MeasureTheory.Integrable (fun y : ℝ => |(⇑f) y| ^ 2) vol := by
    have h0 := (MeasureTheory.Lp.memLp f).integrable_sq
    have hpt : (fun y : ℝ => (⇑f) y ^ 2) = (fun y : ℝ => |(⇑f) y| ^ 2) := by
      funext y
      exact (sq_abs _).symm
    rw [hpt] at h0
    exact h0
  have hintmeas : ∀ a : ℝ,
      AEMeasurable (fun b : ℝ => ENNReal.ofReal (|b - a| ^ (-psi))) vol :=
    fun a => Measurable.comp_aemeasurable
      (g := fun x : ℝ => ENNReal.ofReal x) ENNReal.continuous_ofReal.measurable
      (((measurable_abs_sub_rpow (r := psi)).comp
        (measurable_id.prodMk measurable_const)).aemeasurable)
  have houter : (∫⁻ a : ℝ, ENNReal.ofReal (|(⇑f) a| ^ 2) ∂vol)
      = ENNReal.ofReal (∫ a : ℝ, |(⇑f) a| ^ 2 ∂vol) :=
    lintegral_ofReal_eq (Eventually.of_forall fun a => sq_nonneg _) hfsq hfinabs
  have hfeq : (∫ a : ℝ, |(⇑f) a| ^ 2 ∂vol) = ∫ a : ℝ, (⇑f) a ^ 2 ∂vol :=
    integral_congr_ae (Eventually.of_forall fun a => sq_abs _)
  -- the swapped integrand (the `f`-factor in the outer variable) is a.e.-measurable
  have hGmeas : AEMeasurable
      (fun p : ℝ × ℝ => ENNReal.ofReal (|p.2 - p.1| ^ (-psi) * |(⇑f) p.1| ^ 2)) vol2 := by
    have hreal : AEStronglyMeasurable
        (fun p : ℝ × ℝ => |p.2 - p.1| ^ (-psi) * |(⇑f) p.1| ^ 2) vol2 := by
      have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.2 - p.1| ^ (-psi)) vol2 := by
        refine (measurable_abs_sub_rpow (r := psi)).aestronglyMeasurable.congr ?_
        filter_upwards with p
        rw [abs_sub_comm p.2 p.1]
      exact h1.mul hfsq.comp_fst
    exact Measurable.comp_aemeasurable
      (g := fun x : ℝ => ENNReal.ofReal x) ENNReal.continuous_ofReal.measurable
      hreal.aemeasurable
  calc (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (|p.1 - p.2| ^ (-psi) * |(⇑f) p.2| ^ 2) ∂vol2)
      = ∫⁻ p : ℝ × ℝ,
          (fun p : ℝ × ℝ => ENNReal.ofReal (|p.2 - p.1| ^ (-psi) * |(⇑f) p.1| ^ 2)) p.swap
            ∂vol2 := by
        refine lintegral_congr_ae ?_
        filter_upwards with p
        show ENNReal.ofReal (|p.1 - p.2| ^ (-psi) * |(⇑f) p.2| ^ 2) = _
        rfl
    _ = ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (|p.2 - p.1| ^ (-psi) * |(⇑f) p.1| ^ 2) ∂vol2 :=
        (lintegral_prod_swap (f := fun p : ℝ × ℝ =>
          ENNReal.ofReal (|p.2 - p.1| ^ (-psi) * |(⇑f) p.1| ^ 2)))
    _ = ∫⁻ a : ℝ, ∫⁻ b : ℝ,
          ENNReal.ofReal (|(⇑f) a| ^ 2) * ENNReal.ofReal (|b - a| ^ (-psi)) ∂vol ∂vol := by
          rw [lintegral_prod _ hGmeas]
          have hint2 : ∀ (y z : ℝ), ENNReal.ofReal (|z - y| ^ (-psi) * |(⇑f) y| ^ 2)
              = ENNReal.ofReal (|(⇑f) y| ^ 2) * ENNReal.ofReal (|z - y| ^ (-psi)) := by
            intro y z
            rw [ofReal_mul_eq (Real.rpow_nonneg (abs_nonneg (z - y)) (-psi)), mul_comm]
          refine lintegral_congr_ae (Eventually.of_forall fun (y : ℝ) => ?_)
          exact lintegral_congr_ae (Eventually.of_forall fun (z : ℝ) => hint2 y z)
    _ ≤ ∫⁻ a : ℝ, ENNReal.ofReal (2 + 2 / (1 - psi)) * ENNReal.ofReal (|(⇑f) a| ^ 2) ∂vol := by
          refine lintegral_mono fun a => ?_
          calc (∫⁻ b : ℝ, ENNReal.ofReal (|(⇑f) a| ^ 2)
                  * ENNReal.ofReal (|b - a| ^ (-psi)) ∂vol)
              = ENNReal.ofReal (|(⇑f) a| ^ 2)
                * ∫⁻ b : ℝ, ENNReal.ofReal (|b - a| ^ (-psi)) ∂vol := by
                rw [lintegral_const_mul'' (ENNReal.ofReal (|(⇑f) a| ^ 2)) (hintmeas a)]
            _ ≤ ENNReal.ofReal (|(⇑f) a| ^ 2)
                  * ENNReal.ofReal (2 + 2 / (1 - psi)) :=
                mul_le_mul_of_nonneg_left (lintegral_abs_sub_vol_le hpsi0.le hpsi1 a)
                  (by simp)
            _ = ENNReal.ofReal (2 + 2 / (1 - psi)) * ENNReal.ofReal (|(⇑f) a| ^ 2) := by
                exact mul_comm _ _
    _ = ENNReal.ofReal (2 + 2 / (1 - psi))
          * (∫⁻ a : ℝ, ENNReal.ofReal (|(⇑f) a| ^ 2) ∂vol) :=
          lintegral_const_mul' (ENNReal.ofReal (2 + 2 / (1 - psi))) _ (by simp)
    _ = ENNReal.ofReal ((2 + 2 / (1 - psi)) * ‖f‖ ^ 2) := by
          rw [houter, hfeq, L2norm_sq]
          exact (ofReal_mul_eq hC0).symm

/-- **Schur direction bound** (the `p.1`-factor): the symmetric form of
`lintegral_schur_dir`. -/
private theorem lintegral_schur_dir_swap {psi : ℝ} (hpsi0 : 0 < psi) (hpsi1 : psi < 1)
    (f : L2) :
    (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (|p.1 - p.2| ^ (-psi) * |(⇑f) p.1| ^ 2) ∂vol2)
      ≤ ENNReal.ofReal ((2 + 2 / (1 - psi)) * ‖f‖ ^ 2) := by
  have h := lintegral_schur_dir hpsi0 hpsi1 f
  refine le_trans ?_ h
  rw [← lintegral_prod_swap (f := fun p : ℝ × ℝ =>
    ENNReal.ofReal (|p.1 - p.2| ^ (-psi) * |(⇑f) p.1| ^ 2))]
  exact (lintegral_congr_ae (Eventually.of_forall fun (p : ℝ × ℝ) => by
    show ENNReal.ofReal (|p.2 - p.1| ^ (-psi) * |(⇑f) p.2| ^ 2) = _
    rw [abs_sub_comm p.2 p.1])).le
set_option maxHeartbeats 1000000 in
/-- **The Schur-test discharge**: absolute integrability of the Gamma–Laplace triple
integrand `s^{ψ-1} e^{-s|x-y|} f(y) f(x)` over `vol2 × ν`, `ν = volume.restrict (Ioi 0)`.
Route: Tonelli over `s` (Gamma–Laplace identity per off-diagonal section), then the
`2ab ≤ a² + b²` split and the uniform section bound. -/
theorem integrable_laplace_integrand {psi : ℝ} (hpsi0 : 0 < psi) (hpsi2 : 2 * psi < 1)
    (f : L2) :
    MeasureTheory.Integrable
      (fun q : (ℝ × ℝ) × ℝ =>
        q.2 ^ (psi - 1) * (exp (-(q.2 * |q.1.1 - q.1.2|)) * (⇑f) q.1.2 * (⇑f) q.1.1))
      (vol2.prod (volume.restrict (Ioi (0 : ℝ)))) := by
  classical
  set G : (ℝ × ℝ) × ℝ → ℝ := fun q =>
    q.2 ^ (psi - 1) * (exp (-(q.2 * |q.1.1 - q.1.2|)) * (⇑f) q.1.2 * (⇑f) q.1.1) with hGdef
  have hcontA : ContinuousOn (fun s : ℝ => s ^ (psi - 1)) (Ioi (0:ℝ)) := by
    intro x hx
    exact (ContinuousAt.rpow_const (p := psi - 1) continuousAt_id
      (Or.inl (ne_of_gt hx))).continuousWithinAt
  have hA2 : AEStronglyMeasurable (fun q : (ℝ × ℝ) × ℝ => q.2 ^ (psi - 1))
      (vol2.prod (volume.restrict (Ioi (0 : ℝ)))) :=
    (hcontA.aestronglyMeasurable measurableSet_Ioi).comp_snd
  have hE : AEStronglyMeasurable
      (fun q : (ℝ × ℝ) × ℝ => exp (-(q.2 * |q.1.1 - q.1.2|)))
      (vol2.prod (volume.restrict (Ioi (0 : ℝ)))) :=
    (Real.continuous_exp.comp (Continuous.neg (continuous_snd.mul
      (((continuous_fst.comp continuous_fst).sub
        (continuous_snd.comp continuous_fst)).abs)))).aestronglyMeasurable
  have hF2 : AEStronglyMeasurable (fun q : (ℝ × ℝ) × ℝ => (⇑f) q.1.2)
      (vol2.prod (volume.restrict (Ioi (0 : ℝ)))) :=
    ((MeasureTheory.Lp.aestronglyMeasurable f).comp_snd).comp_fst
  have hF1 : AEStronglyMeasurable (fun q : (ℝ × ℝ) × ℝ => (⇑f) q.1.1)
      (vol2.prod (volume.restrict (Ioi (0 : ℝ)))) :=
    ((MeasureTheory.Lp.aestronglyMeasurable f).comp_fst).comp_fst
  have hGae : AEStronglyMeasurable
      (fun q : (ℝ × ℝ) × ℝ =>
        q.2 ^ (psi - 1) * (exp (-(q.2 * |q.1.1 - q.1.2|)) * (⇑f) q.1.2 * (⇑f) q.1.1))
      (vol2.prod (volume.restrict (Ioi (0 : ℝ)))) := hA2.mul ((hE.mul hF2).mul hF1)
  -- the set `q.2 ≤ 0` is null
  have hnull : (vol2.prod (volume.restrict (Ioi (0 : ℝ))))
      {q : (ℝ × ℝ) × ℝ | ¬(0:ℝ) < q.2} = 0 := by
    have hset : {q : (ℝ × ℝ) × ℝ | ¬(0:ℝ) < q.2}
        = (Set.univ : Set (ℝ × ℝ)) ×ˢ {s : ℝ | ¬(0:ℝ) < s} := by
      ext q; simp [Set.mem_prod]
    rw [hset, Measure.prod_prod]
    have hν0 : (volume.restrict (Ioi (0 : ℝ))) {s : ℝ | ¬(0:ℝ) < s} = 0 := by
      have hI : {s : ℝ | ¬(0:ℝ) < s} = Set.Iic (0:ℝ) := by
        ext s
        simp only [Set.mem_setOf_eq, Set.mem_Iic, not_lt]
      rw [hI, Measure.restrict_apply (measurableSet_Iic (a := (0:ℝ))),
        Set.Iic_inter_Ioi]
      simp
    rw [hν0]
    simp
  have hpos_ae : ∀ᵐ q : (ℝ × ℝ) × ℝ ∂(vol2.prod (volume.restrict (Ioi (0 : ℝ)))),
      (0:ℝ) < q.2 := by
    rw [MeasureTheory.ae_iff]
    exact hnull
  -- a.e. enorm equality for `|G|` (combined ofReal form, valid off the `q.2 ≤ 0` null set)
  have hae : Filter.Eventually
      (fun q : (ℝ × ℝ) × ℝ => ‖G q‖ₑ
        = ENNReal.ofReal (q.2 ^ (psi - 1) * exp (-(q.2 * |q.1.1 - q.1.2|))
            * (|(⇑f) q.1.2| * |(⇑f) q.1.1|)))
      (MeasureTheory.ae (vol2.prod (volume.restrict (Ioi (0 : ℝ))))) := by
    filter_upwards [hpos_ae] with q hq2
    rw [← ofReal_norm, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg hq2.le (psi - 1)),
      abs_of_nonneg (exp_nonneg _)]
    congr 1
    ring
  refine ⟨hGae, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_def, lintegral_congr_ae hae]
  -- Tonelli over the triple product (one Fubini split of the combined integrand)
  have hF2abs : AEStronglyMeasurable (fun q : (ℝ × ℝ) × ℝ => |(⇑f) q.1.2|)
      (vol2.prod (volume.restrict (Ioi (0 : ℝ)))) :=
    continuous_abs.comp_aestronglyMeasurable hF2
  have hF1abs : AEStronglyMeasurable (fun q : (ℝ × ℝ) × ℝ => |(⇑f) q.1.1|)
      (vol2.prod (volume.restrict (Ioi (0 : ℝ)))) :=
    continuous_abs.comp_aestronglyMeasurable hF1
  have hcomb : AEMeasurable (fun q : (ℝ × ℝ) × ℝ =>
      ENNReal.ofReal (q.2 ^ (psi - 1) * exp (-(q.2 * |q.1.1 - q.1.2|))
        * (|(⇑f) q.1.2| * |(⇑f) q.1.1|)))
      (vol2.prod (volume.restrict (Ioi (0 : ℝ)))) :=
    Measurable.comp_aemeasurable (g := fun x : ℝ => ENNReal.ofReal x)
      ENNReal.continuous_ofReal.measurable
        (((hA2.mul hE).mul (hF2abs.mul hF1abs))).aemeasurable
  rw [lintegral_prod _ hcomb]
  -- the inner `s`-integral: the pair factor is constant in `s`
  have hinner : ∀ p : ℝ × ℝ, (∫⁻ s : ℝ,
      ENNReal.ofReal (s ^ (psi - 1) * exp (-(s * |p.1 - p.2|))
        * (|(⇑f) p.2| * |(⇑f) p.1|)) ∂(volume.restrict (Ioi (0 : ℝ))))
      = (∫⁻ s : ℝ, ENNReal.ofReal (s ^ (psi - 1) * exp (-(s * |p.1 - p.2|)))
          ∂(volume.restrict (Ioi (0 : ℝ))))
        * ENNReal.ofReal (|(⇑f) p.2| * |(⇑f) p.1|) := by
    intro p
    have hcont : ContinuousOn (fun s : ℝ => s ^ (psi - 1) * exp (-(s * |p.1 - p.2|)))
        (Ioi (0:ℝ)) :=
      hcontA.mul (Real.continuous_exp.comp
        (Continuous.neg (continuous_id.mul continuous_const))).continuousOn
    have hmeas : AEMeasurable (fun s : ℝ =>
        ENNReal.ofReal (s ^ (psi - 1) * exp (-(s * |p.1 - p.2|))))
        (volume.restrict (Ioi (0 : ℝ))) :=
      Measurable.comp_aemeasurable (g := fun x : ℝ => ENNReal.ofReal x)
        ENNReal.continuous_ofReal.measurable
          (hcont.aestronglyMeasurable measurableSet_Ioi).aemeasurable
    have hspos : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), (0:ℝ) < s := by
      rw [MeasureTheory.ae_iff]
      have hI : {s : ℝ | ¬(0:ℝ) < s} = Set.Iic (0:ℝ) := by
        ext s; simp only [Set.mem_setOf_eq, Set.mem_Iic, not_lt]
      rw [hI, Measure.restrict_apply (measurableSet_Iic (a := (0:ℝ))),
        Set.Iic_inter_Ioi]
      simp
    rw [lintegral_congr_ae (hspos.mono fun s hs => ENNReal.ofReal_mul
      (mul_nonneg (Real.rpow_nonneg hs.le (psi - 1)) (exp_nonneg _))),
      lintegral_mul_const'' (ENNReal.ofReal (|(⇑f) p.2| * |(⇑f) p.1|)) hmeas]
  -- off the diagonal: the inner integral is `ofReal(Γ·|p.1-p.2|^{-ψ})`
  have hstage : (∫⁻ p : ℝ × ℝ,
      ∫⁻ s : ℝ, ENNReal.ofReal (s ^ (psi - 1) * exp (-(s * |p.1 - p.2|))
          * (|(⇑f) p.2| * |(⇑f) p.1|)) ∂(volume.restrict (Ioi (0 : ℝ))) ∂vol2)
      = ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Real.Gamma psi * |p.1 - p.2| ^ (-psi)
          * (|(⇑f) p.2| * |(⇑f) p.1|)) ∂vol2 := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_ne_diag] with p hp
    have hd : (0:ℝ) < |p.1 - p.2| := abs_pos.mpr (sub_ne_zero.mpr hp)
    have hgd : (0:ℝ) ≤ Real.Gamma psi * |p.1 - p.2| ^ (-psi) :=
      mul_nonneg (Real.Gamma_pos_of_pos hpsi0).le
        (Real.rpow_nonneg (abs_nonneg (p.1 - p.2)) (-psi))
    rw [hinner p, lintegral_laplace_eq hpsi0 hd, ← ENNReal.ofReal_mul hgd]
  rw [hstage]
  -- Schur: the `2ab ≤ a² + b²` split and the section bound
  have hΓ0 : (0:ℝ) ≤ Real.Gamma psi := (Real.Gamma_pos_of_pos hpsi0).le
  have hpt : ∀ p : ℝ × ℝ,
      Real.Gamma psi * |p.1 - p.2| ^ (-psi) * (|(⇑f) p.2| * |(⇑f) p.1|)
      ≤ Real.Gamma psi / 2 * (|p.1 - p.2| ^ (-psi) * |(⇑f) p.2| ^ 2
        + |p.1 - p.2| ^ (-psi) * |(⇑f) p.1| ^ 2) := by
    intro p
    have hab : 2 * (|(⇑f) p.2| * |(⇑f) p.1|)
        ≤ |(⇑f) p.2| ^ 2 + |(⇑f) p.1| ^ 2 := by
      have hsq := sq_nonneg (|(⇑f) p.2| - |(⇑f) p.1|)
      nlinarith
    have hd0 : (0:ℝ) ≤ |p.1 - p.2| ^ (-psi) :=
      Real.rpow_nonneg (abs_nonneg (p.1 - p.2)) (-psi)
    have hgd : (0:ℝ) ≤ Real.Gamma psi * |p.1 - p.2| ^ (-psi) := mul_nonneg hΓ0 hd0
    have hprod := mul_le_mul_of_nonneg_left hab hgd
    nlinarith [hprod]
  have hΓ2 : (0:ℝ) ≤ Real.Gamma psi / 2 := by linarith
  have hY0 : (0:ℝ) ≤ (2 + 2 / (1 - psi)) * ‖f‖ ^ 2 :=
    mul_nonneg (le_of_lt (by
      have h1s : (0:ℝ) < 1 - psi := by linarith
      exact add_pos (by norm_num) (div_pos (by norm_num) h1s))) (sq_nonneg ‖f‖)
  have hsplitL : (∫⁻ p : ℝ × ℝ,
      ENNReal.ofReal (Real.Gamma psi / 2 * (|p.1 - p.2| ^ (-psi) * |(⇑f) p.2| ^ 2)) ∂vol2)
      = ENNReal.ofReal (Real.Gamma psi / 2) * ∫⁻ p : ℝ × ℝ,
        ENNReal.ofReal (|p.1 - p.2| ^ (-psi) * |(⇑f) p.2| ^ 2) ∂vol2 := by
    rw [← lintegral_const_mul' (ENNReal.ofReal (Real.Gamma psi / 2)) _ ENNReal.ofReal_ne_top]
    exact lintegral_congr_ae (Eventually.of_forall fun p => ENNReal.ofReal_mul hΓ2)
  have hsplitR : (∫⁻ p : ℝ × ℝ,
      ENNReal.ofReal (Real.Gamma psi / 2 * (|p.1 - p.2| ^ (-psi) * |(⇑f) p.1| ^ 2)) ∂vol2)
      = ENNReal.ofReal (Real.Gamma psi / 2) * ∫⁻ p : ℝ × ℝ,
        ENNReal.ofReal (|p.1 - p.2| ^ (-psi) * |(⇑f) p.1| ^ 2) ∂vol2 := by
    rw [← lintegral_const_mul' (ENNReal.ofReal (Real.Gamma psi / 2)) _ ENNReal.ofReal_ne_top]
    exact lintegral_congr_ae (Eventually.of_forall fun p => ENNReal.ofReal_mul hΓ2)
  have hdir1 : ∫⁻ p : ℝ × ℝ,
      ENNReal.ofReal (Real.Gamma psi / 2 * (|p.1 - p.2| ^ (-psi) * |(⇑f) p.2| ^ 2)) ∂vol2
      ≤ ENNReal.ofReal (Real.Gamma psi * ((2 + 2 / (1 - psi)) * ‖f‖ ^ 2)) := by
    rw [hsplitL]
    refine le_trans (mul_le_mul_of_nonneg_left
      (lintegral_schur_dir hpsi0 (by linarith : psi < 1) f) (by simp)) ?_
    rw [← ENNReal.ofReal_mul hΓ2]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by linarith) hY0)
  have hdir2 : ∫⁻ p : ℝ × ℝ,
      ENNReal.ofReal (Real.Gamma psi / 2 * (|p.1 - p.2| ^ (-psi) * |(⇑f) p.1| ^ 2)) ∂vol2
      ≤ ENNReal.ofReal (Real.Gamma psi * ((2 + 2 / (1 - psi)) * ‖f‖ ^ 2)) := by
    rw [hsplitR]
    refine le_trans (mul_le_mul_of_nonneg_left
      (lintegral_schur_dir_swap hpsi0 (by linarith : psi < 1) f) (by simp)) ?_
    rw [← ENNReal.ofReal_mul hΓ2]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by linarith) hY0)
  -- measurability of the second summand for the additivity split
  have hF1abs2 : AEStronglyMeasurable (fun p : ℝ × ℝ => |(⇑f) p.1|) vol2 :=
    continuous_abs.comp_aestronglyMeasurable
      (MeasureTheory.Lp.aestronglyMeasurable f).comp_fst
  have hX1r : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      Real.Gamma psi / 2 * (|p.1 - p.2| ^ (-psi) * |(⇑f) p.1| ^ 2)) vol2 :=
    (measurable_const.aestronglyMeasurable).mul
      (((measurable_abs_sub_rpow (r := psi)).aestronglyMeasurable).mul
        ((hF1abs2.mul hF1abs2).congr
          (Eventually.of_forall fun p => (pow_two (|(⇑f) p.1|)).symm)))
  have hX1m : AEMeasurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal (Real.Gamma psi / 2 * (|p.1 - p.2| ^ (-psi) * |(⇑f) p.1| ^ 2))) vol2 :=
    Measurable.comp_aemeasurable (g := fun x : ℝ => ENNReal.ofReal x)
      ENNReal.continuous_ofReal.measurable hX1r.aemeasurable
  have haddint : (∫⁻ p : ℝ × ℝ,
      ENNReal.ofReal (Real.Gamma psi / 2 * (|p.1 - p.2| ^ (-psi) * |(⇑f) p.2| ^ 2))
        + ENNReal.ofReal (Real.Gamma psi / 2 * (|p.1 - p.2| ^ (-psi) * |(⇑f) p.1| ^ 2)) ∂vol2)
      = (∫⁻ p : ℝ × ℝ,
          ENNReal.ofReal (Real.Gamma psi / 2 * (|p.1 - p.2| ^ (-psi) * |(⇑f) p.2| ^ 2)) ∂vol2)
        + (∫⁻ p : ℝ × ℝ,
          ENNReal.ofReal (Real.Gamma psi / 2 * (|p.1 - p.2| ^ (-psi) * |(⇑f) p.1| ^ 2)) ∂vol2) :=
    lintegral_add_right' _ hX1m
  have hnn2 : ∀ p : ℝ × ℝ, (0:ℝ) ≤ Real.Gamma psi / 2 * (|p.1 - p.2| ^ (-psi) * |(⇑f) p.2| ^ 2) :=
    fun p => mul_nonneg hΓ2 (mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (sq_nonneg _))
  have hnn1 : ∀ p : ℝ × ℝ, (0:ℝ) ≤ Real.Gamma psi / 2 * (|p.1 - p.2| ^ (-psi) * |(⇑f) p.1| ^ 2) :=
    fun p => mul_nonneg hΓ2 (mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (sq_nonneg _))
  refine lt_of_le_of_lt (lintegral_mono fun p => ENNReal.ofReal_le_ofReal (hpt p)) ?_
  calc ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Real.Gamma psi / 2 * (|p.1 - p.2| ^ (-psi) * |(⇑f) p.2| ^ 2
          + |p.1 - p.2| ^ (-psi) * |(⇑f) p.1| ^ 2)) ∂vol2
      = ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Real.Gamma psi / 2 * (|p.1 - p.2| ^ (-psi) * |(⇑f) p.2| ^ 2))
            + ENNReal.ofReal (Real.Gamma psi / 2 * (|p.1 - p.2| ^ (-psi) * |(⇑f) p.1| ^ 2)) ∂vol2 := by
          refine lintegral_congr_ae (Eventually.of_forall fun p => ?_)
          simp only []
          rw [← ENNReal.ofReal_add (hnn2 p) (hnn1 p)]
          congr 1
          ring
    _ = ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Real.Gamma psi / 2 * (|p.1 - p.2| ^ (-psi) * |(⇑f) p.2| ^ 2)) ∂vol2
          + ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Real.Gamma psi / 2 * (|p.1 - p.2| ^ (-psi) * |(⇑f) p.1| ^ 2)) ∂vol2 := haddint
    _ ≤ ENNReal.ofReal (Real.Gamma psi * ((2 + 2 / (1 - psi)) * ‖f‖ ^ 2))
          + ENNReal.ofReal (Real.Gamma psi * ((2 + 2 / (1 - psi)) * ‖f‖ ^ 2)) := add_le_add hdir1 hdir2
    _ = ENNReal.ofReal (2 * (Real.Gamma psi * ((2 + 2 / (1 - psi)) * ‖f‖ ^ 2))) := by
          rw [← ENNReal.ofReal_add (mul_nonneg hΓ0 hY0) (mul_nonneg hΓ0 hY0)]
          congr 1
          ring
    _ < ⊤ := ENNReal.ofReal_lt_top

theorem inner_TOp_unweightedRiesz_nonneg {psi c : ℝ} (hpsi0 : 0 < psi) (hpsi2 : 2 * psi < 1)
    (hc : 0 ≤ c) (f : L2) :
    0 ≤ inner ℝ (TOp (unweightedRieszKernel psi c)
      (hsKernel_unweightedRieszKernel (le_of_lt hpsi0) hpsi2) f) f := by
  rw [inner_TOp]
  exact kernelPSD_rpow_dist_of_poisson hpsi0 (by linarith) hc (kernelPSD_exp_dist)
    (integrable_laplace_integrand hpsi0 hpsi2) f

/-! ### The complete nonneg eigenfamily -/

set_option maxHeartbeats 1000000 in
/-- **Frozen §2 (with the declared `hc : 0 ≤ c` deviation)**: a complete orthonormal
eigenfamily of the unweighted Riesz operator, with nonnegative eigenvalues and
square-summable eigenvalues. -/
theorem exists_nonneg_eigenfamily {psi c : ℝ} (hpsi0 : 0 < psi) (hpsi2 : 2 * psi < 1)
    (hc : 0 ≤ c) :
    ∃ (ι : Type) (v : ι → L2) (κ : ι → ℝ), Orthonormal ℝ v
      ∧ (∀ i, TOp (unweightedRieszKernel psi c)
          (hsKernel_unweightedRieszKernel (le_of_lt hpsi0) hpsi2) (v i) = κ i • v i)
      ∧ ((span ℝ (Set.range v))ᗮ = ⊥)
      ∧ (∀ i, 0 ≤ κ i) ∧ Summable (fun i => κ i ^ 2) := by
  classical
  obtain ⟨ι, v, κ, hv, he, hcomp⟩ :=
    exists_complete_eigenfamily_of_symmetric
      (T := (↑(TOp (unweightedRieszKernel psi c)
        (hsKernel_unweightedRieszKernel (le_of_lt hpsi0) hpsi2)) : L2 →ₗ[ℝ] L2))
      (isSymmetric_TOp_unweightedRiesz (le_of_lt hpsi0) hpsi2)
      (fun μ hμ => finiteDimensional_eigenspace_TOp
        (isCompactOperator_TOp_unweightedRiesz (le_of_lt hpsi0) hpsi2) hμ)
      (ContinuousLinearMap.isClosed_ker
        (TOp (unweightedRieszKernel psi c)
          (hsKernel_unweightedRieszKernel (le_of_lt hpsi0) hpsi2)))
      (orthogonalComplement_iSup_eigenspaces_TOp
        (isCompactOperator_TOp_unweightedRiesz (le_of_lt hpsi0) hpsi2)
        (isSymmetric_TOp_unweightedRiesz (le_of_lt hpsi0) hpsi2))
  refine ⟨ι, v, κ, hv, he, hcomp, ?_, ?_⟩
  · -- κ i ≥ 0 from the positivity of the quadratic form and the eigen equation
    intro i
    have hpos := inner_TOp_unweightedRiesz_nonneg hpsi0 hpsi2 hc (v i)
    rw [show inner ℝ (TOp (unweightedRieszKernel psi c)
          (hsKernel_unweightedRieszKernel (le_of_lt hpsi0) hpsi2) (v i)) (v i)
        = inner ℝ ((↑(TOp (unweightedRieszKernel psi c)
          (hsKernel_unweightedRieszKernel (le_of_lt hpsi0) hpsi2)) : L2 →ₗ[ℝ] L2)
          (v i)) (v i) from rfl, he i, real_inner_smul_left,
      real_inner_self_eq_norm_sq, hv.1 i, one_pow, mul_one] at hpos
    exact hpos
  · -- Summable κ² from `hsNorm K² = ∑' κ²`
    have h2 := hsNorm_sq_eq_tsum_eigenvalue_sq_of_orthonormal_complete
      (K := unweightedRieszKernel psi c)
      (hK := hsKernel_unweightedRieszKernel (le_of_lt hpsi0) hpsi2) hv hcomp he
    rcases eq_or_ne (hsNorm (unweightedRieszKernel psi c)) 0 with h0 | h0
    · -- hsNorm = 0 forces every eigenvalue to vanish
      have hκ0 : ∀ i, κ i = 0 := by
        intro i
        have hnorm : ‖TOp (unweightedRieszKernel psi c)
              (hsKernel_unweightedRieszKernel (le_of_lt hpsi0) hpsi2) (v i)‖ = |κ i| := by
          rw [show TOp (unweightedRieszKernel psi c)
              (hsKernel_unweightedRieszKernel (le_of_lt hpsi0) hpsi2) (v i)
              = (↑(TOp (unweightedRieszKernel psi c)
                (hsKernel_unweightedRieszKernel (le_of_lt hpsi0) hpsi2)) :
                L2 →ₗ[ℝ] L2) (v i) from rfl, he i, norm_smul, Real.norm_eq_abs,
            hv.1 i, mul_one]
        have hb : |κ i| ≤ hsNorm (unweightedRieszKernel psi c) := by
          refine le_trans hnorm.symm.le ?_
          refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
          rw [hv.1 i, mul_one]
          exact TOp_norm_le _
        rw [h0] at hb
        have h6 := abs_le.mp hb
        linarith
      have hz : ∀ i, κ i ^ 2 = 0 := by
        intro i
        rw [hκ0 i]
        ring
      have hsum : Summable (fun i : ι => (0:ℝ)) :=
        ⟨0, by simpa using tendsto_const_nhdf (a := (0:ℝ))⟩
      exact hsum.congr fun i => by rw [hz i]
    · by_cases hS : Summable (fun i => κ i ^ 2)
      · exact hS
      · rw [tsum_eq_zero_of_not_summable hS] at h2
        exact absurd (sq_eq_zero_iff.mp h2) h0

end HS

end
