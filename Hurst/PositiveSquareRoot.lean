import Hurst.HSOperatorFoundation
import Hurst.HSNormIdentity
import Hurst.ReverseParseval
import Hurst.TensorParsevalTracePair
import Hurst.EquivalentKernel
import Hurst.ActiveWeightProfile

/-!
# The abstract operator layer of the hconst fix (part 1): the multiplication operator

This file is the abstract operator-theoretic layer prescribed for
`Hurst/PositiveSquareRoot.lean` in the M1 contract (§3 of
`milestone1_hconst_elimination_math_spec.md`).  It is stated for **abstract**
operators on the carrier Hilbert space `HS.L2 = L²(vol)`, `vol` = Lebesgue
measure restricted to `I = [-1,1]`; no kernel and no `omega`-specifics appear
in the interface, so the file is independent of the concrete unweighted Riesz
layer and its theorems are instantiated later by a glue agent.

Construction route for the multiplication operator (mirroring the landed `TOp`
construction of `Hurst.HSOperatorFoundation`): the pairing
`mpair omega f g = ∫ omega(x) f(x) g(x) dvol` is a continuous bilinear form
(measurability gives an a.e.-measurable integrand, the essential bound
`∀ᵐ x ∂vol, |omega x| ≤ MR` gives integrability and the bound
`|mpair f g| ≤ MR‖f‖‖g‖`), and `M_omega` is its Fréchet–Riesz representation.
Since `vol` is supported on `I = [-1,1]`, only `omega|_I` matters; the
essential bound is exactly what the operator needs.
-/

open MeasureTheory Measure Real Set Submodule
open scoped Real

noncomputable section

namespace HS

/-! ### B. The multiplication operator `M_omega` -/

/-- An essential bound on a measurable function forces `0 ≤ MR`. -/
theorem MR_nonneg {omega : ℝ → ℝ} {MR : ℝ} (hess : ∀ᵐ x ∂vol, |omega x| ≤ MR) : 0 ≤ MR := by
  by_contra h
  have hM : MR < 0 := not_le.mp h
  have h0 : ∀ᵐ x ∂vol, (0:ℝ) ≤ MR := hess.mono fun _ hx => (abs_nonneg _).trans hx
  rw [ae_iff] at h0
  have h1 : ({x : ℝ | ¬ (0:ℝ) ≤ MR} : Set ℝ) = Set.univ := by
    ext x
    simp [hM]
  rw [h1] at h0
  have h2 : vol Set.univ ≠ 0 := by
    rw [Measure.restrict_apply MeasurableSet.univ]
    simp [Real.volume_Icc]
  exact h2 h0

/-- The multiplication pairing `∫ omega(x) f(x) g(x) dvol` over `I`. -/
def mpair (omega : ℝ → ℝ) (f g : L2) : ℝ :=
  ∫ x : ℝ, omega x * ⇑f x * ⇑g x ∂vol

/-- Measurability of `omega * f` on the carrier. -/
theorem aestronglyMeasurable_omega_mul {omega : ℝ → ℝ} (hm : Measurable omega) (f : L2) :
    AEStronglyMeasurable (fun x : ℝ => omega x * ⇑f x) vol :=
  (hm.aestronglyMeasurable (μ := vol)).mul (Lp.aestronglyMeasurable f)

/-- The pointwise product `omega * f` of a measurably, essentially-bounded
`omega` and an `L²` element is again in `L²`. -/
theorem memLp_omega_mul {omega : ℝ → ℝ} (hm : Measurable omega) {MR : ℝ}
    (hess : ∀ᵐ x ∂vol, |omega x| ≤ MR) (f : L2) :
    MemLp (fun x : ℝ => omega x * ⇑f x) 2 vol := by
  have hMR0 : 0 ≤ MR := MR_nonneg hess
  have hle : ∀ᵐ x ∂vol, ‖(fun x : ℝ => omega x * ⇑f x) x‖ ≤ ‖(fun x : ℝ => MR * ⇑f x) x‖ := by
    filter_upwards [hess] with x hx
    show |omega x * ⇑f x| ≤ |MR * ⇑f x|
    rw [abs_mul, abs_mul, abs_of_nonneg hMR0]
    exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)
  have hMRF : MemLp (fun x : ℝ => MR * ⇑f x) 2 vol := MemLp.const_mul (Lp.memLp f) MR
  refine ⟨aestronglyMeasurable_omega_mul hm f,
    lt_of_le_of_lt (eLpNorm_mono_ae hle) hMRF.2⟩

/-- Integrability of the multiplication pairing integrand. -/
theorem integrable_mpair {omega : ℝ → ℝ} (hm : Measurable omega) {MR : ℝ}
    (hess : ∀ᵐ x ∂vol, |omega x| ≤ MR) (f g : L2) :
    Integrable (fun x : ℝ => omega x * ⇑f x * ⇑g x) vol :=
  memLp_one_iff_integrable.mp
    (MemLp.mul (Lp.memLp g) (memLp_omega_mul hm hess f))

theorem mpair_bound {omega : ℝ → ℝ} (hm : Measurable omega) {MR : ℝ}
    (hess : ∀ᵐ x ∂vol, |omega x| ≤ MR) (f g : L2) :
    |mpair omega f g| ≤ MR * ‖f‖ * ‖g‖ := by
  have hMR0 : 0 ≤ MR := MR_nonneg hess
  have hf' : MemLp (⇑f) (ENNReal.ofReal 2) vol := by rw [real_two_ofReal]; exact Lp.memLp f
  have hg' : MemLp (⇑g) (ENNReal.ofReal 2) vol := by rw [real_two_ofReal]; exact Lp.memLp g
  have hcs := integral_mul_norm_le_Lp_mul_Lq holderTriple221 hf' hg'
  simp only [Real.norm_eq_abs] at hcs
  have h2f : ∫ a : ℝ, |⇑f a| ^ (2:ℝ) ∂vol = ∫ a : ℝ, ⇑f a ^ 2 ∂vol := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    exact (Real.rpow_two _).trans (sq_abs _)
  have h2g : ∫ a : ℝ, |⇑g a| ^ (2:ℝ) ∂vol = ∫ a : ℝ, ⇑g a ^ 2 ∂vol := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    exact (Real.rpow_two _).trans (sq_abs _)
  rw [h2f, h2g] at hcs
  have hint : Integrable (fun x : ℝ => MR * (|⇑f x| * |⇑g x|)) vol := by
    have h1 : Integrable (fun x : ℝ => |⇑g x * ⇑f x|) vol :=
      (memLp_one_iff_integrable.mp
        (MemLp.mul (Lp.memLp f) (Lp.memLp g))).abs
    refine h1.const_mul MR |>.congr ?_
    exact Filter.Eventually.of_forall fun x => by
      show MR * |⇑g x * ⇑f x| = MR * (|⇑f x| * |⇑g x|)
      rw [abs_mul]
      ring
  calc |mpair omega f g|
      = |∫ x : ℝ, omega x * ⇑f x * ⇑g x ∂vol| := rfl
    _ ≤ ∫ x : ℝ, |omega x * ⇑f x * ⇑g x| ∂vol := abs_integral_le_integral_abs
    _ ≤ ∫ x : ℝ, MR * (|⇑f x| * |⇑g x|) ∂vol := by
        refine integral_mono_ae (integrable_mpair hm hess f g).abs hint ?_
        filter_upwards [hess] with x hx
        rw [abs_mul, abs_mul, mul_assoc]
        exact mul_le_mul_of_nonneg_right hx (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = MR * ∫ x : ℝ, |⇑f x| * |⇑g x| ∂vol := by
        rw [integral_const_mul MR (fun x : ℝ => |⇑f x| * |⇑g x|)]
    _ ≤ MR * ((∫ x : ℝ, ⇑f x ^ 2 ∂vol) ^ ((1:ℝ)/2)
        * (∫ x : ℝ, ⇑g x ^ 2 ∂vol) ^ ((1:ℝ)/2)) :=
        mul_le_mul_of_nonneg_left hcs hMR0
    _ = MR * ‖f‖ * ‖g‖ :=
        (congrArg (fun t : ℝ => MR * t)
          (congrArg₂ (· * ·) (L2sq_eq_norm f) (L2sq_eq_norm g))).trans
          (mul_assoc MR ‖f‖ ‖g‖).symm

theorem mpair_add_g {omega : ℝ → ℝ} (hm : Measurable omega) {MR : ℝ}
    (hess : ∀ᵐ x ∂vol, |omega x| ≤ MR) (f g₁ g₂ : L2) :
    mpair omega f (g₁ + g₂) = mpair omega f g₁ + mpair omega f g₂ := by
  have hcongr : (fun x : ℝ => omega x * ⇑f x * ⇑(g₁ + g₂) x)
      =ᵐ[vol] fun x : ℝ => (omega x * ⇑f x * ⇑g₁ x + omega x * ⇑f x * ⇑g₂ x) := by
    filter_upwards [Lp.coeFn_add g₁ g₂] with x hx
    rw [hx, Pi.add_apply]
    ring
  show ∫ x : ℝ, omega x * ⇑f x * ⇑(g₁ + g₂) x ∂vol
      = ∫ x : ℝ, omega x * ⇑f x * ⇑g₁ x ∂vol + ∫ x : ℝ, omega x * ⇑f x * ⇑g₂ x ∂vol
  rw [integral_congr_ae hcongr, integral_add (integrable_mpair hm hess f g₁)
    (integrable_mpair hm hess f g₂)]

theorem mpair_smul_g (omega : ℝ → ℝ) (c : ℝ) (f g : L2) :
    mpair omega f (c • g) = c * mpair omega f g := by
  have hcongr : (fun x : ℝ => omega x * ⇑f x * ⇑(c • g) x)
      =ᵐ[vol] fun x : ℝ => c * (omega x * ⇑f x * ⇑g x) := by
    filter_upwards [Lp.coeFn_smul c g] with x hx
    rw [hx, Pi.smul_apply, smul_eq_mul]
    ring
  show ∫ x : ℝ, omega x * ⇑f x * ⇑(c • g) x ∂vol
      = c * ∫ x : ℝ, omega x * ⇑f x * ⇑g x ∂vol
  rw [integral_congr_ae hcongr, integral_const_mul c (fun x : ℝ => omega x * ⇑f x * ⇑g x)]

theorem mpair_add_f {omega : ℝ → ℝ} (hm : Measurable omega) {MR : ℝ}
    (hess : ∀ᵐ x ∂vol, |omega x| ≤ MR) (f₁ f₂ g : L2) :
    mpair omega (f₁ + f₂) g = mpair omega f₁ g + mpair omega f₂ g := by
  have hcongr : (fun x : ℝ => omega x * ⇑(f₁ + f₂) x * ⇑g x)
      =ᵐ[vol] fun x : ℝ => (omega x * ⇑f₁ x * ⇑g x + omega x * ⇑f₂ x * ⇑g x) := by
    filter_upwards [Lp.coeFn_add f₁ f₂] with x hx
    rw [hx, Pi.add_apply]
    ring
  show ∫ x : ℝ, omega x * ⇑(f₁ + f₂) x * ⇑g x ∂vol
      = ∫ x : ℝ, omega x * ⇑f₁ x * ⇑g x ∂vol + ∫ x : ℝ, omega x * ⇑f₂ x * ⇑g x ∂vol
  rw [integral_congr_ae hcongr, integral_add (integrable_mpair hm hess f₁ g)
    (integrable_mpair hm hess f₂ g)]

theorem mpair_smul_f (omega : ℝ → ℝ) (c : ℝ) (f g : L2) :
    mpair omega (c • f) g = c * mpair omega f g := by
  have hcongr : (fun x : ℝ => omega x * ⇑(c • f) x * ⇑g x)
      =ᵐ[vol] fun x : ℝ => c * (omega x * ⇑f x * ⇑g x) := by
    filter_upwards [Lp.coeFn_smul c f] with x hx
    rw [hx, Pi.smul_apply, smul_eq_mul]
    ring
  show ∫ x : ℝ, omega x * ⇑(c • f) x * ⇑g x ∂vol
      = c * ∫ x : ℝ, omega x * ⇑f x * ⇑g x ∂vol
  rw [integral_congr_ae hcongr, integral_const_mul c (fun x : ℝ => omega x * ⇑f x * ⇑g x)]

/-- Symmetry of the multiplication pairing (real case). -/
theorem mpair_symm (omega : ℝ → ℝ) (f g : L2) : mpair omega f g = mpair omega g f := by
  show ∫ x : ℝ, omega x * ⇑f x * ⇑g x ∂vol = ∫ x : ℝ, omega x * ⇑g x * ⇑f x ∂vol
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)

/-- The linear functional `g ↦ mpair omega f g`. -/
def mpairLm (omega : ℝ → ℝ) (hm : Measurable omega) {MR : ℝ}
    (hess : ∀ᵐ x ∂vol, |omega x| ≤ MR) (f : L2) : L2 →ₗ[ℝ] ℝ where
  toFun g := mpair omega f g
  map_add' := fun g₁ g₂ => mpair_add_g hm hess f g₁ g₂
  map_smul' := fun c g => by rw [RingHom.id_apply]; exact mpair_smul_g omega c f g

/-- The Fréchet–Riesz representer of `g ↦ ∫ omega(x) f(x) g(x) dvol`. -/
def mulOperatorFun (omega : ℝ → ℝ) (hm : Measurable omega) {MR : ℝ}
    (hess : ∀ᵐ x ∂vol, |omega x| ≤ MR) (f : L2) : L2 :=
  (InnerProductSpace.toDual ℝ L2).symm
    (LinearMap.mkContinuous (mpairLm omega hm hess f) (MR * ‖f‖)
      (fun g => by simp only [Real.norm_eq_abs]; exact mpair_bound hm hess f g))

/-- **Master formula for the representer**: `⟪M_omega f, g⟫ = ∫ omega f g`. -/
theorem inner_mulOperatorFun (omega : ℝ → ℝ) (hm : Measurable omega) {MR : ℝ}
    (hess : ∀ᵐ x ∂vol, |omega x| ≤ MR) (f g : L2) :
    inner ℝ (mulOperatorFun omega hm hess f) g = mpair omega f g := by
  unfold mulOperatorFun
  rw [InnerProductSpace.toDual_symm_apply]
  simp only [LinearMap.mkContinuous_apply, mpairLm]
  rfl

theorem mulOperatorFun_norm_le (omega : ℝ → ℝ) (hm : Measurable omega) {MR : ℝ}
    (hess : ∀ᵐ x ∂vol, |omega x| ≤ MR) (f : L2) :
    ‖mulOperatorFun omega hm hess f‖ ≤ MR * ‖f‖ := by
  have hMR0 : 0 ≤ MR := MR_nonneg hess
  unfold mulOperatorFun
  rw [LinearIsometryEquiv.norm_map]
  exact LinearMap.mkContinuous_norm_le _ (mul_nonneg hMR0 (norm_nonneg f)) _

theorem mulOperatorFun_add (omega : ℝ → ℝ) (hm : Measurable omega) {MR : ℝ}
    (hess : ∀ᵐ x ∂vol, |omega x| ≤ MR) (f₁ f₂ : L2) :
    mulOperatorFun omega hm hess (f₁ + f₂)
      = mulOperatorFun omega hm hess f₁ + mulOperatorFun omega hm hess f₂ :=
  eq_of_forall_inner_eq fun g => by
    rw [inner_add_left, inner_mulOperatorFun omega hm hess, inner_mulOperatorFun omega hm hess,
      inner_mulOperatorFun omega hm hess, mpair_add_f hm hess f₁ f₂ g]

theorem mulOperatorFun_smul (omega : ℝ → ℝ) (hm : Measurable omega) {MR : ℝ}
    (hess : ∀ᵐ x ∂vol, |omega x| ≤ MR) (c : ℝ) (f : L2) :
    mulOperatorFun omega hm hess (c • f) = c • mulOperatorFun omega hm hess f :=
  eq_of_forall_inner_eq fun g => by
    rw [real_inner_smul_left, inner_mulOperatorFun omega hm hess,
      inner_mulOperatorFun omega hm hess, mpair_smul_f omega c f]

/-- **The multiplication operator** `M_omega : L² → L²` of a measurable,
essentially bounded `omega` (Fréchet–Riesz construction on the multiplication
pairing).  Since `vol` is supported on `I = [-1,1]`, only `omega|_I` matters;
the essential bound `∀ᵐ x ∂vol, |omega x| ≤ MR` is exactly the hypothesis the
operator needs (a pointwise bound `∀ x, |omega x| ≤ MR` implies it via
`Filter.Eventually.of_forall`). -/
def mulOperator (omega : ℝ → ℝ) (hm : Measurable omega) {MR : ℝ}
    (hess : ∀ᵐ x ∂vol, |omega x| ≤ MR) : L2 →L[ℝ] L2 :=
  LinearMap.mkContinuous
    { toFun := mulOperatorFun omega hm hess
      map_add' := mulOperatorFun_add omega hm hess
      map_smul' := mulOperatorFun_smul omega hm hess }
    MR (fun f => mulOperatorFun_norm_le omega hm hess f)

theorem mulOperator_apply (omega : ℝ → ℝ) (hm : Measurable omega) {MR : ℝ}
    (hess : ∀ᵐ x ∂vol, |omega x| ≤ MR) (f : L2) :
    mulOperator omega hm hess f = mulOperatorFun omega hm hess f := rfl

/-- **Master formula**: `⟪M_omega f, g⟫ = ∫ omega(x) f(x) g(x) dvol`. -/
theorem inner_mulOperator (omega : ℝ → ℝ) (hm : Measurable omega) {MR : ℝ}
    (hess : ∀ᵐ x ∂vol, |omega x| ≤ MR) (f g : L2) :
    inner ℝ (mulOperator omega hm hess f) g = mpair omega f g :=
  inner_mulOperatorFun omega hm hess f g

/-- **Master formula** in integral form. -/
theorem inner_mulOperator' (omega : ℝ → ℝ) (hm : Measurable omega) {MR : ℝ}
    (hess : ∀ᵐ x ∂vol, |omega x| ≤ MR) (f g : L2) :
    inner ℝ (mulOperator omega hm hess f) g = ∫ x : ℝ, omega x * ⇑f x * ⇑g x ∂vol := by
  rw [inner_mulOperator omega hm hess]
  rfl

/-- Self-adjointness of the real multiplication operator. -/
theorem mulOperator_symm (omega : ℝ → ℝ) (hm : Measurable omega) {MR : ℝ}
    (hess : ∀ᵐ x ∂vol, |omega x| ≤ MR) :
    (↑(mulOperator omega hm hess) : L2 →ₗ[ℝ] L2).IsSymmetric := by
  intro f g
  have h1 := inner_mulOperator omega hm hess f g
  have h2 := inner_mulOperator omega hm hess g f
  rw [show inner ℝ f ((mulOperator omega hm hess : L2 →ₗ[ℝ] L2) g)
      = inner ℝ (mulOperator omega hm hess g) f from real_inner_comm _ _]
  show inner ℝ ((mulOperator omega hm hess : L2 →L[ℝ] L2) f) g
      = inner ℝ ((mulOperator omega hm hess : L2 →L[ℝ] L2) g) f
  rw [h1, h2, mpair_symm]

/-- Operator norm bound: `‖M_omega‖ ≤ MR` given the essential bound
`|omega| ≤ MR`. -/
theorem norm_mulOperator_le (omega : ℝ → ℝ) (hm : Measurable omega) {MR : ℝ}
    (hess : ∀ᵐ x ∂vol, |omega x| ≤ MR) : ‖mulOperator omega hm hess‖ ≤ MR :=
  LinearMap.mkContinuous_norm_le _ (MR_nonneg hess) (fun f => mulOperatorFun_norm_le omega hm hess f)

/-- Pointwise action bound: `‖M_omega f‖ ≤ MR * ‖f‖`. -/
theorem norm_mulOperator_apply_le (omega : ℝ → ℝ) (hm : Measurable omega) {MR : ℝ}
    (hess : ∀ᵐ x ∂vol, |omega x| ≤ MR) (f : L2) : ‖mulOperator omega hm hess f‖ ≤ MR * ‖f‖ := by
  refine le_trans (ContinuousLinearMap.le_opNorm _ f) ?_
  exact mul_le_mul_of_nonneg_right (norm_mulOperator_le omega hm hess) (norm_nonneg f)

/-- The a.e. action of `M_omega`: its representative is (the class of)
`omega • f` in `L²`. -/
theorem mulOperator_action (omega : ℝ → ℝ) (hm : Measurable omega) {MR : ℝ}
    (hess : ∀ᵐ x ∂vol, |omega x| ≤ MR) (f : L2) :
    mulOperator omega hm hess f = MemLp.toLp (fun x : ℝ => omega x * ⇑f x)
      (memLp_omega_mul hm hess f) :=
  eq_of_forall_inner_eq fun g => by
    rw [inner_mulOperator omega hm hess, inner_Lp_eq_coe]
    refine integral_congr_ae ?_
    symm
    exact (MemLp.coeFn_toLp (memLp_omega_mul hm hess f)).mul
      (Filter.Eventually.of_forall fun _ => rfl)

/-- The a.e. action in coercion form: `⇑(M_omega f) =ᵐ[vol] (omega • ⇑f)`. -/
theorem coeFn_mulOperator_action (omega : ℝ → ℝ) (hm : Measurable omega) {MR : ℝ}
    (hess : ∀ᵐ x ∂vol, |omega x| ≤ MR) (f : L2) :
    ⇑(mulOperator omega hm hess f) =ᵐ[vol] fun x : ℝ => omega x * ⇑f x := by
  rw [mulOperator_action omega hm hess f]
  exact MemLp.coeFn_toLp _

/-! ### Applicability: `omega := Hurst.equivalentKernel r` -/

/-- The model weight is measurable (continuous ⇒ measurable). -/
theorem measurable_equivalentKernel (r : ℕ) : Measurable (Hurst.equivalentKernel r) :=
  (Hurst.equivalentKernel_continuous r).measurable

/-- The model weight is essentially bounded. -/
theorem aeBounded_equivalentKernel (r : ℕ) :
    ∃ MR : ℝ, ∀ᵐ x ∂vol, |Hurst.equivalentKernel r x| ≤ MR := by
  obtain ⟨D, _, hD⟩ := Hurst.equivalentKernel_bounded r
  exact ⟨D, Filter.Eventually.of_forall hD⟩

/-! ### A. Series Cauchy–Schwarz and elementary tsum bounds -/

/-- Finset Cauchy–Schwarz: `(∑_{i ∈ s} |a i * b i|)² ≤ (∑_{i ∈ s} a i²)(∑_{i ∈ s} b i²)`. -/
theorem finset_abs_mul_sq_le {ι : Type*} (s : Finset ι) (a b : ι → ℝ) :
    (∑ i ∈ s, |a i * b i|) ^ 2 ≤ (∑ i ∈ s, a i ^ 2) * (∑ i ∈ s, b i ^ 2) := by
  calc (∑ i ∈ s, |a i * b i|) ^ 2
      = (∑ i ∈ s, |a i| * |b i|) ^ 2 := by
        rw [Finset.sum_congr rfl fun i _ => abs_mul (a i) (b i)]
    _ ≤ (∑ i ∈ s, |a i| ^ 2) * (∑ i ∈ s, |b i| ^ 2) :=
        Finset.sum_mul_sq_le_sq_mul_sq s (fun i => |a i|) (fun i => |b i|)
    _ = (∑ i ∈ s, a i ^ 2) * (∑ i ∈ s, b i ^ 2) := by
        simp only [sq_abs]



/-- Squared-index families are summable, and so is the pointwise product family
(in absolute value). -/
theorem summable_abs_mul_of_sq {ι : Type*} {a b : ι → ℝ}
    (ha : Summable (fun i => a i ^ 2)) (hb : Summable (fun i => b i ^ 2)) :
    Summable (fun i => |a i * b i|) :=
  Summable.of_norm_bounded (ha.add hb) fun i => by
    rw [Real.norm_eq_abs, abs_abs]
    exact abs_mul_le_sq_add_sq _ _

/-- **Series Cauchy–Schwarz**:
`∑' |a i b i| ≤ (∑' a i²)^(1/2) * (∑' b i²)^(1/2)`. -/
theorem tsum_abs_mul_le_sqrt {ι : Type*} (a b : ι → ℝ)
    (ha : Summable (fun i => a i ^ 2)) (hb : Summable (fun i => b i ^ 2)) :
    ∑' i, |a i * b i| ≤ ((∑' i, a i ^ 2) * (∑' i, b i ^ 2)) ^ ((1:ℝ) / 2) := by
  classical
  set C : ℝ := ((∑' i, a i ^ 2) * (∑' i, b i ^ 2)) ^ ((1:ℝ) / 2) with hCdef
  have hA0 : (0:ℝ) ≤ ∑' i, a i ^ 2 := tsum_nonneg fun _ => sq_nonneg _
  have hB0 : (0:ℝ) ≤ ∑' i, b i ^ 2 := tsum_nonneg fun _ => sq_nonneg _
  have hC0 : 0 ≤ C := Real.rpow_nonneg (mul_nonneg hA0 hB0) _
  have hfin : ∀ s : Finset ι, ∑ i ∈ s, |a i * b i| ≤ C := by
    intro s
    have h1 := finset_abs_mul_sq_le s a b
    have h2 : (∑ i ∈ s, a i ^ 2) ≤ ∑' i, a i ^ 2 :=
      Summable.sum_le_tsum s (fun i _ => sq_nonneg (a i)) ha
    have h3 : (∑ i ∈ s, b i ^ 2) ≤ ∑' i, b i ^ 2 :=
      Summable.sum_le_tsum s (fun i _ => sq_nonneg (b i)) hb
    have h3n : (0:ℝ) ≤ ∑ x ∈ s, a x ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg (a i)
    have h3n2 : (0:ℝ) ≤ ∑ x ∈ s, b x ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg (b i)
    have heq : C ^ 2 = (∑' i, a i ^ 2) * ∑' i, b i ^ 2 := by
      rw [hCdef, ← Real.sqrt_eq_rpow, Real.sq_sqrt (mul_nonneg hA0 hB0)]
    have h4 : (∑ i ∈ s, |a i * b i|) ^ 2 ≤ C ^ 2 := by
      refine le_trans h1 (le_trans (mul_le_mul h2 h3 h3n2 hA0) heq.symm.le)
    exact le_trans (Real.le_sqrt_of_sq_le h4) (by rw [Real.sqrt_sq hC0])
  refine le_of_tendsto (summable_abs_mul_of_sq ha hb).hasSum
    (Filter.Eventually.of_forall hfin)

/-- The triangle inequality for tsums: `|∑' t| ≤ ∑' |t|`. -/
theorem abs_tsum_le_abs {ι : Type*} {t : ι → ℝ} (ht : Summable t) :
    |∑' i, t i| ≤ ∑' i, |t i| := by
  have habs : Summable (fun i => |t i|) := ht.abs
  have hpos : ∑' i, t i ≤ ∑' i, |t i| :=
    Summable.tsum_le_tsum (fun i => le_abs_self _) ht habs
  have hneg : -(∑' i, |t i|) ≤ ∑' i, t i := by
    have hle : ∑' i, -|t i| ≤ ∑' i, t i :=
      Summable.tsum_le_tsum
        (fun i => by linarith [le_abs_self (-t i), abs_neg (t i)]) ht.abs.neg ht
    rw [tsum_neg] at hle
    exact hle
  rw [abs_le]
  exact ⟨hneg, hpos⟩

/-! ### C. The spectral (positive square-root) operator -/


variable {ι : Type} {v : ι → L2}

/-- Bessel: the squared coordinates of a vector along an orthonormal family are
summable and bounded by `‖u‖²`. -/
theorem norm_sq_eq_sq_inner {v : ι → L2} (u : L2) (i : ι) :
    ‖inner ℝ (v i) u‖ ^ 2 = inner ℝ (v i) u ^ 2 := by
  rw [Real.norm_eq_abs, sq_abs]

theorem summable_inner_sq_orth (hv : Orthonormal ℝ v) (u : L2) :
    Summable (fun i => inner ℝ (v i) u ^ 2) :=
  (hv.inner_products_summable u).congr fun i => norm_sq_eq_sq_inner (v := v) u i

theorem bessel_inner_sq (hv : Orthonormal ℝ v) (u : L2) :
    ∑' i, inner ℝ (v i) u ^ 2 ≤ ‖u‖ ^ 2 := by
  have h := hv.tsum_inner_products_le u
  have h2 : (∑' i, inner ℝ (v i) u ^ 2) = ∑' i, ‖inner ℝ (v i) u‖ ^ 2 :=
    tsum_congr fun i => (norm_sq_eq_sq_inner (v := v) u i).symm
  rw [h2]
  exact h

/-! ### D. The spectral pairing and the spectral operator -/

/-- The spectral pairing series attached to a coefficient family `c` on the
orthonormal family `v` (absolutely convergent whenever `c` is bounded). -/
def specPair (c : ι → ℝ) (x y : L2) : ℝ := ∑' i, c i * inner ℝ (v i) x * inner ℝ (v i) y

theorem specPair_symm {c : ι → ℝ} {v : ι → L2} (x y : L2) :
    specPair (v := v) c x y = specPair (v := v) c y x :=
  tsum_congr fun i => by ring

/-- Absolute summability of the spectral series for bounded coefficients. -/
theorem summable_specPair {c : ι → ℝ} {C : ℝ} (hc : ∀ i, |c i| ≤ C) (hC0 : 0 ≤ C)
    (hv : Orthonormal ℝ v) (x y : L2) :
    Summable (fun i => c i * inner ℝ (v i) x * inner ℝ (v i) y) := by
  have hx := bessel_inner_sq hv x
  have hy := bessel_inner_sq hv y
  have hdom : Summable (fun i => C * (inner ℝ (v i) x ^ 2 + inner ℝ (v i) y ^ 2)) :=
    Summable.mul_left C ((summable_inner_sq_orth hv x).add (summable_inner_sq_orth hv y))
  refine Summable.of_norm_bounded hdom fun i => ?_
  rw [Real.norm_eq_abs]
  have h2 : |inner ℝ (v i) x| * |inner ℝ (v i) y|
      ≤ inner ℝ (v i) x ^ 2 + inner ℝ (v i) y ^ 2 := by
    nlinarith [sq_abs (inner ℝ (v i) x), sq_abs (inner ℝ (v i) y),
      sq_nonneg (|inner ℝ (v i) x| - |inner ℝ (v i) y|)]
  rw [abs_mul, abs_mul]
  calc |c i| * |inner ℝ (v i) x| * |inner ℝ (v i) y|
      = |c i| * (|inner ℝ (v i) x| * |inner ℝ (v i) y|) := by ring
    _ ≤ C * (|inner ℝ (v i) x| * |inner ℝ (v i) y|) :=
        mul_le_mul_of_nonneg_right (hc i)
          (mul_nonneg (abs_nonneg (inner ℝ (v i) x)) (abs_nonneg (inner ℝ (v i) y)))
    _ ≤ C * (inner ℝ (v i) x ^ 2 + inner ℝ (v i) y ^ 2) :=
        mul_le_mul_of_nonneg_left h2 hC0

theorem specPair_add_f {c : ι → ℝ} {C : ℝ} (hc : ∀ i, |c i| ≤ C) (hC0 : 0 ≤ C)
    {v : ι → L2} (hv : Orthonormal ℝ v) (x₁ x₂ y : L2) :
    specPair (v := v) c (x₁ + x₂) y
      = specPair (v := v) c x₁ y + specPair (v := v) c x₂ y := by
  rw [specPair, specPair, specPair, ← Summable.tsum_add
    (summable_specPair hc hC0 hv x₁ y) (summable_specPair hc hC0 hv x₂ y)]
  exact tsum_congr fun i => by rw [inner_add_right]; ring

theorem specPair_smul_f {c : ι → ℝ} {C : ℝ} (hc : ∀ i, |c i| ≤ C) (hC0 : 0 ≤ C)
    {v : ι → L2} (hv : Orthonormal ℝ v) (t : ℝ) (x y : L2) :
    specPair (v := v) c (t • x) y = t * specPair (v := v) c x y := by
  rw [specPair, specPair, ← Summable.tsum_mul_left t (summable_specPair hc hC0 hv x y)]
  exact tsum_congr fun i => by rw [real_inner_smul_right]; ring

/-- **Operator-form Cauchy–Schwarz for the spectral series**:
`|specPair c x y| ≤ C ‖x‖ ‖y‖` for bounded coefficients. -/
theorem abs_specPair_le {c : ι → ℝ} {C : ℝ} (hc : ∀ i, |c i| ≤ C) (hC0 : 0 ≤ C)
    {v : ι → L2} (hv : Orthonormal ℝ v) (x y : L2) :
    |specPair (v := v) c x y| ≤ C * ‖x‖ * ‖y‖ := by
  have hterm := summable_specPair hc hC0 hv x y
  have hx := bessel_inner_sq hv x
  have hy := bessel_inner_sq hv y
  have hA0 : (0:ℝ) ≤ ∑' i, inner ℝ (v i) x ^ 2 :=
    tsum_nonneg fun i => sq_nonneg (inner ℝ (v i) x)
  have hB0 : (0:ℝ) ≤ ∑' i, inner ℝ (v i) y ^ 2 :=
    tsum_nonneg fun i => sq_nonneg (inner ℝ (v i) y)
  have hsqrtx : Real.sqrt (∑' i, inner ℝ (v i) x ^ 2) ≤ ‖x‖ := by
    refine (Real.sqrt_le_sqrt hx).trans ?_
    rw [Real.sqrt_sq (norm_nonneg x)]
  have hsqrty : Real.sqrt (∑' i, inner ℝ (v i) y ^ 2) ≤ ‖y‖ := by
    refine (Real.sqrt_le_sqrt hy).trans ?_
    rw [Real.sqrt_sq (norm_nonneg y)]
  calc |specPair (v := v) c x y|
      = |∑' i, c i * inner ℝ (v i) x * inner ℝ (v i) y| := rfl
    _ ≤ ∑' i, |c i * inner ℝ (v i) x * inner ℝ (v i) y| := abs_tsum_le_abs hterm
    _ ≤ C * (Real.sqrt (∑' i, inner ℝ (v i) x ^ 2)
        * Real.sqrt (∑' i, inner ℝ (v i) y ^ 2)) := by
      have hab := tsum_abs_mul_le_sqrt (fun i => inner ℝ (v i) x)
        (fun i => inner ℝ (v i) y) (summable_inner_sq_orth hv x) (summable_inner_sq_orth hv y)
      rw [← Real.sqrt_eq_rpow, Real.sqrt_mul hA0] at hab
      have habs2 : Summable (fun i => |inner ℝ (v i) x * inner ℝ (v i) y|) :=
        summable_abs_mul_of_sq (summable_inner_sq_orth hv x) (summable_inner_sq_orth hv y)
      have hCab : Summable (fun i => C * |inner ℝ (v i) x * inner ℝ (v i) y|) :=
        Summable.mul_left C habs2
      have h2' : ∑' i, |c i * inner ℝ (v i) x * inner ℝ (v i) y|
          ≤ ∑' i, C * |inner ℝ (v i) x * inner ℝ (v i) y| :=
        Summable.tsum_mono hterm.abs hCab fun i => by
          show |c i * inner ℝ (v i) x * inner ℝ (v i) y|
            ≤ C * |inner ℝ (v i) x * inner ℝ (v i) y|
          rw [abs_mul, abs_mul, abs_mul, mul_assoc]
          exact mul_le_mul_of_nonneg_right (hc i) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      have h1 : ∑' i, |c i * inner ℝ (v i) x * inner ℝ (v i) y|
          ≤ C * ∑' i, |inner ℝ (v i) x * inner ℝ (v i) y| :=
        h2'.trans (Summable.tsum_mul_left C habs2).le
      exact le_trans h1 (mul_le_mul_of_nonneg_left hab hC0)
    _ ≤ C * ‖x‖ * ‖y‖ :=
        (mul_le_mul_of_nonneg_left
          (mul_le_mul hsqrtx hsqrty (Real.sqrt_nonneg (∑' i, inner ℝ (v i) y ^ 2))
            (norm_nonneg x)) hC0).trans
          (mul_assoc C ‖x‖ ‖y‖).symm.le

/-! ### E. The spectral operator bundled via Frechet–Riesz -/

variable {c : ι → ℝ}

/-- The linear functional `y ↦ specPair c x y` (additivity/homogeneity need the
summability side conditions, supplied by the bound `hc`). -/
def specLm {c : ι → ℝ} {C : ℝ} (hc : ∀ i, |c i| ≤ C) (hC0 : 0 ≤ C) (hv : Orthonormal ℝ v)
    (x : L2) : L2 →ₗ[ℝ] ℝ where
  toFun y := specPair (v := v) c x y
  map_add' := fun y₁ y₂ => by
    show (∑' i, c i * inner ℝ (v i) x * inner ℝ (v i) (y₁ + y₂))
      = (∑' i, c i * inner ℝ (v i) x * inner ℝ (v i) y₁
        + ∑' i, c i * inner ℝ (v i) x * inner ℝ (v i) y₂)
    simp only [inner_add_right]
    rw [← Summable.tsum_add (summable_specPair hc hC0 hv x y₁)
      (summable_specPair hc hC0 hv x y₂)]
    exact tsum_congr fun i => by ring
  map_smul' := fun t y => by
    show (∑' i, c i * inner ℝ (v i) x * inner ℝ (v i) (t • y))
      = t * ∑' i, c i * inner ℝ (v i) x * inner ℝ (v i) y
    rw [← Summable.tsum_mul_left t (summable_specPair hc hC0 hv x y)]
    exact tsum_congr fun i => by rw [real_inner_smul_right]; ring

/-- The Frechet–Riesz representer of `y ↦ specPair c x y`. -/
def specOperatorFun {c : ι → ℝ} {C : ℝ} (hc : ∀ i, |c i| ≤ C) (hC0 : 0 ≤ C)
    (hv : Orthonormal ℝ v) (x : L2) : L2 :=
  (InnerProductSpace.toDual ℝ L2).symm
    (LinearMap.mkContinuous (specLm hc hC0 hv x) (C * ‖x‖)
      (fun y => by
        simp only [Real.norm_eq_abs]
        exact abs_specPair_le hc hC0 hv x y))

/-- **Master formula for the spectral representer**:
`⟪S x, y⟫ = ∑' i, c i ⟪v i, x⟫ ⟪v i, y⟫`. -/
theorem inner_specOperatorFun {c : ι → ℝ} {C : ℝ} (hc : ∀ i, |c i| ≤ C) (hC0 : 0 ≤ C)
    {v : ι → L2} (hv : Orthonormal ℝ v) (x y : L2) :
    inner ℝ (specOperatorFun hc hC0 hv x) y = specPair (v := v) c x y := by
  unfold specOperatorFun
  rw [InnerProductSpace.toDual_symm_apply]
  simp only [LinearMap.mkContinuous_apply, specLm]
  rfl

theorem specOperatorFun_norm_le {c : ι → ℝ} {C : ℝ} (hc : ∀ i, |c i| ≤ C) (hC0 : 0 ≤ C)
    {v : ι → L2} (hv : Orthonormal ℝ v) (x : L2) : ‖specOperatorFun hc hC0 hv x‖ ≤ C * ‖x‖ := by
  unfold specOperatorFun
  rw [LinearIsometryEquiv.norm_map]
  exact LinearMap.mkContinuous_norm_le _ (mul_nonneg hC0 (norm_nonneg x)) _

theorem specOperatorFun_add {c : ι → ℝ} {C : ℝ} (hc : ∀ i, |c i| ≤ C) (hC0 : 0 ≤ C)
    {v : ι → L2} (hv : Orthonormal ℝ v) (x₁ x₂ : L2) :
    specOperatorFun hc hC0 hv (x₁ + x₂)
      = specOperatorFun hc hC0 hv x₁ + specOperatorFun hc hC0 hv x₂ :=
  eq_of_forall_inner_eq fun y => by
    rw [inner_add_left, inner_specOperatorFun hc hC0 hv, inner_specOperatorFun hc hC0 hv,
      inner_specOperatorFun hc hC0 hv, specPair_add_f hc hC0 hv x₁ x₂ y]

theorem specOperatorFun_smul {c : ι → ℝ} {C : ℝ} (hc : ∀ i, |c i| ≤ C) (hC0 : 0 ≤ C)
    {v : ι → L2} (hv : Orthonormal ℝ v) (t : ℝ) (x : L2) :
    specOperatorFun hc hC0 hv (t • x) = t • specOperatorFun hc hC0 hv x :=
  eq_of_forall_inner_eq fun y => by
    rw [real_inner_smul_left, inner_specOperatorFun hc hC0 hv, inner_specOperatorFun hc hC0 hv,
      specPair_smul_f hc hC0 hv t x y]

/-- **The spectral operator** `S : L² → L²` with `⟪S x, y⟫ = ∑' i, c i ⟪v i, x⟫ ⟪v i, y⟫`. -/
def specOperator {c : ι → ℝ} {C : ℝ} (hc : ∀ i, |c i| ≤ C) (hC0 : 0 ≤ C)
    {v : ι → L2} (hv : Orthonormal ℝ v) : L2 →L[ℝ] L2 :=
  LinearMap.mkContinuous
    { toFun := specOperatorFun hc hC0 hv
      map_add' := specOperatorFun_add hc hC0 hv
      map_smul' := specOperatorFun_smul hc hC0 hv }
    C (fun x => specOperatorFun_norm_le hc hC0 hv x)

theorem specOperator_apply {c : ι → ℝ} {C : ℝ} (hc : ∀ i, |c i| ≤ C) (hC0 : 0 ≤ C)
    {v : ι → L2} (hv : Orthonormal ℝ v) (x : L2) :
    specOperator hc hC0 hv x = specOperatorFun hc hC0 hv x := rfl

/-- **Master formula**: `⟪S x, y⟫ = specPair c x y`. -/
theorem inner_specOperator {c : ι → ℝ} {C : ℝ} (hc : ∀ i, |c i| ≤ C) (hC0 : 0 ≤ C)
    {v : ι → L2} (hv : Orthonormal ℝ v) (x y : L2) :
    inner ℝ (specOperator hc hC0 hv x) y = specPair (v := v) c x y :=
  inner_specOperatorFun hc hC0 hv x y

/-- Operator norm bound: `‖S‖ ≤ C`. -/
theorem norm_specOperator_le {c : ι → ℝ} {C : ℝ} (hc : ∀ i, |c i| ≤ C) (hC0 : 0 ≤ C)
    {v : ι → L2} (hv : Orthonormal ℝ v) : ‖specOperator hc hC0 hv‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC0 (fun x => specOperatorFun_norm_le hc hC0 hv x)

/-- Self-adjointness of the spectral operator (real coefficients). -/
theorem specOperator_symm {c : ι → ℝ} {C : ℝ} (hc : ∀ i, |c i| ≤ C) (hC0 : 0 ≤ C)
    {v : ι → L2} (hv : Orthonormal ℝ v) :
    (↑(specOperator hc hC0 hv) : L2 →ₗ[ℝ] L2).IsSymmetric := by
  intro x y
  have h1 := inner_specOperator hc hC0 hv x y
  have h2 := inner_specOperator hc hC0 hv y x
  rw [show inner ℝ x ((specOperator hc hC0 hv : L2 →ₗ[ℝ] L2) y)
      = inner ℝ (specOperator hc hC0 hv y) x from real_inner_comm _ _]
  show inner ℝ ((specOperator hc hC0 hv : L2 →L[ℝ] L2) x) y
    = inner ℝ ((specOperator hc hC0 hv : L2 →L[ℝ] L2) y) x
  rw [h1, h2, specPair_symm]

/-- The spectral operator acts diagonally on the basis family. -/
theorem specOperator_apply_basis {c : ι → ℝ} {C : ℝ} (hc : ∀ i, |c i| ≤ C) (hC0 : 0 ≤ C)
    {v : ι → L2} (hv : Orthonormal ℝ v) (j : ι) :
    specOperator hc hC0 hv (v j) = c j • v j := by
  refine eq_of_forall_inner_eq fun y => ?_
  rw [real_inner_smul_left, inner_specOperator hc hC0 hv, specPair]
  rw [tsum_eq_single j (fun i hi => by
    rw [hv.2 hi]
    simp)]
  rw [real_inner_self_eq_norm_sq, hv.1 j, one_pow, mul_one]

/-- The pairing against a basis vector: `⟪v k, S x⟫ = c k ⟪v k, x⟫`. -/
theorem inner_specOperator_apply_right {c : ι → ℝ} {C : ℝ} (hc : ∀ i, |c i| ≤ C)
    (hC0 : 0 ≤ C) {v : ι → L2} (hv : Orthonormal ℝ v) (k : ι) (x : L2) :
    inner ℝ (v k) (specOperator hc hC0 hv x) = c k * inner ℝ (v k) x := by
  rw [real_inner_comm (specOperator hc hC0 hv x) (v k)]
  calc inner ℝ (specOperator hc hC0 hv x) (v k)
      = inner ℝ x (specOperator hc hC0 hv (v k)) := specOperator_symm hc hC0 hv x (v k)
    _ = c k * inner ℝ x (v k) := by
      rw [specOperator_apply_basis hc hC0 hv, real_inner_smul_right]
    _ = c k * inner ℝ (v k) x := by rw [real_inner_comm x (v k)]

/-- **Spectral norm formula**: `‖S x‖² = ∑' i, c i² ⟪v i, x⟫²`. -/
theorem norm_specOperator_sq {c : ι → ℝ} {C : ℝ} (hc : ∀ i, |c i| ≤ C) (hC0 : 0 ≤ C)
    {v : ι → L2} (hv : Orthonormal ℝ v) (x : L2) :
    ‖specOperator hc hC0 hv x‖ ^ 2 = ∑' i, c i ^ 2 * inner ℝ (v i) x ^ 2 := by
  rw [show ‖specOperator hc hC0 hv x‖ ^ 2
      = inner ℝ (specOperator hc hC0 hv x) (specOperator hc hC0 hv x) from
      (real_inner_self_eq_norm_sq _).symm, inner_specOperator hc hC0 hv]
  have hflip : ∀ k : ι, inner ℝ (v k) (specOperator hc hC0 hv x) = c k * inner ℝ (v k) x :=
    fun k => inner_specOperator_apply_right hc hC0 hv k x
  exact tsum_congr (fun k => by rw [hflip k]; ring)


/-! ### F. `sqrtOp`: the positive square root of `T` -/

/-- The eigenvalue bound `|κ i| ≤ ‖T‖` for an orthonormal eigenfamily. -/
theorem abs_kappa_le_norm {T : L2 →L[ℝ] L2} {κ : ι → ℝ} {v : ι → L2} (hv : Orthonormal ℝ v)
    (he : ∀ i, T (v i) = κ i • v i) (i : ι) : |κ i| ≤ ‖T‖ := by
  have h1 : ‖T (v i)‖ = ‖κ i • v i‖ := by rw [he i]
  rw [norm_smul, Real.norm_eq_abs, hv.1 i, mul_one] at h1
  have h2 : ‖T (v i)‖ ≤ ‖T‖ * ‖v i‖ := ContinuousLinearMap.le_opNorm T (v i)
  rw [hv.1 i, mul_one] at h2
  rw [← h1]
  exact h2

/-- Eigenvalue bound `κ i ≤ ‖T‖` for a nonnegative eigenfamily. -/
theorem kappa_le_norm_T {T : L2 →L[ℝ] L2} {κ : ι → ℝ} {v : ι → L2} (hv : Orthonormal ℝ v)
    (he : ∀ i, T (v i) = κ i • v i) (i : ι) : κ i ≤ ‖T‖ :=
  le_trans (le_abs_self (κ i)) (abs_kappa_le_norm hv he i)

/-- **The positive square-root operator**: the spectral operator with
coefficients `Real.sqrt (κ i)`; bounded because `κ i ≤ ‖T‖`. -/
theorem sqrt_kappa_le {T : L2 →L[ℝ] L2} {κ : ι → ℝ} {v : ι → L2} (hv : Orthonormal ℝ v)
    (he : ∀ i, T (v i) = κ i • v i) (_hκ0 : ∀ i, 0 ≤ κ i) (i : ι) :
    |Real.sqrt (κ i)| ≤ Real.sqrt ‖T‖ := by
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_sqrt (kappa_le_norm_T hv he i)

def sqrtOp {T : L2 →L[ℝ] L2} {κ : ι → ℝ} {v : ι → L2} (hv : Orthonormal ℝ v)
    (he : ∀ i, T (v i) = κ i • v i) (hκ0 : ∀ i, 0 ≤ κ i) : L2 →L[ℝ] L2 :=
  specOperator (c := fun i => Real.sqrt (κ i))
    (hc := fun i => sqrt_kappa_le hv he hκ0 i) (hC0 := Real.sqrt_nonneg ‖T‖) hv

theorem sqrtOp_apply {T : L2 →L[ℝ] L2} {κ : ι → ℝ} {v : ι → L2} (hv : Orthonormal ℝ v)
    (he : ∀ i, T (v i) = κ i • v i) (hκ0 : ∀ i, 0 ≤ κ i) (j : ι) :
    sqrtOp hv he hκ0 (v j) = Real.sqrt (κ j) • v j := by
  exact specOperator_apply_basis (hc := fun i => sqrt_kappa_le hv he hκ0 i)
    (hC0 := Real.sqrt_nonneg ‖T‖) hv j


theorem sqrtOp_symm {T : L2 →L[ℝ] L2} {κ : ι → ℝ} {v : ι → L2} (hv : Orthonormal ℝ v)
    (he : ∀ i, T (v i) = κ i • v i) (hκ0 : ∀ i, 0 ≤ κ i) :
    (↑(sqrtOp hv he hκ0) : L2 →ₗ[ℝ] L2).IsSymmetric := by
  exact specOperator_symm (hc := fun i => sqrt_kappa_le hv he hκ0 i)
    (hC0 := Real.sqrt_nonneg ‖T‖) hv


theorem inner_sqrtOp_apply_right {T : L2 →L[ℝ] L2} {κ : ι → ℝ} {v : ι → L2}
    (hv : Orthonormal ℝ v) (he : ∀ i, T (v i) = κ i • v i) (hκ0 : ∀ i, 0 ≤ κ i)
    (k : ι) (x : L2) :
    inner ℝ (v k) (sqrtOp hv he hκ0 x) = Real.sqrt (κ k) * inner ℝ (v k) x := by
  exact inner_specOperator_apply_right (hc := fun i => sqrt_kappa_le hv he hκ0 i)
    (hC0 := Real.sqrt_nonneg ‖T‖) hv k x

/-- **The reconstruction of `T` from its eigenfamily** (standard). -/
theorem inner_T_eq_specPair {T : L2 →L[ℝ] L2} {κ : ι → ℝ} (hTsym : (↑T : L2 →ₗ[ℝ] L2).IsSymmetric)
    {v : ι → L2} (hv : Orthonormal ℝ v) (he : ∀ i, T (v i) = κ i • v i)
    (hcomp : (span ℝ (Set.range v))ᗮ = ⊥) (x y : L2) :
    inner ℝ (T x) y = specPair (v := v) (fun i => κ i) x y := by
  have hexp := (HilbertBasis.mkOfOrthogonalEqBot hv hcomp).tsum_inner_mul_inner (T x) y
  simp only [HilbertBasis.coe_mkOfOrthogonalEqBot] at hexp
  rw [← hexp]
  refine tsum_congr fun i => ?_
  have h1 : inner ℝ (T x) (v i) = inner ℝ x (T (v i)) := hTsym x (v i)
  rw [h1, he i, real_inner_smul_right, real_inner_comm x (v i)]

/-- The spectral norm formula for the square root: `‖S u‖² = ∑' κ k ⟪v k, u⟫²`. -/
theorem norm_sqrtOp_sq {T : L2 →L[ℝ] L2} {κ : ι → ℝ} {v : ι → L2} (hv : Orthonormal ℝ v)
    (he : ∀ i, T (v i) = κ i • v i) (hκ0 : ∀ i, 0 ≤ κ i) (u : L2) :
    ‖sqrtOp hv he hκ0 u‖ ^ 2 = ∑' i, κ i * inner ℝ (v i) u ^ 2 := by
  unfold sqrtOp
  rw [norm_specOperator_sq (hc := fun i => sqrt_kappa_le hv he hκ0 i)
    (hC0 := Real.sqrt_nonneg ‖T‖) hv u]
  exact tsum_congr fun i => by rw [Real.sq_sqrt (hκ0 i)]

theorem sqrtOp_sq {T : L2 →L[ℝ] L2} {κ : ι → ℝ} {v : ι → L2}
    (hTsym : (↑T : L2 →ₗ[ℝ] L2).IsSymmetric) (hv : Orthonormal ℝ v)
    (he : ∀ i, T (v i) = κ i • v i) (hcomp : (span ℝ (Set.range v))ᗮ = ⊥)
    (hκ0 : ∀ i, 0 ≤ κ i) (x : L2) :
    sqrtOp hv he hκ0 (sqrtOp hv he hκ0 x) = T x := by
  unfold sqrtOp
  refine eq_of_forall_inner_eq fun y => ?_
  rw [inner_specOperator (hc := fun i => sqrt_kappa_le hv he hκ0 i)
    (hC0 := Real.sqrt_nonneg ‖T‖) hv
    (specOperator (c := fun i => Real.sqrt (κ i)) (hc := fun i => sqrt_kappa_le hv he hκ0 i)
      (hC0 := Real.sqrt_nonneg ‖T‖) hv x) y,
    inner_T_eq_specPair hTsym hv he hcomp]
  refine tsum_congr fun i => ?_
  show Real.sqrt (κ i) * inner ℝ (v i) (specOperator (c := fun i => Real.sqrt (κ i))
      (hc := fun i => sqrt_kappa_le hv he hκ0 i) (hC0 := Real.sqrt_nonneg ‖T‖) hv x)
    * inner ℝ (v i) y = κ i * inner ℝ (v i) x * inner ℝ (v i) y
  rw [inner_specOperator_apply_right (hc := fun i => sqrt_kappa_le hv he hκ0 i)
    (hC0 := Real.sqrt_nonneg ‖T‖) hv i x]
  linear_combination (inner ℝ (v i) x * inner ℝ (v i) y) * (Real.mul_self_sqrt (hκ0 i))
/-- Positivity of the positive square root. -/
theorem sqrtOp_nonneg {T : L2 →L[ℝ] L2} {κ : ι → ℝ} {v : ι → L2} (hv : Orthonormal ℝ v)
    (he : ∀ i, T (v i) = κ i • v i) (hκ0 : ∀ i, 0 ≤ κ i) (x : L2) :
    0 ≤ inner ℝ x (sqrtOp hv he hκ0 x) := by
  unfold sqrtOp
  rw [real_inner_comm (specOperator (c := fun i => Real.sqrt (κ i))
    (hc := fun i => sqrt_kappa_le hv he hκ0 i) (hC0 := Real.sqrt_nonneg ‖T‖) hv x) x,
    inner_specOperator (hc := fun i => sqrt_kappa_le hv he hκ0 i)
    (hC0 := Real.sqrt_nonneg ‖T‖) hv x x]
  show 0 ≤ ∑' i, Real.sqrt (κ i) * inner ℝ (v i) x * inner ℝ (v i) x
  refine tsum_nonneg fun i => ?_
  have hn : (0:ℝ) ≤ Real.sqrt (κ i) := Real.sqrt_nonneg _
  have hp : (0:ℝ) ≤ inner ℝ (v i) x * inner ℝ (v i) x := mul_self_nonneg _
  nlinarith [hn, hp]

/-- Norm corollary: `‖S (v i)‖ = Real.sqrt (κ i)`. -/
theorem norm_sqrtOp_apply {T : L2 →L[ℝ] L2} {κ : ι → ℝ} {v : ι → L2} (hv : Orthonormal ℝ v)
    (he : ∀ i, T (v i) = κ i • v i) (hκ0 : ∀ i, 0 ≤ κ i) (i : ι) :
    ‖sqrtOp hv he hκ0 (v i)‖ = Real.sqrt (κ i) := by
  rw [sqrtOp_apply hv he hκ0, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), hv.1 i, mul_one]

/-- **`exists_positive_sqrt` (frozen deliverable)**: a self-adjoint positive
square root of `T` on the complete nonnegative eigenfamily. -/
theorem exists_positive_sqrt {T : L2 →L[ℝ] L2} {v : ι → L2} {κ : ι → ℝ}
    (hTsym : (↑T : L2 →ₗ[ℝ] L2).IsSymmetric)
    (hv : Orthonormal ℝ v) (he : ∀ i, T (v i) = κ i • v i)
    (hcomp : (span ℝ (Set.range v))ᗮ = ⊥) (hκ0 : ∀ i, 0 ≤ κ i) :
    ∃ S : L2 →L[ℝ] L2,
      ((↑S : L2 →ₗ[ℝ] L2).IsSymmetric
        ∧ (∀ i, S (v i) = Real.sqrt (κ i) • v i)
        ∧ (∀ x, S (S x) = T x)
        ∧ (∀ x, 0 ≤ inner ℝ x (S x))
        ∧ (∀ i, ‖S (v i)‖ = Real.sqrt (κ i))) :=
  ⟨sqrtOp hv he hκ0, sqrtOp_symm hv he hκ0, sqrtOp_apply hv he hκ0,
    fun x => sqrtOp_sq hTsym hv he hcomp hκ0 x, sqrtOp_nonneg hv he hκ0,
    norm_sqrtOp_apply hv he hκ0⟩

/-! ### G. `B = S ∘ M_omega ∘ S`: self-adjointness and the A7 matrix bound -/

set_option maxHeartbeats 800000 in
/-- **A7 core**: the matrix family `κ i κ j * ⟪v j, W (v i)⟫²` is summable over
`ι × ι` with total at most `MR² * ∑' κ²` (AM–GM + Parseval per row and per
column + `‖W (v k)‖ ≤ MR`). -/
theorem summable_and_bound_matrix {κ : ι → ℝ} {v : ι → L2}
    {MR : ℝ} (hv : Orthonormal ℝ v) (hcomp : (span ℝ (Set.range v))ᗮ = ⊥)
    (hκ0 : ∀ i, 0 ≤ κ i) (hκ : Summable (fun i => κ i ^ 2)) (W : L2 →L[ℝ] L2)
    (hWsymm : ∀ x y : L2, inner ℝ (W x) y = inner ℝ x (W y))
    (hWn : ∀ u : L2, ‖W u‖ ≤ MR * ‖u‖) :
    Summable (fun p : ι × ι => κ p.1 * κ p.2 * inner ℝ (v p.2) (W (v p.1)) ^ 2)
      ∧ ∑' p : ι × ι, κ p.1 * κ p.2 * inner ℝ (v p.2) (W (v p.1)) ^ 2
        ≤ MR ^ 2 * ∑' i : ι, κ i ^ 2 := by
  classical
  -- the κ-bound and the norm bound
  have hWk : ∀ k : ι, ‖W (v k)‖ ≤ MR := by
    intro k
    have h2 := hWn (v k)
    rwa [hv.1 k, mul_one] at h2
  -- Parseval in v, two orientations
  have hpv : ∀ u : L2, ‖u‖ ^ 2 = ∑' i : ι, inner ℝ (v i) u ^ 2 := by
    intro u
    rw [norm_sq_eq_tsum_inner_sq_of_complete hv hcomp u]
    exact tsum_congr fun i => by rw [real_inner_comm]
  have hsumv : ∀ u : L2, Summable (fun i : ι => inner ℝ (v i) u ^ 2) := fun u =>
    summable_inner_sq_orth hv u
  -- the row-weighted family G and the column-weighted family H
  set G : ι × ι → ℝ := fun p => κ p.1 ^ 2 * inner ℝ (v p.2) (W (v p.1)) ^ 2 with hGdef
  set H : ι × ι → ℝ := fun p => κ p.2 ^ 2 * inner ℝ (v p.2) (W (v p.1)) ^ 2 with hHdef
  have hGnn : ∀ p : ι × ι, 0 ≤ G p := fun p => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hHnn : ∀ p : ι × ι, 0 ≤ H p := fun p => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  -- G: rows over the second coordinate (Bessel for the vector W (v i))
  have hGrow : ∀ i : ι, Summable (fun j : ι => G (i, j)) :=
    fun i => (hsumv (W (v i))).mul_left (κ i ^ 2)
  have hGrowsum : ∀ i : ι, ∑' j : ι, G (i, j) = κ i ^ 2 * ‖W (v i)‖ ^ 2 := by
    intro i
    rw [hGdef, Summable.tsum_mul_left (κ i ^ 2) (hsumv (W (v i))), hpv (W (v i))]
  have hGrowle : ∀ i : ι, ∑' j : ι, G (i, j) ≤ MR ^ 2 * κ i ^ 2 := by
    intro i
    rw [hGrowsum i]
    have hle : ‖W (v i)‖ ^ 2 ≤ MR * MR := by
      nlinarith [hWk i, norm_nonneg (W (v i))]
    calc κ i ^ 2 * ‖W (v i)‖ ^ 2 ≤ κ i ^ 2 * (MR * MR) :=
          mul_le_mul_of_nonneg_left hle (sq_nonneg (κ i))
      _ = MR ^ 2 * κ i ^ 2 := by ring
  have hG1sum : Summable (fun i : ι => ∑' j : ι, G (i, j)) :=
    Summable.of_nonneg_of_le (fun i => by rw [hGrowsum i]; positivity) hGrowle
      (Summable.mul_left (MR ^ 2) hκ)
  have hG1 : Summable G := (summable_prod_of_nonneg (f := G) hGnn).mpr ⟨hGrow, hG1sum⟩
  -- bound of ∑' G via its rows
  have hGbound : ∑' p : ι × ι, G p ≤ MR ^ 2 * ∑' i : ι, κ i ^ 2 := by
    rw [Summable.tsum_prod' hG1 hGrow]
    refine le_trans (Summable.tsum_le_tsum (fun i => ?_) hG1sum
      (Summable.mul_left (MR ^ 2) hκ)) ?_
    · rw [hGrowsum i]
      have hle : ‖W (v i)‖ ^ 2 ≤ MR * MR := by
        nlinarith [hWk i, norm_nonneg (W (v i))]
      calc κ i ^ 2 * ‖W (v i)‖ ^ 2 ≤ κ i ^ 2 * (MR * MR) :=
            mul_le_mul_of_nonneg_left hle (sq_nonneg (κ i))
        _ = MR ^ 2 * κ i ^ 2 := by ring
    · rw [Summable.tsum_mul_left _ hκ]
  -- `H` is `G` composed with the coordinate swap (self-adjointness of `W`):
  -- `H p = κ p.2²·⟪v p.2, W (v p.1)⟫² = κ p.2²·⟪v p.1, W (v p.2)⟫² = G p.swap`.
  have hfam : ∀ (i j : ι), inner ℝ (v j) (W (v i)) = inner ℝ (v i) (W (v j)) := by
    intro i j
    rw [← real_inner_comm (v j) (W (v i)), hWsymm (v i) (v j)]
  have hHswapG : ∀ p : ι × ι, H p = G p.swap := by
    intro p
    rw [hHdef, hGdef]
    show κ p.2 ^ 2 * inner ℝ (v p.2) (W (v p.1)) ^ 2
        = κ p.2 ^ 2 * inner ℝ (v p.1) (W (v p.2)) ^ 2
    rw [hfam p.1 p.2]
  have hHb0 : ∀ s : Finset (ι × ι),
      ∑ p ∈ s, H p ≤ MR ^ 2 * ∑' i : ι, κ i ^ 2 := by
    intro s
    have h1 : ∑ p ∈ s, H p = ∑ p ∈ s, G p.swap :=
      Finset.sum_congr rfl fun p _ => hHswapG p
    rw [h1]
    have h2 : ∑ p ∈ s, G p.swap = ∑ q ∈ s.image Prod.swap, G q :=
      (Finset.sum_image
        (fun x _hx y _hy hxy => by simpa using congrArg Prod.swap hxy)).symm
    rw [h2]
    exact le_trans (Summable.sum_le_tsum _ (fun i _ => hGnn i) hG1) hGbound
  have hH : Summable H := summable_of_sum_le hHnn hHb0
  -- bound of `∑' H` (same constant as `hGbound`)
  have hHbound : ∑' p : ι × ι, H p ≤ MR ^ 2 * ∑' i : ι, κ i ^ 2 :=
    Real.tsum_le_of_sum_le hHnn hHb0
  -- the AM–GM domination of the matrix family by `(1/2)·(G + H)`
  have hW2le : ∀ p : ι × ι,
      κ p.1 * κ p.2 * inner ℝ (v p.2) (W (v p.1)) ^ 2
        ≤ (1 / 2 : ℝ) * (G p + H p) := by
    intro p
    rw [hGdef, hHdef]
    have h2 : 2 * (κ p.1 * κ p.2) ≤ κ p.1 ^ 2 + κ p.2 ^ 2 := by
      nlinarith [sq_nonneg (κ p.1 - κ p.2)]
    nlinarith [sq_nonneg (inner ℝ (v p.2) (W (v p.1))), h2]
  have hDsum : Summable (fun p : ι × ι => (1 / 2 : ℝ) * (G p + H p)) :=
    (hG1.add hH).mul_left (1 / 2)
  have hW2sum : Summable (fun p : ι × ι => κ p.1 * κ p.2 * inner ℝ (v p.2) (W (v p.1)) ^ 2) :=
    Summable.of_norm_bounded hDsum fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (mul_nonneg (hκ0 p.1) (hκ0 p.2)) (sq_nonneg _))]
      exact hW2le p
  -- the bound
  have hstep : ∑' p : ι × ι, κ p.1 * κ p.2 * inner ℝ (v p.2) (W (v p.1)) ^ 2
      ≤ ∑' p : ι × ι, (1 / 2 : ℝ) * (G p + H p) :=
    Summable.tsum_le_tsum hW2le hW2sum hDsum
  have hsplit : ∑' p : ι × ι, (1 / 2 : ℝ) * (G p + H p)
      = (1 / 2 : ℝ) * (∑' p : ι × ι, G p + ∑' p : ι × ι, H p) := by
    rw [Summable.tsum_mul_left (1 / 2) (hG1.add hH), Summable.tsum_add hG1 hH]
  refine ⟨hW2sum, ?_⟩
  rw [hsplit] at hstep
  refine le_trans hstep ?_
  nlinarith [hGbound, hHbound]

end HS

end