import Mathlib

/-!
# Hilbert–Schmidt operator foundation for kernel operators on L² over the unit square

Mathlib v4.31 has no `HilbertSchmidt`/`Schatten` API (verified by search), so this file
builds the minimal working layer that the Riesz spectrum construction (file 23, A2/A3) needs.

## Encoding choice

* Carrier measure: `vol := volume.restrict (Icc (-1:ℝ) 1)` on the type `ℝ`.  Thus
  `L2 := MeasureTheory.Lp ℝ 2 vol` is (a model of) `L²(Icc(-1,1))` with all Mathlib
  instances (`InnerProductSpace ℝ`, `CompleteSpace`, `SFinite`, …) available.  We avoid the
  subtype type `↥(Icc (-1:ℝ) 1)` because it carries no `MeasureSpace` instance in v4.31.
* Kernels are plain functions `K : ℝ × ℝ → ℝ` (values off `Icc × Icc` are irrelevant to the
  restricted measures) with `HSKernel K := MemLp K 2 (vol.prod vol)`, and
  `hsNorm K = (∫∫ K²)^{1/2}` is the kernel L² (Hilbert–Schmidt) norm.
* The operator `TOp K hK : L2 →L[ℝ] L2` is defined through the **Fréchet–Riesz representation**
  from the kernel pairing `kpair K f g = ∫∫ K(x,y) f(y) g(x)`, rather than by a pointwise a.e.
  construction `x ↦ ∫ K(x,y) f(y) dy`.  This avoids all a.e.-section bookkeeping; the master
  formula `inner_TOpFun` recovers the pointwise pairing anyway.

## Deviations from the file-23 A2/A3 wishlist

* The k = 1 trace identity `tr(TOp K) = ∫ K(x,x)` is **not** landed: for a general
  square-integrable kernel the diagonal integral is not well-defined independent of basis, and
  `∑⟨Te_i,e_i⟩` need not converge absolutely for HS operators.  The spec (A3 item 6 and the
  closing remark) only uses trace pairings of products with ≥ 2 HS factors; the k = 2 cycle
  pairing `cycle2` and its absolute bound are landed here, which is exactly the form A2 uses.
* The general-k cycle bound A2 is not yet landed (it needs iterated-Fubini composition
  machinery on `ℝ^k`); the k = 2 case and the full operator layer are.
* The kernel-norm triangle inequality is deferred; linearity of `K ↦ TOp K` (`TOp_add`,
  `TOp_smul`) is proved directly.

## Main results

* `hsNorm`, `HSKernel`: kernel-level HS structure; transpose-invariance `hsNorm_transpose`.
* `TOp K hK : L2 →L[ℝ] L2` with
  * `TOp_le : ‖TOp K f‖ ≤ hsNorm K * ‖f‖`, `TOp_norm_le : ‖TOp K‖ ≤ hsNorm K`;
  * `inner_TOpFun : ⟪TOp K f, g⟫ = ∫∫ K(x,y) f y g x` (master formula);
  * `TOp_add`, `TOp_smul`: linearity in the kernel;
  * `TOp_adjoint : (TOp K)† = TOp Kᵀ`, `TOp_selfAdjoint` for symmetric kernels.
* `cycle2 K L = ∫∫ K(x,y) L(y,x)` with `cycle2_bound : |cycle2 K L| ≤ hsNorm K * hsNorm L`
  and `cycle2_symm` — the k = 2 cycle input for trace powers.
-/

open MeasureTheory Measure Real Set
open scoped Real

noncomputable section

namespace HS

/-- The unit interval `[-1, 1]` as a set of reals. -/
abbrev I : Set ℝ := Icc (-1 : ℝ) 1

/-- Lebesgue measure restricted to `[-1, 1]`; the measure of the carrier space. -/
abbrev vol : Measure ℝ := volume.restrict I

instance volIsFin : IsFiniteMeasure vol := by
  constructor
  rw [Measure.restrict_apply MeasurableSet.univ]
  simp [Real.volume_Icc]

/-- Product measure on the unit square. -/
abbrev vol2 : Measure (ℝ × ℝ) := vol.prod vol

/-- `L²(Icc(-1,1))` — the carrier Hilbert space. -/
abbrev L2 : Type := MeasureTheory.Lp ℝ 2 vol

/-- Kernel-level Hilbert–Schmidt (L²) norm: `(∫∫ K²)^{1/2}`. -/
def hsNorm (K : ℝ × ℝ → ℝ) : ℝ := (∫ p : ℝ × ℝ, K p ^ 2 ∂vol2) ^ ((1 : ℝ) / 2)

/-- A square-integrable (Hilbert–Schmidt) kernel. -/
abbrev HSKernel (K : ℝ × ℝ → ℝ) : Prop := MemLp K 2 vol2

theorem hsNorm_def (K : ℝ × ℝ → ℝ) : hsNorm K = Real.sqrt (∫ p : ℝ × ℝ, K p ^ 2 ∂vol2) := by
  simp only [hsNorm, ← Real.sqrt_eq_rpow]

theorem hsNorm_nonneg (K : ℝ × ℝ → ℝ) : 0 ≤ hsNorm K := by
  apply Real.rpow_nonneg
  exact integral_nonneg fun _ => sq_nonneg _

theorem holderTriple221 : Real.HolderTriple 2 2 1 := ⟨by norm_num, by norm_num, by norm_num⟩

theorem real_two_ofReal : ENNReal.ofReal (2 : ℝ) = 2 := by simp

/-! ### Bridges between `L2` norms and integrals -/

theorem Lp_coe_memLp (f : L2) : MemLp (⇑f) 2 vol := Lp.memLp f

/-- `‖f‖² = ∫ f²` for `f : L2`. -/
theorem L2norm_sq (f : L2) : ‖f‖ ^ 2 = ∫ x : ℝ, (⇑f) x ^ 2 ∂vol := by
  rw [show ‖f‖ ^ 2 = inner ℝ f f from (real_inner_self_eq_norm_sq f).symm, L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [RCLike.inner_apply, RCLike.conj_to_real]
  ring

theorem L2sq_eq_norm (f : L2) : (∫ x : ℝ, (⇑f) x ^ 2 ∂vol) ^ ((1 : ℝ) / 2) = ‖f‖ := by
  rw [← Real.sqrt_eq_rpow, ← L2norm_sq f]
  exact Real.sqrt_sq (norm_nonneg f)

/-! ### Elementary lifting and exponent bridges -/

/-- Bridge between the real-power and the usual square inside integrals. -/
theorem integral_pow_two (u : ℝ × ℝ → ℝ) :
    ∫ p : ℝ × ℝ, u p ^ (2 : ℝ) ∂vol2 = ∫ p : ℝ × ℝ, u p ^ 2 ∂vol2 := by
  apply integral_congr_ae
  filter_upwards with p
  rw [Real.rpow_two, pow_two]

/-- Lift an a.e. equality on the first coordinate to the product measure
(the Mathlib product measure is defined on all sets, so `prod_prod` applies without
measurability side conditions). -/
theorem eventual_fst {u v : ℝ → ℝ} (h : u =ᵐ[vol] v) :
    (fun p : ℝ × ℝ => u p.1) =ᵐ[vol2] (fun p : ℝ × ℝ => v p.1) := by
  have h' : ∀ᵐ x : ℝ ∂vol, u x = v x := h
  rw [ae_iff] at h'
  show ∀ᵐ p : ℝ × ℝ ∂vol2, u p.1 = v p.1
  rw [ae_iff]
  have hset : {p : ℝ × ℝ | ¬ (u p.1 = v p.1)}
      = {x : ℝ | ¬ (u x = v x)} ×ˢ (univ : Set ℝ) := by
    ext p
    simp [Set.mem_prod]
  rw [hset, Measure.prod_prod, h']
  simp

/-- Lift an a.e. equality on the second coordinate to the product measure. -/
theorem eventual_snd {u v : ℝ → ℝ} (h : u =ᵐ[vol] v) :
    (fun p : ℝ × ℝ => u p.2) =ᵐ[vol2] (fun p : ℝ × ℝ => v p.2) := by
  have h' : ∀ᵐ x : ℝ ∂vol, u x = v x := h
  rw [ae_iff] at h'
  show ∀ᵐ p : ℝ × ℝ ∂vol2, u p.2 = v p.2
  rw [ae_iff]
  have hset : {p : ℝ × ℝ | ¬ (u p.2 = v p.2)}
      = (univ : Set ℝ) ×ˢ {x : ℝ | ¬ (u x = v x)} := by
    ext p
    simp [Set.mem_prod]
  rw [hset, Measure.prod_prod, h']
  simp

/-! ### Square-integrability of the coordinate pairing -/

/-- The pairing function `(x, y) ↦ f y * g x` is square-integrable on the unit square. -/
theorem memLp_pair (f g : L2) :
    MemLp (fun p : ℝ × ℝ => (⇑f) p.2 * (⇑g) p.1) 2 vol2 := by
  have h1 : Integrable (fun x : ℝ => (⇑g) x ^ 2) vol := (Lp.memLp g).integrable_sq
  have h2 : Integrable (fun y : ℝ => (⇑f) y ^ 2) vol := (Lp.memLp f).integrable_sq
  have hae : AEStronglyMeasurable (fun p : ℝ × ℝ => (⇑f) p.2 * (⇑g) p.1) vol2 :=
    ((Lp.aestronglyMeasurable f).comp_snd).mul (Lp.aestronglyMeasurable g).comp_fst
  rw [memLp_two_iff_integrable_sq_norm hae]
  have h3 : Integrable (fun p : ℝ × ℝ => (⇑g) p.1 ^ 2 * (⇑f) p.2 ^ 2) vol2 :=
    Integrable.op_fst_snd (op := fun a b : ℝ => a * b)
      (by fun_prop) ⟨1, fun a b => by simp [Real.norm_eq_abs, abs_mul]⟩ h1 h2
  refine h3.congr ?_
  filter_upwards with p
  simp only [Real.norm_eq_abs, abs_mul, mul_pow, sq_abs]
  ring

/-- **Cauchy–Schwarz on the unit square**: the triple-product kernel bound. -/
theorem kernel_CS {K : ℝ × ℝ → ℝ} (hK : HSKernel K) (f g : L2) :
    ∫ p : ℝ × ℝ, |K p * (⇑f) p.2 * (⇑g) p.1| ∂vol2 ≤ hsNorm K * ‖f‖ * ‖g‖ := by
  have hK' : MemLp K (ENNReal.ofReal 2) vol2 := by rw [real_two_ofReal]; exact hK
  have hv : MemLp (fun p : ℝ × ℝ => (⇑f) p.2 * (⇑g) p.1) (ENNReal.ofReal 2) vol2 := by
    rw [real_two_ofReal]; exact memLp_pair f g
  have hcs := integral_mul_norm_le_Lp_mul_Lq holderTriple221 hK' hv
  simp only [Real.norm_eq_abs] at hcs
  rw [integral_pow_two (fun p => |K p|),
    integral_pow_two (fun p => |(⇑f) p.2 * (⇑g) p.1|)] at hcs
  have hKabs : (∫ p : ℝ × ℝ, |K p| ^ 2 ∂vol2) ^ ((1 : ℝ) / 2) = hsNorm K := by
    rw [← Real.sqrt_eq_rpow, hsNorm_def]
    refine congrArg Real.sqrt ?_
    exact integral_congr_ae (Filter.Eventually.of_forall fun p => by simp [sq_abs])
  have hpt : ∀ p : ℝ × ℝ, |(⇑f) p.2 * (⇑g) p.1| ^ 2 = (⇑g) p.1 ^ 2 * (⇑f) p.2 ^ 2 := by
    intro p; simp only [Real.norm_eq_abs, abs_mul, mul_pow, sq_abs]; ring
  have hsq : (∫ p : ℝ × ℝ, |(⇑f) p.2 * (⇑g) p.1| ^ 2 ∂vol2) ^ ((1 : ℝ) / 2) = ‖f‖ * ‖g‖ := by
    have hI : ∫ p : ℝ × ℝ, |(⇑f) p.2 * (⇑g) p.1| ^ 2 ∂vol2
        = (∫ x : ℝ, (⇑g) x ^ 2 ∂vol) * (∫ y : ℝ, (⇑f) y ^ 2 ∂vol) := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
        integral_prod_mul (fun x : ℝ => (⇑g) x ^ 2) (fun y : ℝ => (⇑f) y ^ 2)]
    rw [← Real.sqrt_eq_rpow, hI, (L2norm_sq g).symm, (L2norm_sq f).symm,
      Real.sqrt_mul (sq_nonneg ‖g‖), Real.sqrt_sq (norm_nonneg g),
      Real.sqrt_sq (norm_nonneg f)]
    ring
  rw [hKabs, hsq] at hcs
  have hsplit : ∫ p : ℝ × ℝ, |K p * (⇑f) p.2 * (⇑g) p.1| ∂vol2
      = ∫ p : ℝ × ℝ, |K p| * |(⇑f) p.2 * (⇑g) p.1| ∂vol2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [Real.norm_eq_abs, abs_mul]
    ring_nf
  rw [hsplit]; exact hcs.trans_eq (by ring)

/-! ### The kernel pairing -/

/-- The kernel pairing `kpair K f g = ∫∫ K(x,y) f(y) g(x) dxdy` over the unit square. -/
def kpair (K : ℝ × ℝ → ℝ) (f g : L2) : ℝ :=
  ∫ p : ℝ × ℝ, K p * (⇑f) p.2 * (⇑g) p.1 ∂vol2

theorem integrable_kintegrand {K : ℝ × ℝ → ℝ} (hK : HSKernel K) (f g : L2) :
    Integrable (fun p : ℝ × ℝ => K p * (⇑f) p.2 * (⇑g) p.1) vol2 := by
  haveI : ENNReal.HolderTriple 2 2 1 := inferInstance
  have h : MemLp (K * fun p : ℝ × ℝ => (⇑f) p.2 * (⇑g) p.1) 1 vol2 :=
    MemLp.mul (memLp_pair f g) hK
  refine (memLp_one_iff_integrable.mp h).congr ?_
  filter_upwards with p
  simp only [Pi.mul_apply]
  ring

theorem kpair_bound {K : ℝ × ℝ → ℝ} (hK : HSKernel K) (f g : L2) :
    |kpair K f g| ≤ hsNorm K * ‖f‖ * ‖g‖ := by
  have e : kpair K f g = ∫ p : ℝ × ℝ, K p * (⇑f) p.2 * (⇑g) p.1 ∂vol2 := rfl
  calc |kpair K f g|
      = |∫ p : ℝ × ℝ, K p * (⇑f) p.2 * (⇑g) p.1 ∂vol2| := by rw [e]
    _ ≤ ∫ p : ℝ × ℝ, |K p * (⇑f) p.2 * (⇑g) p.1| ∂vol2 := abs_integral_le_integral_abs
    _ ≤ hsNorm K * ‖f‖ * ‖g‖ := kernel_CS hK f g

/-- Additivity of the pairing in `g`. -/
theorem kpair_add_g {K : ℝ × ℝ → ℝ} (hK : HSKernel K) (f g₁ g₂ : L2) :
    kpair K f (g₁ + g₂) = kpair K f g₁ + kpair K f g₂ := by
  have e1 : kpair K f (g₁ + g₂)
      = ∫ p : ℝ × ℝ, K p * (⇑f) p.2 * (⇑(g₁ + g₂)) p.1 ∂vol2 := rfl
  have e2 : kpair K f g₁ = ∫ p : ℝ × ℝ, K p * (⇑f) p.2 * (⇑g₁) p.1 ∂vol2 := rfl
  have e3 : kpair K f g₂ = ∫ p : ℝ × ℝ, K p * (⇑f) p.2 * (⇑g₂) p.1 ∂vol2 := rfl
  have hcongr : ∫ p : ℝ × ℝ, K p * (⇑f) p.2 * (⇑(g₁ + g₂)) p.1 ∂vol2
      = ∫ p : ℝ × ℝ, (K p * (⇑f) p.2 * (⇑g₁) p.1 + K p * (⇑f) p.2 * (⇑g₂) p.1) ∂vol2 := by
    refine integral_congr_ae ?_
    filter_upwards [eventual_fst (Lp.coeFn_add g₁ g₂)] with p hp
    rw [hp]; simp only [Pi.add_apply]; ring
  rw [e1, e2, e3, hcongr,
    integral_add (integrable_kintegrand hK f g₁) (integrable_kintegrand hK f g₂)]

/-- Homogeneity of the pairing in `g`. -/
theorem kpair_smul_g {K : ℝ × ℝ → ℝ} (hK : HSKernel K) (f : L2) (c : ℝ) (g : L2) :
    kpair K f (c • g) = c * kpair K f g := by
  have e1 : kpair K f (c • g) = ∫ p : ℝ × ℝ, K p * (⇑f) p.2 * (⇑(c • g)) p.1 ∂vol2 := rfl
  have e2 : kpair K f g = ∫ p : ℝ × ℝ, K p * (⇑f) p.2 * (⇑g) p.1 ∂vol2 := rfl
  have hcongr : ∫ p : ℝ × ℝ, K p * (⇑f) p.2 * (⇑(c • g)) p.1 ∂vol2
      = ∫ p : ℝ × ℝ, c * (K p * (⇑f) p.2 * (⇑g) p.1) ∂vol2 := by
    refine integral_congr_ae ?_
    filter_upwards [eventual_fst (Lp.coeFn_smul c g)] with p hp
    rw [hp]; simp only [Pi.smul_apply, smul_eq_mul]; ring
  rw [e1, e2, hcongr, integral_const_mul c (fun p : ℝ × ℝ => K p * (⇑f) p.2 * (⇑g) p.1)]

/-- Additivity of the pairing in `f`. -/
theorem kpair_add_f {K : ℝ × ℝ → ℝ} (hK : HSKernel K) (f₁ f₂ g : L2) :
    kpair K (f₁ + f₂) g = kpair K f₁ g + kpair K f₂ g := by
  have e1 : kpair K (f₁ + f₂) g = ∫ p : ℝ × ℝ, K p * (⇑(f₁ + f₂)) p.2 * (⇑g) p.1 ∂vol2 := rfl
  have e2 : kpair K f₁ g = ∫ p : ℝ × ℝ, K p * (⇑f₁) p.2 * (⇑g) p.1 ∂vol2 := rfl
  have e3 : kpair K f₂ g = ∫ p : ℝ × ℝ, K p * (⇑f₂) p.2 * (⇑g) p.1 ∂vol2 := rfl
  have hcongr : ∫ p : ℝ × ℝ, K p * (⇑(f₁ + f₂)) p.2 * (⇑g) p.1 ∂vol2
      = ∫ p : ℝ × ℝ, (K p * (⇑f₁) p.2 * (⇑g) p.1 + K p * (⇑f₂) p.2 * (⇑g) p.1) ∂vol2 := by
    refine integral_congr_ae ?_
    filter_upwards [eventual_snd (Lp.coeFn_add f₁ f₂)] with p hp
    rw [hp]; simp only [Pi.add_apply]; ring
  rw [e1, e2, e3, hcongr,
    integral_add (integrable_kintegrand hK f₁ g) (integrable_kintegrand hK f₂ g)]

/-- Homogeneity of the pairing in `f`. -/
theorem kpair_smul_f {K : ℝ × ℝ → ℝ} (hK : HSKernel K) (c : ℝ) (f g : L2) :
    kpair K (c • f) g = c * kpair K f g := by
  have e1 : kpair K (c • f) g = ∫ p : ℝ × ℝ, K p * (⇑(c • f)) p.2 * (⇑g) p.1 ∂vol2 := rfl
  have e2 : kpair K f g = ∫ p : ℝ × ℝ, K p * (⇑f) p.2 * (⇑g) p.1 ∂vol2 := rfl
  have hcongr : ∫ p : ℝ × ℝ, K p * (⇑(c • f)) p.2 * (⇑g) p.1 ∂vol2
      = ∫ p : ℝ × ℝ, c * (K p * (⇑f) p.2 * (⇑g) p.1) ∂vol2 := by
    refine integral_congr_ae ?_
    filter_upwards [eventual_snd (Lp.coeFn_smul c f)] with p hp
    rw [hp]; simp only [Pi.smul_apply, smul_eq_mul]; ring
  rw [e1, e2, hcongr, integral_const_mul c (fun p : ℝ × ℝ => K p * (⇑f) p.2 * (⇑g) p.1)]

/-! ### The kernel operator via Fréchet–Riesz -/

/-- The raw linear functional `g ↦ kpair K f g`. -/
def kpairLm (K : ℝ × ℝ → ℝ) (hK : HSKernel K) (f : L2) : L2 →ₗ[ℝ] ℝ where
  toFun g := kpair K f g
  map_add' := fun g₁ g₂ => kpair_add_g hK f g₁ g₂
  map_smul' := fun c g => by
    rw [RingHom.id_apply]
    exact kpair_smul_g hK f c g

/-- `TOpFun K hK f` is the Riesz representer of `g ↦ ∫∫ K(x,y) f y g x`. -/
def TOpFun (K : ℝ × ℝ → ℝ) (hK : HSKernel K) (f : L2) : L2 :=
  (InnerProductSpace.toDual ℝ L2).symm
    (LinearMap.mkContinuous (kpairLm K hK f) (hsNorm K * ‖f‖)
      (fun g => by simp only [Real.norm_eq_abs]; exact kpair_bound hK f g))

/-- **Master formula**: `⟪TOp K f, g⟫ = ∫∫ K(x,y) f(y) g(x)`. -/
theorem inner_TOpFun {K : ℝ × ℝ → ℝ} (hK : HSKernel K) (f g : L2) :
    inner ℝ (TOpFun K hK f) g = kpair K f g := by
  have hd : TOpFun K hK f = (InnerProductSpace.toDual ℝ L2).symm
      (LinearMap.mkContinuous (kpairLm K hK f) (hsNorm K * ‖f‖)
        (fun x => by simp only [Real.norm_eq_abs]; exact kpair_bound hK f x)) := rfl
  rw [hd, InnerProductSpace.toDual_symm_apply]
  simp only [LinearMap.mkContinuous_apply, kpairLm]
  rfl

theorem TOpFun_norm_le {K : ℝ × ℝ → ℝ} (hK : HSKernel K) (f : L2) :
    ‖TOpFun K hK f‖ ≤ hsNorm K * ‖f‖ := by
  unfold TOpFun
  rw [LinearIsometryEquiv.norm_map]
  exact LinearMap.mkContinuous_norm_le _ (mul_nonneg (hsNorm_nonneg K) (norm_nonneg f)) _

/-- Riesz uniqueness: equality of all pairings gives equality in `L2`. -/
theorem eq_of_forall_inner_eq {u v : L2} (h : ∀ g : L2, inner ℝ u g = inner ℝ v g) : u = v := by
  have hz : inner ℝ (u - v) (u - v) = 0 := by
    rw [inner_sub_left, h (u - v)]
    ring
  have h1 : ‖u - v‖ ^ 2 = 0 := by
    rw [← real_inner_self_eq_norm_sq]; exact hz
  have h2 : ‖u - v‖ = 0 := sq_eq_zero_iff.mp h1
  exact sub_eq_zero.mp (norm_eq_zero.mp h2)

theorem TOpFun_add {K : ℝ × ℝ → ℝ} (hK : HSKernel K) (f₁ f₂ : L2) :
    TOpFun K hK (f₁ + f₂) = TOpFun K hK f₁ + TOpFun K hK f₂ :=
  eq_of_forall_inner_eq fun g => by
    rw [inner_add_left, inner_TOpFun hK, inner_TOpFun hK, inner_TOpFun hK,
      kpair_add_f hK]

theorem TOpFun_smul {K : ℝ × ℝ → ℝ} (hK : HSKernel K) (c : ℝ) (f : L2) :
    TOpFun K hK (c • f) = c • TOpFun K hK f :=
  eq_of_forall_inner_eq fun g => by
    rw [real_inner_smul_left, inner_TOpFun hK, inner_TOpFun hK, kpair_smul_f hK c]

/-- The bundled Hilbert–Schmidt integral operator `TOp K : L² → L²`. -/
def TOp (K : ℝ × ℝ → ℝ) (hK : HSKernel K) : L2 →L[ℝ] L2 :=
  LinearMap.mkContinuous
    { toFun := TOpFun K hK
      map_add' := TOpFun_add hK
      map_smul' := TOpFun_smul hK }
    (hsNorm K) (fun f => TOpFun_norm_le hK f)

theorem TOp_apply {K : ℝ × ℝ → ℝ} (hK : HSKernel K) (f : L2) :
    TOp K hK f = TOpFun K hK f := rfl

theorem inner_TOp {K : ℝ × ℝ → ℝ} (hK : HSKernel K) (f g : L2) :
    inner ℝ (TOp K hK f) g = kpair K f g := by
  rw [TOp_apply]; exact inner_TOpFun hK f g

theorem TOp_le {K : ℝ × ℝ → ℝ} (hK : HSKernel K) (f : L2) :
    ‖TOp K hK f‖ ≤ hsNorm K * ‖f‖ := TOpFun_norm_le hK f

theorem TOp_norm_le {K : ℝ × ℝ → ℝ} (hK : HSKernel K) : ‖TOp K hK‖ ≤ hsNorm K :=
  LinearMap.mkContinuous_norm_le _ (hsNorm_nonneg K) _

/-! ### Linearity of `TOp` in the kernel -/

theorem kpair_add_kernel {K₁ K₂ : ℝ × ℝ → ℝ} (hK₁ : HSKernel K₁) (hK₂ : HSKernel K₂)
    (f g : L2) : kpair (K₁ + K₂) f g = kpair K₁ f g + kpair K₂ f g := by
  have e1 : kpair (K₁ + K₂) f g = ∫ p : ℝ × ℝ, (K₁ + K₂) p * (⇑f) p.2 * (⇑g) p.1 ∂vol2 := rfl
  have e2 : kpair K₁ f g = ∫ p : ℝ × ℝ, K₁ p * (⇑f) p.2 * (⇑g) p.1 ∂vol2 := rfl
  have e3 : kpair K₂ f g = ∫ p : ℝ × ℝ, K₂ p * (⇑f) p.2 * (⇑g) p.1 ∂vol2 := rfl
  have hcongr : ∫ p : ℝ × ℝ, (K₁ + K₂) p * (⇑f) p.2 * (⇑g) p.1 ∂vol2
      = ∫ p : ℝ × ℝ, (K₁ p * (⇑f) p.2 * (⇑g) p.1 + K₂ p * (⇑f) p.2 * (⇑g) p.1) ∂vol2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [Pi.add_apply]; ring
  rw [e1, e2, e3, hcongr,
    integral_add (integrable_kintegrand hK₁ f g) (integrable_kintegrand hK₂ f g)]

theorem TOp_add {K₁ K₂ : ℝ × ℝ → ℝ} (hK₁ : HSKernel K₁) (hK₂ : HSKernel K₂) :
    TOp (K₁ + K₂) (MemLp.add hK₁ hK₂) = TOp K₁ hK₁ + TOp K₂ hK₂ := by
  refine ContinuousLinearMap.ext fun f => eq_of_forall_inner_eq fun g => ?_
  rw [inner_TOp (MemLp.add hK₁ hK₂), kpair_add_kernel hK₁ hK₂,
    ContinuousLinearMap.add_apply, inner_add_left, inner_TOp hK₁, inner_TOp hK₂]

theorem kpair_smul_kernel (c : ℝ) {K : ℝ × ℝ → ℝ} (hK : HSKernel K) (f g : L2) :
    kpair (c • K) f g = c * kpair K f g := by
  have e1 : kpair (c • K) f g = ∫ p : ℝ × ℝ, (c • K) p * (⇑f) p.2 * (⇑g) p.1 ∂vol2 := rfl
  have e2 : kpair K f g = ∫ p : ℝ × ℝ, K p * (⇑f) p.2 * (⇑g) p.1 ∂vol2 := rfl
  have hcongr : ∫ p : ℝ × ℝ, (c • K) p * (⇑f) p.2 * (⇑g) p.1 ∂vol2
      = ∫ p : ℝ × ℝ, c * (K p * (⇑f) p.2 * (⇑g) p.1) ∂vol2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [Pi.smul_apply, smul_eq_mul]; ring
  rw [e1, e2, hcongr, integral_const_mul c (fun p : ℝ × ℝ => K p * (⇑f) p.2 * (⇑g) p.1)]

theorem TOp_smul (c : ℝ) {K : ℝ × ℝ → ℝ} (hK : HSKernel K) :
    TOp (c • K) (MemLp.const_smul hK c) = c • TOp K hK := by
  refine ContinuousLinearMap.ext fun f => eq_of_forall_inner_eq fun g => ?_
  rw [inner_TOp (MemLp.const_smul hK c), kpair_smul_kernel c hK f g,
    ContinuousLinearMap.smul_apply, real_inner_smul_left, inner_TOp hK]

/-! ### Transpose kernels and the adjoint -/

/-- Kernel transpose `Kᵀ(x, y) = K(y, x)`. -/
def ktranspose (K : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ := fun p => K p.swap

theorem hsKernel_transpose {K : ℝ × ℝ → ℝ} (hK : HSKernel K) : HSKernel (ktranspose K) := by
  refine ⟨hK.1.prod_swap, ?_⟩
  have h := eLpNorm_comp_measurePreserving (p := 2) (μ := vol2) (ν := vol2) hK.1
    (measurePreserving_swap (μ := vol) (ν := vol))
  rw [show ktranspose K = K ∘ Prod.swap from rfl, h]
  exact hK.2

theorem hsNorm_transpose {K : ℝ × ℝ → ℝ} (hK : HSKernel K) :
    hsNorm (ktranspose K) = hsNorm K := by
  have h1 : ∫ p : ℝ × ℝ, ktranspose K p ^ 2 ∂vol2
      = ∫ p : ℝ × ℝ, (fun q : ℝ × ℝ => K q ^ 2) p.swap ∂vol2 := rfl
  have key : ∫ p : ℝ × ℝ, (fun q : ℝ × ℝ => K q ^ 2) p.swap ∂vol2
      = ∫ p : ℝ × ℝ, K p ^ 2 ∂vol2 :=
    integral_prod_swap (fun q : ℝ × ℝ => K q ^ 2)
  rw [hsNorm, hsNorm, h1, key]

theorem kpair_transpose {K : ℝ × ℝ → ℝ} (hK : HSKernel K) (f g : L2) :
    kpair (ktranspose K) g f = kpair K f g := by
  show ∫ p : ℝ × ℝ, ktranspose K p * (⇑g) p.2 * (⇑f) p.1 ∂vol2
      = ∫ p : ℝ × ℝ, K p * (⇑f) p.2 * (⇑g) p.1 ∂vol2
  rw [← integral_prod_swap (fun q : ℝ × ℝ => K q * (⇑f) q.2 * (⇑g) q.1)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [ktranspose, Prod.swap]
  ring

/-- **Adjointness**: the adjoint of `TOp K` is `TOp Kᵀ`. -/
theorem TOp_adjoint {K : ℝ × ℝ → ℝ} (hK : HSKernel K) :
    (TOp K hK).adjoint = TOp (ktranspose K) (hsKernel_transpose hK) := by
  refine ContinuousLinearMap.ext fun g => eq_of_forall_inner_eq fun f => ?_
  rw [real_inner_comm, ContinuousLinearMap.adjoint_inner_right, inner_TOp hK,
    inner_TOp (hsKernel_transpose hK), kpair_transpose hK]

/-- Congruence of `TOp` for pointwise-equal kernels. -/
theorem TOp_congr {K L : ℝ × ℝ → ℝ} (hKL : ∀ p : ℝ × ℝ, K p = L p)
    (hK : HSKernel K) (hL : HSKernel L) : TOp K hK = TOp L hL := by
  refine ContinuousLinearMap.ext fun f => eq_of_forall_inner_eq fun g => ?_
  have e1 : kpair K f g = ∫ p : ℝ × ℝ, K p * (⇑f) p.2 * (⇑g) p.1 ∂vol2 := rfl
  have e2 : kpair L f g = ∫ p : ℝ × ℝ, L p * (⇑f) p.2 * (⇑g) p.1 ∂vol2 := rfl
  rw [inner_TOp hK, e1, inner_TOp hL, e2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  show K p * (⇑f) p.2 * (⇑g) p.1 = L p * (⇑f) p.2 * (⇑g) p.1
  rw [hKL p]

/-- Self-adjointness of `TOp K` for a symmetric kernel. -/
theorem TOp_selfAdjoint {K : ℝ × ℝ → ℝ} (hK : HSKernel K)
    (hsym : ∀ p : ℝ × ℝ, K p = K p.swap) :
    (TOp K hK).adjoint = TOp K hK :=
  (TOp_adjoint hK).trans (TOp_congr (fun p => by simp only [ktranspose]; exact hsym p.swap)
    (hsKernel_transpose hK) hK)

/-! ### The k = 2 cycle pairing -/

/-- Two-point cycle integral `Φ₂(K, L) = ∫∫ K(x,y) L(y,x) dxdy`. -/
def cycle2 (K L : ℝ × ℝ → ℝ) : ℝ := ∫ p : ℝ × ℝ, K p * L p.swap ∂vol2

/-- `|∫∫ K(x,y) L(y,x)| ≤ ‖K‖_{L²} ‖L‖_{L²}` — the k = 2 case of the cycle bound (A2). -/
theorem cycle2_bound {K L : ℝ × ℝ → ℝ} (hK : HSKernel K) (hL : HSKernel L) :
    |cycle2 K L| ≤ hsNorm K * hsNorm L := by
  have e1 : cycle2 K L = ∫ p : ℝ × ℝ, K p * L p.swap ∂vol2 := rfl
  have hL' : HSKernel (ktranspose L) := hsKernel_transpose hL
  have hcongr : ∫ p : ℝ × ℝ, |K p * L p.swap| ∂vol2
      = ∫ p : ℝ × ℝ, |K p| * |ktranspose L p| ∂vol2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [Real.norm_eq_abs, abs_mul, ktranspose]
  have hK' : MemLp K (ENNReal.ofReal 2) vol2 := by rw [real_two_ofReal]; exact hK
  have hLt : MemLp (ktranspose L) (ENNReal.ofReal 2) vol2 := by
    rw [real_two_ofReal]; exact hL'
  have hcs := integral_mul_norm_le_Lp_mul_Lq holderTriple221 hK' hLt
  simp only [Real.norm_eq_abs] at hcs
  rw [integral_pow_two (fun p => |K p|),
    integral_pow_two (fun p => |ktranspose L p|)] at hcs
  have hKabs : (∫ p : ℝ × ℝ, |K p| ^ 2 ∂vol2) ^ ((1 : ℝ) / 2) = hsNorm K := by
    rw [← Real.sqrt_eq_rpow, hsNorm_def]
    refine congrArg Real.sqrt ?_
    exact integral_congr_ae (Filter.Eventually.of_forall fun p => by simp [sq_abs])
  have hLabs : (∫ p : ℝ × ℝ, |ktranspose L p| ^ 2 ∂vol2) ^ ((1 : ℝ) / 2) = hsNorm L := by
    rw [← Real.sqrt_eq_rpow, hsNorm_def]
    refine congrArg Real.sqrt ?_
    have hpt : ∀ p : ℝ × ℝ, |ktranspose L p| ^ 2 = ktranspose L p ^ 2 := by
      intro p; simp only [sq_abs]
    have hswap : ∫ p : ℝ × ℝ, |ktranspose L p| ^ 2 ∂vol2
        = ∫ p : ℝ × ℝ, L p ^ 2 ∂vol2 := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
        ← integral_prod_swap (fun q : ℝ × ℝ => L q ^ 2)]
      exact integral_congr_ae (Filter.Eventually.of_forall fun p => rfl)
    rw [hswap]
  calc |cycle2 K L|
      = |∫ p : ℝ × ℝ, K p * L p.swap ∂vol2| := by rw [e1]
    _ ≤ ∫ p : ℝ × ℝ, |K p * L p.swap| ∂vol2 := abs_integral_le_integral_abs
    _ = ∫ p : ℝ × ℝ, |K p| * |ktranspose L p| ∂vol2 := hcongr
    _ ≤ hsNorm K * hsNorm L := by rw [hKabs, hLabs] at hcs; exact hcs

/-- Symmetry of the k = 2 cycle pairing. -/
theorem cycle2_symm (K L : ℝ × ℝ → ℝ) : cycle2 K L = cycle2 L K := by
  have e1 : cycle2 K L = ∫ p : ℝ × ℝ, K p * L p.swap ∂vol2 := rfl
  have e2 : cycle2 L K = ∫ p : ℝ × ℝ, L p * K p.swap ∂vol2 := rfl
  have hpt : ∫ p : ℝ × ℝ, K p * L p.swap ∂vol2
      = ∫ p : ℝ × ℝ, (fun q : ℝ × ℝ => L q * K q.swap) p.swap ∂vol2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [Prod.swap_swap]
    ring
  rw [e1, hpt, integral_prod_swap (fun q : ℝ × ℝ => L q * K q.swap), e2]

end HS
