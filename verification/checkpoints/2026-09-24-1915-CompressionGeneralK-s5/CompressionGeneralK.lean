import Mathlib
import Hurst.CompressionIdentity
import Hurst.TracePairCycle
import Hurst.HSCycleComposition
import Hurst.GeneralKPeelInduction
import Hurst.HSOperatorLayer3

/-!
# The compression identity, general `k ≥ 2` (under construction, section by section)

Target: `diagSum_Bop_eq_weightedCycle` — for every `k ≥ 2` and Hilbert basis `e`,
`∑' i, ⟪((S ∘ M_omega ∘ S) ^ k) (e i), e i⟫ = weightedRieszCycleIntegral k psi c omega`
— together with `exists_weightedRieszSpectrum_min` and its instantiation at
`omega := Hurst.equivalentKernel r` (spec §5 of
`milestone1_hconst_elimination_math_spec.md`, A8–A9 compressed route).

## Route (spectral truncations; no `hconst`-type premise)

Fix a complete nonnegative eigenfamily `(v, κ)` of the *unweighted* Riesz
operator `T`, an injection `f : ι → ℕ` (`countable_of_orthonormal` line), the
level truncations `s N = f ⁻¹ (range N)` and the finite-rank spectral operators
`S N := specOperator (√κ · χ_{s N})` and `T N := specOperator (κ · χ_{s N})`:

1. `mulOperator_comp_TOp_gen` — `TOp (fun p => omega p.1 * K p) = M_omega ∘ TOp K`
   for every HS kernel `K` (a.e.-congruence transport, no Fubini).
2. The truncated tensor kernel `KN N := ∑_{i ∈ s N} κ i • (g i ⊗ g i)` (built
   from measurable representatives `g i` of `v i`) realizes `T N`:
   `TOp (KN N) = T N`, hence `W ∘ T N = TOp (omega • KN N)` with a measurable
   truncated weighted kernel, and `hsNorm (K − KN N) ^ 2 = ∑'_{i ∉ s N} κ i ^ 2 → 0`
   (tensor-ONB Parseval + `tendsto_tsum_compl_atTop_zero`).
3. Finite-rank cyclicity (`tracePair_cyclic`): with `B N := S N ∘ W ∘ S N`,
   `Diag_k((B N)^k) = Diag_k((W ∘ T N)^k)` — the power regrouping plus the
   cyclic move of the *finite-rank* `S N` (the non-HS `S` never moves).
4. Kernel-side limit: `cycle2`-Lipschitz comparison of the kernel towers
   (`hsNorm_comp_le` + the tower Lipschitz), against the landed
   `Diag_k((TOp (rieszKernel))^k) = weightedRieszCycleIntegral k`.
5. B-side limit: the landed A4 `diag_pow_sub_diag_pow_le` between `B` and `B N`,
   with `‖B − B N‖ → 0` (level-set finiteness of the κ-tail) and the
   diagonal-ℓ² content of `B − B N` equal to the A7 matrix tail
   (`matrixSq_sum_eq_of_complete`) — both tending to `0`.
-/

open MeasureTheory Measure Real Set Submodule
open scoped Real

noncomputable section

namespace HS

/-! ### Section 1a: a.e.-transport of kernel data -/

/-- `HSKernel` transports across a.e.-equal kernels. -/
theorem hSKernel_congr_ae {K K' : ℝ × ℝ → ℝ} (hK : HSKernel K) (h : K =ᵐ[vol2] K') :
    HSKernel K' :=
  MemLp.ae_eq h hK

/-- The kernel operator only sees the a.e.-class of its kernel. -/
theorem TOp_congr_ae {K K' : ℝ × ℝ → ℝ} (hK : HSKernel K) (hK' : HSKernel K')
    (h : K =ᵐ[vol2] K') : TOp K hK = TOp K' hK' := by
  refine ContinuousLinearMap.ext fun x => eq_of_forall_inner_eq fun g => ?_
  rw [inner_TOp hK x g, inner_TOp hK' x g]
  exact integral_congr_ae (h.mono fun p hp => by dsimp only; rw [hp])

/-- The hsNorm only sees the a.e.-class. -/
theorem hsNorm_congr_ae {K K' : ℝ × ℝ → ℝ} (h : K =ᵐ[vol2] K') :
    hsNorm K = hsNorm K' := by
  refine congrArg (fun t => t ^ ((1 : ℝ) / 2)) ?_
  exact integral_congr_ae (h.mono fun p hp => by dsimp only; rw [hp])

/-- Pointwise domination bounds the hsNorm. -/
theorem hsNorm_le_of_abs_le {K D : ℝ × ℝ → ℝ} (hD : HSKernel D)
    (h : ∀ p, |K p| ≤ D p) : hsNorm K ≤ hsNorm D := by
  rw [hsNorm_def K, hsNorm_def D]
  refine Real.sqrt_le_sqrt ?_
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun p => sq_nonneg _)
    (MemLp.integrable_sq hD) ?_
  exact Filter.Eventually.of_forall fun p =>
    sq_le_sq.mpr (le_trans (h p) (le_abs_self (D p)))

/-! ### Section 1b: the general left-multiplication identity -/

/-- The pointwise-weighted kernel is HS when the weight is bounded
(domination by `MR • K`). -/
theorem hSKernel_weight_mul {K : ℝ × ℝ → ℝ} (hK : HSKernel K) {omega : ℝ → ℝ}
    (hm : Measurable omega) {MR : ℝ} (hbdd : ∀ x : ℝ, |omega x| ≤ MR) :
    HSKernel (fun p => omega p.1 * K p) := by
  have hMR : (0 : ℝ) ≤ MR := le_trans (abs_nonneg (omega 0)) (hbdd 0)
  have hMF : MemLp (fun p => MR * K p) 2 vol2 := MemLp.const_mul hK MR
  refine ⟨((hm.comp measurable_fst).aestronglyMeasurable (μ := vol2)).mul hK.1,
    lt_of_le_of_lt (eLpNorm_mono_ae ?_) hMF.2⟩
  filter_upwards with p
  show ‖omega p.1 * K p‖ ≤ ‖MR * K p‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hMR]
  exact mul_le_mul_of_nonneg_right (hbdd p.1) (abs_nonneg (K p))

/-- **Left multiplication by the weight is the kernel operation** — general
kernel form: `TOp (fun p => omega p.1 * K p) = M_omega ∘ TOp K` for every HS
kernel `K` (the `k = 2` file's `mulOperator_comp_TOp_riesz`, abstracted; the
proof is the same a.e.-congruence chain, with the weight moved to the test side
by self-adjointness — no Fubini). -/
theorem mulOperator_comp_TOp_gen {K : ℝ × ℝ → ℝ} (hK : HSKernel K)
    {omega : ℝ → ℝ} (hm : Measurable omega) {MR : ℝ}
    (hess : ∀ᵐ x ∂vol, |omega x| ≤ MR) (hbdd : ∀ x : ℝ, |omega x| ≤ MR) :
    TOp (fun p => omega p.1 * K p) (hSKernel_weight_mul hK hm hbdd)
      = (mulOperator omega hm hess).comp (TOp K hK) := by
  have hW : HSKernel (fun p => omega p.1 * K p) := hSKernel_weight_mul hK hm hbdd
  refine ContinuousLinearMap.ext fun f => eq_of_forall_inner_eq fun g => ?_
  calc inner ℝ (TOp (fun p => omega p.1 * K p) hW f) g
      = kpair (fun p => omega p.1 * K p) f g := inner_TOp hW f g
    _ = ∫ p : ℝ × ℝ, K p * (⇑f) p.2 * (omega p.1 * (⇑g) p.1) ∂vol2 := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
          show omega p.1 * K p * (⇑f) p.2 * (⇑g) p.1
              = K p * (⇑f) p.2 * (omega p.1 * (⇑g) p.1)
          ring
    _ = ∫ p : ℝ × ℝ, K p * (⇑f) p.2 * (⇑(mulOperator omega hm hess g)) p.1 ∂vol2 := by
          refine integral_congr_ae ?_
          filter_upwards [eventual_fst (coeFn_mulOperator_action omega hm hess g)]
            with p hp
          show K p * (⇑f) p.2 * (omega p.1 * (⇑g) p.1)
              = K p * (⇑f) p.2 * (⇑(mulOperator omega hm hess g)) p.1
          rw [hp]
    _ = kpair K f (mulOperator omega hm hess g) := rfl
    _ = inner ℝ (TOp K hK f) (mulOperator omega hm hess g) := (inner_TOp hK f _).symm
    _ = inner ℝ (mulOperator omega hm hess (TOp K hK f)) g :=
        (mulOperator_symm omega hm hess (TOp K hK f) g).symm
    _ = inner ℝ ((mulOperator omega hm hess).comp (TOp K hK) f) g := rfl

/-! ### Section 1c: hsNorm helpers and the tower Lipschitz -/

/-- Crude hsNorm subadditivity (the constant `2` is harmless for limit purposes). -/
theorem hsNorm_add_le2 {F G : ℝ × ℝ → ℝ} (hF : HSKernel F) (hG : HSKernel G) :
    hsNorm (F + G) ≤ 2 * (hsNorm F + hsNorm G) := by
  have hintF : Integrable (fun p : ℝ × ℝ => F p ^ 2) vol2 := MemLp.integrable_sq hF
  have hintG : Integrable (fun p : ℝ × ℝ => G p ^ 2) vol2 := MemLp.integrable_sq hG
  have hint2 : Integrable (fun p : ℝ × ℝ => 2 * (F p ^ 2 + G p ^ 2)) vol2 :=
    (hintF.add hintG).const_mul 2
  have hpt : ∀ p : ℝ × ℝ, (F p + G p) ^ 2 ≤ 2 * (F p ^ 2 + G p ^ 2) := fun p => by
    nlinarith [sq_nonneg (F p - G p), sq_nonneg (F p), sq_nonneg (G p)]
  have hsplit : ∫ p : ℝ × ℝ, 2 * (F p ^ 2 + G p ^ 2) ∂vol2
      = 2 * (∫ p : ℝ × ℝ, F p ^ 2 ∂vol2 + ∫ p : ℝ × ℝ, G p ^ 2 ∂vol2) := by
    rw [integral_const_mul 2 (fun p : ℝ × ℝ => F p ^ 2 + G p ^ 2),
      integral_add hintF hintG]
  have hmono : ∫ p : ℝ × ℝ, (F + G) p ^ 2 ∂vol2
      ≤ 2 * (∫ p : ℝ × ℝ, F p ^ 2 ∂vol2 + ∫ p : ℝ × ℝ, G p ^ 2 ∂vol2) := by
    rw [← hsplit]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun p => sq_nonneg _)
      hint2 ?_
    exact Filter.Eventually.of_forall fun p => by
      show (F p + G p) ^ 2 ≤ 2 * (F p ^ 2 + G p ^ 2)
      exact hpt p
  have hF0 : (0 : ℝ) ≤ hsNorm F := hsNorm_nonneg F
  have hG0 : (0 : ℝ) ≤ hsNorm G := hsNorm_nonneg G
  have hFA : (0 : ℝ) ≤ Real.sqrt (∫ p : ℝ × ℝ, F p ^ 2 ∂vol2) :=
    Real.sqrt_nonneg _
  have hGA : (0 : ℝ) ≤ Real.sqrt (∫ p : ℝ × ℝ, G p ^ 2 ∂vol2) :=
    Real.sqrt_nonneg _
  calc hsNorm (F + G) = Real.sqrt (∫ p : ℝ × ℝ, (F + G) p ^ 2 ∂vol2) := hsNorm_def _
    _ ≤ Real.sqrt (2 * (∫ p : ℝ × ℝ, F p ^ 2 ∂vol2 + ∫ p : ℝ × ℝ, G p ^ 2 ∂vol2)) :=
        Real.sqrt_le_sqrt hmono
    _ ≤ 2 * (Real.sqrt (∫ p : ℝ × ℝ, F p ^ 2 ∂vol2)
          + Real.sqrt (∫ p : ℝ × ℝ, G p ^ 2 ∂vol2)) := by
        have hR : (2 : ℝ) * (Real.sqrt (∫ p : ℝ × ℝ, F p ^ 2 ∂vol2)
              + Real.sqrt (∫ p : ℝ × ℝ, G p ^ 2 ∂vol2))
            = Real.sqrt (((2 : ℝ) * (Real.sqrt (∫ p : ℝ × ℝ, F p ^ 2 ∂vol2)
              + Real.sqrt (∫ p : ℝ × ℝ, G p ^ 2 ∂vol2))) ^ 2) :=
          (Real.sqrt_sq (by positivity)).symm
        rw [hR]
        have hFa : (Real.sqrt (∫ p : ℝ × ℝ, F p ^ 2 ∂vol2)) ^ 2
            = ∫ p : ℝ × ℝ, F p ^ 2 ∂vol2 :=
          Real.sq_sqrt (integral_nonneg (fun p : ℝ × ℝ => sq_nonneg (F p)))
        have hGa : (Real.sqrt (∫ p : ℝ × ℝ, G p ^ 2 ∂vol2)) ^ 2
            = ∫ p : ℝ × ℝ, G p ^ 2 ∂vol2 :=
          Real.sq_sqrt (integral_nonneg (fun p : ℝ × ℝ => sq_nonneg (G p)))
        refine Real.sqrt_le_sqrt ?_
        nlinarith [sq_nonneg (Real.sqrt (∫ p : ℝ × ℝ, F p ^ 2 ∂vol2)
            + Real.sqrt (∫ p : ℝ × ℝ, G p ^ 2 ∂vol2)),
          mul_nonneg hFA hGA, hFa, hGa]
    _ ≤ 2 * (hsNorm F + hsNorm G) := by
        rw [hsNorm_def F, hsNorm_def G]

/-- A.e. integrability of the mixed section products of two HS kernels
(the per-point ingredient for the sub-linearity of `compKernel`). -/
theorem integrable_section_prod_ae {A B : ℝ × ℝ → ℝ} (hAm : Measurable A) (hBm : Measurable B)
    (hA : HSKernel A) (hB : HSKernel B) :
    ∀ᵐ p : ℝ × ℝ ∂vol2, Integrable (fun t => A (p.1, t) * B (t, p.2)) vol := by
  classical
  have hliftA : ∀ᵐ p : ℝ × ℝ ∂vol2, MemLp (fun t => A (p.1, t)) 2 vol := by
    have hind : ∀ᵐ x ∂vol,
        (if Integrable (fun t => A (x, t) ^ 2) vol then (1 : ℝ) else 0) = (1 : ℝ) := by
      filter_upwards [ae_section_integrable_fst hAm hA] with x hx
      rw [if_pos hx]
    filter_upwards [eventual_fst hind] with p hp
    by_cases hc : Integrable (fun t => A (p.1, t) ^ 2) vol
    · exact memLp_two_of_aemeasurable
        ((hAm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable) hc
    · rw [if_neg hc] at hp
      exact absurd hp (by norm_num)
  have hliftB : ∀ᵐ p : ℝ × ℝ ∂vol2, MemLp (fun t => B (t, p.2)) 2 vol := by
    have hind : ∀ᵐ y ∂vol,
        (if Integrable (fun t => B (t, y) ^ 2) vol then (1 : ℝ) else 0) = (1 : ℝ) := by
      filter_upwards [ae_section_integrable_snd hBm hB] with y hy
      rw [if_pos hy]
    filter_upwards [eventual_snd hind] with p hp
    by_cases hc : Integrable (fun t => B (t, p.2) ^ 2) vol
    · exact memLp_two_of_aemeasurable
        ((hBm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable) hc
    · rw [if_neg hc] at hp
      exact absurd hp (by norm_num)
  filter_upwards [hliftA, hliftB] with p hAp hBp
  haveI hpqr : Real.HolderTriple 2 2 1 := holderTriple221
  exact memLp_one_iff_integrable.mp (MemLp.mul' hBp hAp)

/-- **Sub-linearity of `compKernel`** (a.e.): the difference of two composed kernels
splits along either factor. -/
theorem compKernel_sub_ae {X X' C C' : ℝ × ℝ → ℝ}
    (hXm : Measurable X) (hX'm : Measurable X') (hCm : Measurable C) (hC'm : Measurable C')
    (hX : HSKernel X) (hX' : HSKernel X') (hC : HSKernel C) (hC' : HSKernel C') :
    (compKernel X C - compKernel X' C') =ᵐ[vol2]
      (compKernel (X - X') C + compKernel X' (C - C')) := by
  filter_upwards [integrable_section_prod_ae hXm hCm hX hC,
    integrable_section_prod_ae hX'm hC'm hX' hC',
    integrable_section_prod_ae hX'm hCm hX' hC,
    integrable_section_prod_ae hXm hC'm hX hC'] with p h1 h2 h3 h4
  show (∫ t : ℝ, X (p.1, t) * C (t, p.2) ∂vol - ∫ t : ℝ, X' (p.1, t) * C' (t, p.2) ∂vol)
      = (∫ t : ℝ, (X - X') (p.1, t) * C (t, p.2) ∂vol
          + ∫ t : ℝ, X' (p.1, t) * (C - C') (t, p.2) ∂vol)
  have h5 : Integrable (fun t => (X - X') (p.1, t) * C (t, p.2)) vol := by
    refine (h1.sub h3).congr (Filter.Eventually.of_forall fun t => ?_)
    show X (p.1, t) * C (t, p.2) - X' (p.1, t) * C (t, p.2)
        = (X - X') (p.1, t) * C (t, p.2)
    simp only [Pi.sub_apply]
    ring
  have h6 : Integrable (fun t => X' (p.1, t) * (C - C') (t, p.2)) vol := by
    refine (h3.sub h2).congr (Filter.Eventually.of_forall fun t => ?_)
    show X' (p.1, t) * C (t, p.2) - X' (p.1, t) * C' (t, p.2)
        = X' (p.1, t) * (C - C') (t, p.2)
    simp only [Pi.sub_apply]
    ring
  calc ∫ t : ℝ, X (p.1, t) * C (t, p.2) ∂vol - ∫ t : ℝ, X' (p.1, t) * C' (t, p.2) ∂vol
      = ∫ t : ℝ, X (p.1, t) * C (t, p.2) - X' (p.1, t) * C' (t, p.2) ∂vol :=
        (integral_sub h1 h2).symm
    _ = ∫ t : ℝ, (X - X') (p.1, t) * C (t, p.2) + X' (p.1, t) * (C - C') (t, p.2) ∂vol := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        show X (p.1, t) * C (t, p.2) - X' (p.1, t) * C' (t, p.2)
            = (X - X') (p.1, t) * C (t, p.2) + X' (p.1, t) * (C - C') (t, p.2)
        simp only [Pi.sub_apply]
        ring
    _ = (∫ t : ℝ, (X - X') (p.1, t) * C (t, p.2) ∂vol
          + ∫ t : ℝ, X' (p.1, t) * (C - C') (t, p.2) ∂vol) :=
        integral_add h5 h6

/-- **Tower Lipschitz**: the composition tower is Lipschitz in the base kernel
(the base norm bound enters through the landed `hsNorm_compPowR_le`). -/
theorem hsNorm_compPowR_sub_le {C C' : ℝ × ℝ → ℝ} (hCm : Measurable C) (hC'm : Measurable C')
    (hC : HSKernel C) (hC' : HSKernel C') {M δ : ℝ}
    (hCM : hsNorm C ≤ M) (hC'M : hsNorm C' ≤ M) (hδ : hsNorm (C - C') ≤ δ) (r : ℕ) :
    hsNorm (compPowR r C - compPowR r C') ≤ 2 ^ (r + 1) * ((r : ℝ) + 1) * M ^ r * δ := by
  have hM0 : (0 : ℝ) ≤ M := le_trans (hsNorm_nonneg C) hCM
  have hδ0 : (0 : ℝ) ≤ δ := le_trans (hsNorm_nonneg _) hδ
  induction r with
  | zero =>
      rw [compPowR, compPowR]
      refine le_trans hδ ?_
      norm_num
      linarith
  | succ m ih =>
      rw [compPowR, compPowR]
      set X := compPowR m C with hXdef
      set X' := compPowR m C' with hX'def
      have hXm : Measurable X := measurable_compPowR m hCm
      have hX'm : Measurable X' := measurable_compPowR m hC'm
      have hX : HSKernel X := hsKernel_compPowR m hCm hC
      have hX' : HSKernel X' := hsKernel_compPowR m hC'm hC'
      have hdiffm : Measurable (X - X') := hXm.sub hX'm
      have hcdiffm : Measurable (C - C') := hCm.sub hC'm
      have hdiff : HSKernel (X - X') := hX.sub hX'
      have hcdiff : HSKernel (C - C') := hC.sub hC'
      have hae := compKernel_sub_ae hXm hX'm hCm hC'm hX hX' hC hC'
      rw [hsNorm_congr_ae hae]
      have hstep2 : hsNorm (compKernel (X - X') C + compKernel X' (C - C'))
          ≤ 2 * (hsNorm (X - X') * hsNorm C + hsNorm X' * hsNorm (C - C')) := by
        refine le_trans (hsNorm_add_le2
          (peelHsKernel_comp hdiffm hCm hdiff hC)
          (peelHsKernel_comp hX'm hcdiffm hX' hcdiff)) ?_
        refine mul_le_mul_of_nonneg_left
          (add_le_add (hsNorm_comp_le hdiffm hCm hdiff hC)
            (hsNorm_comp_le hX'm hcdiffm hX' hcdiff)) (by norm_num)
      refine le_trans hstep2 ?_
      have hB'0 : (0 : ℝ) ≤ 2 ^ (m + 1) * ((m : ℝ) + 1) * M ^ m * δ :=
        mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity))
          (pow_nonneg hM0 _)) hδ0
      have h3 : hsNorm (X - X') * hsNorm C
          ≤ 2 ^ (m + 1) * ((m : ℝ) + 1) * M ^ m * δ * M := by
        refine le_trans (mul_le_mul_of_nonneg_right ih (hsNorm_nonneg C)) ?_
        exact mul_le_mul_of_nonneg_left hCM hB'0
      have hX'M : hsNorm X' ≤ M ^ (m + 1) :=
        le_trans (hsNorm_compPowR_le m hC'm hC')
          (pow_le_pow_left₀ (hsNorm_nonneg C') hC'M (m + 1))
      have h4 : hsNorm X' * hsNorm (C - C') ≤ M ^ (m + 1) * δ := by
        refine le_trans (mul_le_mul_of_nonneg_right hX'M (hsNorm_nonneg _)) ?_
        exact mul_le_mul_of_nonneg_left hδ (pow_nonneg hM0 _)
      refine le_trans (mul_le_mul_of_nonneg_left (add_le_add h3 h4) (by norm_num)) ?_
      have hstepEq : 2 ^ (m + 1) * (((m : ℝ) + 1)) * M ^ m * δ * M
          = 2 ^ (m + 1) * (((m : ℝ) + 1)) * M ^ (m + 1) * δ := by
        rw [show M ^ (m + 1) = M ^ m * M from by rw [pow_succ] <;> ring] <;> ring
      rw [hstepEq]
      have hcast : (((m + 1 : ℕ) : ℝ) + 1) = ((m : ℝ) + 1) + 1 := by
        push_cast
        ring
      rw [hcast]
      have h2x : 2 ^ (m + 1 + 1) = (2 : ℝ) * 2 ^ (m + 1) := by rw [pow_succ] <;> ring
      rw [h2x]
      have hw0 : (0 : ℝ) ≤ 2 ^ (m + 1) := by positivity
      have hq0 : (0 : ℝ) ≤ ((m : ℝ) + 1) := by positivity
      have hz0 : (0 : ℝ) ≤ M ^ (m + 1) * δ := mul_nonneg (pow_nonneg hM0 _) hδ0
      have hwz0 : (0 : ℝ) ≤ 2 ^ (m + 1) * (((m : ℝ) + 1) + 1) * M ^ (m + 1) * δ :=
        mul_nonneg (mul_nonneg (mul_nonneg hw0 (add_nonneg hq0 zero_le_one))
          (pow_nonneg hM0 _)) hδ0
      have hgen : ∀ n : ℕ, (1 : ℝ) ≤ 2 ^ n := by
        intro n
        induction n with
        | zero => norm_num
        | succ k ih =>
            rw [pow_succ]
            nlinarith [ih]
      have hA1 : (1 : ℝ) ≤ 2 ^ (m + 1) := hgen (m + 1)
      nlinarith [hA1, hw0, hq0, hz0]

/-! ### Section 2a: finite-support exhaustion tails (level-set truncations)

The truncation lattice of the A8–A9 route needs NO countability: for a nonnegative
summable family `r`, the level sets `{i | ε ≤ r i}` are finite, they exhaust the
support as `ε ↓ 0`, and the complementary tails tend to `0`.  This replaces the
injection-into-ℕ bookkeeping of the original plan. -/

/-- Domination lemma for indicator families of a nonnegative family. -/
theorem summable_indicator {r : ι → ℝ} (hr0 : ∀ i, 0 ≤ r i) (hrs : Summable r)
    (s : Set ι) : Summable (fun i : ι => s.indicator r i) := by
  classical
  refine Summable.of_norm_bounded hrs fun i => ?_
  rw [Real.norm_eq_abs]
  by_cases h : i ∈ s
  · rw [Set.indicator_of_mem h, abs_of_nonneg (hr0 i)]
  · rw [Set.indicator_of_notMem h, abs_zero]
    exact hr0 i

/-- The tsum splits along a finite set: `∑' r = ∑' (ind_u r) + ∑' (ind_{uᶜ} r)`
(nonnegative summable families). -/
theorem tsum_split_indicator {r : ι → ℝ} (hr0 : ∀ i, 0 ≤ r i) (hrs : Summable r)
    (u : Finset ι) :
    (∑' i : ι, r i)
      = (∑' i : ι, (u : Set ι).indicator r i)
        + (∑' i : ι, ((u : Set ι)ᶜ).indicator r i) := by
  classical
  rw [← Summable.tsum_add (summable_indicator hr0 hrs _) (summable_indicator hr0 hrs _)]
  refine tsum_congr fun i => ?_
  by_cases h : i ∈ (u : Set ι)
  · rw [Set.indicator_of_mem h,
      Set.indicator_of_notMem (fun hc => (Set.mem_compl_iff _ _).mp hc h), add_zero]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_mem ((Set.mem_compl_iff _ _).mpr h),
      zero_add]

/-- Finite-sum monotonicity under inclusion on `ℝ` (the landed
`Finset.sum_le_sum_of_subset` needs `CanonicallyOrderedAdd`, absent on `ℝ`;
the ENNReal transport restores it). -/
theorem finset_sum_le_finset_sum_of_subset {f : ι → ℝ} (hnf : ∀ i, 0 ≤ f i)
    {s t : Finset ι} (h : s ⊆ t) : ∑ x ∈ s, f x ≤ ∑ x ∈ t, f x := by
  have hso : (∑ x ∈ s, ENNReal.ofReal (f x)) = ENNReal.ofReal (∑ x ∈ s, f x) :=
    (ENNReal.ofReal_sum_of_nonneg (fun i _ => hnf i)).symm
  have hto : (∑ x ∈ t, ENNReal.ofReal (f x)) = ENNReal.ofReal (∑ x ∈ t, f x) :=
    (ENNReal.ofReal_sum_of_nonneg (fun i _ => hnf i)).symm
  have hmon := Finset.sum_le_sum_of_subset (h : s ⊆ t) (f := fun i => ENNReal.ofReal (f i))
  rw [hso, hto] at hmon
  exact (ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg fun i _ => hnf i)).mp hmon

/-- The tsum of a nonnegative finite-support family is the finite sum. -/
theorem tsum_finite_support {f : ι → ℝ} (hnf : ∀ i, 0 ≤ f i) (hf : Summable f)
    (u : Finset ι) (hf0 : ∀ i ∉ u, f i = 0) :
    (∑' i : ι, f i) = ∑ i ∈ u, f i := by
  classical
  refine le_antisymm ?_ (Summable.sum_le_tsum u (fun i _ => hnf i) hf)
  refine Real.tsum_le_of_sum_le hnf ?_
  intro w
  rw [← Finset.sum_subset (Finset.filter_subset (· ∈ u) w)
    (fun i hi hiu => hf0 i fun hmem => hiu (Finset.mem_filter.mpr ⟨hi, hmem⟩))]
  exact finset_sum_le_finset_sum_of_subset hnf
    (fun i hi => (Finset.mem_filter.mp hi).2)

/-- **Finite-support exhaustion**: for every `ε > 0` there is a finite set whose
complementary tail is below `ε` (nonnegative summable families). -/
theorem exists_finite_small_tail {r : ι → ℝ} (hr0 : ∀ i, 0 ≤ r i) (hrs : Summable r)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t : Finset ι, ∑' i : ι, ((t : Set ι)ᶜ).indicator r i < ε := by
  classical
  by_contra hno
  push_neg at hno
  have hpart : ∀ w : Finset ι, ∑ i ∈ w, r i ≤ (∑' i : ι, r i) - ε := by
    intro w
    have h1 := hno w
    have hsplit := tsum_split_indicator hr0 hrs w
    have hnn : ∀ i : ι, 0 ≤ (w : Set ι).indicator r i :=
      fun i => Set.indicator_nonneg (fun a _ => hr0 a) i
    have h2 : (∑' i : ι, (w : Set ι).indicator r i) = ∑ i ∈ w, r i := by
      rw [tsum_finite_support hnn (summable_indicator hr0 hrs w) w
        (fun i hi => Set.indicator_of_notMem hi r),
        Finset.sum_congr rfl (fun i hi => by
          rw [Set.indicator_of_mem (Finset.mem_coe.mpr hi)])]
    rw [h2] at hsplit
    linarith
  have hcontra := le_of_tendsto hrs.hasSum (Filter.Eventually.of_forall hpart)
  linarith

/-- **Level-set truncation tails tend to zero** (the exhaustion engine of the
general-`k` route): along a sequence of finite sets that eventually captures every
nonzero element, the complementary tails of a nonnegative summable family tend
to `0`. -/
theorem tail_indicator_tendsto_zero {r : ι → ℝ} (hr0 : ∀ i, 0 ≤ r i) (hrs : Summable r)
    (s : ℕ → Finset ι)
    (hex : ∀ i, r i ≠ 0 → ∃ N₀ : ℕ, ∀ N ≥ N₀, i ∈ s N) :
    Filter.Tendsto (fun N : ℕ => ∑' i : ι, (((s N : Set ι))ᶜ).indicator r i)
      Filter.atTop (nhds 0) := by
  classical
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨t, htail⟩ := exists_finite_small_tail hr0 hrs hε
  have hdomN : ∀ N : ℕ, Summable (fun i : ι => (((s N : Set ι))ᶜ).indicator r i) :=
    fun N => summable_indicator hr0 hrs _
  have hdomT : Summable (fun i : ι => ((t : Set ι)ᶜ).indicator r i) :=
    summable_indicator hr0 hrs _
  -- the level sets eventually capture every nonzero element of the finite witness
  have hfin0 : ∀ w : Finset ι, (∀ i ∈ w, ∃ M, ∀ N ≥ M, i ∈ s N) →
      ∃ M, ∀ i ∈ w, ∀ N ≥ M, i ∈ s N := by
    intro w
    induction w using Finset.induction_on with
    | empty => intro _; exact ⟨0, by simp⟩
    | @insert j w hj ih =>
        intro hw
        obtain ⟨M1, hM1⟩ := hw j (Finset.mem_insert_self j w)
        obtain ⟨M2, hM2⟩ := ih (fun i hi => hw i (Finset.mem_insert_of_mem hi))
        refine ⟨max M1 M2, fun i hi N hN => ?_⟩
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact hM1 N (le_trans (le_max_left _ _) hN)
        · exact hM2 i hi N (le_trans (le_max_right _ _) hN)
  obtain ⟨N₀, hN₀⟩ := hfin0 (t.filter (fun i => r i ≠ 0))
    (fun i hi => hex i (Finset.mem_filter.mp hi).2)
  -- pointwise domination of every level tail by the finite witness tail
  -- (the witness must be filtered to its nonzero part for the containment)
  have hpointN : ∀ N ≥ N₀, ∀ i : ι,
      (((s N : Set ι))ᶜ).indicator r i ≤ ((t : Set ι)ᶜ).indicator r i := by
    intro N hN i
    by_cases hi : i ∈ t
    · by_cases hr : r i = 0
      · by_cases hn : i ∈ ((s N : Set ι))ᶜ
        · rw [Set.indicator_of_mem hn,
            Set.indicator_of_notMem (Set.notMem_compl_iff.mpr (Finset.mem_coe.mpr hi)), hr]
        · rw [Set.indicator_of_notMem hn,
            Set.indicator_of_notMem (Set.notMem_compl_iff.mpr (Finset.mem_coe.mpr hi))]
      · have hi0 : i ∈ t.filter (fun i => r i ≠ 0) := Finset.mem_filter.mpr ⟨hi, hr⟩
        have his : i ∈ s N := hN₀ i hi0 N hN
        rw [Set.indicator_of_notMem (Set.notMem_compl_iff.mpr (Finset.mem_coe.mpr his)),
          Set.indicator_of_notMem (Set.notMem_compl_iff.mpr (Finset.mem_coe.mpr hi))]
    · by_cases hn : i ∈ ((s N : Set ι))ᶜ
      · rw [Set.indicator_of_mem hn,
          Set.indicator_of_mem
            ((Set.mem_compl_iff ((t : Set ι)) i).mpr (Finset.mem_coe.not.mpr hi))]
      · rw [Set.indicator_of_notMem hn,
          Set.indicator_of_mem
            ((Set.mem_compl_iff ((t : Set ι)) i).mpr (Finset.mem_coe.not.mpr hi))]
        exact hr0 i
  refine Filter.eventually_atTop.mpr ⟨N₀, fun N hN => ?_⟩
  rw [dist_eq, sub_zero, abs_of_nonneg
    (tsum_nonneg (Set.indicator_nonneg (fun a _ => hr0 a)))]
  refine lt_of_le_of_lt (Summable.tsum_le_tsum (hpointN N hN) (hdomN N) hdomT) htail

/-- The partial sums over an exhausting sequence of finite sets tend to the total
(nonnegative summable families). -/
theorem partial_tendsto_tsum {r : ι → ℝ} (hr0 : ∀ i, 0 ≤ r i) (hrs : Summable r)
    (s : ℕ → Finset ι)
    (hex : ∀ i, r i ≠ 0 → ∃ N₀ : ℕ, ∀ N ≥ N₀, i ∈ s N) :
    Filter.Tendsto (fun N : ℕ => ∑ i ∈ s N, r i) Filter.atTop
      (nhds (∑' i : ι, r i)) := by
  classical
  have hsplit : ∀ N : ℕ,
      (∑' i : ι, r i)
        = (∑ i ∈ s N, r i)
          + (∑' i : ι, (((s N : Set ι))ᶜ).indicator r i) := by
    intro N
    have hnn : ∀ i : ι, 0 ≤ ((s N : Set ι)).indicator r i :=
      fun i => Set.indicator_nonneg (fun a _ => hr0 a) i
    rw [tsum_split_indicator hr0 hrs (s N),
      tsum_finite_support hnn (summable_indicator hr0 hrs (s N)) (s N)
        (fun i hi => Set.indicator_of_notMem hi r),
      Finset.sum_congr rfl (fun i hi => by
        rw [Set.indicator_of_mem (Finset.mem_coe.mpr hi)])]
  have htail := tail_indicator_tendsto_zero hr0 hrs s hex
  have hgoal : (fun N : ℕ => ∑ i ∈ s N, r i)
      = fun N : ℕ => (∑' i : ι, r i)
        - ∑' i : ι, (((s N : Set ι))ᶜ).indicator r i := by
    funext N
    rw [hsplit N]
    ring
  rw [hgoal]
  refine Filter.Tendsto.congr' (Filter.Eventually.of_forall fun _ => rfl) ?_
  have hconst := Filter.Tendsto.sub (tendsto_const_nhds (x := (∑' i : ι, r i))) htail
  rw [sub_zero] at hconst
  exact hconst

/-- Collapse of an indicator-truncated series to the finite sum (signed form,
via eventually-constant partial sums along `Filter.atTop` on `Finset`). -/
theorem tsum_indicator_finset {ι : Type*} {F : ι → ℝ} (t : Finset ι) :
    (∑' i, (t : Set ι).indicator F i) = ∑ i ∈ t, F i := by
  classical
  have hpart : (fun u : Finset ι => ∑ i ∈ u, (t : Set ι).indicator F i)
      =ᶠ[Filter.atTop] fun _ => ∑ i ∈ t, F i := by
    filter_upwards [(Filter.eventually_atTop).mpr ⟨t, fun _ hu => hu⟩] with u htu
    have hsub : u.filter (fun i => i ∈ t) = t := by
      refine Finset.ext fun i => ?_
      simp only [Finset.mem_filter]
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨htu h, h⟩
    have h1 : ∑ i ∈ u, (t : Set ι).indicator F i
        = ∑ i ∈ u.filter (fun i => i ∈ t), F i := by
      rw [Finset.sum_filter]
      exact Finset.sum_congr rfl fun i _ => Set.indicator_apply t F i
    rw [h1, hsub]
  exact HasSum.tsum_eq (Filter.Tendsto.congr' hpart.symm tendsto_const_nhds)

/-! ### Section 2b: truncated tensor kernels (representative level) -/

section TruncKernel

variable {ι : Type} {v : ι → L2} {κ : ι → ℝ} {g : ι → ℝ → ℝ}

/-- The single-term tensor kernel of a measurable representative family. -/
def tensKernel (g : ι → ℝ → ℝ) (i : ι) : ℝ × ℝ → ℝ :=
  fun p => g i p.1 * g i p.2

/-- The truncated tensor kernel `∑_{i ∈ t} κ i • (g i ⊗ g i)`. -/
def truncKernel (g : ι → ℝ → ℝ) (κ : ι → ℝ) (t : Finset ι) : ℝ × ℝ → ℝ :=
  fun p => ∑ i ∈ t, κ i * tensKernel g i p

/-- Tensor kernels of `L²` representatives are HS. -/
theorem hSKernel_tensKernel (hgLp : ∀ i, MemLp (g i) 2 vol) (i : ι) :
    HSKernel (tensKernel g i) := memLp2_prod_fst_snd (hgLp i) (hgLp i)

/-- The truncated tensor kernel of `L²` representatives is HS (finite sums). -/
theorem hSKernel_truncKernel (hgLp : ∀ i, MemLp (g i) 2 vol) (t : Finset ι) :
    HSKernel (truncKernel g κ t) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      have h0 : truncKernel g κ ∅ = 0 := by funext p; rfl
      rw [h0]
      exact MemLp.zero
  | @insert j t hj ih =>
      have hins : truncKernel g κ (insert j t)
          = (κ j • tensKernel g j) + truncKernel g κ t := by
        funext p
        show (∑ i ∈ insert j t, κ i * tensKernel g i p)
            = κ j * tensKernel g j p + ∑ i ∈ t, κ i * tensKernel g i p
        rw [Finset.sum_insert hj]
      rw [hins]
      exact MemLp.add (MemLp.const_smul (hSKernel_tensKernel hgLp j) (κ j)) ih

/-- Integral over a finite sum of integrable families. -/
private theorem integral_finset_sum {Fh : ι → (ℝ × ℝ) → ℝ} (t : Finset ι)
    (hint : ∀ i ∈ t, Integrable (Fh i) vol2) :
    (∫ p : ℝ × ℝ, ∑ i ∈ t, Fh i p ∂vol2) = ∑ i ∈ t, ∫ p : ℝ × ℝ, Fh i p ∂vol2 := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert j t hj ih =>
      have hjm : j ∈ insert j t := Finset.mem_insert_self _ _
      have htm : ∀ i ∈ t, i ∈ insert j t := fun i hi => Finset.mem_insert_of_mem hi
      have hI : Integrable (fun p : ℝ × ℝ => ∑ i ∈ t, Fh i p) vol2 :=
        integrable_finsetSum t (fun i hi => hint i (htm i hi))
      calc (∫ p : ℝ × ℝ, ∑ i ∈ insert j t, Fh i p ∂vol2)
          = (∫ p : ℝ × ℝ, Fh j p ∂vol2) + ∫ p : ℝ × ℝ, ∑ i ∈ t, Fh i p ∂vol2 := by
            simp only [Finset.sum_insert hj]
            exact integral_add (hint j hjm) hI
        _ = (∫ p : ℝ × ℝ, Fh j p ∂vol2) + ∑ i ∈ t, ∫ p : ℝ × ℝ, Fh i p ∂vol2 :=
            congrArg _ (ih (fun i hi => hint i (htm i hi)))
        _ = ∑ i ∈ insert j t, ∫ p : ℝ × ℝ, Fh i p ∂vol2 := by
            rw [Finset.sum_insert hj]

/-- **The pairing of a truncated tensor kernel is the truncated spectral pairing**:
`kpair (truncKernel g κ t) f g' = ∑_{i ∈ t} κ i • ⟪v i, f⟫ • ⟪v i, g'⟫` — the
finite-rank step of the compression route (the representatives `g i` only enter
through the a.e.-hypothesis `g i =ᵐ ⇑(v i)`). -/
theorem kpair_truncKernel (hgae : ∀ i, (g i) =ᵐ[vol] (⇑(v i)))
    (hgLp : ∀ i, MemLp (g i) 2 vol) (f g' : L2) (t : Finset ι) :
    kpair (truncKernel g κ t) f g'
      = ∑ i ∈ t, κ i * inner ℝ (v i) f * inner ℝ (v i) g' := by
  classical
  -- the per-term one-variable products are integrable (L² · L² ⊆ L¹)
  have hint1 : ∀ i : ι, Integrable (fun x : ℝ => g i x * (⇑g') x) vol := fun i =>
    (memLp_one_iff_integrable.mp (MemLp.mul (hgLp i) (Lp.memLp g'))).congr
      (Filter.Eventually.of_forall fun x => mul_comm ((⇑g') x) (g i x))
  have hint2 : ∀ i : ι, Integrable (fun y : ℝ => g i y * (⇑f) y) vol := fun i =>
    (memLp_one_iff_integrable.mp (MemLp.mul (hgLp i) (Lp.memLp f))).congr
      (Filter.Eventually.of_forall fun y => mul_comm ((⇑f) y) (g i y))
  have hint : ∀ i ∈ t, Integrable
      (fun p : ℝ × ℝ => κ i * ((g i p.1 * (⇑g') p.1) * (g i p.2 * (⇑f) p.2))) vol2 :=
    fun i _ => Integrable.const_mul
      (Integrable.op_fst_snd (op := fun a b : ℝ => a * b) (by fun_prop)
        ⟨1, fun x y => by simp [Real.norm_eq_abs]⟩ (hint1 i) (hint2 i)) (κ i)
  -- pointwise reshuffling into the per-term form
  have hpt : ∀ p : ℝ × ℝ,
      truncKernel g κ t p * (⇑f) p.2 * (⇑g') p.1
        = ∑ i ∈ t, κ i * ((g i p.1 * (⇑g') p.1) * (g i p.2 * (⇑f) p.2)) := by
    intro p
    show (∑ i ∈ t, κ i * tensKernel g i p) * (⇑f) p.2 * (⇑g') p.1
        = ∑ i ∈ t, κ i * ((g i p.1 * (⇑g') p.1) * (g i p.2 * (⇑f) p.2))
    rw [Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by
      show κ i * (g i p.1 * g i p.2) * (⇑f) p.2 * (⇑g') p.1
          = κ i * ((g i p.1 * (⇑g') p.1) * (g i p.2 * (⇑f) p.2))
      ring
  -- swap the integral with the finite sum
  show (∫ p : ℝ × ℝ, truncKernel g κ t p * (⇑f) p.2 * (⇑g') p.1 ∂vol2)
      = ∑ i ∈ t, κ i * inner ℝ (v i) f * inner ℝ (v i) g'
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_finset_sum t hint]
  -- per-term Fubini + identification with inner products
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsplit : (∫ p : ℝ × ℝ, κ i * ((g i p.1 * (⇑g') p.1) * (g i p.2 * (⇑f) p.2)) ∂vol2)
      = κ i * ((∫ x : ℝ, g i x * (⇑g') x ∂vol) * (∫ y : ℝ, g i y * (⇑f) y ∂vol)) := by
    rw [show (∫ p : ℝ × ℝ, κ i * ((g i p.1 * (⇑g') p.1) * (g i p.2 * (⇑f) p.2)) ∂vol2)
        = ∫ p : ℝ × ℝ, (κ i) * ((fun q : ℝ × ℝ =>
            (g i q.1 * (⇑g') q.1) * (g i q.2 * (⇑f) q.2)) p) ∂vol2 from rfl,
      integral_const_mul (κ i)
        (fun q : ℝ × ℝ => (g i q.1 * (⇑g') q.1) * (g i q.2 * (⇑f) q.2)),
      integral_prod_mul (f := fun x : ℝ => g i x * (⇑g') x)
        (g := fun y : ℝ => g i y * (⇑f) y)]
  rw [hsplit]
  have hA : (∫ x : ℝ, g i x * (⇑g') x ∂vol) = inner ℝ (v i) g' := by
    rw [inner_Lp_eq_coe]
    exact integral_congr_ae ((hgae i).mono fun x hx => by
      show g i x * (⇑g') x = (⇑(v i)) x * (⇑g') x
      rw [hx])
  have hB : (∫ y : ℝ, g i y * (⇑f) y ∂vol) = inner ℝ (v i) f := by
    rw [inner_Lp_eq_coe]
    exact integral_congr_ae ((hgae i).mono fun y hy => by
      show g i y * (⇑f) y = (⇑(v i)) y * (⇑f) y
      rw [hy])
  rw [hA, hB]
  ring

end TruncKernel

/-! ### Section 2c: truncated spectral operators (`S_t`, `T_t`, `B_t`)

The truncated tensor kernel of Section 2b realizes the *finite-rank spectral
operator* with the truncated coefficient families; the truncated square root
squares to the truncated eigenvalue operator, and the truncated model
`B_t = S_t ∘L M_omega ∘L S_t` carries the `√(chi_i kappa_i)-matrix formula`
(the truncation analogue of `inner_Bop_matrix`). -/

section TruncOp

open scoped Classical

variable {ι : Type} {v : ι → L2} {κ : ι → ℝ} {g : ι → ℝ → ℝ}

/-- The truncated eigenvalue coefficients `kappa · chi_t` (coefficient family
of the finite-rank operator `T_t`). -/
def truncKappaCoeff (κ : ι → ℝ) (t : Finset ι) (i : ι) : ℝ :=
  if i ∈ t then κ i else 0

/-- The truncated square-root coefficients `sqrt kappa · chi_t` (coefficient
family of the finite-rank operator `S_t`). -/
def truncSqrtCoeff (κ : ι → ℝ) (t : Finset ι) (i : ι) : ℝ :=
  if i ∈ t then Real.sqrt (κ i) else 0

/-- Bound for the truncated eigenvalue coefficients. -/
theorem abs_truncKappaCoeff_le {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ i, |κ i| ≤ C)
    (t : Finset ι) : ∀ i, |truncKappaCoeff κ t i| ≤ C := by
  intro i
  by_cases hi : i ∈ t
  · show |if i ∈ t then κ i else 0| ≤ C
    rw [if_pos hi]
    exact hC i
  · show |if i ∈ t then κ i else 0| ≤ C
    rw [if_neg hi]
    simpa using hC0

/-- Bound for the truncated square-root coefficients. -/
theorem abs_truncSqrtCoeff_le {C : ℝ} (hC : ∀ i, |κ i| ≤ C) (t : Finset ι) (i : ι) :
    |truncSqrtCoeff κ t i| ≤ Real.sqrt C := by
  by_cases hi : i ∈ t
  · show |if i ∈ t then Real.sqrt (κ i) else 0| ≤ Real.sqrt C
    rw [if_pos hi, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt (le_trans (le_abs_self (κ i)) (hC i))
  · show |if i ∈ t then Real.sqrt (κ i) else 0| ≤ Real.sqrt C
    rw [if_neg hi]
    simpa using Real.sqrt_nonneg C

/-- Squares of the truncated square-root coefficients are the truncated
eigenvalue coefficients (needs `kappa ≥ 0`). -/
theorem truncSqrtCoeff_sq (hκ0 : ∀ i, 0 ≤ κ i) (t : Finset ι) (i : ι) :
    truncSqrtCoeff κ t i ^ 2 = truncKappaCoeff κ t i := by
  by_cases hi : i ∈ t
  · show (if i ∈ t then Real.sqrt (κ i) else 0) ^ 2 = if i ∈ t then κ i else 0
    rw [if_pos hi, if_pos hi, Real.sq_sqrt (hκ0 i)]
  · show (if i ∈ t then Real.sqrt (κ i) else 0) ^ 2 = if i ∈ t then κ i else 0
    rw [if_neg hi, if_neg hi, zero_pow (by norm_num)]

/-- The truncated spectral operator `T_t` (coefficients `kappa · chi_t`). -/
def kappaTruncOp {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ i, |κ i| ≤ C) (t : Finset ι)
    (hv : Orthonormal ℝ v) : L2 →L[ℝ] L2 :=
  specOperator (c := truncKappaCoeff κ t) (abs_truncKappaCoeff_le hC0 hC t) hC0 hv

/-- The truncated square-root spectral operator `S_t` (coefficients
`sqrt kappa · chi_t`). -/
def sqrtTruncOp {C : ℝ} (hC : ∀ i, |κ i| ≤ C) (t : Finset ι)
    (hv : Orthonormal ℝ v) : L2 →L[ℝ] L2 :=
  specOperator (c := truncSqrtCoeff κ t) (abs_truncSqrtCoeff_le hC t)
    (Real.sqrt_nonneg C) hv

/-- **Operator identification** (Section 2c master): the kernel operator of the
truncated tensor kernel is the truncated spectral operator `T_t`.  The
representatives `g i` enter only through the a.e.-hypotheses. -/
theorem TOp_truncKernel_eq_specOperator {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ i, |κ i| ≤ C)
    (t : Finset ι) (hv : Orthonormal ℝ v)
    (hgae : ∀ i, (g i) =ᵐ[vol] (⇑(v i))) (hgLp : ∀ i, MemLp (g i) 2 vol) :
    TOp (truncKernel g κ t) (hSKernel_truncKernel hgLp t) = kappaTruncOp hC0 hC t hv := by
  have hκC : ∀ i, |truncKappaCoeff κ t i| ≤ C := abs_truncKappaCoeff_le hC0 hC t
  have hK : kappaTruncOp hC0 hC t hv
      = specOperator (c := truncKappaCoeff κ t) hκC hC0 hv := rfl
  refine ContinuousLinearMap.ext fun x => eq_of_forall_inner_eq fun y => ?_
  rw [inner_TOp (hSKernel_truncKernel hgLp t) x y, kpair_truncKernel hgae hgLp x y t,
    hK, inner_specOperator hκC hC0 hv x y, specPair]
  -- bridge the finite sum to the indicator tsum
  have hind : ∑' i, truncKappaCoeff κ t i * inner ℝ (v i) x * inner ℝ (v i) y
      = ∑' i, (t : Set ι).indicator
          (fun i => κ i * inner ℝ (v i) x * inner ℝ (v i) y) i := by
    refine tsum_congr fun i => ?_
    by_cases hi : i ∈ t
    · show (if i ∈ t then κ i else 0) * inner ℝ (v i) x * inner ℝ (v i) y
          = (t : Set ι).indicator
              (fun i => κ i * inner ℝ (v i) x * inner ℝ (v i) y) i
      rw [if_pos hi,
        Set.indicator_of_mem hi (fun i => κ i * inner ℝ (v i) x * inner ℝ (v i) y)]
    · show (if i ∈ t then κ i else 0) * inner ℝ (v i) x * inner ℝ (v i) y
          = (t : Set ι).indicator
              (fun i => κ i * inner ℝ (v i) x * inner ℝ (v i) y) i
      rw [if_neg hi,
        Set.indicator_of_notMem hi (fun i => κ i * inner ℝ (v i) x * inner ℝ (v i) y)]
      ring
  rw [hind, tsum_indicator_finset]

/-- **The truncated square root squares to the truncated operator**: `S_t ∘ S_t
= T_t` (pointwise `(sqrt kappa · chi_t) ^ 2 = kappa · chi_t`). -/
theorem sqrtTruncOp_comp_eq_kappaTruncOp (hκ0 : ∀ i, 0 ≤ κ i) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ i, |κ i| ≤ C) (t : Finset ι) (hv : Orthonormal ℝ v) :
    (sqrtTruncOp hC t hv).comp (sqrtTruncOp hC t hv) = kappaTruncOp hC0 hC t hv := by
  have hsC : ∀ i, |truncSqrtCoeff κ t i| ≤ Real.sqrt C := abs_truncSqrtCoeff_le hC t
  have hκC : ∀ i, |truncKappaCoeff κ t i| ≤ C := abs_truncKappaCoeff_le hC0 hC t
  have hS : sqrtTruncOp hC t hv
      = specOperator (c := truncSqrtCoeff κ t) hsC (Real.sqrt_nonneg C) hv := rfl
  have hK : kappaTruncOp hC0 hC t hv
      = specOperator (c := truncKappaCoeff κ t) hκC hC0 hv := rfl
  refine ContinuousLinearMap.ext fun x => eq_of_forall_inner_eq fun y => ?_
  rw [hS, hK, ContinuousLinearMap.comp_apply,
    inner_specOperator hsC (Real.sqrt_nonneg C) hv
      (specOperator (c := truncSqrtCoeff κ t) hsC (Real.sqrt_nonneg C) hv x) y,
    specPair,
    inner_specOperator hκC hC0 hv x y,
    specPair]
  have hflip : ∀ i : ι, inner ℝ (v i)
      (specOperator (c := truncSqrtCoeff κ t) hsC (Real.sqrt_nonneg C) hv x)
      = truncSqrtCoeff κ t i * inner ℝ (v i) x :=
    fun i => inner_specOperator_apply_right hsC (Real.sqrt_nonneg C) hv i x
  refine tsum_congr fun i => ?_
  rw [hflip i,
    show truncSqrtCoeff κ t i * (truncSqrtCoeff κ t i * inner ℝ (v i) x)
        = truncSqrtCoeff κ t i ^ 2 * inner ℝ (v i) x from by ring,
    truncSqrtCoeff_sq hκ0 t i]

/-- Power form of `S_t ^ 2 = T_t`. -/
theorem sqrtTruncOp_sq (hκ0 : ∀ i, 0 ≤ κ i) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ i, |κ i| ≤ C)
    (t : Finset ι) (hv : Orthonormal ℝ v) :
    (sqrtTruncOp hC t hv) ^ 2 = kappaTruncOp hC0 hC t hv := by
  have h2 : (sqrtTruncOp hC t hv) ^ 2
      = (sqrtTruncOp hC t hv).comp (sqrtTruncOp hC t hv) := by
    rw [pow_two]
    rfl
  rw [h2, sqrtTruncOp_comp_eq_kappaTruncOp hκ0 hC0 hC t hv]

/-- The truncated model operator `B_t := S_t ∘L M_omega ∘L S_t`. -/
def BtruncOp {C : ℝ} (hC : ∀ i, |κ i| ≤ C) (t : Finset ι) (hv : Orthonormal ℝ v)
    (omega : ℝ → ℝ) (hm : Measurable omega) {MR : ℝ}
    (hess : ∀ᵐ x ∂vol, |omega x| ≤ MR) : L2 →L[ℝ] L2 :=
  (sqrtTruncOp hC t hv).comp ((mulOperator omega hm hess).comp (sqrtTruncOp hC t hv))

theorem BtruncOp_apply {C : ℝ} (hC : ∀ i, |κ i| ≤ C) (t : Finset ι) (hv : Orthonormal ℝ v)
    (omega : ℝ → ℝ) (hm : Measurable omega) {MR : ℝ}
    (hess : ∀ᵐ x ∂vol, |omega x| ≤ MR) (x : L2) :
    BtruncOp hC t hv omega hm hess x
      = sqrtTruncOp hC t hv (mulOperator omega hm hess (sqrtTruncOp hC t hv x)) := rfl

/-- **Matrix formula for the truncated model** (the `sqrt(chi_i kappa_i · chi_j
kappa_j)`-form, the truncation analogue of `inner_Bop_matrix`):
`⟪v i, B_t (v j)⟫ = S-coeff_i · S-coeff_j · ⟪v i, M_omega (v j)⟫`. -/
theorem inner_Btrunc_matrix {C : ℝ} (hC : ∀ i, |κ i| ≤ C) (t : Finset ι)
    (hv : Orthonormal ℝ v) (omega : ℝ → ℝ) (hm : Measurable omega) {MR : ℝ}
    (hess : ∀ᵐ x ∂vol, |omega x| ≤ MR) (i j : ι) :
    inner ℝ (v i) (BtruncOp hC t hv omega hm hess (v j))
      = truncSqrtCoeff κ t i * truncSqrtCoeff κ t j
          * inner ℝ (v i) (mulOperator omega hm hess (v j)) := by
  have hsC : ∀ i, |truncSqrtCoeff κ t i| ≤ Real.sqrt C := abs_truncSqrtCoeff_le hC t
  have hS : sqrtTruncOp hC t hv
      = specOperator (c := truncSqrtCoeff κ t) hsC (Real.sqrt_nonneg C) hv := rfl
  rw [BtruncOp_apply hC t hv omega hm hess (v j), hS,
    inner_specOperator_apply_right hsC (Real.sqrt_nonneg C) hv i,
    specOperator_apply_basis hsC (Real.sqrt_nonneg C) hv j,
    ContinuousLinearMap.map_smul, real_inner_smul_right]
  ring

end TruncOp

/-! ### Section 3a: finite-rank matrix-square tools

The reusable pieces for the Section 3 cyclicity step: Parseval over a Hilbert
basis, the collapse of a tsum with finite support, the finite-sum action
formula for finitely supported spectral operators, and the matrix-square
summability (with explicit bound) of operators carrying a finite rank-one
decomposition — the HS-type packages consumed by `tracePair_cyclic`. -/

section FinRankTools

open scoped ENNReal

variable {ι : Type}

/-- Parseval equality over a Hilert basis of `L2` (second-argument form). -/
theorem tsum_inner_sq_hilbertBasis_eq_norm_sq (e : HilbertBasis ℕ ℝ L2) (u : L2) :
    (∑' i : ℕ, inner ℝ (e i) u ^ 2) = ‖u‖ ^ 2 := by
  have h := e.tsum_inner_mul_inner u u
  rw [real_inner_self_eq_norm_sq] at h
  rw [← h]
  exact tsum_congr fun i => by rw [real_inner_comm u (e i)]; ring

/-- A tsum that vanishes off a finite set equals the finite sum (no sign
restriction). -/
theorem tsum_eq_finset_sum_of_forall_notMem {F : ι → ℝ} {t : Finset ι}
    (hs : ∀ i, i ∉ t → F i = 0) : (∑' i, F i) = ∑ i ∈ t, F i := by
  refine Eq.trans (tsum_congr fun i => ?_) (tsum_indicator_finset (t := t))
  by_cases hi : i ∈ t
  · rw [Set.indicator_of_mem hi F]
  · rw [Set.indicator_of_notMem hi F, hs i hi]

/-- **Action formula for finitely supported spectral operators**: `S x` is the
finite sum `∑_{i ∈ t} c i • ⟪v i, x⟫ • v i`. -/
theorem specOperator_apply_eq_finset_sum {c : ι → ℝ} {C : ℝ} (hc : ∀ i, |c i| ≤ C)
    (hC0 : 0 ≤ C) {v : ι → L2} (hv : Orthonormal ℝ v) {t : Finset ι}
    (hsup : ∀ i, i ∉ t → c i = 0) (x : L2) :
    specOperator hc hC0 hv x = ∑ i ∈ t, (c i * inner ℝ (v i) x) • (v i) := by
  refine eq_of_forall_inner_eq fun y => ?_
  have hR : inner ℝ (∑ i ∈ t, (c i * inner ℝ (v i) x) • (v i)) y
      = ∑ i ∈ t, c i * inner ℝ (v i) x * inner ℝ (v i) y := by
    rw [sum_inner]
    exact Finset.sum_congr rfl fun i _ => by
      rw [real_inner_smul_left]
  have hbr : (∑' i, c i * inner ℝ (v i) x * inner ℝ (v i) y)
      = ∑ i ∈ t, c i * inner ℝ (v i) x * inner ℝ (v i) y :=
    tsum_eq_finset_sum_of_forall_notMem (fun i hi => by rw [hsup i hi]; ring)
  rw [inner_specOperator hc hC0 hv x y, specPair, hR, ← hbr]

/-- Swapping a tsum with a finite sum in `ℝ≥0∞` (no summability needed). -/
private theorem ennreal_tsum_sum_finset {α : Type*} [Countable α]
    {F : ι → α → ℝ≥0∞} (t : Finset ι) :
    (∑' a, ∑ i ∈ t, F i a) = ∑ i ∈ t, ∑' a, F i a := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert j t hj ih =>
      rw [show (∑' a, ∑ i ∈ insert j t, F i a) = ∑' a, (F j a + ∑ i ∈ t, F i a) from by
            refine tsum_congr fun a => ?_
            rw [Finset.sum_insert hj],
        Finset.sum_insert hj, ENNReal.tsum_add, ih]

/-- **Matrix squares of a finitely decomposed operator are summable**: if
`A x = ∑_{i ∈ t} ⟪w i, x⟫ • u i` (a finite rank-one decomposition), then over
every Hilbert basis `e` of `L2` the double matrix-square family of `A` is
summable with the explicit bound `#t • ∑_{i ∈ t} (‖w i‖ * ‖u i‖)²` — exactly the
HS-type package consumed by `tracePair_cyclic`. -/
theorem matrixSq_summable_of_decomp {w u : ι → L2} {t : Finset ι}
    {A : L2 →L[ℝ] L2} (hdec : ∀ x, A x = ∑ i ∈ t, (inner ℝ (w i) x) • (u i))
    (e : HilbertBasis ℕ ℝ L2) :
    ∃ CA : ℝ, 0 ≤ CA ∧ Summable (fun p : ℕ × ℕ => (inner ℝ (e p.1) (A (e p.2))) ^ 2)
      ∧ (∑' p : ℕ × ℕ, (inner ℝ (e p.1) (A (e p.2))) ^ 2) ≤ CA := by
  classical
  -- pointwise expansion of the matrix entries
  have hpt : ∀ p : ℕ × ℕ, inner ℝ (e p.1) (A (e p.2))
      = ∑ i ∈ t, inner ℝ (w i) (e p.2) * inner ℝ (e p.1) (u i) := by
    intro p
    rw [hdec (e p.2), inner_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [real_inner_smul_right]
  -- Parseval, both argument orders
  have hp1 : ∀ z : L2, (∑' b : ℕ, inner ℝ z (e b) ^ 2) = ‖z‖ ^ 2 := by
    intro z
    rw [← tsum_inner_sq_hilbertBasis_eq_norm_sq e z]
    exact tsum_congr fun b => by rw [real_inner_comm z (e b)]
  have hp2 : ∀ z : L2, (∑' a : ℕ, inner ℝ (e a) z ^ 2) = ‖z‖ ^ 2 :=
    fun z => tsum_inner_sq_hilbertBasis_eq_norm_sq e z
  -- per-i factorization of the double tsum
  have hfac : ∀ i : ι, (∑' p : ℕ × ℕ, ENNReal.ofReal
        ((inner ℝ (w i) (e p.2) * inner ℝ (e p.1) (u i)) ^ 2))
      = ENNReal.ofReal (‖w i‖ ^ 2 * ‖u i‖ ^ 2) := by
    intro i
    have h1 : (∑' p : ℕ × ℕ, ENNReal.ofReal
        ((inner ℝ (w i) (e p.2) * inner ℝ (e p.1) (u i)) ^ 2))
        = ∑' a : ℕ, ∑' b : ℕ, ENNReal.ofReal
          ((inner ℝ (w i) (e (a, b).2) * inner ℝ (e (a, b).1) (u i)) ^ 2) :=
      ENNReal.tsum_prod' (f := fun p : ℕ × ℕ => ENNReal.ofReal
        ((inner ℝ (w i) (e p.2) * inner ℝ (e p.1) (u i)) ^ 2))
    have hpair : ∀ q : ℕ × ℕ, ENNReal.ofReal
        ((inner ℝ (w i) (e q.2) * inner ℝ (e q.1) (u i)) ^ 2)
        = ENNReal.ofReal (inner ℝ (w i) (e q.2) ^ 2)
          * ENNReal.ofReal (inner ℝ (e q.1) (u i) ^ 2) := by
      intro q
      rw [mul_pow, ENNReal.ofReal_mul (sq_nonneg _)]
    have hin : ∀ a : ℕ, (∑' b : ℕ, ENNReal.ofReal (inner ℝ (w i) (e b) ^ 2)
            * ENNReal.ofReal (inner ℝ (e a) (u i) ^ 2))
        = (∑' b : ℕ, ENNReal.ofReal (inner ℝ (w i) (e b) ^ 2))
          * ENNReal.ofReal (inner ℝ (e a) (u i) ^ 2) :=
      fun a => ENNReal.tsum_mul_right
    have hsw : Summable fun b : ℕ => inner ℝ (w i) (e b) ^ 2 :=
      summable_inner_sq_of_hilbertBasis e (w i)
    have hsu : Summable fun a : ℕ => inner ℝ (e a) (u i) ^ 2 :=
      (summable_inner_sq_of_hilbertBasis e (u i)).congr fun a => by
        rw [real_inner_comm (u i) (e a)]
    rw [h1, tsum_congr fun a => tsum_congr fun b => hpair (a, b),
      tsum_congr hin, ENNReal.tsum_mul_left,
      ← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hsw,
      ← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hsu,
      hp1 (w i), hp2 (u i)]
    exact (ENNReal.ofReal_mul (by positivity)).symm
  -- the ENNReal Tonelli bound
  have key : ∑' p : ℕ × ℕ, ENNReal.ofReal ((inner ℝ (e p.1) (A (e p.2))) ^ 2)
      ≤ ENNReal.ofReal ((t.card : ℝ) * ∑ i ∈ t, (‖w i‖ * ‖u i‖) ^ 2) := by
    calc ∑' p : ℕ × ℕ, ENNReal.ofReal ((inner ℝ (e p.1) (A (e p.2))) ^ 2)
        ≤ ∑' p : ℕ × ℕ, ((t.card : ℝ≥0∞) * ∑ i ∈ t, ENNReal.ofReal
            ((inner ℝ (w i) (e p.2) * inner ℝ (e p.1) (u i)) ^ 2)) := by
          refine ENNReal.tsum_le_tsum fun p => ?_
          refine le_trans (ENNReal.ofReal_le_ofReal
            (show (inner ℝ (e p.1) (A (e p.2))) ^ 2
                ≤ (t.card : ℝ) * ∑ i ∈ t, (inner ℝ (w i) (e p.2)
                  * inner ℝ (e p.1) (u i)) ^ 2 from by
              rw [hpt p]; exact sq_sum_le_card_mul_sum_sq)) ?_
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
            ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _)]
      _ = (t.card : ℝ≥0∞) * ∑' p : ℕ × ℕ, ∑ i ∈ t, ENNReal.ofReal
            ((inner ℝ (w i) (e p.2) * inner ℝ (e p.1) (u i)) ^ 2) :=
          ENNReal.tsum_mul_left
      _ = (t.card : ℝ≥0∞) * ∑ i ∈ t, ∑' p : ℕ × ℕ, ENNReal.ofReal
            ((inner ℝ (w i) (e p.2) * inner ℝ (e p.1) (u i)) ^ 2) :=
          congrArg _ (ennreal_tsum_sum_finset t)
      _ = (t.card : ℝ≥0∞) * ∑ i ∈ t, ENNReal.ofReal (‖w i‖ ^ 2 * ‖u i‖ ^ 2) :=
          congrArg _ (Finset.sum_congr rfl fun i _ => hfac i)
      _ = ENNReal.ofReal ((t.card : ℝ) * ∑ i ∈ t, (‖w i‖ * ‖u i‖) ^ 2) := by
          have hsum : ∑ i ∈ t, ENNReal.ofReal (‖w i‖ ^ 2 * ‖u i‖ ^ 2)
              = ∑ i ∈ t, ENNReal.ofReal ((‖w i‖ * ‖u i‖) ^ 2) :=
            Finset.sum_congr rfl fun i _ => by rw [mul_pow]
          rw [hsum, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _),
            ← ENNReal.ofReal_mul (by positivity)]
  -- the A7-style transport to ℝ
  have hC0 : (0:ℝ) ≤ (t.card : ℝ) * ∑ i ∈ t, (‖w i‖ * ‖u i‖) ^ 2 := by positivity
  have hkeynt : (∑' p : ℕ × ℕ, ENNReal.ofReal ((inner ℝ (e p.1) (A (e p.2))) ^ 2)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top key
  have hfin : ∀ s : Finset (ℕ × ℕ),
      ∑ p ∈ s, (inner ℝ (e p.1) (A (e p.2))) ^ 2
        ≤ (t.card : ℝ) * ∑ i ∈ t, (‖w i‖ * ‖u i‖) ^ 2 := by
    intro s
    have h3 : ENNReal.ofReal (∑ p ∈ s, (inner ℝ (e p.1) (A (e p.2))) ^ 2)
        ≤ ∑' p : ℕ × ℕ, ENNReal.ofReal ((inner ℝ (e p.1) (A (e p.2))) ^ 2) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun p _ => sq_nonneg _)]
      exact Summable.sum_le_tsum s (fun _ _ => zero_le) ENNReal.summable
    have h4 : ∑ p ∈ s, (inner ℝ (e p.1) (A (e p.2))) ^ 2
        ≤ (∑' p : ℕ × ℕ, ENNReal.ofReal ((inner ℝ (e p.1) (A (e p.2))) ^ 2)).toReal :=
      (ENNReal.ofReal_le_iff_le_toReal hkeynt).1 h3
    refine le_trans h4 ?_
    calc (∑' p : ℕ × ℕ, ENNReal.ofReal ((inner ℝ (e p.1) (A (e p.2))) ^ 2)).toReal
        ≤ (ENNReal.ofReal ((t.card : ℝ) * ∑ i ∈ t, (‖w i‖ * ‖u i‖) ^ 2)).toReal :=
          (ENNReal.toReal_le_toReal hkeynt ENNReal.ofReal_ne_top).2 key
      _ = (t.card : ℝ) * ∑ i ∈ t, (‖w i‖ * ‖u i‖) ^ 2 := ENNReal.toReal_ofReal hC0
  exact ⟨_, hC0, summable_of_sum_le (fun p => sq_nonneg _) hfin,
    Real.tsum_le_of_sum_le (fun p => sq_nonneg _) hfin⟩

end FinRankTools

/-! ### Section 3b: the finite-rank cyclicity middle equality

`Diag_k(B_t) = Diag_k(W ∘ T_t)` for every `k ≥ 1`: the power regrouping
`B_t^{m+1} z = S_t ((W∘T_t)^m (W (S_t z)))` (induction on `m` consuming
`S_t² = T_t`), the finite decompositions of `W ∘ S_t`, `S_t ∘ (W∘T_t)^m` and
both composites (Section 3a tools), and one application of `tracePair_cyclic`. -/

section Cyclicity

open scoped Classical

variable {ι : Type} {v : ι → L2} {κ : ι → ℝ}

/-- **The middle equality on the truncated level** (Section 3 master): for every
`k ≥ 1` and Hilbert basis `e`, the `k`-th power diagonal of the truncated model
`B_t = S_t ∘L M_omega ∘L S_t` equals that of the truncated weighted kernel
composite `M_omega ∘ T_t`. -/
theorem diagTsum_Btrunc_pow_eq_diagTsum_WTtrunc_pow (hκ0 : ∀ i, 0 ≤ κ i)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ i, |κ i| ≤ C) (t : Finset ι) (hv : Orthonormal ℝ v)
    (omega : ℝ → ℝ) (hm : Measurable omega) {MR : ℝ}
    (hess : ∀ᵐ x ∂vol, |omega x| ≤ MR) (e : HilbertBasis ℕ ℝ L2) (k : ℕ) (hk : 1 ≤ k) :
    (∑' i : ℕ, inner ℝ (((BtruncOp hC t hv omega hm hess) ^ k) (e i)) (e i))
      = (∑' i : ℕ, inner ℝ ((((mulOperator omega hm hess).comp
          (kappaTruncOp hC0 hC t hv)) ^ k) (e i)) (e i)) := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m + 1 := ⟨k - 1, by omega⟩
  set W : L2 →L[ℝ] L2 := mulOperator omega hm hess with hWdef
  set S : L2 →L[ℝ] L2 := sqrtTruncOp hC t hv with hSdef
  set T : L2 →L[ℝ] L2 := kappaTruncOp hC0 hC t hv with hTdef
  set P : L2 →L[ℝ] L2 := W.comp T with hPdef
  -- iterating a power: `(X ^ (n+1)) z = X ((X ^ n) z)`
  have hpow : ∀ (X : L2 →L[ℝ] L2) (n : ℕ) (z : L2), (X ^ (n + 1)) z = X ((X ^ n) z) := by
    intro X n z
    rw [pow_succ']
    rfl
  -- the finite-sum action formulas
  have hSfin : ∀ x : L2, S x = ∑ i ∈ t, (truncSqrtCoeff κ t i * inner ℝ (v i) x) • (v i) := by
    intro x
    rw [hSdef]
    exact specOperator_apply_eq_finset_sum (abs_truncSqrtCoeff_le hC t)
      (Real.sqrt_nonneg C) hv
      (fun i hi => by
        show truncSqrtCoeff κ t i = 0
        rw [show truncSqrtCoeff κ t i = if i ∈ t then Real.sqrt (κ i) else 0 from rfl,
          if_neg hi]) x
  have hTfin : ∀ x : L2, T x = ∑ i ∈ t, (truncKappaCoeff κ t i * inner ℝ (v i) x) • (v i) := by
    intro x
    rw [hTdef]
    exact specOperator_apply_eq_finset_sum (abs_truncKappaCoeff_le hC0 hC t) hC0 hv
      (fun i hi => by
        show truncKappaCoeff κ t i = 0
        rw [show truncKappaCoeff κ t i = if i ∈ t then κ i else 0 from rfl, if_neg hi]) x
  -- the model action, the square identity (apply and compose forms)
  have hBap : ∀ z : L2, BtruncOp hC t hv omega hm hess z = S (W (S z)) := by
    intro z
    rw [hSdef, hWdef]
    exact BtruncOp_apply hC t hv omega hm hess z
  have hSS : ∀ u : L2, S (S u) = T u := by
    intro u
    rw [hSdef, hTdef]
    have h := congrArg (fun (X : L2 →L[ℝ] L2) => X u)
      (sqrtTruncOp_comp_eq_kappaTruncOp hκ0 hC0 hC t hv)
    rw [ContinuousLinearMap.comp_apply] at h
    exact h
  have hSScomp : ∀ Y : L2 →L[ℝ] L2, S.comp (S.comp Y) = T.comp Y := by
    intro Y
    rw [hSdef, hTdef]
    have h := congrArg (fun (X : L2 →L[ℝ] L2) => X.comp Y)
      (sqrtTruncOp_comp_eq_kappaTruncOp hκ0 hC0 hC t hv)
    rw [← ContinuousLinearMap.comp_assoc]
    exact h
  -- the power regrouping (induction consuming `S ∘ S = T`)
  have hreg : ∀ (n : ℕ) (z : L2), ((BtruncOp hC t hv omega hm hess) ^ (n + 1)) z
      = S ((P ^ n) (W (S z))) := by
    intro n
    induction n with
    | zero =>
        intro z
        rw [pow_zero]
        exact hBap z
    | succ n ih =>
        intro z
        rw [hpow (BtruncOp hC t hv omega hm hess) (n + 1) z, ih z, hBap, hSS,
          hpow P n (W (S z)), hPdef, ContinuousLinearMap.comp_apply]
  -- the finite rank-one decompositions of the factored operators
  have dV' : ∀ x : L2, (W.comp S) x
      = ∑ i ∈ t, (inner ℝ (v i) x) • ((truncSqrtCoeff κ t i) • (W (v i))) := by
    intro x
    rw [ContinuousLinearMap.comp_apply, hSfin x, _root_.map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ContinuousLinearMap.map_smul, smul_smul,
      mul_comm (truncSqrtCoeff κ t i) (inner ℝ (v i) x)]
  have dSZ : ∀ (Z : L2 →L[ℝ] L2) (x : L2), (S.comp Z) x
      = ∑ i ∈ t, (inner ℝ (Z.adjoint (v i)) x) • ((truncSqrtCoeff κ t i) • (v i)) := by
    intro Z x
    rw [ContinuousLinearMap.comp_apply, hSfin (Z x)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ContinuousLinearMap.adjoint_inner_left Z x (v i), smul_smul,
      mul_comm (truncSqrtCoeff κ t i) (inner ℝ (v i) (Z x))]
  have dWZ : ∀ (Z : L2 →L[ℝ] L2) (x : L2), (W.comp (T.comp Z)) x
      = ∑ i ∈ t, (inner ℝ (Z.adjoint (v i)) x)
          • ((truncKappaCoeff κ t i) • (W (v i))) := by
    intro Z x
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hTfin (Z x),
      _root_.map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ContinuousLinearMap.adjoint_inner_left Z x (v i), ContinuousLinearMap.map_smul,
      smul_smul, mul_comm (truncKappaCoeff κ t i) (inner ℝ (v i) (Z x))]
  -- the four HS-type packages (only the factor ones are consumed by cyclicity)
  have hUpkg := matrixSq_summable_of_decomp (dSZ (P ^ m)) e
  have hVpkg := matrixSq_summable_of_decomp dV' e
  have hUVdec : ∀ x : L2, ((S.comp (P ^ m)).comp (W.comp S)) x
      = ∑ i ∈ t, (inner ℝ (((P ^ m).comp (W.comp S)).adjoint (v i)) x)
          • ((truncSqrtCoeff κ t i) • (v i)) := by
    intro x
    rw [ContinuousLinearMap.comp_assoc]
    exact dSZ ((P ^ m).comp (W.comp S)) x
  have hVUdec : ∀ x : L2, ((W.comp S).comp (S.comp (P ^ m))) x
      = ∑ i ∈ t, (inner ℝ ((P ^ m).adjoint (v i)) x)
          • ((truncKappaCoeff κ t i) • (W (v i))) := by
    intro x
    rw [ContinuousLinearMap.comp_assoc, hSScomp]
    exact dWZ (P ^ m) x
  have hUVpkg := matrixSq_summable_of_decomp hUVdec e
  have hVUpkg := matrixSq_summable_of_decomp hVUdec e
  -- one cyclic move of the finite-rank factor
  have hcy := tracePair_cyclic (U := S.comp (P ^ m)) (V := W.comp S) e
    hUpkg hVpkg hUVpkg hVUpkg
  -- bridge the B-side diagonal to the cyclic form
  have hL : (∑' i : ℕ, inner ℝ (((BtruncOp hC t hv omega hm hess) ^ (m + 1)) (e i)) (e i))
      = (∑' i : ℕ, inner ℝ (e i) ((S.comp (P ^ m)) ((W.comp S) (e i)))) := by
    refine tsum_congr fun i => ?_
    rw [hreg m (e i)]
    exact real_inner_comm _ _
  -- bridge the cyclic counter-side to the kernel composite diagonal
  have hR : (∑' i : ℕ, inner ℝ (e i) ((W.comp S) ((S.comp (P ^ m)) (e i))))
      = (∑' i : ℕ, inner ℝ ((P ^ (m + 1)) (e i)) (e i)) := by
    refine tsum_congr fun i => ?_
    have hstep : (W.comp S) ((S.comp (P ^ m)) (e i)) = W (T ((P ^ m) (e i))) := by
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hSS]
    have hstep2 : ((P ^ (m + 1)) (e i)) = W (T ((P ^ m) (e i))) := by
      rw [hpow P m (e i), hPdef, ContinuousLinearMap.comp_apply]
    rw [hstep, ← hstep2]
    exact real_inner_comm _ _
  exact hL.trans (hcy.trans hR)

end Cyclicity

/-! ### Section 4a: representatives, tensor coordinates, and the HS-square tail

The kernel-side limit input: the tensor coordinates of the unweighted Riesz
kernel along a complete eigenfamily are `κ i • ⟪v i, v j⟫` (the eigen-equation),
so the Parseval expansion of the kernel-space norm over the tensor basis
collapses along the diagonal to the κ²-tail off the truncation set,
`hsNorm (K_R − truncKernel g κ t) ^ 2 = ∑'_{i ∉ t} κ i ^ 2`.  The tail tends to
`0` along any exhausting sequence of finite sets (Section 2a engine). -/

section KernelTail

open scoped Classical

variable {ι : Type} {v : ι → L2} {κ : ι → ℝ} {g : ι → ℝ → ℝ}

/-- Every family of `L²` classes has a family of measurable representatives
carrying the same `MemLp 2 vol` data (the `AEStronglyMeasurable` definition
destructs to `∃ g, StronglyMeasurable g ∧ f =ᵐ g`; `MemLp` transports by
`MemLp.ae_eq`). -/
theorem exists_measurable_rep_family (v : ι → L2) :
    ∃ g : ι → ℝ → ℝ, (∀ i, Measurable (g i)) ∧ (∀ i, MemLp (g i) 2 vol)
      ∧ ∀ i, (g i) =ᵐ[vol] (⇑(v i)) := by
  classical
  choose g hgsm hae using fun i : ι => (Lp.memLp (v i)).aestronglyMeasurable
  exact ⟨g, fun i => (hgsm i).measurable,
    fun i => MemLp.ae_eq (hae i) (Lp.memLp (v i)), fun i => (hae i).symm⟩

/-- **Tensor coordinates of the unweighted Riesz kernel** along a complete
eigenfamily: the `(p.1, p.2)`-coordinate of `K_R` in the tensor basis is
`κ p.1 • ⟪v p.1, v p.2⟫` (the eigen-equation, transported through
`inner_prodKernel_pairing`). -/
theorem tensorCoord_unweightedRiesz {psi c : ℝ} (hpsi0 : 0 ≤ psi)
    (hpsi2 : 2 * psi < 1) (hv : Orthonormal ℝ v)
    (he : ∀ i, TOp (unweightedRieszKernel psi c)
        (hsKernel_unweightedRieszKernel hpsi0 hpsi2) (v i) = κ i • v i)
    (p : ι × ι) :
    inner ℝ (MemLp.toLp (unweightedRieszKernel psi c)
        (hsKernel_unweightedRieszKernel hpsi0 hpsi2))
        (prodKernel (v p.2) (v p.1))
      = κ p.1 * inner ℝ (v p.1) (v p.2) := by
  rw [inner_prodKernel_pairing (K := unweightedRieszKernel psi c)
    (hK := hsKernel_unweightedRieszKernel hpsi0 hpsi2) (v := v) p, he p.1,
    real_inner_smul_left]

/-- **Tensor coordinates of the truncated tensor kernel**: the
`(p.1, p.2)`-coordinate is the truncated spectral pairing (the finite sum of
`kpair_truncKernel`). -/
theorem tensorCoord_truncKernel (hgae : ∀ i, (g i) =ᵐ[vol] (⇑(v i)))
    (hgLp : ∀ i, MemLp (g i) 2 vol) (t : Finset ι) (p : ι × ι) :
    inner ℝ (MemLp.toLp (truncKernel g κ t) (hSKernel_truncKernel hgLp t))
        (prodKernel (v p.2) (v p.1))
      = ∑ i ∈ t, κ i * inner ℝ (v i) (v p.1) * inner ℝ (v i) (v p.2) := by
  rw [inner_prodKernel_pairing (K := truncKernel g κ t)
    (hK := hSKernel_truncKernel hgLp t) (v := v) p,
    inner_TOp (hSKernel_truncKernel hgLp t) (v p.1) (v p.2),
    kpair_truncKernel hgae hgLp (v p.1) (v p.2) t]

/-- **The HS-square tail identity** (Section 4a master): the squared HS norm of
the difference between the unweighted Riesz kernel and its truncated tensor
kernel is exactly the κ²-tail off the truncation set — the tensor-basis Parseval
of the difference collapses along the diagonal (the coordinates are
`(κ − κ·χ_t) · δ`). -/
theorem hsNorm_sub_truncKernel_sq_eq_tail {psi c : ℝ} (hpsi0 : 0 ≤ psi)
    (hpsi2 : 2 * psi < 1) (hv : Orthonormal ℝ v)
    (he : ∀ i, TOp (unweightedRieszKernel psi c)
        (hsKernel_unweightedRieszKernel hpsi0 hpsi2) (v i) = κ i • v i)
    (hcomp : (span ℝ (Set.range v))ᗮ = ⊥)
    (hgae : ∀ i, (g i) =ᵐ[vol] (⇑(v i))) (hgLp : ∀ i, MemLp (g i) 2 vol)
    (hκ : Summable (fun i => κ i ^ 2)) (t : Finset ι) :
    hsNorm (unweightedRieszKernel psi c - truncKernel g κ t) ^ 2
      = ∑' i, ((t : Set ι)ᶜ).indicator (fun i => κ i ^ 2) i := by
  classical
  have hKR : HSKernel (unweightedRieszKernel psi c) :=
    hsKernel_unweightedRieszKernel hpsi0 hpsi2
  have hKN : HSKernel (truncKernel g κ t) := hSKernel_truncKernel hgLp t
  have hKX : HSKernel (unweightedRieszKernel psi c - truncKernel g κ t) :=
    hKR.sub hKN
  -- orthonormality of the family, as an explicit rewrite table
  have hortho : ∀ i j : ι,
      inner ℝ (v i) (v j) = if i = j then 1 else 0 := by
    intro i j
    by_cases h : i = j
    · rw [if_pos h, h, real_inner_self_eq_norm_sq, hv.1 j, one_pow]
    · rw [if_neg h, hv.2 h]
  -- the finite truncated sum collapses by orthonormality
  have hfold : ∀ p : ι × ι,
      (∑ i ∈ t, κ i * inner ℝ (v i) (v p.1) * inner ℝ (v i) (v p.2))
        = (if p.1 = p.2 then truncKappaCoeff κ t p.1 else 0) := by
    intro p
    by_cases hp : p.1 = p.2
    · rw [if_pos hp]
      have hterm : ∀ i : ι, κ i * inner ℝ (v i) (v p.1) * inner ℝ (v i) (v p.2)
          = if i = p.1 then κ i else 0 := by
        intro i
        rw [hortho i p.1, hortho i p.2, ← hp]
        by_cases h : i = p.1
        · rw [if_pos h, if_pos h]; ring
        · rw [if_neg h, if_neg h]; ring
      have hsingle : ∑ i ∈ t, (if i = p.1 then κ i else 0)
          = if p.1 ∈ t then κ p.1 else 0 := by
        by_cases hm : p.1 ∈ t
        · rw [if_pos hm]
          have hs := Finset.sum_eq_single (f := fun i => if i = p.1 then κ i else 0)
            p.1 (fun b _ hne => if_neg hne) (fun hcon => absurd hm hcon)
          rw [if_pos rfl] at hs
          exact hs
        · rw [if_neg hm]
          exact Finset.sum_eq_zero fun i hi =>
            if_neg (fun hc => hm (by rw [← hc]; exact hi))
      rw [Finset.sum_congr rfl (fun i _ => hterm i), hsingle,
        show truncKappaCoeff κ t p.1 = if p.1 ∈ t then κ p.1 else 0 from rfl]
    · rw [if_neg hp]
      have hterm0 : ∀ i : ι,
          κ i * inner ℝ (v i) (v p.1) * inner ℝ (v i) (v p.2) = 0 := by
        intro i
        rw [hortho i p.1, hortho i p.2]
        by_cases h : i = p.1
        · rw [if_pos h, if_neg (by rw [h]; exact hp)]
          ring
        · rw [if_neg h]
          ring
      rw [Finset.sum_congr rfl (fun i _ => hterm0 i), Finset.sum_const_zero]
  -- the tensor coordinate of the difference
  have hA : ∀ p : ι × ι,
      inner ℝ (TOp (unweightedRieszKernel psi c) hKR (v p.1)) (v p.2)
        = κ p.1 * inner ℝ (v p.1) (v p.2) := fun p =>
    (inner_prodKernel_pairing (K := unweightedRieszKernel psi c)
      (hK := hKR) (v := v) p).symm.trans
        (tensorCoord_unweightedRiesz hpsi0 hpsi2 hv he p)
  have hB : ∀ p : ι × ι,
      inner ℝ (TOp (truncKernel g κ t) hKN (v p.1)) (v p.2)
        = ∑ i ∈ t, κ i * inner ℝ (v i) (v p.1) * inner ℝ (v i) (v p.2) := fun p =>
    (inner_prodKernel_pairing (K := truncKernel g κ t)
      (hK := hKN) (v := v) p).symm.trans
        (tensorCoord_truncKernel hgae hgLp t p)
  have hP : ∀ p : ι × ι,
      inner ℝ (MemLp.toLp (unweightedRieszKernel psi c - truncKernel g κ t) hKX)
          (prodKernel (v p.2) (v p.1))
        = (if p.1 = p.2 then κ p.1 - truncKappaCoeff κ t p.1 else 0) := by
    intro p
    calc inner ℝ (MemLp.toLp (unweightedRieszKernel psi c - truncKernel g κ t) hKX)
          (prodKernel (v p.2) (v p.1))
        = inner ℝ (TOp (unweightedRieszKernel psi c - truncKernel g κ t) hKX
            (v p.1)) (v p.2) :=
          inner_prodKernel_pairing (K := unweightedRieszKernel psi c
            - truncKernel g κ t) (hK := hKX) (v := v) p
      _ = inner ℝ (TOp (unweightedRieszKernel psi c) hKR (v p.1)) (v p.2)
            - inner ℝ (TOp (truncKernel g κ t) hKN (v p.1)) (v p.2) := by
          rw [TOp_sub hKR hKN, _root_.sub_apply, inner_sub_left]
      _ = κ p.1 * inner ℝ (v p.1) (v p.2)
            - ∑ i ∈ t, κ i * inner ℝ (v i) (v p.1) * inner ℝ (v i) (v p.2) := by
          rw [hA p, hB p]
      _ = (if p.1 = p.2 then κ p.1 - truncKappaCoeff κ t p.1 else 0) := by
          rw [hfold p]
          by_cases hp : p.1 = p.2
          · rw [if_pos hp, hortho p.1 p.2, if_pos hp, mul_one, if_pos hp]
          · rw [if_neg hp, hortho p.1 p.2, if_neg hp, mul_zero, sub_zero,
              if_neg hp]
  -- Parseval over the tensor basis: hsNorm² = ∑' (coordinate)²
  have hnorm : hsNorm (unweightedRieszKernel psi c - truncKernel g κ t) ^ 2
      = ∑' p : ι × ι,
          (if p.1 = p.2 then κ p.1 - truncKappaCoeff κ t p.1 else 0) ^ 2 := by
    rw [hsNorm_def, Real.sq_sqrt (integral_nonneg fun p => sq_nonneg _)]
    have hI : (∫ p : ℝ × ℝ,
          (unweightedRieszKernel psi c - truncKernel g κ t) p ^ 2 ∂vol2)
        = inner ℝ
            (MemLp.toLp (unweightedRieszKernel psi c - truncKernel g κ t) hKX)
            (MemLp.toLp (unweightedRieszKernel psi c - truncKernel g κ t) hKX) := by
      rw [inner_toLp_toLp hKX hKX]
      exact integral_congr_ae (Filter.Eventually.of_forall fun p => by
        show (unweightedRieszKernel psi c - truncKernel g κ t) p ^ 2
            = (unweightedRieszKernel psi c - truncKernel g κ t) p
              * (unweightedRieszKernel psi c - truncKernel g κ t) p
        ring)
    rw [hI, kernel_inner_eq_tsum_prodKernel' hv hcomp _ _]
    exact tsum_congr fun p => by rw [hP p, sq]
  -- the diagonal collapse (HasSum along the injective diagonal embedding)
  rw [hnorm]
  set F : ι × ι → ℝ :=
    fun p => (if p.1 = p.2 then κ p.1 - truncKappaCoeff κ t p.1 else 0) ^ 2 with hFdef
  have hdiag : Function.Injective (fun i : ι => (i, i)) := by
    intro i j hij
    exact congrArg Prod.fst hij
  have hF0 : ∀ q : ι × ι, q ∉ Set.range (fun i : ι => (i, i)) → F q = 0 := by
    intro q hq
    by_cases hq12 : q.1 = q.2
    · exfalso
      apply hq
      exact ⟨q.2, Prod.ext hq12.symm rfl⟩
    · have hq0 : F q
          = (if q.1 = q.2 then κ q.1 - truncKappaCoeff κ t q.1 else 0) ^ 2 := rfl
      rw [hq0, if_neg hq12]
      norm_num
  have hFe : ∀ i : ι, F (i, i)
      = ((t : Set ι)ᶜ).indicator (fun i => κ i ^ 2) i := by
    intro i
    have h1 : F (i, i) = (κ i - truncKappaCoeff κ t i) ^ 2 := by
      simp only [hFdef, if_true]
    rw [h1]
    by_cases hi : i ∈ t
    · rw [show truncKappaCoeff κ t i = if i ∈ t then κ i else 0 from rfl, if_pos hi,
        sub_self, zero_pow (by norm_num)]
      exact (Set.indicator_of_notMem
        (fun hc => absurd (show i ∈ (t : Set ι) from Finset.mem_coe.mpr hi)
          ((Set.mem_compl_iff ((t : Set ι)) i).mp hc)) (fun i => κ i ^ 2)).symm
    · have hm : i ∈ ((t : Set ι)ᶜ) :=
        (Set.mem_compl_iff ((t : Set ι)) i).mpr (fun hc => hi (Finset.mem_coe.mp hc))
      rw [show truncKappaCoeff κ t i = if i ∈ t then κ i else 0 from rfl, if_neg hi,
        sub_zero, Set.indicator_of_mem hm]
  have hsumind : HasSum (fun i : ι => ((t : Set ι)ᶜ).indicator (fun i => κ i ^ 2) i)
      (∑' i, ((t : Set ι)ᶜ).indicator (fun i => κ i ^ 2) i) :=
    (summable_indicator (fun i => sq_nonneg (κ i)) hκ _).hasSum
  have hcompF : HasSum (fun i : ι => F (i, i))
      (∑' i, ((t : Set ι)ᶜ).indicator (fun i => κ i ^ 2) i) :=
    hsumind.congr_fun fun i => hFe i
  exact ((hdiag.hasSum_iff hF0).mp hcompF).tsum_eq

/-- Level-set finiteness for a nonnegative summable family (local copy of the
BopCompactness private helper, which does not cross files). -/
private theorem levelSet_finite {r : ι → ℝ} (hr0 : ∀ i, 0 ≤ r i)
    (hrs : Summable r) {ε : ℝ} (hε : 0 < ε) :
    {i : ι | ε ≤ r i}.Finite := by
  classical
  by_contra hinf
  set B : ℝ := ∑' i, r i with hBdef
  have hB0 : (0:ℝ) ≤ B := tsum_nonneg hr0
  obtain ⟨N, hNgt⟩ : ∃ N : ℕ, B / ε + 1 < (N : ℝ) := exists_nat_gt _
  obtain ⟨t, hts, htc⟩ := Set.Infinite.exists_subset_card_eq hinf N
  have hsum : ∑ i ∈ t, r i ≤ B := Summable.sum_le_tsum t (fun i _ => hr0 i) hrs
  have hge : ∀ i ∈ t, ε ≤ r i := fun i hi => hts hi
  have hcard : (N:ℝ) * ε ≤ ∑ i ∈ t, r i := by
    have h0 : (∑ i ∈ t, ε) ≤ ∑ i ∈ t, r i := Finset.sum_le_sum hge
    rw [Finset.sum_const, nsmul_eq_mul, htc] at h0
    exact h0
  have hε2 : (0:ℝ) < ε := hε
  have hkey : B + ε < (N:ℝ) * ε := by
    have hscal : (B / ε + 1) * ε < (N:ℝ) * ε := mul_lt_mul_of_pos_right hNgt hε2
    have hexp : (B / ε + 1) * ε = B + ε := by
      rw [add_mul, div_mul_cancel₀ B (ne_of_gt hε2), one_mul]
    rw [hexp] at hscal
    exact hscal
  have hfinal : B + ε ≤ B := (le_of_lt hkey).trans (le_trans hcard hsum)
  exact absurd hfinal (by linarith)

/-- **Exhausting level-set sequence**: every nonnegative summable family carries
a sequence of finite sets eventually capturing every nonzero element. -/
theorem exists_exhausting_finsets {r : ι → ℝ} (hr0 : ∀ i, 0 ≤ r i)
    (hrs : Summable r) :
    ∃ s : ℕ → Finset ι, ∀ i, r i ≠ 0 → ∃ N₀ : ℕ, ∀ N ≥ N₀, i ∈ s N := by
  classical
  have hfin : ∀ N : ℕ, {i : ι | (1:ℝ) / ((N:ℝ) + 1) ≤ r i}.Finite :=
    fun N => levelSet_finite hr0 hrs (by positivity)
  refine ⟨fun N => (hfin N).toFinset, ?_⟩
  intro i hri
  have hpos : 0 < r i := lt_of_le_of_ne (hr0 i) (Ne.symm hri)
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, (1:ℝ) / ((N₀:ℝ) + 1) ≤ r i := by
    obtain ⟨N, hN⟩ : ∃ N : ℕ, (1:ℝ) / r i < (N : ℝ) := exists_nat_gt _
    refine ⟨N, ?_⟩
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (N:ℝ) + 1)]
    have h1 : (1:ℝ) ≤ r i * (N:ℝ) := by
      have h2 := (div_lt_iff₀ hpos).mp hN
      rw [mul_comm] at h2
      exact le_of_lt h2
    nlinarith [h1, hpos]
  refine ⟨N₀, ?_⟩
  intro N hN
  rw [(hfin N).mem_toFinset]
  refine le_trans ?_ hN₀
  have hmono : ((N₀:ℝ) + 1) ≤ (N:ℝ) + 1 := by
    have h1 : (N₀:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    linarith
  exact (div_le_div_iff₀ (by positivity : (0:ℝ) < (N:ℝ) + 1)
    (by positivity : (0:ℝ) < (N₀:ℝ) + 1)).mpr (by rw [one_mul, one_mul]; exact hmono)

/-- **The kernel tail tends to zero** (Section 4a limit): along any sequence of
finite truncation sets exhausting the κ-support, the HS norm of the difference
between the unweighted Riesz kernel and the truncated tensor kernel tends to
`0`. -/
theorem hsNorm_sub_truncKernel_tendsto_zero {psi c : ℝ} (hpsi0 : 0 ≤ psi)
    (hpsi2 : 2 * psi < 1) (hv : Orthonormal ℝ v)
    (he : ∀ i, TOp (unweightedRieszKernel psi c)
        (hsKernel_unweightedRieszKernel hpsi0 hpsi2) (v i) = κ i • v i)
    (hcomp : (span ℝ (Set.range v))ᗮ = ⊥)
    (hgae : ∀ i, (g i) =ᵐ[vol] (⇑(v i))) (hgLp : ∀ i, MemLp (g i) 2 vol)
    (hκ : Summable (fun i => κ i ^ 2))
    (s : ℕ → Finset ι) (hex : ∀ i, κ i ≠ 0 → ∃ N₀ : ℕ, ∀ N ≥ N₀, i ∈ s N) :
    Filter.Tendsto (fun N : ℕ =>
      hsNorm (unweightedRieszKernel psi c - truncKernel g κ (s N)))
      Filter.atTop (nhds 0) := by
  have hex2 : ∀ i, (fun i => κ i ^ 2) i ≠ 0 → ∃ N₀ : ℕ, ∀ N ≥ N₀, i ∈ s N := by
    intro i h2
    exact hex i (fun hc => h2 (by show κ i ^ 2 = 0; rw [hc, zero_pow]; norm_num))
  have htail := tail_indicator_tendsto_zero (fun i => sq_nonneg (κ i)) hκ s hex2
  have hfun : (fun N : ℕ =>
        hsNorm (unweightedRieszKernel psi c - truncKernel g κ (s N)))
      = fun N : ℕ => Real.sqrt
        (∑' i, (((s N : Set ι))ᶜ).indicator (fun i => κ i ^ 2) i) := by
    funext N
    have hmain := hsNorm_sub_truncKernel_sq_eq_tail hpsi0 hpsi2 hv he hcomp
      hgae hgLp hκ (s N)
    rw [← Real.sqrt_sq (hsNorm_nonneg _), hmain]
  rw [hfun]
  have hsqrt : Filter.Tendsto (fun N : ℕ => Real.sqrt
      (∑' i, (((s N : Set ι))ᶜ).indicator (fun i => κ i ^ 2) i))
      Filter.atTop (nhds 0) := by
    have h := (Real.continuous_sqrt.tendsto (0:ℝ)).comp htail
    rw [Real.sqrt_zero] at h
    exact h
  exact hsqrt

end KernelTail

/-! ### Section 4b: the truncated composite is the weighted truncated kernel operator

`M_omega ∘ T_t = TOp (omega · truncKernel g κ t)` — assembling the Section 1
left-multiplication identity with the Section 2c operator identification. -/

section WeightedTrunc

open scoped Classical

variable {ι : Type} {v : ι → L2} {κ : ι → ℝ} {g : ι → ℝ → ℝ}

/-- The truncated tensor kernel is measurable (finite induction over the
truncation set; the representatives are measurable). -/
theorem measurable_truncKernel (hgm : ∀ i, Measurable (g i)) (t : Finset ι) :
    Measurable (truncKernel g κ t) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      have h0 : truncKernel g κ ∅ = fun _ : ℝ × ℝ => (0:ℝ) := by
        funext p; rfl
      rw [h0]
      exact measurable_const
  | @insert j t hj ih =>
      have hins : truncKernel g κ (insert j t)
          = (fun p : ℝ × ℝ => κ j * (g j p.1 * g j p.2)) + truncKernel g κ t := by
        funext p
        show (∑ i ∈ insert j t, κ i * tensKernel g i p)
            = κ j * (g j p.1 * g j p.2) + ∑ i ∈ t, κ i * tensKernel g i p
        rw [Finset.sum_insert hj,
          show tensKernel g j p = g j p.1 * g j p.2 from rfl]
      rw [hins]
      exact Measurable.add (measurable_const.mul
        (((hgm j).comp measurable_fst).mul ((hgm j).comp measurable_snd))) ih

/-- The weighted truncated kernel is measurable. -/
theorem measurable_weightedTruncKernel (hgm : ∀ i, Measurable (g i))
    (omega : ℝ → ℝ) (hm : Measurable omega) (t : Finset ι) :
    Measurable (fun p : ℝ × ℝ => omega p.1 * truncKernel g κ t p) :=
  (hm.comp measurable_fst).mul (measurable_truncKernel hgm t)

/-- **Section 4b identification**: the truncated composite is the kernel
operator of the weighted truncated kernel,
`M_omega ∘ T_t = TOp (omega p.1 * truncKernel g κ t p)`. -/
theorem comp_mulOperator_kappaTruncOp_eq_TOp (hgae : ∀ i, (g i) =ᵐ[vol] (⇑(v i)))
    (hgLp : ∀ i, MemLp (g i) 2 vol) (hgm : ∀ i, Measurable (g i))
    (t : Finset ι) (omega : ℝ → ℝ) (hm : Measurable omega) {MR : ℝ}
    (hess : ∀ᵐ x ∂vol, |omega x| ≤ MR) (hbdd : ∀ x : ℝ, |omega x| ≤ MR)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ i, |κ i| ≤ C) (hv : Orthonormal ℝ v) :
    (mulOperator omega hm hess).comp (kappaTruncOp hC0 hC t hv)
      = TOp (fun p => omega p.1 * truncKernel g κ t p)
          (hSKernel_weight_mul (hSKernel_truncKernel hgLp t) hm hbdd) := by
  rw [← TOp_truncKernel_eq_specOperator hC0 hC t hv hgae hgLp,
    ← mulOperator_comp_TOp_gen (hSKernel_truncKernel hgLp t) hm hess hbdd]

end WeightedTrunc

/-! ### Section 4c: weighted kernel-difference control

Multiplying a kernel difference by the bounded weight on the left is
`MR`-Lipschitz for the HS norm (a pointwise-square domination; no Fubini). -/

section WeightControl

/-- **Weighted difference control** (Section 4c master): for a bounded weight,
`hsNorm (omega·K − omega·N) ≤ MR * hsNorm (K − N)`. -/
theorem hsNorm_weight_mul_sub_le {K N : ℝ × ℝ → ℝ} (hK : HSKernel K)
    (hN : HSKernel N) {omega : ℝ → ℝ} {MR : ℝ}
    (hbdd : ∀ x : ℝ, |omega x| ≤ MR) :
    hsNorm (fun p => omega p.1 * K p - omega p.1 * N p) ≤ MR * hsNorm (K - N) := by
  have hMR0 : (0:ℝ) ≤ MR := le_trans (abs_nonneg (omega 0)) (hbdd 0)
  have hX : HSKernel (K - N) := hK.sub hN
  have hfun : (fun p : ℝ × ℝ => omega p.1 * K p - omega p.1 * N p)
      = fun p : ℝ × ℝ => omega p.1 * (K - N) p := by
    funext p
    show omega p.1 * K p - omega p.1 * N p = omega p.1 * (K - N) p
    simp only [Pi.sub_apply]
    ring
  rw [hfun]
  have hintX : Integrable (fun p : ℝ × ℝ => (K - N) p ^ 2) vol2 :=
    MemLp.integrable_sq hX
  have hintMX : Integrable (fun p : ℝ × ℝ => (MR * (K - N) p) ^ 2) vol2 := by
    have h1 : (fun p : ℝ × ℝ => (MR * (K - N) p) ^ 2)
        = fun p : ℝ × ℝ => MR ^ 2 * (K - N) p ^ 2 := by
      funext p; rw [mul_pow]
    rw [h1]
    exact hintX.const_mul (MR ^ 2)
  calc hsNorm (fun p => omega p.1 * (K - N) p)
      = Real.sqrt (∫ p : ℝ × ℝ, (omega p.1 * (K - N) p) ^ 2 ∂vol2) := hsNorm_def _
    _ ≤ Real.sqrt (∫ p : ℝ × ℝ, (MR * (K - N) p) ^ 2 ∂vol2) := by
        refine Real.sqrt_le_sqrt ?_
        refine integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun p => sq_nonneg _) hintMX ?_
        exact Filter.Eventually.of_forall fun p => by
          refine sq_le_sq.mpr ?_
          rw [abs_mul, abs_mul, abs_of_nonneg hMR0]
          exact mul_le_mul_of_nonneg_right (hbdd p.1) (abs_nonneg ((K - N) p))
    _ = MR * hsNorm (K - N) := by
        rw [hsNorm_def]
        have hc : (∫ p : ℝ × ℝ, (MR * (K - N) p) ^ 2 ∂vol2)
            = ∫ p : ℝ × ℝ, MR ^ 2 * (K - N) p ^ 2 ∂vol2 :=
          integral_congr_ae (Filter.Eventually.of_forall fun p => by
            show (MR * (K - N) p) ^ 2 = MR ^ 2 * (K - N) p ^ 2
            rw [mul_pow])
        rw [hc, integral_const_mul (MR ^ 2) (fun p : ℝ × ℝ => (K - N) p ^ 2),
          Real.sqrt_mul (by positivity : (0:ℝ) ≤ MR ^ 2),
          Real.sqrt_sq hMR0]

/-- **Weighted kernel norm control**: `hsNorm (omega·K) ≤ MR * hsNorm K`. -/
theorem hsNorm_weight_mul_le {K : ℝ × ℝ → ℝ} (hK : HSKernel K)
    {omega : ℝ → ℝ} {MR : ℝ} (hbdd : ∀ x : ℝ, |omega x| ≤ MR) :
    hsNorm (fun p => omega p.1 * K p) ≤ MR * hsNorm K := by
  have h := hsNorm_weight_mul_sub_le hK MemLp.zero hbdd
  have h1 : (fun p : ℝ × ℝ => omega p.1 * K p - omega p.1 * ((0:ℝ × ℝ → ℝ) p))
      = fun p : ℝ × ℝ => omega p.1 * K p := by
    funext p
    simp only [Pi.zero_apply]
    ring
  have h2 : (K - (0:ℝ × ℝ → ℝ)) = K := by
    funext p
    simp only [Pi.sub_apply, Pi.zero_apply]
    ring
  rw [h1, h2] at h
  exact h

end WeightControl

/-! ### Section 4d: the power-diagonal convergence (kernel side)

For a measurable HS kernel `C` the `k`-power diagonal sum of `TOp C` is the
`cycle2` pairing of the kernel tower with the top (`tracePair_comp_tsum`), and
`cycle2` is bilinearly Lipschitz; the Section 1 tower Lipschitz then drives the
diagonal sums of the weighted truncated kernels to that of the weighted Riesz
kernel operator along any exhausting sequence of truncation sets. -/

section PowerDiag

open scoped Classical

variable {ι : Type} {v : ι → L2} {κ : ι → ℝ} {g : ι → ℝ → ℝ}

/-- Local copy of the CompressionIdentity private: the `I`-indicator of the
weight equals the weight a.e. on the carrier measure. -/
private theorem indicator_omega_ae' {omega : ℝ → ℝ} :
    (fun x : ℝ => (I : Set ℝ).indicator omega x) =ᵐ[vol] omega := by
  filter_upwards [MeasureTheory.ae_restrict_mem
    (measurableSet_Icc : MeasurableSet (I : Set ℝ))] with x hx
  rw [Set.indicator_of_mem hx]

/-- The weighted unweighted Riesz kernel is a.e. the Riesz kernel. -/
theorem weightedKernel_ae_rieszKernel {psi c : ℝ} {omega : ℝ → ℝ} :
    (fun p : ℝ × ℝ => omega p.1 * unweightedRieszKernel psi c p)
      =ᵐ[vol2] (rieszKernel psi c omega) := by
  filter_upwards [eventual_fst indicator_omega_ae'] with p hp
  show omega p.1 * unweightedRieszKernel psi c p = rieszKernel psi c omega p
  rw [show rieszKernel psi c omega p
      = (I : Set ℝ).indicator omega p.1 * unweightedRieszKernel psi c p from by
        show (I : Set ℝ).indicator omega p.1 * c * |p.1 - p.2| ^ (-psi)
            = (I : Set ℝ).indicator omega p.1 * (c * |p.1 - p.2| ^ (-psi))
        ring, hp]

/-- Integrability of the product of two HS kernels (the `cycle2` integrand
supply; Hölder as in `cycle2_bound`). -/
private theorem integrable_hskernel_mul {A B : ℝ × ℝ → ℝ} (hA : HSKernel A)
    (hB : HSKernel B) : Integrable (fun p : ℝ × ℝ => A p * B p) vol2 := by
  haveI hpqr : Real.HolderTriple 2 2 1 := holderTriple221
  exact memLp_one_iff_integrable.mp (MemLp.mul' hB hA)

/-- The HS norm is symmetric in the two arguments of the difference. -/
theorem hsNorm_sub_comm {X Y : ℝ × ℝ → ℝ} (hX : HSKernel X) (hY : HSKernel Y) :
    hsNorm (X - Y) = hsNorm (Y - X) := by
  rw [hsNorm_def, hsNorm_def]
  refine congrArg Real.sqrt ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [Pi.sub_apply, sub_sq, sub_sq]
  ring

/-- **Bilinear difference decomposition of `cycle2`**. -/
theorem cycle2_sub_decompose {X X' Y Y' : ℝ × ℝ → ℝ}
    (hX : HSKernel X) (hX' : HSKernel X') (hY : HSKernel Y) (hY' : HSKernel Y') :
    cycle2 X' Y' - cycle2 X Y
      = cycle2 (X' - X) Y' + cycle2 X (Y' - Y) := by
  have hint1 : Integrable (fun p : ℝ × ℝ => X' p * Y' p.swap) vol2 :=
    integrable_hskernel_mul hX' (hsKernel_transpose hY')
  have hint2 : Integrable (fun p : ℝ × ℝ => X p * Y p.swap) vol2 :=
    integrable_hskernel_mul hX (hsKernel_transpose hY)
  have hint3 : Integrable (fun p : ℝ × ℝ => (X' - X) p * Y' p.swap) vol2 :=
    integrable_hskernel_mul (hX'.sub hX) (hsKernel_transpose hY')
  have hint4 : Integrable (fun p : ℝ × ℝ => X p * (Y' - Y) p.swap) vol2 :=
    integrable_hskernel_mul hX (hsKernel_transpose (hY'.sub hY))
  have hpt : ∀ p : ℝ × ℝ,
      X' p * Y' p.swap - X p * Y p.swap
        = (X' - X) p * Y' p.swap + X p * (Y' - Y) p.swap := by
    intro p
    simp only [Pi.sub_apply]
    ring
  calc cycle2 X' Y' - cycle2 X Y
      = ∫ p : ℝ × ℝ, X' p * Y' p.swap - X p * Y p.swap ∂vol2 :=
        (integral_sub hint1 hint2).symm
    _ = ∫ p : ℝ × ℝ, (X' - X) p * Y' p.swap + X p * (Y' - Y) p.swap ∂vol2 :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = (∫ p : ℝ × ℝ, (X' - X) p * Y' p.swap ∂vol2)
          + ∫ p : ℝ × ℝ, X p * (Y' - Y) p.swap ∂vol2 :=
        integral_add hint3 hint4
    _ = cycle2 (X' - X) Y' + cycle2 X (Y' - Y) := rfl

/-- **Absolute bilinear Lipschitz bound for `cycle2` differences**. -/
theorem abs_cycle2_sub_le {X X' Y Y' : ℝ × ℝ → ℝ}
    (hX : HSKernel X) (hX' : HSKernel X') (hY : HSKernel Y) (hY' : HSKernel Y') :
    |cycle2 X' Y' - cycle2 X Y|
      ≤ hsNorm (X' - X) * hsNorm Y' + hsNorm X * hsNorm (Y' - Y) := by
  rw [cycle2_sub_decompose hX hX' hY hY']
  refine le_trans ((AbsoluteValue.add_le AbsoluteValue.abs) _ _)
    (add_le_add (cycle2_bound (hX'.sub hX) hY') (cycle2_bound hX (hY'.sub hY)))

/-- **The k-power diagonal sum of a kernel operator is the `cycle2` pairing of
the tower with the top** (Section 4d per-kernel identity):
`∑' i, ⟪((TOp C)^k)(e i), e i⟫ = cycle2 (compPowR (k−2) C) C`. -/
theorem diagTsum_pow_eq_cycle2 {C : ℝ × ℝ → ℝ} (hCm : Measurable C)
    (hC : HSKernel C) (e : HilbertBasis ℕ ℝ L2) (k : ℕ) (hk : 2 ≤ k) :
    (∑' i : ℕ, inner ℝ ((TOp C hC ^ k) (e i)) (e i))
      = cycle2 (compPowR (k - 2) C) C := by
  have hCL : HSKernel (compPowR (k - 2) C) := hsKernel_compPowR (k - 2) hCm hC
  have hfam : ∀ i : ℕ,
      inner ℝ ((TOp C hC ^ k) (e i)) (e i)
        = inner ℝ (TOp C hC (TOp (compPowR (k - 2) C) hCL (e i))) (e i) := by
    intro i
    rw [← TOpEnd'_pow_apply hC k (e i), ← hPair_uniform hCm hC k hk (e i)]
  calc (∑' i : ℕ, inner ℝ ((TOp C hC ^ k) (e i)) (e i))
      = ∑' i : ℕ, inner ℝ (TOp C hC (TOp (compPowR (k - 2) C) hCL (e i))) (e i) :=
        tsum_congr fun i => hfam i
    _ = cycle2 (compPowR (k - 2) C) C := tracePair_comp_tsum hC hCL e

/-- **Section 4d master (kernel-side power-diagonal convergence)**: along any
exhausting sequence of truncation sets, the `k`-power diagonal sums of the
kernel operators of the weighted truncated kernels converge to that of the
weighted Riesz kernel operator. -/
theorem diagTsum_pow_weightedTrunc_tendsto {psi c : ℝ} (hpsi0 : 0 ≤ psi)
    (hpsi2 : 2 * psi < 1) {omega : ℝ → ℝ} (hm : Measurable omega) {MR : ℝ}
    (hbdd : ∀ x : ℝ, |omega x| ≤ MR)
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hv : Orthonormal ℝ v)
    (he : ∀ i, TOp (unweightedRieszKernel psi c)
        (hsKernel_unweightedRieszKernel hpsi0 hpsi2) (v i) = κ i • v i)
    (hcomp : (span ℝ (Set.range v))ᗮ = ⊥)
    (hgae : ∀ i, (g i) =ᵐ[vol] (⇑(v i))) (hgLp : ∀ i, MemLp (g i) 2 vol)
    (hgm : ∀ i, Measurable (g i)) (hκ : Summable (fun i => κ i ^ 2))
    (e : HilbertBasis ℕ ℝ L2) (k : ℕ) (hk : 2 ≤ k)
    (s : ℕ → Finset ι) (hex : ∀ i, κ i ≠ 0 → ∃ N₀ : ℕ, ∀ N ≥ N₀, i ∈ s N) :
    Filter.Tendsto (fun N : ℕ =>
      ∑' i : ℕ, inner ℝ
        ((TOp (fun p => omega p.1 * truncKernel g κ (s N) p)
          (hSKernel_weight_mul (hSKernel_truncKernel hgLp (s N)) hm hbdd) ^ k)
          (e i)) (e i))
      Filter.atTop
      (nhds (∑' i : ℕ, inner ℝ
        ((TOp (rieszKernel psi c omega) (hsKernel_rieszKernel hpow hm hbdd hg)
          ^ k) (e i)) (e i))) := by
  classical
  have hMR0 : (0:ℝ) ≤ MR := le_trans (abs_nonneg (omega 0)) (hbdd 0)
  have hKR : HSKernel (unweightedRieszKernel psi c) :=
    hsKernel_unweightedRieszKernel hpsi0 hpsi2
  have hKN : ∀ N, HSKernel (truncKernel g κ (s N)) := fun N =>
    hSKernel_truncKernel hgLp (s N)
  have hCN : ∀ N, HSKernel (fun p => omega p.1 * truncKernel g κ (s N) p) :=
    fun N => hSKernel_weight_mul (hKN N) hm hbdd
  have hCNm : ∀ N, Measurable (fun p => omega p.1 * truncKernel g κ (s N) p) :=
    fun N => measurable_weightedTruncKernel hgm omega hm (s N)
  set CR : ℝ × ℝ → ℝ :=
    fun p => omega p.1 * unweightedRieszKernel psi c p with hCRdef
  have hCR : HSKernel CR := hSKernel_weight_mul hKR hm hbdd
  have hCRm : Measurable CR :=
    (hm.comp measurable_fst).mul (measurable_unweightedRieszKernel psi c)
  -- the uniform tail bound
  set B : ℝ := Real.sqrt (∑' i, κ i ^ 2) with hBdef
  have hB0 : (0:ℝ) ≤ B := Real.sqrt_nonneg _
  have hδ : ∀ N, hsNorm (unweightedRieszKernel psi c
      - truncKernel g κ (s N)) ≤ B := by
    intro N
    have hmain := hsNorm_sub_truncKernel_sq_eq_tail hpsi0 hpsi2 hv he hcomp
      hgae hgLp hκ (s N)
    rw [hsNorm_def, Real.sq_sqrt (integral_nonneg fun p => sq_nonneg _)] at hmain
    have hind : ∀ i : ι, (((s N : Set ι))ᶜ).indicator (fun i => κ i ^ 2) i
        ≤ κ i ^ 2 := by
      intro i
      by_cases hi : i ∈ ((s N : Set ι))ᶜ
      · rw [Set.indicator_of_mem hi]
      · rw [Set.indicator_of_notMem hi]
        exact sq_nonneg (κ i)
    have htaille : (∑' i, (((s N : Set ι))ᶜ).indicator (fun i => κ i ^ 2) i)
        ≤ ∑' i, κ i ^ 2 :=
      Summable.tsum_le_tsum hind
        (summable_indicator (fun i => sq_nonneg (κ i)) hκ _) hκ
    rw [hsNorm_def, hmain]
    exact Real.sqrt_le_sqrt htaille
  have hδ0 := hsNorm_sub_truncKernel_tendsto_zero hpsi0 hpsi2 hv he hcomp hgae
    hgLp hκ s hex
  -- the uniform norm bounds
  set A : ℝ := hsNorm (unweightedRieszKernel psi c) with hAdef
  have hA0 : (0:ℝ) ≤ A := hsNorm_nonneg _
  have hsumkn : ∀ N, truncKernel g κ (s N)
      = (truncKernel g κ (s N) - unweightedRieszKernel psi c)
          + unweightedRieszKernel psi c := by
    intro N
    funext p
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  have hKNle : ∀ N, hsNorm (truncKernel g κ (s N)) ≤ 2 * (B + A) := by
    intro N
    have h1 := hsNorm_add_le2 ((hKN N).sub hKR) hKR
    rw [← hsumkn N, hsNorm_sub_comm (hKN N) hKR] at h1
    calc hsNorm (truncKernel g κ (s N))
        ≤ 2 * (hsNorm (unweightedRieszKernel psi c - truncKernel g κ (s N)) + A) :=
          h1
      _ ≤ 2 * (B + A) :=
          mul_le_mul_of_nonneg_left (add_le_add (hδ N) le_rfl) (by norm_num)
  set Mc : ℝ := MR * (2 * (B + A)) with hMcdef
  have hMc0 : (0:ℝ) ≤ Mc := mul_nonneg hMR0 (by positivity)
  have hCNle : ∀ N, hsNorm (fun p => omega p.1 * truncKernel g κ (s N) p)
      ≤ Mc := by
    intro N
    exact le_trans (hsNorm_weight_mul_le (hKN N) hbdd)
      (mul_le_mul_of_nonneg_left (hKNle N) hMR0)
  have hCRle : hsNorm CR ≤ Mc := by
    refine le_trans (hsNorm_weight_mul_le hKR hbdd) ?_
    have hBA : A ≤ 2 * (B + A) := by nlinarith [hA0, hB0]
    exact mul_le_mul_of_nonneg_left hBA hMR0
  -- the weighted difference control
  have hδW : ∀ N, hsNorm ((fun p => omega p.1 * truncKernel g κ (s N) p) - CR)
      ≤ MR * hsNorm (unweightedRieszKernel psi c - truncKernel g κ (s N)) := by
    intro N
    have h := hsNorm_weight_mul_sub_le (hKN N) hKR hbdd
    rw [hsNorm_sub_comm (hKN N) hKR] at h
    have hfun : ((fun p : ℝ × ℝ => omega p.1 * truncKernel g κ (s N) p) - CR)
        = fun p : ℝ × ℝ => omega p.1 * truncKernel g κ (s N) p
            - omega p.1 * unweightedRieszKernel psi c p := rfl
    rw [hfun]
    exact h
  -- the per-N key bound
  set m := k - 2 with hmdef
  have hkm : k = m + 2 := by rw [hmdef]; omega
  set Rk : ℝ := MR * ((2 ^ (m + 1) * ((m : ℝ) + 1) * Mc ^ m * Mc)
    + Mc ^ (m + 1)) with hRkdef
  have hkey : ∀ N : ℕ, |(∑' i : ℕ, inner ℝ
        ((TOp (fun p => omega p.1 * truncKernel g κ (s N) p) (hCN N) ^ k) (e i)) (e i))
      - (∑' i : ℕ, inner ℝ ((TOp CR hCR ^ k) (e i)) (e i))|
      ≤ Rk * hsNorm (unweightedRieszKernel psi c - truncKernel g κ (s N)) := by
    intro N
    have hL := diagTsum_pow_eq_cycle2 (hCNm N) (hCN N) e k hk
    have hRdiag := diagTsum_pow_eq_cycle2 hCRm hCR e k hk
    rw [hL, hRdiag]
    have hab := abs_cycle2_sub_le
      (hsKernel_compPowR m hCRm hCR) (hsKernel_compPowR m (hCNm N) (hCN N))
      hCR (hCN N)
    have h1 : hsNorm (compPowR m ((fun p : ℝ × ℝ => omega p.1
          * truncKernel g κ (s N) p)) - compPowR m CR)
        ≤ 2 ^ (m + 1) * ((m : ℝ) + 1) * Mc ^ m
          * (MR * hsNorm (unweightedRieszKernel psi c - truncKernel g κ (s N))) :=
      hsNorm_compPowR_sub_le (hCNm N) hCRm (hCN N) hCR (hCNle N) hCRle
        (hδW N) m
    have h2 : hsNorm (compPowR m CR) ≤ Mc ^ (m + 1) :=
      le_trans (hsNorm_compPowR_le m hCRm hCR)
        (pow_le_pow_left₀ (hsNorm_nonneg _) hCRle (m + 1))
    have h3 : hsNorm ((fun p : ℝ × ℝ => omega p.1 * truncKernel g κ (s N) p) - CR)
        ≤ MR * hsNorm (unweightedRieszKernel psi c - truncKernel g κ (s N)) :=
      hδW N
    have hnd : (0:ℝ) ≤ hsNorm (unweightedRieszKernel psi c
      - truncKernel g κ (s N)) := hsNorm_nonneg _
    have hzA : (0:ℝ) ≤ 2 ^ (m + 1) * ((m : ℝ) + 1) * Mc ^ m
      * (MR * hsNorm (unweightedRieszKernel psi c - truncKernel g κ (s N))) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity))
        (pow_nonneg hMc0 _)) (mul_nonneg hMR0 hnd)
    have hzB : (0:ℝ) ≤ MR * hsNorm (unweightedRieszKernel psi c
      - truncKernel g κ (s N)) := mul_nonneg hMR0 hnd
    have hzM : (0:ℝ) ≤ Mc ^ (m + 1) := pow_nonneg hMc0 _
    have hP : hsNorm (compPowR m ((fun p : ℝ × ℝ => omega p.1
          * truncKernel g κ (s N) p)) - compPowR m CR)
          * hsNorm ((fun p : ℝ × ℝ => omega p.1 * truncKernel g κ (s N) p))
        ≤ (2 ^ (m + 1) * ((m : ℝ) + 1) * Mc ^ m
            * (MR * hsNorm (unweightedRieszKernel psi c - truncKernel g κ (s N)))) * Mc :=
      le_trans (mul_le_mul_of_nonneg_right h1 (hsNorm_nonneg _))
        (mul_le_mul_of_nonneg_left (hCNle N) hzA)
    have hQ : hsNorm (compPowR m CR)
          * hsNorm ((fun p : ℝ × ℝ => omega p.1 * truncKernel g κ (s N) p) - CR)
        ≤ Mc ^ (m + 1)
          * (MR * hsNorm (unweightedRieszKernel psi c - truncKernel g κ (s N))) :=
      le_trans (mul_le_mul_of_nonneg_left h3 (hsNorm_nonneg _))
        (mul_le_mul_of_nonneg_right h2 hzB)
    refine le_trans hab (le_trans (add_le_add hP hQ) ?_)
    refine le_of_eq ?_
    rw [hRkdef]
    ring
  -- the operator bridge to the Riesz kernel
  have hop : TOp CR hCR
      = TOp (rieszKernel psi c omega) (hsKernel_rieszKernel hpow hm hbdd hg) :=
    TOp_congr_ae hCR _ weightedKernel_ae_rieszKernel
  have hL2 : (∑' i : ℕ, inner ℝ ((TOp CR hCR ^ k) (e i)) (e i))
      = (∑' i : ℕ, inner ℝ
          ((TOp (rieszKernel psi c omega) (hsKernel_rieszKernel hpow hm hbdd hg)
            ^ k) (e i)) (e i)) :=
    tsum_congr fun i => by rw [congrArg (fun X : L2 →L[ℝ] L2 => X ^ k) hop]
  -- assemble the squeeze
  have habs : ∀ N : ℕ, |(fun N : ℕ =>
        ∑' i : ℕ, inner ℝ
          ((TOp (fun p => omega p.1 * truncKernel g κ (s N) p)
            (hSKernel_weight_mul (hSKernel_truncKernel hgLp (s N)) hm hbdd) ^ k)
          (e i)) (e i)
        - ∑' i : ℕ, inner ℝ
          ((TOp (rieszKernel psi c omega) (hsKernel_rieszKernel hpow hm hbdd hg)
            ^ k) (e i)) (e i)) N|
      ≤ Rk * hsNorm (unweightedRieszKernel psi c - truncKernel g κ (s N)) := by
    intro N
    have hkeyN := hkey N
    rw [hL2] at hkeyN
    exact hkeyN
  have hRkδ : Filter.Tendsto (fun N : ℕ => Rk * hsNorm
      (unweightedRieszKernel psi c - truncKernel g κ (s N))) Filter.atTop (nhds 0) := by
    have h := Filter.Tendsto.const_mul Rk hδ0
    rw [mul_zero] at h
    exact h
  have habs : ∀ N : ℕ, |(fun N : ℕ =>
        ∑' i : ℕ, inner ℝ
          ((TOp (fun p => omega p.1 * truncKernel g κ (s N) p)
            (hSKernel_weight_mul (hSKernel_truncKernel hgLp (s N)) hm hbdd) ^ k)
          (e i)) (e i)
        - ∑' i : ℕ, inner ℝ
          ((TOp (rieszKernel psi c omega) (hsKernel_rieszKernel hpow hm hbdd hg)
            ^ k) (e i)) (e i)) N|
      ≤ Rk * hsNorm (unweightedRieszKernel psi c - truncKernel g κ (s N)) := by
    intro N
    have hkeyN := hkey N
    rw [hL2] at hkeyN
    exact hkeyN
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [Metric.tendsto_nhds.mp hRkδ (ε / max Rk 1)
      (by positivity)] with N hN
  rw [dist_eq]
  refine lt_of_le_of_lt (habs N) ?_
  have hmax1 : (1:ℝ) ≤ max Rk 1 := le_max_right _ _
  calc Rk * hsNorm (unweightedRieszKernel psi c - truncKernel g κ (s N))
      ≤ |Rk * hsNorm (unweightedRieszKernel psi c - truncKernel g κ (s N))| :=
        le_abs_self _
    _ = dist (Rk * hsNorm (unweightedRieszKernel psi c - truncKernel g κ (s N))) 0 :=
        by rw [dist_eq, sub_zero]
    _ < ε / max Rk 1 := hN
    _ ≤ ε := div_le_self hε.le hmax1

end PowerDiag

/-! ### Section 5a: column-square sums as matrix double sums

The A4 diagonal-ℓ² supply: over a Hilbert basis, the sum of the squared column
norms of an operator equals its matrix-square double sum (with summability
transport).  Also the self-adjointness and matrix packages of the truncated
model `B_t` (the Section 3a finite-rank decomposition of `S_t ∘ (W ∘ S_t)`). -/

section ColumnSquares

open scoped Classical

variable {ι : Type} {v : ι → L2} {κ : ι → ℝ} {g : ι → ℝ → ℝ}

/-- **Column-square sums are matrix double sums** (summability and equality):
`∑' i, ‖Z (e i)‖ ^ 2 = ∑'_{p : ℕ²} ⟪e p.1, Z (e p.2)⟫ ^ 2` for every
self-adjoint operator whose matrix-square family is summable (the A4
diagonal-ℓ² supply). -/
theorem summable_normSq_apply_and_eq (Z : L2 →L[ℝ] L2)
    (hZsym : (↑Z : L2 →ₗ[ℝ] L2).IsSymmetric) (e : HilbertBasis ℕ ℝ L2)
    (hS : Summable (fun p : ℕ × ℕ => (inner ℝ (e p.1) (Z (e p.2))) ^ 2)) :
    Summable (fun i : ℕ => ‖Z (e i)‖ ^ 2)
      ∧ (∑' i : ℕ, ‖Z (e i)‖ ^ 2)
        = ∑' p : ℕ × ℕ, (inner ℝ (e p.1) (Z (e p.2))) ^ 2 := by
  classical
  -- Bessel/Parseval data along `e`
  have pee : ∀ u : L2, ‖u‖ ^ 2 = ∑' i : ℕ, inner ℝ (e i) u ^ 2 := fun u =>
    (tsum_inner_sq_hilbertBasis_eq_norm_sq e u).symm
  -- the swapped double family and its fibers
  have hswap : Summable (fun p : ℕ × ℕ =>
      inner ℝ (e p.2) (Z (e p.1)) ^ 2) := by
    have h2 : Summable ((fun p : ℕ × ℕ => (inner ℝ (e p.1) (Z (e p.2))) ^ 2)
        ∘ (Equiv.prodComm ℕ ℕ)) := Equiv.summable_iff (Equiv.prodComm ℕ ℕ) |>.mpr hS
    exact h2.congr fun p => rfl
  have hDfibswap : ∀ b : ℕ, Summable (fun c : ℕ =>
      inner ℝ (e c) (Z (e b)) ^ 2) := fun b =>
    (summable_inner_sq_of_hilbertBasis e (Z (e b))).congr fun c => by
      rw [real_inner_comm]
  -- the self-adjoint flip
  have hflipE : ∀ p : ℕ × ℕ,
      inner ℝ (e p.2) (Z (e p.1)) = inner ℝ (e p.1) (Z (e p.2)) := by
    intro p
    calc inner ℝ (e p.2) (Z (e p.1))
        = inner ℝ (Z (e p.1)) (e p.2) := (real_inner_comm (e p.2) (Z (e p.1))).symm
      _ = inner ℝ (e p.1) (Z (e p.2)) := hZsym (e p.1) (e p.2)
  -- the column family equals the fiber-sum family of the swapped matrix
  have hrow : Summable (fun i : ℕ =>
      ∑' c : ℕ, inner ℝ (e (i, c).2) (Z (e (i, c).1)) ^ 2) :=
    Summable.prod hswap
  refine ⟨hrow.congr (fun i => by
      show ∑' c : ℕ, inner ℝ (e c) (Z (e i)) ^ 2 = ‖Z (e i)‖ ^ 2
      rw [pee (Z (e i))]), ?_⟩
  calc (∑' i : ℕ, ‖Z (e i)‖ ^ 2)
      = ∑' i : ℕ, ∑' c : ℕ, inner ℝ (e c) (Z (e i)) ^ 2 :=
        tsum_congr fun i => pee (Z (e i))
    _ = ∑' p : ℕ × ℕ, inner ℝ (e p.2) (Z (e p.1)) ^ 2 :=
          (Summable.tsum_prod' hswap hDfibswap).symm
    _ = ∑' p : ℕ × ℕ, inner ℝ (e p.1) (Z (e p.2)) ^ 2 :=
          tsum_congr fun p => by rw [hflipE p]

/-- **Self-adjointness of the truncated model** `B_t = S_t ∘L M_omega ∘L S_t`
(composition of the three self-adjoint operators). -/
theorem BtruncOp_symm (hκ0 : ∀ i, 0 ≤ κ i) {C : ℝ} (hC : ∀ i, |κ i| ≤ C)
    (t : Finset ι) (hv : Orthonormal ℝ v)
    (omega : ℝ → ℝ) (hm : Measurable omega) {MR : ℝ}
    (hess : ∀ᵐ x ∂vol, |omega x| ≤ MR) :
    (↑(BtruncOp hC t hv omega hm hess) : L2 →ₗ[ℝ] L2).IsSymmetric := by
  intro x y
  have hSt := specOperator_symm (abs_truncSqrtCoeff_le hC t)
    (Real.sqrt_nonneg C) hv
  have hW := mulOperator_symm omega hm hess
  show inner ℝ (sqrtTruncOp hC t hv (mulOperator omega hm hess
        (sqrtTruncOp hC t hv x))) y
      = inner ℝ x (sqrtTruncOp hC t hv (mulOperator omega hm hess
          (sqrtTruncOp hC t hv y)))
  calc inner ℝ (sqrtTruncOp hC t hv (mulOperator omega hm hess
          (sqrtTruncOp hC t hv x))) y
      = inner ℝ (mulOperator omega hm hess (sqrtTruncOp hC t hv x))
          (sqrtTruncOp hC t hv y) := hSt _ _
    _ = inner ℝ (sqrtTruncOp hC t hv x)
          (mulOperator omega hm hess (sqrtTruncOp hC t hv y)) := hW _ _
    _ = inner ℝ x (sqrtTruncOp hC t hv (mulOperator omega hm hess
          (sqrtTruncOp hC t hv y))) := hSt x _

/-- **The truncated model carries a matrix-square package over every Hilbert
basis** (finite rank: the Section 3a decomposition of `S_t ∘ (W ∘ S_t)`; the
bound `CAt` is the one produced by `matrixSq_summable_of_decomp`). -/
theorem BtruncOp_matrixSq_summable {C : ℝ} (hC : ∀ i, |κ i| ≤ C)
    (t : Finset ι) (hv : Orthonormal ℝ v)
    (omega : ℝ → ℝ) (hm : Measurable omega) {MR : ℝ}
    (hess : ∀ᵐ x ∂vol, |omega x| ≤ MR) (e : HilbertBasis ℕ ℝ L2) :
    ∃ CAt : ℝ, 0 ≤ CAt ∧ Summable (fun p : ℕ × ℕ =>
        (inner ℝ (e p.1) (BtruncOp hC t hv omega hm hess (e p.2))) ^ 2)
      ∧ (∑' p : ℕ × ℕ,
          (inner ℝ (e p.1) (BtruncOp hC t hv omega hm hess (e p.2))) ^ 2) ≤ CAt := by
  -- the finite action formula for `S_t`
  have hSfin : ∀ x : L2, sqrtTruncOp hC t hv x
      = ∑ i ∈ t, (truncSqrtCoeff κ t i * inner ℝ (v i) x) • (v i) := by
    intro x
    rw [show sqrtTruncOp hC t hv
        = specOperator (c := truncSqrtCoeff κ t) (abs_truncSqrtCoeff_le hC t)
          (Real.sqrt_nonneg C) hv from rfl]
    exact specOperator_apply_eq_finset_sum (abs_truncSqrtCoeff_le hC t)
      (Real.sqrt_nonneg C) hv
      (fun i hi => by
        show truncSqrtCoeff κ t i = 0
        rw [show truncSqrtCoeff κ t i = if i ∈ t then Real.sqrt (κ i) else 0 from rfl,
          if_neg hi]) x
  -- the finite rank-one decomposition of `B_t = S_t ∘ (W ∘ S_t)`
  have dSZ : ∀ (Z : L2 →L[ℝ] L2) (x : L2), (sqrtTruncOp hC t hv).comp Z x
      = ∑ i ∈ t, (inner ℝ (Z.adjoint (v i)) x) • ((truncSqrtCoeff κ t i) • (v i)) := by
    intro Z x
    rw [ContinuousLinearMap.comp_apply, hSfin (Z x)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ContinuousLinearMap.adjoint_inner_left Z x (v i), smul_smul,
      mul_comm (truncSqrtCoeff κ t i) (inner ℝ (v i) (Z x))]
  have hdec : ∀ x : L2, BtruncOp hC t hv omega hm hess x
      = ∑ i ∈ t, (inner ℝ (((mulOperator omega hm hess).comp
          (sqrtTruncOp hC t hv)).adjoint (v i)) x)
          • ((truncSqrtCoeff κ t i) • (v i)) := by
    intro x
    calc BtruncOp hC t hv omega hm hess x
        = (sqrtTruncOp hC t hv).comp
            ((mulOperator omega hm hess).comp (sqrtTruncOp hC t hv)) x := rfl
      _ = ∑ i ∈ t, (inner ℝ (((mulOperator omega hm hess).comp
            (sqrtTruncOp hC t hv)).adjoint (v i)) x)
            • ((truncSqrtCoeff κ t i) • (v i)) :=
          dSZ ((mulOperator omega hm hess).comp (sqrtTruncOp hC t hv)) x
  exact matrixSq_summable_of_decomp hdec e

end ColumnSquares

/-! ### Section 5b: operator-norm convergence `S → S_t` and `B → B_t`

The truncated square root approximates the full square root in operator norm
(level-set argument, local copies of the BopCompactness private helpers), and
the convergence transports through `B = S ∘ W ∘ S` vs `B_t = S_t ∘ W ∘ S_t`
with the two-term split `B − B_t = S W (S − S_t) + (S − S_t) W S_t`. -/

section NormConv

open scoped Classical

variable {ι : Type} {v : ι → L2} {κ : ι → ℝ}

/-- An exhausting sequence eventually contains any fixed finite set. -/
private theorem finset_eventually_mem (s : ℕ → Finset ι) (w : Finset ι)
    (hex : ∀ i ∈ w, ∃ N₀ : ℕ, ∀ N ≥ N₀, i ∈ s N) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ i ∈ w, i ∈ s N := by
  classical
  induction w using Finset.induction_on with
  | empty => exact ⟨0, fun N _ i hi => absurd hi (Finset.notMem_empty i)⟩
  | @insert j w hj ih =>
      obtain ⟨N1, hN1⟩ := hex j (Finset.mem_insert_self j w)
      obtain ⟨N2, hN2⟩ := ih (fun i hi => hex i (Finset.mem_insert_of_mem hi))
      refine ⟨max N1 N2, fun N hN i hi => ?_⟩
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hN1 N (le_trans (le_max_left _ _) hN)
      · exact hN2 N (le_trans (le_max_right _ _) hN) i hi

/-- Local copy of the BopCompactness private helper (private lemmas do not
cross files): spectral operators with pointwise-close coefficient families
are norm-close. -/
private theorem norm_specOperator_sub_of_bound' {c₀ c₁ : ι → ℝ} {bnd δ : ℝ}
    (hb0 : ∀ i, |c₀ i| ≤ bnd) (hb1 : ∀ i, |c₁ i| ≤ bnd) (hC0 : 0 ≤ bnd)
    (hv : Orthonormal ℝ v) (hδ : 0 ≤ δ) (hδb : ∀ i, |c₁ i - c₀ i| ≤ δ) :
    ‖specOperator hb1 hC0 hv - specOperator hb0 hC0 hv‖ ≤ δ := by
  have hEq : specOperator hb1 hC0 hv - specOperator hb0 hC0 hv
      = specOperator hδb hδ hv := by
    refine ContinuousLinearMap.ext fun x => eq_of_forall_inner_eq fun y => ?_
    rw [_root_.sub_apply, inner_sub_left, inner_specOperator hb1 hC0 hv x y,
      inner_specOperator hb0 hC0 hv x y, inner_specOperator hδb hδ hv x y]
    refine Eq.trans (((summable_specPair hb1 hC0 hv x y).hasSum.sub
      (summable_specPair hb0 hC0 hv x y).hasSum).tsum_eq.symm) ?_
    refine tsum_congr fun i => ?_
    ring
  rw [hEq]
  exact norm_specOperator_le hδb hδ hv

/-- **Norm approximation of the square root**: if the truncation set captures
every index with `κ i ≥ δ ^ 2`, then `‖S − S_t‖ ≤ δ`. -/
theorem norm_sqrtOp_sub_sqrtTruncOp_le {T : L2 →L[ℝ] L2} (hv : Orthonormal ℝ v)
    (he : ∀ i, T (v i) = κ i • v i) (hκ0 : ∀ i, 0 ≤ κ i) (t : Finset ι)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hlev : ∀ i ∉ t, κ i ≤ δ ^ 2) :
    ‖sqrtOp hv he hκ0
        - sqrtTruncOp (fun i => abs_kappa_le_norm hv he i) t hv‖ ≤ δ := by
  have hb0 : ∀ i, |Real.sqrt (κ i)| ≤ Real.sqrt ‖T‖ :=
    fun i => sqrt_kappa_le hv he hκ0 i
  have hb1 : ∀ i, |truncSqrtCoeff κ t i| ≤ Real.sqrt ‖T‖ :=
    abs_truncSqrtCoeff_le (fun i => abs_kappa_le_norm hv he i) t
  have hsub : ∀ i, |Real.sqrt (κ i) - truncSqrtCoeff κ t i| ≤ δ := by
    intro i
    by_cases hi : i ∈ t
    · rw [show truncSqrtCoeff κ t i = if i ∈ t then Real.sqrt (κ i) else 0 from rfl,
        if_pos hi, sub_self, abs_zero]
      exact hδ0
    · have hκlt : κ i ≤ δ ^ 2 := hlev i hi
      have hs : Real.sqrt (κ i) ≤ δ := by
        rw [← Real.sqrt_sq hδ0]
        exact Real.sqrt_le_sqrt hκlt
      rw [show truncSqrtCoeff κ t i = if i ∈ t then Real.sqrt (κ i) else 0 from rfl,
        if_neg hi, sub_zero, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact hs
  rw [show sqrtOp hv he hκ0 = specOperator (c := fun i => Real.sqrt (κ i)) hb0
      (Real.sqrt_nonneg ‖T‖) hv from rfl,
    show sqrtTruncOp (fun i => abs_kappa_le_norm hv he i) t hv
        = specOperator (c := truncSqrtCoeff κ t) hb1 (Real.sqrt_nonneg ‖T‖) hv
      from rfl]
  exact norm_specOperator_sub_of_bound' hb1 hb0 (Real.sqrt_nonneg ‖T‖) hv hδ0 hsub

/-- **The square-root truncations converge in operator norm** along any
exhausting sequence. -/
theorem norm_sqrtOp_sub_sqrtTruncOp_tendsto_zero {T : L2 →L[ℝ] L2}
    (hv : Orthonormal ℝ v) (he : ∀ i, T (v i) = κ i • v i) (hκ0 : ∀ i, 0 ≤ κ i)
    (hκ : Summable (fun i => κ i ^ 2)) (s : ℕ → Finset ι)
    (hex : ∀ i, κ i ≠ 0 → ∃ N₀ : ℕ, ∀ N ≥ N₀, i ∈ s N) :
    Filter.Tendsto (fun N : ℕ =>
      ‖sqrtOp hv he hκ0
        - sqrtTruncOp (fun i => abs_kappa_le_norm hv he i) (s N) hv‖)
      Filter.atTop (nhds 0) := by
  classical
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hfin : {i : ι | (ε / 2) ^ 2 ≤ κ i}.Finite := by
    have h1 : {i : ι | (ε / 2) ^ 2 ≤ κ i}
        ⊆ {i : ι | (ε / 2) ^ 4 ≤ κ i ^ 2} := by
      intro i hi
      simp only [Set.mem_setOf_eq] at hi ⊢
      have habs : |(ε / 2) ^ 2| ≤ |κ i| := by
        rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (ε / 2) ^ 2),
          abs_of_nonneg (hκ0 i)]
        exact hi
      calc (ε / 2) ^ 4 = ((ε / 2) ^ 2) ^ 2 := by ring
        _ ≤ (κ i) ^ 2 := sq_le_sq.mpr habs
    exact Set.Finite.subset
      (levelSet_finite (fun i => sq_nonneg (κ i)) hκ (by positivity)) h1
  obtain ⟨N₀, hN₀⟩ := finset_eventually_mem (fun N => s N) hfin.toFinset
    (fun i hi => hex i (fun hc => by
      have himem : (ε / 2) ^ 2 ≤ κ i := by
        simpa only [Set.mem_setOf_eq] using hfin.mem_toFinset.mp hi
      have h1 : (0:ℝ) < (ε / 2) ^ 2 := by positivity
      rw [hc] at himem
      exact absurd (h1.trans_le himem) (lt_irrefl 0)))
  refine Filter.eventually_atTop.mpr ⟨N₀, fun N hN => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  refine lt_of_le_of_lt (norm_sqrtOp_sub_sqrtTruncOp_le hv he hκ0 (s N)
    (δ := ε / 2) (by positivity) ?_) (by linarith)
  intro i hiN
  have hlt : κ i < (ε / 2) ^ 2 := by
    refine lt_of_not_ge (fun hc => hiN (hN₀ N hN i (hfin.mem_toFinset.mpr hc)))
  exact le_of_lt hlt

/-- **The two-term split of the model difference**: `B − B_t
= S W (S − S_t) + (S − S_t) W S_t`. -/
theorem Bop_sub_BtruncOp_eq {T : L2 →L[ℝ] L2} (hv : Orthonormal ℝ v)
    (he : ∀ i, T (v i) = κ i • v i) (hκ0 : ∀ i, 0 ≤ κ i) (t : Finset ι)
    (omega : ℝ → ℝ) (hm : Measurable omega) {MR : ℝ}
    (hess : ∀ᵐ x ∂vol, |omega x| ≤ MR) :
    Bop hv he hκ0 omega hm hess
        - BtruncOp (fun i => abs_kappa_le_norm hv he i) t hv omega hm hess
      = (sqrtOp hv he hκ0).comp
          ((mulOperator omega hm hess).comp
            (sqrtOp hv he hκ0
              - sqrtTruncOp (fun i => abs_kappa_le_norm hv he i) t hv))
        + (sqrtOp hv he hκ0
              - sqrtTruncOp (fun i => abs_kappa_le_norm hv he i) t hv).comp
            ((mulOperator omega hm hess).comp
              (sqrtTruncOp (fun i => abs_kappa_le_norm hv he i) t hv)) := by
  classical
  refine ContinuousLinearMap.ext fun x => ?_
  set S := sqrtOp hv he hκ0 with hSdef
  set St := sqrtTruncOp (fun i => abs_kappa_le_norm hv he i) t hv with hStdef
  set W := mulOperator omega hm hess with hWdef
  have e1 : (S.comp (W.comp (S - St))) x = S (W (S x)) - S (W (St x)) := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      _root_.sub_apply, map_sub, map_sub]
  have e2 : ((S - St).comp (W.comp St)) x = S (W (St x)) - St (W (St x)) := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      _root_.sub_apply]
  have e3 : Bop hv he hκ0 omega hm hess x = S (W (S x)) := rfl
  have e4 : BtruncOp (fun i => abs_kappa_le_norm hv he i) t hv omega hm hess x
      = St (W (St x)) := rfl
  rw [_root_.sub_apply, _root_.add_apply, e3, e4, e1, e2]
  abel

/-- **Norm control of the model difference**: `‖B − B_t‖` is at most
`2 · √‖T‖ · MR · ‖S − S_t‖`. -/
theorem norm_Bop_sub_BtruncOp_le {T : L2 →L[ℝ] L2} (hv : Orthonormal ℝ v)
    (he : ∀ i, T (v i) = κ i • v i) (hκ0 : ∀ i, 0 ≤ κ i) (t : Finset ι)
    (omega : ℝ → ℝ) (hm : Measurable omega) {MR : ℝ}
    (hess : ∀ᵐ x ∂vol, |omega x| ≤ MR) :
    ‖Bop hv he hκ0 omega hm hess
        - BtruncOp (fun i => abs_kappa_le_norm hv he i) t hv omega hm hess‖
      ≤ 2 * (Real.sqrt ‖T‖ * MR)
          * ‖sqrtOp hv he hκ0
              - sqrtTruncOp (fun i => abs_kappa_le_norm hv he i) t hv‖ := by
  have hWn : ‖mulOperator omega hm hess‖ ≤ MR := norm_mulOperator_le omega hm hess
  have hrn : (0:ℝ) ≤ Real.sqrt ‖T‖ := Real.sqrt_nonneg _
  have hSn : ‖sqrtOp hv he hκ0‖ ≤ Real.sqrt ‖T‖ := by
    rw [show sqrtOp hv he hκ0 = specOperator (c := fun i => Real.sqrt (κ i))
        (fun i => sqrt_kappa_le hv he hκ0 i) (Real.sqrt_nonneg ‖T‖) hv from rfl]
    exact norm_specOperator_le (fun i => sqrt_kappa_le hv he hκ0 i)
      (Real.sqrt_nonneg ‖T‖) hv
  have hStn : ‖sqrtTruncOp (fun i => abs_kappa_le_norm hv he i) t hv‖
      ≤ Real.sqrt ‖T‖ := by
    rw [show sqrtTruncOp (fun i => abs_kappa_le_norm hv he i) t hv
        = specOperator (c := truncSqrtCoeff κ t)
          (abs_truncSqrtCoeff_le (fun i => abs_kappa_le_norm hv he i) t)
          (Real.sqrt_nonneg ‖T‖) hv from rfl]
    exact norm_specOperator_le
      (abs_truncSqrtCoeff_le (fun i => abs_kappa_le_norm hv he i) t)
      (Real.sqrt_nonneg ‖T‖) hv
  have hsplit := Bop_sub_BtruncOp_eq hv he hκ0 t omega hm hess
  have hd0 : (0:ℝ) ≤ ‖sqrtOp hv he hκ0
      - sqrtTruncOp (fun i => abs_kappa_le_norm hv he i) t hv‖ := norm_nonneg _
  calc ‖Bop hv he hκ0 omega hm hess
        - BtruncOp (fun i => abs_kappa_le_norm hv he i) t hv omega hm hess‖
      = ‖(sqrtOp hv he hκ0).comp
          ((mulOperator omega hm hess).comp
            (sqrtOp hv he hκ0
              - sqrtTruncOp (fun i => abs_kappa_le_norm hv he i) t hv))
        + (sqrtOp hv he hκ0
              - sqrtTruncOp (fun i => abs_kappa_le_norm hv he i) t hv).comp
            ((mulOperator omega hm hess).comp
              (sqrtTruncOp (fun i => abs_kappa_le_norm hv he i) t hv))‖ := by
        rw [hsplit]
    _ ≤ ‖(sqrtOp hv he hκ0).comp
          ((mulOperator omega hm hess).comp
            (sqrtOp hv he hκ0
              - sqrtTruncOp (fun i => abs_kappa_le_norm hv he i) t hv))‖
        + ‖(sqrtOp hv he hκ0
              - sqrtTruncOp (fun i => abs_kappa_le_norm hv he i) t hv).comp
            ((mulOperator omega hm hess).comp
              (sqrtTruncOp (fun i => abs_kappa_le_norm hv he i) t hv))‖ :=
          norm_add_le _ _
    _ ≤ Real.sqrt ‖T‖ * (MR * ‖sqrtOp hv he hκ0
          - sqrtTruncOp (fun i => abs_kappa_le_norm hv he i) t hv‖)
        + ‖sqrtOp hv he hκ0
            - sqrtTruncOp (fun i => abs_kappa_le_norm hv he i) t hv‖
            * (MR * Real.sqrt ‖T‖) := by
          have hMR0 : (0:ℝ) ≤ MR := MR_nonneg hess
          have hWd : ‖mulOperator omega hm hess‖ * ‖sqrtOp hv he hκ0
              - sqrtTruncOp (fun i => abs_kappa_le_norm hv he i) t hv‖
              ≤ MR * ‖sqrtOp hv he hκ0
                - sqrtTruncOp (fun i => abs_kappa_le_norm hv he i) t hv‖ :=
            mul_le_mul_of_nonneg_right hWn hd0
          have hWSt : ‖mulOperator omega hm hess‖
              * ‖sqrtTruncOp (fun i => abs_kappa_le_norm hv he i) t hv‖
              ≤ MR * Real.sqrt ‖T‖ := by
            calc ‖mulOperator omega hm hess‖
                    * ‖sqrtTruncOp (fun i => abs_kappa_le_norm hv he i) t hv‖
                  ≤ MR * ‖sqrtTruncOp (fun i => abs_kappa_le_norm hv he i) t hv‖ :=
                    mul_le_mul_of_nonneg_right hWn (norm_nonneg _)
              _ ≤ MR * Real.sqrt ‖T‖ :=
                    mul_le_mul_of_nonneg_left hStn hMR0
          refine add_le_add ?_ ?_
          · calc ‖(sqrtOp hv he hκ0).comp ((mulOperator omega hm hess).comp
                    (sqrtOp hv he hκ0
                      - sqrtTruncOp (fun i => abs_kappa_le_norm hv he i) t hv))‖
                  ≤ ‖sqrtOp hv he hκ0‖ * ‖(mulOperator omega hm hess).comp
                      (sqrtOp hv he hκ0
                        - sqrtTruncOp (fun i => abs_kappa_le_norm hv he i) t hv)‖ :=
                    ContinuousLinearMap.opNorm_comp_le _ _
                _ ≤ Real.sqrt ‖T‖ * ‖(mulOperator omega hm hess).comp
                      (sqrtOp hv he hκ0
                        - sqrtTruncOp (fun i => abs_kappa_le_norm hv he i) t hv)‖ :=
                    mul_le_mul_of_nonneg_right hSn (norm_nonneg _)
                _ ≤ Real.sqrt ‖T‖ * (‖mulOperator omega hm hess‖ * ‖sqrtOp hv he hκ0
                      - sqrtTruncOp (fun i => abs_kappa_le_norm hv he i) t hv‖) :=
                    mul_le_mul_of_nonneg_left
                      (ContinuousLinearMap.opNorm_comp_le _ _) hrn
                _ ≤ Real.sqrt ‖T‖ * (MR * ‖sqrtOp hv he hκ0
                      - sqrtTruncOp (fun i => abs_kappa_le_norm hv he i) t hv‖) :=
                    mul_le_mul_of_nonneg_left hWd hrn
          · calc ‖(sqrtOp hv he hκ0
                      - sqrtTruncOp (fun i => abs_kappa_le_norm hv he i) t hv).comp
                      ((mulOperator omega hm hess).comp
                        (sqrtTruncOp (fun i => abs_kappa_le_norm hv he i) t hv))‖
                  ≤ ‖sqrtOp hv he hκ0
                      - sqrtTruncOp (fun i => abs_kappa_le_norm hv he i) t hv‖
                      * ‖(mulOperator omega hm hess).comp
                        (sqrtTruncOp (fun i => abs_kappa_le_norm hv he i) t hv)‖ :=
                    ContinuousLinearMap.opNorm_comp_le _ _
                _ ≤ ‖sqrtOp hv he hκ0
                      - sqrtTruncOp (fun i => abs_kappa_le_norm hv he i) t hv‖
                      * (‖mulOperator omega hm hess‖
                        * ‖sqrtTruncOp (fun i => abs_kappa_le_norm hv he i) t hv‖) :=
                    mul_le_mul_of_nonneg_left
                      (ContinuousLinearMap.opNorm_comp_le _ _) hd0
                _ ≤ ‖sqrtOp hv he hκ0
                      - sqrtTruncOp (fun i => abs_kappa_le_norm hv he i) t hv‖
                      * (MR * Real.sqrt ‖T‖) :=
                    mul_le_mul_of_nonneg_left hWSt hd0
    _ = 2 * (Real.sqrt ‖T‖ * MR)
          * ‖sqrtOp hv he hκ0
              - sqrtTruncOp (fun i => abs_kappa_le_norm hv he i) t hv‖ := by
          ring

/-- **The model truncations converge in operator norm** along any exhausting
sequence. -/
theorem norm_Bop_sub_BtruncOp_tendsto_zero {T : L2 →L[ℝ] L2}
    (hv : Orthonormal ℝ v) (he : ∀ i, T (v i) = κ i • v i) (hκ0 : ∀ i, 0 ≤ κ i)
    (hκ : Summable (fun i => κ i ^ 2)) (s : ℕ → Finset ι)
    (hex : ∀ i, κ i ≠ 0 → ∃ N₀ : ℕ, ∀ N ≥ N₀, i ∈ s N)
    (omega : ℝ → ℝ) (hm : Measurable omega) {MR : ℝ}
    (hess : ∀ᵐ x ∂vol, |omega x| ≤ MR) :
    Filter.Tendsto (fun N : ℕ =>
      ‖Bop hv he hκ0 omega hm hess
        - BtruncOp (fun i => abs_kappa_le_norm hv he i) (s N) hv omega hm hess‖)
      Filter.atTop (nhds 0) := by
  have hS := norm_sqrtOp_sub_sqrtTruncOp_tendsto_zero hv he hκ0 hκ s hex
  have hK0 : (0:ℝ) ≤ 2 * (Real.sqrt ‖T‖ * MR) :=
    mul_nonneg (by norm_num)
      (mul_nonneg (Real.sqrt_nonneg _) (MR_nonneg hess))
  have hbound : ∀ N : ℕ, ‖Bop hv he hκ0 omega hm hess
      - BtruncOp (fun i => abs_kappa_le_norm hv he i) (s N) hv omega hm hess‖
      ≤ 2 * (Real.sqrt ‖T‖ * MR)
          * ‖sqrtOp hv he hκ0
              - sqrtTruncOp (fun i => abs_kappa_le_norm hv he i) (s N) hv‖ :=
    fun N => norm_Bop_sub_BtruncOp_le hv he hκ0 (s N) omega hm hess
  have hmul := Filter.Tendsto.const_mul (2 * (Real.sqrt ‖T‖ * MR)) hS
  rw [mul_zero] at hmul
  exact squeeze_zero (fun N => norm_nonneg _) (fun N => hbound N) hmul

end NormConv

/-! ### Section 5c: the diagonal-ℓ² content of `B − B_t` as the A7 matrix tail

The v-matrix squares of `B − B_t` are exactly the complementary indicator of
the A7 matrix family `κ_i κ_j ⟪v_i, W v_j⟫²` over the product truncation set
(the √-coefficient difference collapses since `1 − χ_i χ_j` is idempotent),
and the A7_aux transport plus the basis-invariance of matrix squares identify
the e-basis column-square sum with this tail — which tends to `0` along any
exhausting sequence (Section 2a engine over `ι × ι`). -/

section MatrixTail

open scoped Classical

variable {ι : Type} {v : ι → L2} {κ : ι → ℝ}

/-- **The v-matrix entries of the model difference**: `⟪v i, (B − B_t)(v j)⟫`
is the coefficient-difference multiple of the weight entry. -/
theorem inner_Bop_sub_Btrunc_vmatrix {T : L2 →L[ℝ] L2} (hv : Orthonormal ℝ v)
    (he : ∀ i, T (v i) = κ i • v i) (hκ0 : ∀ i, 0 ≤ κ i) {C : ℝ}
    (hC : ∀ i, |κ i| ≤ C)
    (t : Finset ι) (omega : ℝ → ℝ) (hm : Measurable omega) {MR : ℝ}
    (hess : ∀ᵐ x ∂vol, |omega x| ≤ MR) (i j : ι) :
    inner ℝ (v i)
        ((Bop hv he hκ0 omega hm hess
          - BtruncOp hC t hv omega hm hess) (v j))
      = (Real.sqrt (κ i * κ j) - truncSqrtCoeff κ t i * truncSqrtCoeff κ t j)
          * inner ℝ (v i) (mulOperator omega hm hess (v j)) := by
  rw [_root_.sub_apply, inner_sub_right,
    inner_Bop_matrix hv he hκ0 omega hm hess i j,
    inner_Btrunc_matrix hC t hv omega hm hess i j]
  ring

/-- **The v-matrix squares of the model difference are the indicator tail of
the A7 family** (pointwise; the √-coefficient difference collapses because
`1 − χ_i χ_j` is idempotent). -/
theorem vmatrixSq_BsubBtrunc_eq_indicator {T : L2 →L[ℝ] L2} (hv : Orthonormal ℝ v)
    (he : ∀ i, T (v i) = κ i • v i) (hκ0 : ∀ i, 0 ≤ κ i) {C : ℝ}
    (hC : ∀ i, |κ i| ≤ C)
    (t : Finset ι) (omega : ℝ → ℝ) (hm : Measurable omega) {MR : ℝ}
    (hess : ∀ᵐ x ∂vol, |omega x| ≤ MR) (q : ι × ι) :
    inner ℝ (v q.1)
        ((Bop hv he hκ0 omega hm hess
          - BtruncOp hC t hv omega hm hess) (v q.2)) ^ 2
      = (((t ×ˢ t : Finset (ι × ι)) : Set (ι × ι))ᶜ).indicator
          (fun q => κ q.1 * κ q.2
            * inner ℝ (v q.1) (mulOperator omega hm hess (v q.2)) ^ 2) q := by
  classical
  rw [inner_Bop_sub_Btrunc_vmatrix hv he hκ0 hC t omega hm hess q.1 q.2]
  by_cases h1 : q.1 ∈ t
  · by_cases h2 : q.2 ∈ t
    · rw [show truncSqrtCoeff κ t q.1 = Real.sqrt (κ q.1) from by
          rw [show truncSqrtCoeff κ t q.1 = if q.1 ∈ t then Real.sqrt (κ q.1) else 0
            from rfl, if_pos h1],
        show truncSqrtCoeff κ t q.2 = Real.sqrt (κ q.2) from by
          rw [show truncSqrtCoeff κ t q.2 = if q.2 ∈ t then Real.sqrt (κ q.2) else 0
            from rfl, if_pos h2],
        Real.sqrt_mul (hκ0 q.1) (κ q.2), sub_self, zero_mul,
        zero_pow (by norm_num),
        Set.indicator_of_notMem (fun hc =>
          ((Set.mem_compl_iff _ q).mp hc)
            (Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨h1, h2⟩)))]
    · rw [show truncSqrtCoeff κ t q.2 = 0 from by
          rw [show truncSqrtCoeff κ t q.2 = if q.2 ∈ t then Real.sqrt (κ q.2) else 0
            from rfl, if_neg h2],
        mul_zero, sub_zero, mul_pow,
        Real.sq_sqrt (mul_nonneg (hκ0 q.1) (hκ0 q.2)),
        Set.indicator_of_mem (by
          refine (Set.mem_compl_iff _ q).mpr (fun hc => ?_)
          exact h2 (Finset.mem_product.mp (Finset.mem_coe.mp hc)).2)]
  · rw [show truncSqrtCoeff κ t q.1 = 0 from by
        rw [show truncSqrtCoeff κ t q.1 = if q.1 ∈ t then Real.sqrt (κ q.1) else 0
          from rfl, if_neg h1],
      zero_mul, sub_zero, mul_pow,
      Real.sq_sqrt (mul_nonneg (hκ0 q.1) (hκ0 q.2)),
      Set.indicator_of_mem (by
        refine (Set.mem_compl_iff _ q).mpr (fun hc => ?_)
        exact h1 (Finset.mem_product.mp (Finset.mem_coe.mp hc)).1)]

/-- The A7-family summability in the orientation of the indicator identity. -/
theorem summable_aWfamily (hv : Orthonormal ℝ v)
    (hcomp : (span ℝ (Set.range v))ᗮ = ⊥) (hκ0 : ∀ i, 0 ≤ κ i)
    (hκ : Summable (fun i => κ i ^ 2))
    (omega : ℝ → ℝ) (hm : Measurable omega) {MR : ℝ}
    (hess : ∀ᵐ x ∂vol, |omega x| ≤ MR) :
    Summable (fun q : ι × ι => κ q.1 * κ q.2
      * inner ℝ (v q.1) (mulOperator omega hm hess (v q.2)) ^ 2) := by
  obtain ⟨haW, _⟩ := summable_and_bound_matrix (v := v) hv hcomp hκ0 hκ
    (mulOperator omega hm hess) (mulOperator_symm omega hm hess)
    (norm_mulOperator_apply_le omega hm hess)
  refine haW.congr fun q => ?_
  have hstep : inner ℝ (v q.2) (mulOperator omega hm hess (v q.1))
      = inner ℝ (v q.1) (mulOperator omega hm hess (v q.2)) :=
    (real_inner_comm (mulOperator omega hm hess (v q.1)) (v q.2)).trans
      (mulOperator_symm omega hm hess (v q.1) (v q.2))
  show κ q.1 * κ q.2 * inner ℝ (v q.2) (mulOperator omega hm hess (v q.1)) ^ 2
      = κ q.1 * κ q.2 * inner ℝ (v q.1) (mulOperator omega hm hess (v q.2)) ^ 2
  rw [hstep]

/-- **The e-basis matrix squares of the model difference are summable**
(A7_aux transport from the v-side; uniform bound `MR² ∑' κ²`). -/
theorem eMatrixSummable_BsubBtrunc {T : L2 →L[ℝ] L2} (hv : Orthonormal ℝ v)
    (he : ∀ i, T (v i) = κ i • v i) (hκ0 : ∀ i, 0 ≤ κ i)
    (hκ : Summable (fun i => κ i ^ 2)) (hcomp : (span ℝ (Set.range v))ᗮ = ⊥)
    {C : ℝ} (hC : ∀ i, |κ i| ≤ C)
    (t : Finset ι) (omega : ℝ → ℝ) (hm : Measurable omega) {MR : ℝ}
    (hess : ∀ᵐ x ∂vol, |omega x| ≤ MR) (e : HilbertBasis ℕ ℝ L2) :
    Summable (fun p : ℕ × ℕ => inner ℝ (e p.1)
        ((Bop hv he hκ0 omega hm hess
          - BtruncOp hC t hv omega hm hess) (e p.2)) ^ 2) := by
  classical
  set Z : L2 →L[ℝ] L2 := Bop hv he hκ0 omega hm hess
    - BtruncOp hC t hv omega hm hess with hZdef
  have hZsym : (↑Z : L2 →ₗ[ℝ] L2).IsSymmetric := by
    intro x y
    have hBc : ∀ u w : L2, inner ℝ (Bop hv he hκ0 omega hm hess u) w
        = inner ℝ u (Bop hv he hκ0 omega hm hess w) :=
      fun u w => Bop_symm hv he hκ0 omega hm hess u w
    have hBtc : ∀ u w : L2, inner ℝ (BtruncOp hC t hv omega hm hess u) w
        = inner ℝ u (BtruncOp hC t hv omega hm hess w) :=
      fun u w => BtruncOp_symm hκ0 hC t hv omega hm hess u w
    show inner ℝ (Bop hv he hκ0 omega hm hess x
        - BtruncOp hC t hv omega hm hess x) y
        = inner ℝ x (Bop hv he hκ0 omega hm hess y
          - BtruncOp hC t hv omega hm hess y)
    rw [inner_sub_left, inner_sub_right, hBc x y, hBtc x y]
  obtain ⟨haW, haWb⟩ := summable_and_bound_matrix (v := v) hv hcomp hκ0 hκ
    (mulOperator omega hm hess) (mulOperator_symm omega hm hess)
    (norm_mulOperator_apply_le omega hm hess)
  have hstep : ∀ q : ι × ι, inner ℝ (v q.2) (mulOperator omega hm hess (v q.1))
      = inner ℝ (v q.1) (mulOperator omega hm hess (v q.2)) := fun q =>
    (real_inner_comm (mulOperator omega hm hess (v q.1)) (v q.2)).trans
      (mulOperator_symm omega hm hess (v q.1) (v q.2))
  have hfam : Summable (fun q : ι × ι => κ q.1 * κ q.2
      * inner ℝ (v q.1) (mulOperator omega hm hess (v q.2)) ^ 2) :=
    haW.congr fun q => by rw [hstep q]
  have hfam0 : ∀ q : ι × ι, 0 ≤ κ q.1 * κ q.2
      * inner ℝ (v q.1) (mulOperator omega hm hess (v q.2)) ^ 2 := fun q =>
    mul_nonneg (mul_nonneg (hκ0 q.1) (hκ0 q.2)) (sq_nonneg _)
  have hvfam : Summable (fun q : ι × ι => inner ℝ (v q.1) (Z (v q.2)) ^ 2) :=
    (summable_indicator hfam0 hfam _).congr
      (fun q => (vmatrixSq_BsubBtrunc_eq_indicator hv he hκ0 hC t omega hm
        hess q).symm)
  have hflip : ∀ q : ι × ι, inner ℝ (v q.2) (Z (v q.1))
      = inner ℝ (v q.1) (Z (v q.2)) := fun q =>
    (real_inner_comm _ _).trans (hZsym (v q.1) (v q.2))
  have hQ : Summable (fun q : ι × ι => inner ℝ (v q.2) (Z (v q.1)) ^ 2) :=
    hvfam.congr fun q => by rw [hflip q]
  have hpt : ∀ q : ι × ι, inner ℝ (v q.2) (Z (v q.1)) ^ 2
      ≤ κ q.1 * κ q.2
          * inner ℝ (v q.1) (mulOperator omega hm hess (v q.2)) ^ 2 := by
    intro q
    rw [hflip q, hZdef,
      vmatrixSq_BsubBtrunc_eq_indicator hv he hκ0 hC t omega hm hess q]
    by_cases hq : q ∈ (((t ×ˢ t : Finset (ι × ι)) : Set (ι × ι))ᶜ)
    · rw [Set.indicator_of_mem hq]
    · rw [Set.indicator_of_notMem hq]
      exact hfam0 q
  have hmyb : (∑' q : ι × ι, κ q.1 * κ q.2
      * inner ℝ (v q.1) (mulOperator omega hm hess (v q.2)) ^ 2)
      ≤ MR ^ 2 * ∑' i, κ i ^ 2 := by
    refine le_trans (Summable.tsum_le_tsum
      (fun q => le_of_eq (by rw [hstep q])) hfam haW) haWb
  have hQb : (∑' q : ι × ι, inner ℝ (v q.2) (Z (v q.1)) ^ 2)
      ≤ MR ^ 2 * ∑' i, κ i ^ 2 :=
    le_trans (Summable.tsum_le_tsum hpt hQ hfam) hmyb
  exact (A7_aux hv hcomp hZsym hQ hQb e).1

/-- **The e-basis matrix-square sum of the model difference is the A7
indicator tail** (basis invariance of matrix squares + the pointwise
identity). -/
theorem tsum_eMatrixSq_BsubBtrunc_eq_tail {T : L2 →L[ℝ] L2} (hv : Orthonormal ℝ v)
    (he : ∀ i, T (v i) = κ i • v i) (hκ0 : ∀ i, 0 ≤ κ i)
    (hκ : Summable (fun i => κ i ^ 2)) (hcomp : (span ℝ (Set.range v))ᗮ = ⊥)
    {C : ℝ} (hC : ∀ i, |κ i| ≤ C)
    (t : Finset ι) (omega : ℝ → ℝ) (hm : Measurable omega) {MR : ℝ}
    (hess : ∀ᵐ x ∂vol, |omega x| ≤ MR) (e : HilbertBasis ℕ ℝ L2) :
    (∑' p : ℕ × ℕ, inner ℝ (e p.1)
        ((Bop hv he hκ0 omega hm hess
          - BtruncOp hC t hv omega hm hess) (e p.2)) ^ 2)
      = ∑' q : ι × ι, (((t ×ˢ t : Finset (ι × ι)) : Set (ι × ι))ᶜ).indicator
          (fun q => κ q.1 * κ q.2
            * inner ℝ (v q.1) (mulOperator omega hm hess (v q.2)) ^ 2) q := by
  classical
  set Z : L2 →L[ℝ] L2 := Bop hv he hκ0 omega hm hess
    - BtruncOp hC t hv omega hm hess with hZdef
  have hZsym : (↑Z : L2 →ₗ[ℝ] L2).IsSymmetric := by
    intro x y
    have hBc : ∀ u w : L2, inner ℝ (Bop hv he hκ0 omega hm hess u) w
        = inner ℝ u (Bop hv he hκ0 omega hm hess w) :=
      fun u w => Bop_symm hv he hκ0 omega hm hess u w
    have hBtc : ∀ u w : L2, inner ℝ (BtruncOp hC t hv omega hm hess u) w
        = inner ℝ u (BtruncOp hC t hv omega hm hess w) :=
      fun u w => BtruncOp_symm hκ0 hC t hv omega hm hess u w
    show inner ℝ (Bop hv he hκ0 omega hm hess x
        - BtruncOp hC t hv omega hm hess x) y
        = inner ℝ x (Bop hv he hκ0 omega hm hess y
          - BtruncOp hC t hv omega hm hess y)
    rw [inner_sub_left, inner_sub_right, hBc x y, hBtc x y]
  obtain ⟨haW, _⟩ := summable_and_bound_matrix (v := v) hv hcomp hκ0 hκ
    (mulOperator omega hm hess) (mulOperator_symm omega hm hess)
    (norm_mulOperator_apply_le omega hm hess)
  have hstep : ∀ q : ι × ι, inner ℝ (v q.2) (mulOperator omega hm hess (v q.1))
      = inner ℝ (v q.1) (mulOperator omega hm hess (v q.2)) := fun q =>
    (real_inner_comm (mulOperator omega hm hess (v q.1)) (v q.2)).trans
      (mulOperator_symm omega hm hess (v q.1) (v q.2))
  have hfam : Summable (fun q : ι × ι => κ q.1 * κ q.2
      * inner ℝ (v q.1) (mulOperator omega hm hess (v q.2)) ^ 2) :=
    haW.congr fun q => by rw [hstep q]
  have hfam0 : ∀ q : ι × ι, 0 ≤ κ q.1 * κ q.2
      * inner ℝ (v q.1) (mulOperator omega hm hess (v q.2)) ^ 2 := fun q =>
    mul_nonneg (mul_nonneg (hκ0 q.1) (hκ0 q.2)) (sq_nonneg _)
  have hvfam : Summable (fun q : ι × ι => inner ℝ (v q.1) (Z (v q.2)) ^ 2) :=
    (summable_indicator hfam0 hfam _).congr
      (fun q => (vmatrixSq_BsubBtrunc_eq_indicator hv he hκ0 hC t omega hm
        hess q).symm)
  have hflip : ∀ q : ι × ι, inner ℝ (v q.2) (Z (v q.1))
      = inner ℝ (v q.1) (Z (v q.2)) := fun q =>
    (real_inner_comm _ _).trans (hZsym (v q.1) (v q.2))
  have hQ : Summable (fun q : ι × ι => inner ℝ (v q.2) (Z (v q.1)) ^ 2) :=
    hvfam.congr fun q => by rw [hflip q]
  have hE := eMatrixSummable_BsubBtrunc hv he hκ0 hκ hcomp hC t omega hm hess e
  calc (∑' p : ℕ × ℕ, inner ℝ (e p.1)
        ((Bop hv he hκ0 omega hm hess
          - BtruncOp hC t hv omega hm hess) (e p.2)) ^ 2)
      = ∑' q : ι × ι, inner ℝ (v q.1) (Z (v q.2)) ^ 2 :=
        matrixSq_sum_eq_of_complete hv hcomp hZsym hQ e hE
    _ = ∑' q : ι × ι, (((t ×ˢ t : Finset (ι × ι)) : Set (ι × ι))ᶜ).indicator
          (fun q => κ q.1 * κ q.2
            * inner ℝ (v q.1) (mulOperator omega hm hess (v q.2)) ^ 2) q :=
        tsum_congr fun q =>
          vmatrixSq_BsubBtrunc_eq_indicator hv he hκ0 hC t omega hm hess q

/-- **Section 5c master: the diagonal-ℓ² content of the model difference tends
to zero** along any exhausting sequence. -/
theorem diagL2_BsubBtrunc_tendsto_zero {T : L2 →L[ℝ] L2} (hv : Orthonormal ℝ v)
    (he : ∀ i, T (v i) = κ i • v i) (hκ0 : ∀ i, 0 ≤ κ i)
    (hκ : Summable (fun i => κ i ^ 2)) (hcomp : (span ℝ (Set.range v))ᗮ = ⊥)
    {C : ℝ} (hC : ∀ i, |κ i| ≤ C)
    (omega : ℝ → ℝ) (hm : Measurable omega) {MR : ℝ}
    (hess : ∀ᵐ x ∂vol, |omega x| ≤ MR) (e : HilbertBasis ℕ ℝ L2)
    (s : ℕ → Finset ι) (hex : ∀ i, κ i ≠ 0 → ∃ N₀ : ℕ, ∀ N ≥ N₀, i ∈ s N) :
    Filter.Tendsto (fun N : ℕ => ∑' i : ℕ, ‖(Bop hv he hκ0 omega hm hess
        - BtruncOp hC (s N) hv omega hm hess) (e i)‖ ^ 2)
      Filter.atTop (nhds 0) := by
  classical
  have hfam : Summable (fun q : ι × ι => κ q.1 * κ q.2
      * inner ℝ (v q.1) (mulOperator omega hm hess (v q.2)) ^ 2) :=
    summable_aWfamily hv hcomp hκ0 hκ omega hm hess
  have hfam0 : ∀ q : ι × ι, 0 ≤ κ q.1 * κ q.2
      * inner ℝ (v q.1) (mulOperator omega hm hess (v q.2)) ^ 2 := fun q =>
    mul_nonneg (mul_nonneg (hκ0 q.1) (hκ0 q.2)) (sq_nonneg _)
  have hex2 : ∀ q : ι × ι,
      (fun q : ι × ι => κ q.1 * κ q.2
        * inner ℝ (v q.1) (mulOperator omega hm hess (v q.2)) ^ 2) q ≠ 0 →
      ∃ N₀ : ℕ, ∀ N ≥ N₀, q ∈ s N ×ˢ s N := by
    intro q hq
    have h1 : κ q.1 ≠ 0 := by
      intro hc
      apply hq
      show κ q.1 * κ q.2
          * inner ℝ (v q.1) (mulOperator omega hm hess (v q.2)) ^ 2 = 0
      rw [hc, zero_mul]
      ring
    have h2 : κ q.2 ≠ 0 := by
      intro hc
      apply hq
      show κ q.1 * κ q.2
          * inner ℝ (v q.1) (mulOperator omega hm hess (v q.2)) ^ 2 = 0
      rw [hc]
      ring
    obtain ⟨N1, hN1⟩ := hex q.1 h1
    obtain ⟨N2, hN2⟩ := hex q.2 h2
    exact ⟨max N1 N2, fun N hN => Finset.mem_product.mpr
      ⟨hN1 N (le_trans (le_max_left _ _) hN),
        hN2 N (le_trans (le_max_right _ _) hN)⟩⟩
  have htail := tail_indicator_tendsto_zero hfam0 hfam
    (fun N => s N ×ˢ s N) hex2
  have hZsymN : ∀ N : ℕ, ((↑(Bop hv he hκ0 omega hm hess
      - BtruncOp hC (s N) hv omega hm hess) : L2 →ₗ[ℝ] L2)).IsSymmetric := by
    intro N x y
    have hBc : ∀ u w : L2, inner ℝ (Bop hv he hκ0 omega hm hess u) w
        = inner ℝ u (Bop hv he hκ0 omega hm hess w) :=
      fun u w => Bop_symm hv he hκ0 omega hm hess u w
    have hBtc : ∀ u w : L2, inner ℝ (BtruncOp hC (s N) hv omega hm hess u) w
        = inner ℝ u (BtruncOp hC (s N) hv omega hm hess w) :=
      fun u w => BtruncOp_symm hκ0 hC (s N) hv omega hm hess u w
    show inner ℝ (Bop hv he hκ0 omega hm hess x
        - BtruncOp hC (s N) hv omega hm hess x) y
        = inner ℝ x (Bop hv he hκ0 omega hm hess y
          - BtruncOp hC (s N) hv omega hm hess y)
    rw [inner_sub_left, inner_sub_right, hBc x y, hBtc x y]
  have hfun : (fun N : ℕ => ∑' i : ℕ, ‖(Bop hv he hκ0 omega hm hess
        - BtruncOp hC (s N) hv omega hm hess) (e i)‖ ^ 2)
      = fun N : ℕ => ∑' q : ι × ι,
          (((s N ×ˢ s N : Finset (ι × ι)) : Set (ι × ι))ᶜ).indicator
          (fun q => κ q.1 * κ q.2
            * inner ℝ (v q.1) (mulOperator omega hm hess (v q.2)) ^ 2) q := by
    funext N
    have hE := eMatrixSummable_BsubBtrunc hv he hκ0 hκ hcomp hC (s N) omega hm
      hess e
    obtain ⟨_, heq⟩ := summable_normSq_apply_and_eq
      (Bop hv he hκ0 omega hm hess
        - BtruncOp hC (s N) hv omega hm hess) (hZsymN N) e hE
    rw [heq, tsum_eMatrixSq_BsubBtrunc_eq_tail hv he hκ0 hκ hcomp hC (s N)
      omega hm hess e]
  rw [hfun]
  exact htail

end MatrixTail


end HS

end
