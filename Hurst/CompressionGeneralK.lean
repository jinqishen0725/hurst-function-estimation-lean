import Mathlib
import Hurst.CompressionIdentity
import Hurst.TracePairCycle
import Hurst.HSCycleComposition
import Hurst.GeneralKPeelInduction

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

end HS

end
