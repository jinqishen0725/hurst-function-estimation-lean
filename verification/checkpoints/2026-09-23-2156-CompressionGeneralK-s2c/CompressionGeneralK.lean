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
  rw [Real.dist_eq, sub_zero, abs_of_nonneg
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


end HS

end
