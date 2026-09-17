import Hurst.GeneralKHasSumAssembled
import Hurst.EigenFamilySplice
import Hurst.GeneralKIntegrabilityClosed
import Hurst.TensorParsevalTracePair
import Hurst.CycleTraceIdentification
import Hurst.RieszSectionBounds

/-!
# The general-`k` spectral bridge: foundations layer (PARTIALLY LANDED)

## Honest session status

This session landed the **foundations layer** below (zero errors, zero sorries):

* `hasEigenvector_smul`, `isDiagEnum_of_entry` — eigen-pairing helpers;
* `measurable_abs_sub_rpow`, `measurable_rieszKernel`, `rieszKernel_symm` — the
  everywhere-measurability of the Riesz kernel (the landed clause was only a.e.);
* `sectionCS`, `integral_secE2_eq`, `integral_secE1_eq` — the section
  Cauchy–Schwarz engine and the section-energy integral identities;
* `compPowR_section_aux` — the composition tower keeps uniform section `L²` bounds
  (both orientations) and everywhere-`MemLp` sections, the input needed to discharge
  the chain-integrability `hP` via
  `HS.chainProd_integrable_of_sectionBounds` (`Hurst.GeneralKIntegrabilityClosed`,
  imported and consumed-ready).

## Remaining work (NOT landed in this session)

The route items 1–6 of the original plan (the master fractional bound
`fract_section_bound` `∫_I |a-y|^{-s} da ≤ 2 + 2/(1-s)` with its `[-1,1]`-halving
and shift-transport machinery, the uniform bounds `rieszKernel_section_sq` derived
from it, the section-integral form of the Riesz representers, the eigen-action,
the mixed Parseval trace recursion, the multiplicity comparison, and the final
`gate_riesz` / `hasSum_general_k_riesz_final` / `rieszSpectrum_hGen` assembly) were
drafted but did not reach a compiling state within the session budget; the gate
`∑' j, val j ^ k = cycle2 (compPowR (k-2) K) K` therefore remains open here.

# (Original plan header, retained for the continuation)


This file closes the last open gap of hypothesis `hGen` of `Hurst.CapstoneV3`: the
operator-side trace-power gate

  `∑' j, val j ^ k = cycle2 (compPowR (k-2) K) K`

at the constructed Riesz enumeration (`HS.rieszSpectrumVal`,
`Hurst.P2SpectrumCloseout`), and composes it with the landed
`HS.hasSum_general_k_pow` (`Hurst.GeneralKHasSumComplete`) to deliver

  `HasSum (fun j => val j ^ k) (weightedRieszCycleIntegral k psi c omega)`  for all `k ≥ 2`,

including an `hGen`-shaped theorem (`∀ k ≥ 3`) matching verbatim the hypothesis form of
`Hurst.CapstoneV3.actualQ1LongStatistic_tendsto_secondChaos_v3`.

## The route (all glue on landed pieces)

1. **Uniform section bounds for the Riesz kernel** (`rieszKernel_section_sq`): from the
   master fractional bound `fract_section_bound` (`∫_I |a-y|^{-s} da ≤ 2 + 2/(1-s)` for
   `0 ≤ s < 1`, computed with mathlib's `integral_rpow` at `r = -s`) the uniform-in-`y`
   section `L²` bound `∫_a |K_R (a, y)|² da ≤ E_K` holds for every `y` (the uniform-`ω`
   hypothesis makes the kernel a constant multiple of `|a-y|^{-psi}`).
2. **The composition tower keeps uniform section bounds**
   (`compPowR_section_aux`): one application of the landed `abs_compKernel_le`
   per step (sections are `MemLp` EVERYWHERE, thanks to the uniform bounds) plus the
   landed `hsNorm_compPowR_le` gives uniform section `L²` bounds along the whole tower
   `compPowR r K`; Cauchy–Schwarz turns them into uniform `L¹` section bounds.  This
   discharges the chain-integrability `hP` of the landed peel induction via the
   master theorem `HS.chainProd_integrable_of_sectionBounds`
   (`Hurst.GeneralKIntegrabilityClosed`).
3. **The composed kernel's eigen-action** (`TOp_compPowR_eigen`): the pointwise form of
   the Riesz representers (`TOpFun_eq_sectionIntegral`, landed here) gives
   `kpair L (TOpFun K w) g = kpair (compKernel L K) w g` (`kpair_compKernel_apply`),
   hence along the complete ON eigenfamily `(v, κ)` of `T_K`:
   `TOp (compPowR n K) (v i) = κ i ^ (n + 1) • v i`.
4. **The mixed Parseval trace recursion** (`cycle2_compPowR_eq_tsum_kappa_pow`): the
   landed tensor-ONB completeness (`HS.sections_span_orthogonal_eq_bot`,
   `Hurst.TensorONBCompleteness`) plus the mixed Parseval
   `HilbertBasis.tsum_inner_mul_inner` over the section family give
   `cycle2 M K = ∑' p, ⟪TOp M (v p.1), v p.2⟫ · ⟪T_K (v p.2), v p.1⟫`; the eigen-pairing
   collapses the double sum to the diagonal, and the eigen-action of item 3 finishes:
   `cycle2 (compPowR n K) K = ∑' i, κ i ^ (n + 2)`.
5. **The multiplicity comparison at power `k`** (`tsum_pow_eq_tsum_kappa`), under the
   operator-positivity hypothesis `hPos` (the same hypothesis the capstone
   carries): all powers are nonnegative, so the level-fiber comparison applies at
   every `k ≥ 2`: `∑' i, κ i ^ k = ∑' j, val j ^ k`.
6. **The gate and the HasSum** (`gate_riesz`, `hasSum_general_k_riesz_final`,
   `rieszSpectrum_hGen`): the gate is items 5 + 4; the composed `HasSum` is the landed
   `hasSum_general_k_pow`; the transport to `Hurst.weightedRieszCycleIntegral`
   is the general-`k` cube-restriction bridge `cycleIntegral_riesz_eq_weighted`.
-/

set_option maxHeartbeats 1000000

open MeasureTheory Measure Real Set Filter
open scoped Real

noncomputable section

namespace HS

variable {K : ℝ × ℝ → ℝ} {hK : HSKernel K}

/-! ### Eigenvector scaling and the diagonal-enum upgrade -/

/-- Eigenvectors are invariant under nonzero scaling. -/
theorem hasEigenvector_smul {T : Module.End ℝ L2} {μ : ℝ} {v : L2} {c : ℝ} (hc : c ≠ 0)
    (hv : Module.End.HasEigenvector T μ v) :
    Module.End.HasEigenvector T μ (c • v) := by
  refine ⟨?_, ?_⟩
  · exact Submodule.smul_mem _ c hv.1
  · simp only [ne_eq, smul_eq_zero, not_or]
    exact ⟨hc, hv.2⟩

/-- The landed enumeration clause upgrades to the `IsDiagEnum` shape (at the rescaled
enumeration vectors; the VALUES `val` are unchanged). -/
theorem isDiagEnum_of_entry {T : Module.End ℝ L2} {val : ℕ → ℝ} {vec : ℕ → L2}
    (hentry : ∀ j, val j = 0 ∨ Module.End.HasEigenvector T (val j) (vec j)) :
    IsDiagEnum T val (fun j => if val j = 0 then 0 else ‖vec j‖⁻¹ • vec j) := by
  intro j
  by_cases hj : val j = 0
  · refine Or.inl ⟨hj, ?_⟩
    show (if val j = 0 then (0 : L2) else ‖vec j‖⁻¹ • vec j) = 0
    rw [if_pos hj]
  · obtain ⟨he, hne⟩ := (hentry j).resolve_left hj
    have hnz : vec j ≠ 0 := fun h => hne h
    have hc : ‖vec j‖⁻¹ ≠ 0 := inv_ne_zero (norm_ne_zero_iff.mpr hnz)
    refine Or.inr ⟨?_, ?_⟩
    · show Module.End.HasEigenvector T (val j)
        (if val j = 0 then (0 : L2) else ‖vec j‖⁻¹ • vec j)
      rw [if_neg hj]
      exact hasEigenvector_smul hc ⟨he, hne⟩
    · show ‖(if val j = 0 then (0 : L2) else ‖vec j‖⁻¹ • vec j)‖ = 1
      rw [if_neg hj, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hnz)), inv_mul_cancel₀
          (norm_ne_zero_iff.mpr hnz)]

/-! ### Measurability and symmetry of the Riesz kernel -/

/-- Measurability of the distance-power factor `|p.1 - p.2| ^ (-r)`: continuous off the
diagonal, constant `0` on it (the piecewise-measurability route). -/
theorem measurable_abs_sub_rpow {r : ℝ} :
    Measurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-r)) := by
  by_cases hr : r = 0
  · subst hr
    simp only [neg_zero, Real.rpow_zero]
    exact measurable_const
  · classical
    have hdist : Continuous (fun p : ℝ × ℝ => |p.1 - p.2|) :=
      (continuous_fst.sub continuous_snd).abs
    have hSclosed : IsClosed {p : ℝ × ℝ | |p.1 - p.2| = 0} :=
      IsClosed.preimage hdist isClosed_singleton
    have hSmeas : MeasurableSet {p : ℝ × ℝ | |p.1 - p.2| = 0} := hSclosed.measurableSet
    have hopenC : IsOpen {q : ℝ × ℝ | q.1 ≠ 0} :=
      IsOpen.preimage continuous_fst isOpen_compl_singleton
    have hRpowOn : ContinuousOn (fun q : ℝ × ℝ => q.1 ^ q.2) {q : ℝ × ℝ | q.1 ≠ 0} := by
      intro q hq
      show Tendsto (fun w : ℝ × ℝ => w.1 ^ w.2)
        (nhdsWithin q {q : ℝ × ℝ | q.1 ≠ 0}) (nhds _)
      rw [nhdsWithin_eq_nhds.2 (IsOpen.mem_nhds hopenC (by simpa using hq))]
      exact Real.continuousAt_rpow q (Or.inl (by simpa using hq))
    have hMaps : MapsTo (fun p : ℝ × ℝ => (|p.1 - p.2|, -r)) {p : ℝ × ℝ | |p.1 - p.2| ≠ 0}
        {q : ℝ × ℝ | q.1 ≠ 0} := fun p hp => hp
    have key : Measurable
        (Set.piecewise {p : ℝ × ℝ | |p.1 - p.2| = 0} (fun _ : ℝ × ℝ => (0 : ℝ))
          (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-r))) :=
      ContinuousOn.measurable_piecewise continuous_const.continuousOn
        (ContinuousOn.comp hRpowOn
          ((hdist.prodMk continuous_const).continuousOn : ContinuousOn _ _)
          hMaps) hSmeas
    have heq : (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-r))
        = Set.piecewise {p : ℝ × ℝ | |p.1 - p.2| = 0} (fun _ : ℝ × ℝ => (0 : ℝ))
            (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-r)) := by
      funext p
      by_cases hp : p ∈ {p : ℝ × ℝ | |p.1 - p.2| = 0}
      · have hd0 : |p.1 - p.2| = 0 := hp
        show (|p.1 - p.2| ^ (-r) : ℝ) =
          (if p ∈ {p : ℝ × ℝ | |p.1 - p.2| = 0} then (0 : ℝ) else |p.1 - p.2| ^ (-r))
        rw [if_pos hp, hd0, Real.zero_rpow (show (-r : ℝ) ≠ 0 by simpa using hr)]
      · show (|p.1 - p.2| ^ (-r) : ℝ) =
          (if p ∈ {p : ℝ × ℝ | |p.1 - p.2| = 0} then (0 : ℝ) else |p.1 - p.2| ^ (-r))
        rw [if_neg hp]
    rw [heq]
    exact key

/-- The Riesz kernel is everywhere-measurable (the landed clause is only a.e.). -/
theorem measurable_rieszKernel {psi c : ℝ} {omega : ℝ → ℝ} (homega : Measurable omega) :
    Measurable (rieszKernel psi c omega) := by
  unfold rieszKernel
  exact ((((homega.indicator (measurableSet_Icc (a := (-1 : ℝ)) (b := (1 : ℝ)))).comp
    measurable_fst)).mul (measurable_const : Measurable fun _ : ℝ × ℝ => c)).mul
    (measurable_abs_sub_rpow (r := psi))

/-- The Riesz kernel is symmetric (the uniform-`ω` hypothesis makes the weight
constant). -/
theorem rieszKernel_symm {psi c : ℝ} {omega : ℝ → ℝ}
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y)
    (p : ℝ × ℝ) : rieszKernel psi c omega p = rieszKernel psi c omega p.swap := by
  show (I : Set ℝ).indicator omega p.1 * c * |p.1 - p.2| ^ (-psi)
      = (I : Set ℝ).indicator omega p.2 * c * |p.2 - p.1| ^ (-psi)
  rw [hconst p.1 p.2, abs_sub_comm p.1 p.2]

/-! ### The master fractional section bound -/

/-- Nat-pow vs real-pow bridge on `vol` (the landed private pattern, re-landed). -/
private theorem integral_pow_two_vol' (u : ℝ → ℝ) :
    ∫ t : ℝ, u t ^ (2 : ℝ) ∂vol = ∫ t : ℝ, u t ^ 2 ∂vol := by
  apply integral_congr_ae
  filter_upwards with t
  rw [Real.rpow_two, pow_two]

/-- **The section Cauchy–Schwarz bound** (the engine of `abs_compKernel_le`,
extracted): where the sections are `L²`,
`∫_t |K(x,t)| |L(t,y)| ≤ √(secE2 K x) √(secE1 L y)`. -/
theorem sectionCS {K L : ℝ × ℝ → ℝ} (x y : ℝ)
    (hx : MemLp (fun t => K (x, t)) 2 vol) (hy : MemLp (fun t => L (t, y)) 2 vol) :
    ∫ t : ℝ, |K (x, t)| * |L (t, y)| ∂vol
      ≤ Real.sqrt (secE2 K x) * Real.sqrt (secE1 L y) := by
  have hx2 : MemLp (fun t => K (x, t)) (ENNReal.ofReal 2) vol := by
    rw [real_two_ofReal]; exact hx
  have hy2 : MemLp (fun t => L (t, y)) (ENNReal.ofReal 2) vol := by
    rw [real_two_ofReal]; exact hy
  have hcs := integral_mul_norm_le_Lp_mul_Lq holderTriple221 hx2 hy2
  simp only [Real.norm_eq_abs] at hcs
  rw [integral_pow_two_vol' (fun t => |K (x, t)|),
    integral_pow_two_vol' (fun t => |L (t, y)|)] at hcs
  have h1 : (∫ t : ℝ, |K (x, t)| ^ 2 ∂vol) ^ ((1 : ℝ) / 2) = Real.sqrt (secE2 K x) := by
    rw [← Real.sqrt_eq_rpow]
    refine congrArg Real.sqrt ?_
    exact integral_congr_ae (Filter.Eventually.of_forall fun t => by simp [sq_abs])
  have h2 : (∫ t : ℝ, |L (t, y)| ^ 2 ∂vol) ^ ((1 : ℝ) / 2) = Real.sqrt (secE1 L y) := by
    rw [← Real.sqrt_eq_rpow]
    refine congrArg Real.sqrt ?_
    exact integral_congr_ae (Filter.Eventually.of_forall fun t => by simp [sq_abs])
  rw [h1, h2] at hcs
  exact hcs

/-! ### The diagonal section-integral identities -/

/-- The diagonal section-integral identity: `∫ a, secE2 M a = ∫∫ M²`. -/
theorem integral_secE2_eq {M : ℝ × ℝ → ℝ} (hM : HSKernel M) :
    ∫ a : ℝ, secE2 M a ∂vol = ∫ p : ℝ × ℝ, M p ^ 2 ∂vol2 := by
  rw [integral_prod (fun p : ℝ × ℝ => M p ^ 2) (MemLp.integrable_sq hM)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun _ => rfl)

/-- The transposed section-integral identity: `∫ y, secE1 M y = ∫∫ M²`. -/
theorem integral_secE1_eq {M : ℝ × ℝ → ℝ} (hM : HSKernel M) :
    ∫ y : ℝ, secE1 M y ∂vol = ∫ p : ℝ × ℝ, M p ^ 2 ∂vol2 := by
  have hswap : (∫ p : ℝ × ℝ, M p ^ 2 ∂vol2) = ∫ q : ℝ × ℝ, M q.swap ^ 2 ∂vol2 :=
    (integral_prod_swap (fun q => M q ^ 2)).symm
  rw [hswap, integral_prod (fun q : ℝ × ℝ => M q.swap ^ 2)
    (MemLp.integrable_sq (hsKernel_transpose hM))]
  exact integral_congr_ae (Filter.Eventually.of_forall fun _ => rfl)

/-! ### Uniform section bounds along the composition tower -/

/-- **The composition tower keeps uniform section `L²` bounds**: if the base kernel is
everywhere-measurable HS with uniform section `L²` bounds `∫ a, K (a, y)² ≤ E` (both
orientations, with the sections integrable), then for every `r` the tower `compPowR r K`
has `∫ a, (compPowR r K (a, y))² ≤ E * (hsNorm K ^ 2) ^ r` in both orientations, and all
its sections are `MemLp 2` (everywhere). -/
theorem compPowR_section_aux {K : ℝ × ℝ → ℝ} (hKm : Measurable K) (hK : HSKernel K)
    {E : ℝ} (hE : ∀ y : ℝ, ∫ a : ℝ, K (a, y) ^ 2 ∂vol ≤ E)
    (hErow : ∀ x : ℝ, ∫ a : ℝ, K (x, a) ^ 2 ∂vol ≤ E)
    (hEint : ∀ z : ℝ, Integrable (fun a : ℝ => K (a, z) ^ 2) vol)
    (hEintRow : ∀ z : ℝ, Integrable (fun a : ℝ => K (z, a) ^ 2) vol) :
    ∀ r : ℕ, (∀ y : ℝ, ∫ a : ℝ, compPowR r K (a, y) ^ 2 ∂vol ≤ E * (hsNorm K ^ 2) ^ r)
      ∧ (∀ x : ℝ, ∫ a : ℝ, compPowR r K (x, a) ^ 2 ∂vol ≤ E * (hsNorm K ^ 2) ^ r)
      ∧ (∀ y : ℝ, MemLp (fun a : ℝ => compPowR r K (a, y)) 2 vol)
      ∧ (∀ x : ℝ, MemLp (fun a : ℝ => compPowR r K (x, a)) 2 vol) := by
  intro r
  induction r with
  | zero =>
      have hz : compPowR 0 K = K := rfl
      have hmemY : ∀ y : ℝ, MemLp (fun a : ℝ => compPowR 0 K (a, y)) 2 vol := by
        intro y
        exact memLp_two_of_aemeasurable
          ((hKm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable) (hEint y)
      have hmemX : ∀ x : ℝ, MemLp (fun a : ℝ => compPowR 0 K (x, a)) 2 vol := by
        intro x
        exact memLp_two_of_aemeasurable
          ((hKm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
          (hEintRow x)
      refine ⟨fun y => ?_, fun x => ?_, hmemY, hmemX⟩
      · simpa [hz] using hE y
      · simpa [hz] using hErow x
  | succ m ih =>
      obtain ⟨hcol, hrow, hcolMem, hrowMem⟩ := ih
      have hmeasM := measurable_compPowR m hKm
      have hM : HSKernel (compPowR m K) := hsKernel_compPowR m hKm hK
      have hstep : ∀ (x y : ℝ), compPowR (m + 1) K (x, y) ^ 2
          ≤ secE2 (compPowR m K) x * secE1 K y := by
        intro x y
        have h1 := abs_compKernel_le x y (hrowMem x)
          (memLp_two_of_aemeasurable
            ((hKm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
            (hEint y))
        have hn1 : 0 ≤ secE2 (compPowR m K) x := integral_nonneg fun _ => sq_nonneg _
        have hn2 : 0 ≤ secE1 K y := integral_nonneg fun _ => sq_nonneg _
        have hStep : compPowR (m + 1) K (x, y)
            = compKernel (compPowR m K) K (x, y) := rfl
        calc compPowR (m + 1) K (x, y) ^ 2
            = |compKernel (compPowR m K) K (x, y)| ^ 2 := by
                rw [hStep, sq_abs]
          _ ≤ (Real.sqrt (secE2 (compPowR m K) x) * Real.sqrt (secE1 K y)) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) h1 2
          _ = secE2 (compPowR m K) x * secE1 K y := by
              rw [mul_pow, Real.sq_sqrt hn1, Real.sq_sqrt hn2]
      have hpowpow : (hsNorm K ^ (m + 1)) ^ 2 = (hsNorm K ^ 2) ^ (m + 1) := by
        rw [← pow_mul, ← pow_mul, mul_comm]
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- column bound for `r + 1`
        intro y
        have hintsec : ∫ a : ℝ, secE2 (compPowR m K) a ∂vol
            ≤ (hsNorm K ^ 2) ^ (m + 1) := by
          rw [integral_secE2_eq hM]
          calc ∫ p : ℝ × ℝ, compPowR m K p ^ 2 ∂vol2
              = (hsNorm (compPowR m K)) ^ 2 := (hsNorm_sq _).symm
            _ ≤ (hsNorm K ^ (m + 1)) ^ 2 :=
                pow_le_pow_left₀ (hsNorm_nonneg _) (hsNorm_compPowR_le m hKm hK) 2
            _ = (hsNorm K ^ 2) ^ (m + 1) := hpowpow
        have hintdom : Integrable (fun a : ℝ => secE1 K y * secE2 (compPowR m K) a) vol :=
          (integrable_secE2 hM).const_mul (secE1 K y)
        calc ∫ a : ℝ, compPowR (m + 1) K (a, y) ^ 2 ∂vol
            ≤ ∫ a : ℝ, secE1 K y * secE2 (compPowR m K) a ∂vol := by
              refine integral_mono_of_nonneg
                (Filter.Eventually.of_forall fun a => sq_nonneg _) hintdom ?_
              filter_upwards with a
              show compPowR (m + 1) K (a, y) ^ 2 ≤ secE1 K y * secE2 (compPowR m K) a
              exact le_trans (hstep a y)
                (le_of_eq (mul_comm (secE2 (compPowR m K) a) (secE1 K y)))
          _ = secE1 K y * ∫ a : ℝ, secE2 (compPowR m K) a ∂vol := integral_const_mul _ _
          _ ≤ secE1 K y * (hsNorm K ^ 2) ^ (m + 1) :=
              mul_le_mul_of_nonneg_left hintsec (integral_nonneg fun _ => sq_nonneg _)
          _ ≤ E * (hsNorm K ^ 2) ^ (m + 1) :=
              mul_le_mul_of_nonneg_right (hE y) (pow_nonneg (sq_nonneg (hsNorm K)) _)
      · -- row bound for `r + 1`
        intro x
        have hintdom : Integrable (fun a : ℝ => secE2 (compPowR m K) x * secE1 K a) vol :=
          (integrable_secE1 hK).const_mul (secE2 (compPowR m K) x)
        calc ∫ a : ℝ, compPowR (m + 1) K (x, a) ^ 2 ∂vol
            ≤ ∫ a : ℝ, secE2 (compPowR m K) x * secE1 K a ∂vol := by
              refine integral_mono_of_nonneg
                (Filter.Eventually.of_forall fun a => sq_nonneg _) hintdom ?_
              filter_upwards with a
              show compPowR (m + 1) K (x, a) ^ 2 ≤ secE2 (compPowR m K) x * secE1 K a
              exact hstep x a
          _ = secE2 (compPowR m K) x * ∫ a : ℝ, secE1 K a ∂vol := integral_const_mul _ _
          _ = secE2 (compPowR m K) x * (hsNorm K ^ 2) := by
              rw [integral_secE1_eq hK, ← hsNorm_sq]
          _ ≤ (E * (hsNorm K ^ 2) ^ m) * (hsNorm K ^ 2) :=
              mul_le_mul_of_nonneg_right (hrow x) (sq_nonneg (hsNorm K))
          _ = E * (hsNorm K ^ 2) ^ (m + 1) := by
              rw [pow_succ' (hsNorm K ^ 2) m]
              ring
      · -- column sections are MemLp
        intro y
        refine memLp_two_of_aemeasurable
          (((measurable_compPowR (m + 1) hKm).comp
            (measurable_id.prodMk measurable_const)).aestronglyMeasurable) ?_
        refine ((integrable_secE2 hM).const_mul (secE1 K y)).mono ?_ ?_
        · exact (((measurable_compPowR (m + 1) hKm).comp
            (measurable_id.prodMk measurable_const)).pow_const 2).aestronglyMeasurable
        · filter_upwards with a
          show ‖compPowR (m + 1) K (a, y) ^ 2‖ ≤ ‖secE1 K y * secE2 (compPowR m K) a‖
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Real.norm_eq_abs, abs_mul,
            abs_of_nonneg (show (0 : ℝ) ≤ secE1 K y from integral_nonneg fun _ => sq_nonneg _),
            abs_of_nonneg (show (0 : ℝ) ≤ secE2 (compPowR m K) a from integral_nonneg
              fun _ => sq_nonneg _)]
          exact le_trans (hstep a y)
            (le_of_eq (mul_comm (secE2 (compPowR m K) a) (secE1 K y)))
      · -- row sections are MemLp
        intro x
        refine memLp_two_of_aemeasurable
          (((measurable_compPowR (m + 1) hKm).comp
            (measurable_const.prodMk measurable_id)).aestronglyMeasurable) ?_
        refine ((integrable_secE1 hK).const_mul (secE2 (compPowR m K) x)).mono ?_ ?_
        · exact (((measurable_compPowR (m + 1) hKm).comp
            (measurable_const.prodMk measurable_id)).pow_const 2).aestronglyMeasurable
        · filter_upwards with a
          show ‖compPowR (m + 1) K (x, a) ^ 2‖ ≤ ‖secE2 (compPowR m K) x * secE1 K a‖
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Real.norm_eq_abs, abs_mul,
            abs_of_nonneg (show (0 : ℝ) ≤ secE2 (compPowR m K) x from integral_nonneg
              fun _ => sq_nonneg _),
            abs_of_nonneg (show (0 : ℝ) ≤ secE1 K a from integral_nonneg fun _ => sq_nonneg _)]
          exact hstep x a



/-- **The `hP` discharge from uniform tower section bounds** (spec §2): with uniform
`ENNReal.ofReal`-form section bounds for `K` and every tower level `compPowR r K`
(both orientations for `L²`, plus `L¹`), the chain-integrability hypothesis of the
peel induction holds at every level. -/
theorem hP_of_sectionBounds {K : ℝ × ℝ → ℝ} (hKm : Measurable K)
    (hE1 : ∀ (r : ℕ) (y : ℝ),
      ∫⁻ a : ℝ, ENNReal.ofReal |compPowR r K (a, y)| ^ 2 ∂vol ≤ ENNReal.ofReal E)
    (hE2 : ∀ (r : ℕ) (y : ℝ),
      ∫⁻ a : ℝ, ENNReal.ofReal |compPowR r K (y, a)| ^ 2 ∂vol ≤ ENNReal.ofReal E)
    (hD1 : ∀ (r : ℕ) (y : ℝ),
      ∫⁻ a : ℝ, ENNReal.ofReal |compPowR r K (a, y)| ∂vol ≤ ENNReal.ofReal D)
    (hEK1 : ∀ y : ℝ, ∫⁻ a : ℝ, ENNReal.ofReal |K (a, y)| ^ 2 ∂vol ≤ ENNReal.ofReal E)
    (hEK2 : ∀ y : ℝ, ∫⁻ a : ℝ, ENNReal.ofReal |K (y, a)| ^ 2 ∂vol ≤ ENNReal.ofReal E)
    (hDK1 : ∀ y : ℝ, ∫⁻ a : ℝ, ENNReal.ofReal |K (a, y)| ∂vol ≤ ENNReal.ofReal D)
    (n r : ℕ) :
    Integrable (peelChainProd (n + 2) (kchain n r K))
      (Measure.pi fun _ : Fin (n + 2) => vol) := by
  have hWm : ∀ i : Fin (n + 2), Measurable (kchain n r K i) := by
    intro i
    by_cases hi : i = Fin.last (n + 1)
    · rw [kchain, if_pos hi]
      exact measurable_compPowR r hKm
    · rw [kchain, if_neg hi]
      exact hKm
  refine chainProd_integrable_of_sectionBounds (by norm_num) (kchain n r K) hWm E D ?_ ?_ ?_
  · intro i y
    by_cases hi : i = Fin.last (n + 1)
    · rw [kchain, if_pos hi]
      exact hE1 r y
    · rw [kchain, if_neg hi]
      exact hEK1 y
  · intro i y
    by_cases hi : i = Fin.last (n + 1)
    · rw [kchain, if_pos hi]
      exact hE2 r y
    · rw [kchain, if_neg hi]
      exact hEK2 y
  · intro i y
    by_cases hi : i = Fin.last (n + 1)
    · rw [kchain, if_pos hi]
      exact hD1 r y
    · rw [kchain, if_neg hi]
      exact hDK1 y

/-- **The operator-side gate from the enumeration↔basis bridge** (spec §3).  Two
inputs, both the documented isolated gaps of the wider project:

* `hBridge` (Step C) — the diagonal pairing sum of `T^k` over ANY Hilbert basis
  equals the enumerated power sum (trace-class basis-invariance of `T^k` plus the
  multiplicity bookkeeping; `CycleTraceIdentification`'s isolated gap);
* `hPair` (Step B, the operator-power identification) — the composition
  `TOp K hK ∘ TOp (compPowR (k-2) K) hKL` is `T^k` as an operator (the tower
  induction over the landed kernel-composition action, equivalent to the a.e.
  section formula of the Riesz representers).

The kernel-side leg is landed: `tracePair_comp_tsum` identifies the composite
pairing sum with `cycle2 (compPowR (k-2) K) K`. -/
theorem gate_of_bridge {K : ℝ × ℝ → ℝ} {val : ℕ → ℝ} {vec : ℕ → L2} {k : ℕ}
    (hk : 2 ≤ k) (hK : HSKernel K) (hKL : HSKernel (compPowR (k - 2) K))
    (e : HilbertBasis ℕ ℝ L2)
    (hBridge : ∀ j : ℕ, 2 ≤ j → ∀ (e : HilbertBasis ℕ ℝ L2),
      (∑' i : ℕ, inner ℝ ((TOpEnd' K hK ^ j) (e i)) (e i))
        = ∑' m : ℕ, val m ^ j)
    (hPair : ∀ x : L2, (TOp K hK) ((TOp (compPowR (k - 2) K) hKL) x)
        = (TOpEnd' K hK ^ k) x) :
    (∑' j : ℕ, val j ^ k) = cycle2 (compPowR (k - 2) K) K := by
    have hTp := tracePair_comp_tsum hK hKL e
    obtain ⟨S, hS⟩ := tracePair_comp_summable hK hKL e
    have hPow : HasSum (fun i : ℕ => inner ℝ ((TOpEnd' K hK ^ k) (e i)) (e i)) S :=
      hS.congr_fun (fun i =>
        (real_inner_comm ((TOpEnd' K hK ^ k) (e i)) (e i)).symm.trans
          ((congrArg (fun w : L2 => inner ℝ (e i) w) (hPair (e i))).symm.trans
            (real_inner_comm (TOp K hK (TOp (compPowR (k - 2) K) hKL (e i))) (e i))))
    rw [← hBridge k hk e]
    exact hPow.tsum_eq.trans (hS.tsum_eq.symm.trans (tracePair_comp_tsum hK hKL e))

/-- **The composed general-`k` HasSum from the gate** (spec §4): the gate plus the
peel induction plus the discharged chain integrability give the enumerated power
series `HasSum` to the `k`-cycle integral. -/
theorem hasSum_general_k_of_gate {K : ℝ × ℝ → ℝ} (hKm : Measurable K) (hK : HSKernel K)
    (hCompact : IsCompactOperator (TOp K hK))
    (hsym : (↑(TOp K hK) : L2 →ₗ[ℝ] L2).IsSymmetric)
    {val : ℕ → ℝ} {vec : ℕ → L2} {k : ℕ}
    (hk : 2 ≤ k) (hKL : HSKernel (compPowR (k - 2) K))
    (e : HilbertBasis ℕ ℝ L2)
    (hBridge : ∀ j : ℕ, 2 ≤ j → ∀ (e : HilbertBasis ℕ ℝ L2),
      (∑' i : ℕ, inner ℝ ((TOpEnd' K hK ^ j) (e i)) (e i))
        = ∑' m : ℕ, val m ^ j)
    (hPair : ∀ x : L2, (TOp K hK) ((TOp (compPowR (k - 2) K) hKL) x)
        = (TOpEnd' K hK ^ k) x)
    (hE1 : ∀ (r : ℕ) (y : ℝ),
      ∫⁻ a : ℝ, ENNReal.ofReal |compPowR r K (a, y)| ^ 2 ∂vol ≤ ENNReal.ofReal E)
    (hE2 : ∀ (r : ℕ) (y : ℝ),
      ∫⁻ a : ℝ, ENNReal.ofReal |compPowR r K (y, a)| ^ 2 ∂vol ≤ ENNReal.ofReal E)
    (hD1 : ∀ (r : ℕ) (y : ℝ),
      ∫⁻ a : ℝ, ENNReal.ofReal |compPowR r K (a, y)| ∂vol ≤ ENNReal.ofReal D)
    (hEK1 : ∀ y : ℝ, ∫⁻ a : ℝ, ENNReal.ofReal |K (a, y)| ^ 2 ∂vol ≤ ENNReal.ofReal E)
    (hEK2 : ∀ y : ℝ, ∫⁻ a : ℝ, ENNReal.ofReal |K (y, a)| ^ 2 ∂vol ≤ ENNReal.ofReal E)
    (hDK1 : ∀ y : ℝ, ∫⁻ a : ℝ, ENNReal.ofReal |K (a, y)| ∂vol ≤ ENNReal.ofReal D)
    (hdiag : IsDiagEnum (TOpEnd' K hK) val vec)
    (hmult : ∀ μ : ℝ, Module.End.HasEigenvalue (TOpEnd' K hK) μ → μ ≠ 0 →
      Nat.card {j : ℕ // val j = μ}
        = Module.finrank ℝ (Module.End.eigenspace (TOpEnd' K hK) μ)) :
    HasSum (fun j : ℕ => val j ^ k) (cycleIntegral k K) := by
  have hP : ∀ n r : ℕ, Integrable (peelChainProd (n + 2) (kchain n r K))
      (Measure.pi fun _ : Fin (n + 2) => vol) :=
    hP_of_sectionBounds hKm hE1 hE2 hD1 hEK1 hEK2 hDK1
  refine hasSum_general_k_assembled hCompact hsym hdiag hmult hP k hk ?_
  exact gate_of_bridge (vec := vec) hk hK hKL e hBridge hPair

/-- **The general-`k` weighted HasSum (conditional)**: given the k↔weighted
cycle-integral identification (spec §4: both sides are the cyclic kernel product;
the `restrict_pi_pi`-transport of the two encodings on the `I^k`-cylinder), the
gate + composition deliver the capstone-target HasSum for every `k ≥ 2`. -/
theorem hasSum_weighted_of_gate (K : ℝ × ℝ → ℝ) (psi c : ℝ) (omega : ℝ → ℝ)
    (hKm : Measurable K) (hK : HSKernel K)
    (hCompact : IsCompactOperator (TOp K hK))
    (hsym : (↑(TOp K hK) : L2 →ₗ[ℝ] L2).IsSymmetric)
    {val : ℕ → ℝ} {vec : ℕ → L2}
    (hW : ∀ k : ℕ, 2 ≤ k → cycleIntegral k K
      = Hurst.weightedRieszCycleIntegral k psi c omega)
    (hKL : ∀ k : ℕ, HSKernel (compPowR (k - 2) K))
    (e : HilbertBasis ℕ ℝ L2)
    (hBridge : ∀ j : ℕ, 2 ≤ j → ∀ (e : HilbertBasis ℕ ℝ L2),
      (∑' i : ℕ, inner ℝ ((TOpEnd' K hK ^ j) (e i)) (e i))
        = ∑' m : ℕ, val m ^ j)
    (hPair : ∀ (k : ℕ) (x : L2), (TOp K hK) ((TOp (compPowR (k - 2) K) (hKL k)) x)
        = (TOpEnd' K hK ^ k) x)
    (hE1 : ∀ (r : ℕ) (y : ℝ),
      ∫⁻ a : ℝ, ENNReal.ofReal |compPowR r K (a, y)| ^ 2 ∂vol ≤ ENNReal.ofReal E)
    (hE2 : ∀ (r : ℕ) (y : ℝ),
      ∫⁻ a : ℝ, ENNReal.ofReal |compPowR r K (y, a)| ^ 2 ∂vol ≤ ENNReal.ofReal E)
    (hD1 : ∀ (r : ℕ) (y : ℝ),
      ∫⁻ a : ℝ, ENNReal.ofReal |compPowR r K (a, y)| ∂vol ≤ ENNReal.ofReal D)
    (hEK1 : ∀ y : ℝ, ∫⁻ a : ℝ, ENNReal.ofReal |K (a, y)| ^ 2 ∂vol ≤ ENNReal.ofReal E)
    (hEK2 : ∀ y : ℝ, ∫⁻ a : ℝ, ENNReal.ofReal |K (y, a)| ^ 2 ∂vol ≤ ENNReal.ofReal E)
    (hDK1 : ∀ y : ℝ, ∫⁻ a : ℝ, ENNReal.ofReal |K (a, y)| ∂vol ≤ ENNReal.ofReal D)
    (hdiag : IsDiagEnum (TOpEnd' K hK) val vec)
    (hmult : ∀ μ : ℝ, Module.End.HasEigenvalue (TOpEnd' K hK) μ → μ ≠ 0 →
      Nat.card {j : ℕ // val j = μ}
        = Module.finrank ℝ (Module.End.eigenspace (TOpEnd' K hK) μ))
    (k : ℕ) (hk : 2 ≤ k) :
    HasSum (fun j : ℕ => val j ^ k)
      (Hurst.weightedRieszCycleIntegral k psi c omega) := by
  have hcore := hasSum_general_k_of_gate hKm hK hCompact hsym (vec := vec) hk (hKL k) e
    hBridge (hPair k) hE1 hE2 hD1 hEK1 hEK2 hDK1 hdiag hmult
  rw [hW k hk] at hcore
  exact hcore

end HS

end
