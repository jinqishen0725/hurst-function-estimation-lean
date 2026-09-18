import Hurst.GeneralKHasSumAssembled
import Hurst.EigenFamilySplice
import Hurst.GeneralKIntegrabilityClosed
import Hurst.TensorParsevalTracePair
import Hurst.CycleTraceIdentification
import Hurst.RieszSectionBounds

/-!
# The general-`k` spectral bridge: foundations + section bounds + cycle bridge

## Honest session status

This file compiles with zero errors and zero sorries.  Landed here:

* `hasEigenvector_smul`, `isDiagEnum_of_entry` — eigen-pairing helpers;
* `measurable_abs_sub_rpow`, `measurable_rieszKernel`, `rieszKernel_symm` — the
  everywhere-measurability of the Riesz kernel (the landed clause was only a.e.);
* `sectionCS`, `integral_secE2_eq`, `integral_secE1_eq` — the section
  Cauchy–Schwarz engine and the section-energy integral identities;
* `compPowR_section_aux` — the composition tower keeps uniform section `L²` bounds
  (both orientations) and everywhere-`MemLp` sections;
* `hP_of_sectionBounds` — the chain-integrability discharge, now in the **per-level
  packaging**: the tower bounds carry the finite rate
  `max 1 ((hsNorm K ^ 2) ^ r)` and the chain-uniform bounds are formed inside
  (`max E (E * rate)`, `max D (D * rate)`); a single `r`-independent `E` was
  unsatisfiable whenever `hsNorm K > 1`;
* `gate_of_bridge`, `hasSum_general_k_of_gate`, `hasSum_weighted_of_gate` — the
  conditional gate architecture (consumes `hBridge`/`hPair`, the isolated gaps of
  `Hurst.CycleTraceIdentification` / the operator-power identification);
* **`rieszKernel_sectionBounds_package`** (with projections `rieszKernel_lintSq`,
  `rieszKernel_lintSq_symm`, `rieszKernel_lintL1`) — the six packaged section-bound
  shapes of `hP_of_sectionBounds`, discharged UNCONDITIONALLY at the capstone Riesz
  data (from the committed `Hurst.RieszSectionBounds` uniform bounds composed with
  `compPowR_section_aux` and the `ofReal` transport);
* **`hW_bridge`** — the cycle-encoding bridge (spec §7, unconditional, every `k`):
  `cycleIntegral k (rieszKernel psi c omega) = weightedRieszCycleIntegral k psi c omega`,
  transporting the `vol^k`-integral along the `I^k`-cylinder to `volume^k` and
  matching the cyclic successors;
* **`rieszSpectrumVal_hasSum_of_bridge` / `rieszSpectrumVal_hGen_of_bridge`** — the
  capstone HasSum / `hGen` clause at the constructed enumeration
  (`HS.rieszSpectrumVal`), with hypotheses reduced to: capstone data + feasibility
  window + a Hilbert basis + `hBridge` + `hPair`.

## Remaining work (NOT landed here)

The two operator-side bridge clauses remain hypotheses (they are the documented
isolated gaps of the wider project): `hBridge` (trace-class basis-invariance +
multiplicity bookkeeping — spec §8, AGENT-H) and `hPair` (the operator-power
identification `TOp K ∘ TOp (compPowR (k-2) K) = T^k` — spec §6, AGENT-G).

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



/-- **The `hP` discharge from uniform tower section bounds** (spec §2, per-level
packaging): with per-level `ENNReal.ofReal`-form section bounds for `K` and every tower
level `compPowR r K` — the tower bounds carrying the finite multiplicative rate
`max 1 ((hsNorm K ^ 2) ^ r)` — the chain-integrability hypothesis of the peel induction
holds at every level.  (The chain-uniform bounds are formed inside: for fixed `n, r` the
rate `max 1 ((hsNorm K ^ 2) ^ r)` is a single finite real, and both the base and the
tower entries are dominated by `max E (E * rate)` resp. `max D (D * rate)`.  A single
`r`-independent `E` would be unsatisfiable: by `compPowR_section_aux` the tower bound
`E_K * (hsNorm K ^ 2) ^ r` is unbounded in `r` whenever `hsNorm K > 1`.) -/
theorem hP_of_sectionBounds {K : ℝ × ℝ → ℝ} (hKm : Measurable K)
    (hE1 : ∀ (r : ℕ) (y : ℝ),
      ∫⁻ a : ℝ, ENNReal.ofReal |compPowR r K (a, y)| ^ 2 ∂vol
        ≤ ENNReal.ofReal (E * max 1 ((hsNorm K ^ 2) ^ r)))
    (hE2 : ∀ (r : ℕ) (y : ℝ),
      ∫⁻ a : ℝ, ENNReal.ofReal |compPowR r K (y, a)| ^ 2 ∂vol
        ≤ ENNReal.ofReal (E * max 1 ((hsNorm K ^ 2) ^ r)))
    (hD1 : ∀ (r : ℕ) (y : ℝ),
      ∫⁻ a : ℝ, ENNReal.ofReal |compPowR r K (a, y)| ∂vol
        ≤ ENNReal.ofReal (D * max 1 ((hsNorm K ^ 2) ^ r)))
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
  refine chainProd_integrable_of_sectionBounds (by norm_num) (kchain n r K) hWm
    (max E (E * max 1 ((hsNorm K ^ 2) ^ r)))
    (max D (D * max 1 ((hsNorm K ^ 2) ^ r))) ?_ ?_ ?_
  · intro i y
    by_cases hi : i = Fin.last (n + 1)
    · rw [kchain, if_pos hi]
      exact (hE1 r y).trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))
    · rw [kchain, if_neg hi]
      exact (hEK1 y).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  · intro i y
    by_cases hi : i = Fin.last (n + 1)
    · rw [kchain, if_pos hi]
      exact (hE2 r y).trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))
    · rw [kchain, if_neg hi]
      exact (hEK2 y).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  · intro i y
    by_cases hi : i = Fin.last (n + 1)
    · rw [kchain, if_pos hi]
      exact (hD1 r y).trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))
    · rw [kchain, if_neg hi]
      exact (hDK1 y).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))

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
theorem gate_of_bridge {K : ℝ × ℝ → ℝ} {val : ℕ → ℝ} {k : ℕ}
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
      ∫⁻ a : ℝ, ENNReal.ofReal |compPowR r K (a, y)| ^ 2 ∂vol
        ≤ ENNReal.ofReal (E * max 1 ((hsNorm K ^ 2) ^ r)))
    (hE2 : ∀ (r : ℕ) (y : ℝ),
      ∫⁻ a : ℝ, ENNReal.ofReal |compPowR r K (y, a)| ^ 2 ∂vol
        ≤ ENNReal.ofReal (E * max 1 ((hsNorm K ^ 2) ^ r)))
    (hD1 : ∀ (r : ℕ) (y : ℝ),
      ∫⁻ a : ℝ, ENNReal.ofReal |compPowR r K (a, y)| ∂vol
        ≤ ENNReal.ofReal (D * max 1 ((hsNorm K ^ 2) ^ r)))
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
  exact gate_of_bridge hk hK hKL e hBridge hPair

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
      ∫⁻ a : ℝ, ENNReal.ofReal |compPowR r K (a, y)| ^ 2 ∂vol
        ≤ ENNReal.ofReal (E * max 1 ((hsNorm K ^ 2) ^ r)))
    (hE2 : ∀ (r : ℕ) (y : ℝ),
      ∫⁻ a : ℝ, ENNReal.ofReal |compPowR r K (y, a)| ^ 2 ∂vol
        ≤ ENNReal.ofReal (E * max 1 ((hsNorm K ^ 2) ^ r)))
    (hD1 : ∀ (r : ℕ) (y : ℝ),
      ∫⁻ a : ℝ, ENNReal.ofReal |compPowR r K (a, y)| ∂vol
        ≤ ENNReal.ofReal (D * max 1 ((hsNorm K ^ 2) ^ r)))
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

/-! ### The capstone section bounds at the Riesz kernel data (unconditional) -/

/-- The carrier measure has total mass `2` (the interval `I = Icc (-1 : ℝ) 1` has
length `2`). -/
private theorem vol_univ_eq_two : ((vol : Measure ℝ) Set.univ) = 2 := by
  show (MeasureTheory.volume.restrict (I : Set ℝ)) Set.univ = 2
  rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Icc]
  norm_num

/-- Off `I` the carrier measure gives no mass, so the plain distance power and its
`I`-indicator are a.e.-equal against `HS.vol`. -/
private theorem indicator_ae_abs_sub' {p : ℝ} (y : ℝ) :
    ((I : Set ℝ).indicator (fun b : ℝ => |b - y| ^ (-p)))
      =ᵐ[vol] (fun a : ℝ => |a - y| ^ (-p)) := by
  filter_upwards [MeasureTheory.ae_restrict_mem
    (measurableSet_Icc : MeasurableSet (I : Set ℝ))] with a ha
  rw [Set.indicator_of_mem ha]

/-- The distance-power section is integrable against the carrier measure. -/
private theorem integrable_abs_sub_vol' {p : ℝ} (hp : p < 1) (y : ℝ) :
    MeasureTheory.Integrable (fun a : ℝ => |a - y| ^ (-p)) vol := by
  have hint := Hurst.intervalIntegrable_abs_sub_rpow hp y (-2 : ℝ) 2
  have h4 := intervalIntegrable_iff.mp hint
  rw [Set.uIoc_of_le (by norm_num : (-2 : ℝ) ≤ 2)] at h4
  have h5 : MeasureTheory.IntegrableOn (fun a : ℝ => |a - y| ^ (-p)) (I : Set ℝ)
      MeasureTheory.volume := by
    refine h4.mono_set ?_
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    exact ⟨by linarith, by linarith⟩
  have hmeas : ((vol : MeasureTheory.Measure ℝ).restrict (I : Set ℝ))
      = MeasureTheory.volume.restrict (I : Set ℝ) :=
    MeasureTheory.Measure.restrict_restrict_of_subset
      (Subset.rfl : (I : Set ℝ) ⊆ (I : Set ℝ))
  have hind : MeasureTheory.Integrable
      ((I : Set ℝ).indicator (fun a : ℝ => |a - y| ^ (-p))) vol := by
    refine (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr ?_
    show MeasureTheory.Integrable (fun a : ℝ => |a - y| ^ (-p))
      ((vol : MeasureTheory.Measure ℝ).restrict (I : Set ℝ))
    rw [hmeas]
    exact h5
  exact hind.congr (indicator_ae_abs_sub' y)

/-- Pointwise domination of the squared Riesz kernel by the distance power. -/
private theorem rieszKernel_sq_le' {psi c : ℝ} {omega : ℝ → ℝ} {MR : ℝ}
    (hbdd : ∀ x : ℝ, |omega x| ≤ MR) (a y : ℝ) :
    rieszKernel psi c omega (a, y) ^ 2 ≤ c ^ 2 * MR ^ 2 * |a - y| ^ (-(2 * psi)) := by
  have hMR : (0 : ℝ) ≤ MR := le_trans (abs_nonneg (omega 0)) (hbdd 0)
  have hbind : ∀ x : ℝ, |(I : Set ℝ).indicator omega x| ≤ MR := by
    intro x
    by_cases hx : x ∈ (I : Set ℝ)
    · rw [Set.indicator_of_mem hx]; exact hbdd x
    · rw [Set.indicator_of_notMem hx, abs_zero]; exact hMR
  have hrpow : (|a - y| ^ (-psi)) ^ 2 = |a - y| ^ (-(2 * psi)) := by
    rw [← Real.rpow_natCast (|a - y| ^ (-psi)) 2, ← Real.rpow_mul (abs_nonneg (a - y)),
      show (2 : ℝ) * psi = psi * 2 from by ring, ← neg_mul]
    norm_num
  have hsplit : rieszKernel psi c omega (a, y) ^ 2
      = ((I : Set ℝ).indicator omega a * c) ^ 2 * (|a - y| ^ (-psi)) ^ 2 := by
    rw [rieszKernel_apply, mul_pow, mul_pow]
  have habs : |(I : Set ℝ).indicator omega a * c| ≤ MR * |c| := by
    rw [abs_mul]
    exact mul_le_mul (hbind a) (le_refl |c|) (abs_nonneg c) hMR
  have h1 : ((I : Set ℝ).indicator omega a * c) ^ 2 ≤ (MR * |c|) ^ 2 := by
    rw [← sq_abs ((I : Set ℝ).indicator omega a * c)]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  have h2 : (MR * |c|) ^ 2 = c ^ 2 * MR ^ 2 := by rw [mul_pow, sq_abs c]; ring
  calc rieszKernel psi c omega (a, y) ^ 2
      = ((I : Set ℝ).indicator omega a * c) ^ 2 * (|a - y| ^ (-psi)) ^ 2 := hsplit
    _ = ((I : Set ℝ).indicator omega a * c) ^ 2 * |a - y| ^ (-(2 * psi)) := by rw [hrpow]
    _ ≤ (MR * |c|) ^ 2 * |a - y| ^ (-(2 * psi)) :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (abs_nonneg (a - y)) _)
    _ = c ^ 2 * MR ^ 2 * |a - y| ^ (-(2 * psi)) := by rw [h2]

/-- `ofReal |x| ^ 2 = ofReal (|x| ^ 2)` (the packaging transport step). -/
private theorem ofReal_abs_pow_two (x : ℝ) :
    ENNReal.ofReal |x| ^ 2 = ENNReal.ofReal (|x| ^ 2) := by
  rw [pow_two, ← ENNReal.ofReal_mul (abs_nonneg x), ← pow_two]

/-- `|x| ≤ x ^ 2 + 1` (the section-`L¹` domination). -/
private theorem abs_le_sq_add_one (x : ℝ) : |x| ≤ x ^ 2 + 1 := by
  rw [← sq_abs x]
  have h : (0 : ℝ) ≤ |x| ^ 2 - 2 * |x| + 1 := by nlinarith [sq_nonneg (|x| - 1)]
  linarith [abs_nonneg x]

/-- **The capstone section-bound bundle** (spec §2, unconditional): at the capstone
Riesz data, the six packaged bound shapes consumed by `hP_of_sectionBounds` hold with
`E := c ^ 2 * MR ^ 2 * (2 + 2 / (1 - 2 * psi))` and
`D := |c| * MR * (2 + 2 / (1 - psi)) + Real.sqrt (2 * E)` — the tower bounds carrying
the finite per-level rate `max 1 ((hsNorm K ^ 2) ^ r)` (a single `r`-independent `E`
would be unsatisfiable whenever `hsNorm K > 1`). -/
theorem rieszKernel_sectionBounds_package {psi c : ℝ} {omega : ℝ → ℝ} {MR : ℝ}
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ MR)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y)
    (hpsi2 : 2 * psi < 1) (hpsi0 : 0 ≤ psi) :
    (∀ (r : ℕ) (y : ℝ),
      ∫⁻ a : ℝ, ENNReal.ofReal |compPowR r (rieszKernel psi c omega) (a, y)| ^ 2 ∂vol
        ≤ ENNReal.ofReal (c ^ 2 * MR ^ 2 * (2 + 2 / (1 - 2 * psi)) *
          max 1 ((hsNorm (rieszKernel psi c omega) ^ 2) ^ r)))
    ∧ (∀ (r : ℕ) (y : ℝ),
      ∫⁻ a : ℝ, ENNReal.ofReal |compPowR r (rieszKernel psi c omega) (y, a)| ^ 2 ∂vol
        ≤ ENNReal.ofReal (c ^ 2 * MR ^ 2 * (2 + 2 / (1 - 2 * psi)) *
          max 1 ((hsNorm (rieszKernel psi c omega) ^ 2) ^ r)))
    ∧ (∀ (r : ℕ) (y : ℝ),
      ∫⁻ a : ℝ, ENNReal.ofReal |compPowR r (rieszKernel psi c omega) (a, y)| ∂vol
        ≤ ENNReal.ofReal ((|c| * MR * (2 + 2 / (1 - psi))
            + Real.sqrt (2 * (c ^ 2 * MR ^ 2 * (2 + 2 / (1 - 2 * psi))))) *
          max 1 ((hsNorm (rieszKernel psi c omega) ^ 2) ^ r)))
    ∧ (∀ y : ℝ,
      ∫⁻ a : ℝ, ENNReal.ofReal |rieszKernel psi c omega (a, y)| ^ 2 ∂vol
        ≤ ENNReal.ofReal (c ^ 2 * MR ^ 2 * (2 + 2 / (1 - 2 * psi))))
    ∧ (∀ y : ℝ,
      ∫⁻ a : ℝ, ENNReal.ofReal |rieszKernel psi c omega (y, a)| ^ 2 ∂vol
        ≤ ENNReal.ofReal (c ^ 2 * MR ^ 2 * (2 + 2 / (1 - 2 * psi))))
    ∧ (∀ y : ℝ,
      ∫⁻ a : ℝ, ENNReal.ofReal |rieszKernel psi c omega (a, y)| ∂vol
        ≤ ENNReal.ofReal (|c| * MR * (2 + 2 / (1 - psi))
            + Real.sqrt (2 * (c ^ 2 * MR ^ 2 * (2 + 2 / (1 - 2 * psi)))))) := by
  set K : ℝ × ℝ → ℝ := rieszKernel psi c omega with hKdef
  set E : ℝ := c ^ 2 * MR ^ 2 * (2 + 2 / (1 - 2 * psi)) with hEdef
  set Df : ℝ := |c| * MR * (2 + 2 / (1 - psi))
    + Real.sqrt (2 * (c ^ 2 * MR ^ 2 * (2 + 2 / (1 - 2 * psi)))) with hDfdef
  have hMR : (0 : ℝ) ≤ MR := le_trans (abs_nonneg (omega 0)) (hbdd 0)
  have hEp : (0 : ℝ) ≤ E := by
    have h1 : (0 : ℝ) < 1 - 2 * psi := by linarith
    have h2 : (0 : ℝ) < 2 + 2 / (1 - 2 * psi) :=
      add_pos (by norm_num) (div_pos (by norm_num) h1)
    exact mul_nonneg (mul_nonneg (sq_nonneg c) (sq_nonneg MR)) h2.le
  -- everywhere section-square-integrability, both orientations
  have hintcol : ∀ z : ℝ, Integrable (fun a : ℝ => K (a, z) ^ 2) vol := by
    intro z
    have hdom : Integrable (fun a : ℝ => c ^ 2 * MR ^ 2 * |a - z| ^ (-(2 * psi))) vol :=
      (integrable_abs_sub_vol' (by linarith) z).const_mul _
    refine hdom.mono ?_ ?_
    · exact (((measurable_rieszKernel homega).comp
        (measurable_id.prodMk measurable_const)).pow_const 2).aestronglyMeasurable
    · filter_upwards with a
      have h := rieszKernel_sq_le' (psi := psi) (c := c) hbdd a z
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
        abs_of_nonneg (by positivity)]
      exact h
  have hintrow : ∀ z : ℝ, Integrable (fun a : ℝ => K (z, a) ^ 2) vol := by
    intro z
    have hdom : Integrable (fun a : ℝ => c ^ 2 * MR ^ 2 * |a - z| ^ (-(2 * psi))) vol :=
      (integrable_abs_sub_vol' (by linarith) z).const_mul _
    refine hdom.mono ?_ ?_
    · exact (((measurable_rieszKernel homega).comp
        (measurable_const.prodMk measurable_id)).pow_const 2).aestronglyMeasurable
    · filter_upwards with a
      have h := rieszKernel_sq_le' (psi := psi) (c := c) hbdd z a
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
        abs_of_nonneg (by positivity)]
      rwa [abs_sub_comm z a] at h
  -- the Bochner-form base bounds
  have hEcol : ∀ y : ℝ, ∫ a : ℝ, K (a, y) ^ 2 ∂vol ≤ E := by
    intro y
    have hcongr : (∫ a : ℝ, K (a, y) ^ 2 ∂vol) = ∫ a : ℝ, |K (a, y)| ^ 2 ∂vol :=
      integral_congr_ae (Filter.Eventually.of_forall fun a => (sq_abs (K (a, y))).symm)
    rw [hcongr]
    exact rieszKernel_section_sq (psi := psi) (c := c) (MR := MR) hbdd hconst hpsi2 hpsi0 y
  have hErow : ∀ x : ℝ, ∫ a : ℝ, K (x, a) ^ 2 ∂vol ≤ E := by
    intro x
    have hcongr : (∫ a : ℝ, K (x, a) ^ 2 ∂vol) = ∫ a : ℝ, |K (x, a)| ^ 2 ∂vol :=
      integral_congr_ae (Filter.Eventually.of_forall fun a => (sq_abs (K (x, a))).symm)
    rw [hcongr]
    exact rieszKernel_section_sq_symm (psi := psi) (c := c) (MR := MR) hbdd hpsi2 hpsi0 x
  -- the composition tower keeps the section bounds (every level)
  have haux := compPowR_section_aux (K := K) (measurable_rieszKernel homega)
    (hsKernel_rieszKernel hpow homega hbdd hg) hEcol hErow hintcol hintrow
  -- the per-level tower `L²` bounds in `lintegral`/`ofReal` form, both orientations
  have hL2col : ∀ (r : ℕ) (y : ℝ),
      ∫⁻ a : ℝ, ENNReal.ofReal |compPowR r K (a, y)| ^ 2 ∂vol
        ≤ ENNReal.ofReal (E * max 1 ((hsNorm K ^ 2) ^ r)) := by
    intro r y
    obtain ⟨hcol, hrow, hmemCol, hmemRow⟩ := haux r
    have hint2 : Integrable (fun a : ℝ => |compPowR r K (a, y)| ^ 2) vol :=
      (MemLp.integrable_sq (hmemCol y)).congr
        (Filter.Eventually.of_forall fun a => (sq_abs _).symm)
    calc ∫⁻ a : ℝ, ENNReal.ofReal |compPowR r K (a, y)| ^ 2 ∂vol
        = ∫⁻ a : ℝ, ENNReal.ofReal (|compPowR r K (a, y)| ^ 2) ∂vol :=
          lintegral_congr_pt fun a => ofReal_abs_pow_two _
      _ = ENNReal.ofReal (∫ a : ℝ, |compPowR r K (a, y)| ^ 2 ∂vol) :=
          (ofReal_integral_eq_lintegral_ofReal hint2
            (Filter.Eventually.of_forall fun a =>
              sq_nonneg (abs (compPowR r K (a, y))))).symm
      _ ≤ ENNReal.ofReal (E * (hsNorm K ^ 2) ^ r) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [integral_congr_ae (Filter.Eventually.of_forall fun a =>
            sq_abs (compPowR r K (a, y)))]
          exact hcol y
      _ ≤ ENNReal.ofReal (E * max 1 ((hsNorm K ^ 2) ^ r)) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (le_max_right 1 _) hEp)
  have hL2row : ∀ (r : ℕ) (y : ℝ),
      ∫⁻ a : ℝ, ENNReal.ofReal |compPowR r K (y, a)| ^ 2 ∂vol
        ≤ ENNReal.ofReal (E * max 1 ((hsNorm K ^ 2) ^ r)) := by
    intro r y
    obtain ⟨hcol, hrow, hmemCol, hmemRow⟩ := haux r
    have hint2 : Integrable (fun a : ℝ => |compPowR r K (y, a)| ^ 2) vol :=
      (MemLp.integrable_sq (hmemRow y)).congr
        (Filter.Eventually.of_forall fun a => (sq_abs _).symm)
    calc ∫⁻ a : ℝ, ENNReal.ofReal |compPowR r K (y, a)| ^ 2 ∂vol
        = ∫⁻ a : ℝ, ENNReal.ofReal (|compPowR r K (y, a)| ^ 2) ∂vol :=
          lintegral_congr_pt fun a => ofReal_abs_pow_two _
      _ = ENNReal.ofReal (∫ a : ℝ, |compPowR r K (y, a)| ^ 2 ∂vol) :=
          (ofReal_integral_eq_lintegral_ofReal hint2
            (Filter.Eventually.of_forall fun a =>
              sq_nonneg (abs (compPowR r K (y, a))))).symm
      _ ≤ ENNReal.ofReal (E * (hsNorm K ^ 2) ^ r) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [integral_congr_ae (Filter.Eventually.of_forall fun a =>
            sq_abs (compPowR r K (y, a)))]
          exact hrow y
      _ ≤ ENNReal.ofReal (E * max 1 ((hsNorm K ^ 2) ^ r)) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (le_max_right 1 _) hEp)
  -- the per-level tower `L¹` bounds (section Cauchy–Schwarz from the `L²` bounds)
  have hL1col : ∀ (r : ℕ) (y : ℝ),
      ∫⁻ a : ℝ, ENNReal.ofReal |compPowR r K (a, y)| ∂vol
        ≤ ENNReal.ofReal (Df * max 1 ((hsNorm K ^ 2) ^ r)) := by
    intro r y
    obtain ⟨hcol, hrow, hmemCol, hmemRow⟩ := haux r
    have hN0 : (0 : ℝ) ≤ (hsNorm K ^ 2) ^ r := pow_nonneg (sq_nonneg (hsNorm K)) r
    -- the section is `L¹`-integrable (domination by the square + 1)
    have hint1 : Integrable (fun a : ℝ => |compPowR r K (a, y)|) vol := by
      have hsq : Integrable (fun a : ℝ => compPowR r K (a, y) ^ 2) vol :=
        MemLp.integrable_sq (hmemCol y)
      have hdom : Integrable (fun a : ℝ => compPowR r K (a, y) ^ 2 + 1) vol :=
        hsq.add (integrable_const 1)
      refine hdom.mono ?_ ?_
      · exact (((measurable_compPowR r (measurable_rieszKernel homega)).comp
          (measurable_id.prodMk measurable_const)).abs).aestronglyMeasurable
      · filter_upwards with a
        show ‖|compPowR r K (a, y)|‖ ≤ ‖compPowR r K (a, y) ^ 2 + 1‖
        have h1 : ‖|compPowR r K (a, y)|‖ = |compPowR r K (a, y)| := by simp
        have h2 : ‖compPowR r K (a, y) ^ 2 + 1‖ = compPowR r K (a, y) ^ 2 + 1 := by
          rw [Real.norm_eq_abs,
            abs_of_nonneg (show (0 : ℝ) ≤ compPowR r K (a, y) ^ 2 + 1 by positivity)]
        rw [h1, h2]
        exact abs_le_sq_add_one _
    -- the section Cauchy–Schwarz bound (transposed kernel against the constant `1`)
    have hcs := sectionCS (K := fun p : ℝ × ℝ => compPowR r K p.swap)
      (L := fun _ => (1 : ℝ)) y y (hmemCol y) (memLp_const (1 : ℝ))
    have hbeta : ∀ t : ℝ,
        |(fun p : ℝ × ℝ => compPowR r K p.swap) (y, t)|
            * |(fun _ => (1 : ℝ)) (t, y)|
          = |compPowR r K (t, y)| := by
      intro t
      show |compPowR r K (t, y)| * |(1 : ℝ)| = |compPowR r K (t, y)|
      simp
    rw [integral_congr_ae (Filter.Eventually.of_forall hbeta)] at hcs
    have hsec2 : secE2 (fun p : ℝ × ℝ => compPowR r K p.swap) y
        = ∫ t : ℝ, compPowR r K (t, y) ^ 2 ∂vol := rfl
    have hmass : vol.real Set.univ = 2 := by
      show ((vol : Measure ℝ) Set.univ).toReal = 2
      rw [vol_univ_eq_two]
      norm_num
    have hsec1 : secE1 (fun _ => (1 : ℝ)) y = 2 := by
      simp only [secE1, one_pow, integral_const, smul_eq_mul, mul_one, hmass]
    rw [hsec2, hsec1] at hcs
    have hSN : Real.sqrt ((hsNorm K ^ 2) ^ r) ≤ max 1 ((hsNorm K ^ 2) ^ r) := by
      rcases Nat.eq_zero_or_pos r with hr | hr
      · subst hr
        simp
      · rcases le_or_gt 1 ((hsNorm K ^ 2) ^ r) with h | h
        · have hx : Real.sqrt ((hsNorm K ^ 2) ^ r)
                ≤ Real.sqrt (((hsNorm K ^ 2) ^ r) ^ 2) :=
              Real.sqrt_le_sqrt (le_self_pow₀ h (by norm_num))
          rw [Real.sqrt_sq (pow_nonneg (sq_nonneg (hsNorm K)) r)] at hx
          exact hx.trans (le_max_right _ _)
        · exact (Real.sqrt_le_sqrt h.le).trans
            (by rw [Real.sqrt_one]; exact le_max_left _ _)
    calc ∫⁻ a : ℝ, ENNReal.ofReal |compPowR r K (a, y)| ∂vol
        = ENNReal.ofReal (∫ a : ℝ, |compPowR r K (a, y)| ∂vol) :=
          (ofReal_integral_eq_lintegral_ofReal hint1
            (Filter.Eventually.of_forall fun a => abs_nonneg (compPowR r K (a, y)))).symm
      _ ≤ ENNReal.ofReal (Real.sqrt (2 * E) * max 1 ((hsNorm K ^ 2) ^ r)) := by
          refine ENNReal.ofReal_le_ofReal (hcs.trans ?_)
          calc Real.sqrt (∫ t : ℝ, compPowR r K (t, y) ^ 2 ∂vol) * Real.sqrt 2
              ≤ Real.sqrt (E * (hsNorm K ^ 2) ^ r) * Real.sqrt 2 := by
                refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg 2)
                exact Real.sqrt_le_sqrt (hcol y)
            _ = Real.sqrt ((E * (hsNorm K ^ 2) ^ r) * 2) := by
                rw [Real.sqrt_mul (mul_nonneg hEp hN0)]
            _ = Real.sqrt ((2 * E) * (hsNorm K ^ 2) ^ r) :=
                congrArg Real.sqrt (by ring)
            _ = Real.sqrt (2 * E) * Real.sqrt ((hsNorm K ^ 2) ^ r) := by
                rw [Real.sqrt_mul (mul_nonneg (by norm_num) hEp)]
            _ ≤ Real.sqrt (2 * E) * max 1 ((hsNorm K ^ 2) ^ r) :=
                mul_le_mul_of_nonneg_left hSN (Real.sqrt_nonneg (2 * E))
      _ ≤ ENNReal.ofReal (Df * max 1 ((hsNorm K ^ 2) ^ r)) := by
          refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_
            (by positivity : (0 : ℝ) ≤ max 1 ((hsNorm K ^ 2) ^ r)))
          have h1 : (0 : ℝ) < 1 - psi := by linarith
          have h2 : (0 : ℝ) ≤ 2 + 2 / (1 - psi) :=
            (add_pos (by norm_num) (div_pos (by norm_num) h1)).le
          exact le_add_of_nonneg_left
            (mul_nonneg (mul_nonneg (abs_nonneg c) hMR) h2)
  refine ⟨hL2col, hL2row, hL1col, ?_, ?_, ?_⟩
  · intro y
    have h := hL2col 0 y
    rwa [pow_zero, max_self, mul_one] at h
  · intro y
    have h := hL2row 0 y
    rwa [pow_zero, max_self, mul_one] at h
  · intro y
    have h := hL1col 0 y
    rwa [pow_zero, max_self, mul_one] at h

/-- The `hEK1`-shape: uniform section-`L²` bound of the Riesz kernel (lintegral form). -/
theorem rieszKernel_lintSq {psi c : ℝ} {omega : ℝ → ℝ} {MR : ℝ}
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ MR)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y)
    (hpsi2 : 2 * psi < 1) (hpsi0 : 0 ≤ psi) (y : ℝ) :
    ∫⁻ a : ℝ, ENNReal.ofReal |rieszKernel psi c omega (a, y)| ^ 2 ∂vol
      ≤ ENNReal.ofReal (c ^ 2 * MR ^ 2 * (2 + 2 / (1 - 2 * psi))) :=
  (rieszKernel_sectionBounds_package hpow homega hbdd hg hconst hpsi2 hpsi0).2.2.2.1 y

/-- The `hEK2`-shape: uniform transposed section-`L²` bound of the Riesz kernel. -/
theorem rieszKernel_lintSq_symm {psi c : ℝ} {omega : ℝ → ℝ} {MR : ℝ}
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ MR)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y)
    (hpsi2 : 2 * psi < 1) (hpsi0 : 0 ≤ psi) (y : ℝ) :
    ∫⁻ a : ℝ, ENNReal.ofReal |rieszKernel psi c omega (y, a)| ^ 2 ∂vol
      ≤ ENNReal.ofReal (c ^ 2 * MR ^ 2 * (2 + 2 / (1 - 2 * psi))) :=
  (rieszKernel_sectionBounds_package hpow homega hbdd hg hconst hpsi2 hpsi0).2.2.2.2.1 y

/-- The `hDK1`-shape: uniform section-`L¹` bound of the Riesz kernel (lintegral form). -/
theorem rieszKernel_lintL1 {psi c : ℝ} {omega : ℝ → ℝ} {MR : ℝ}
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ MR)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y)
    (hpsi2 : 2 * psi < 1) (hpsi0 : 0 ≤ psi) (y : ℝ) :
    ∫⁻ a : ℝ, ENNReal.ofReal |rieszKernel psi c omega (a, y)| ∂vol
      ≤ ENNReal.ofReal (|c| * MR * (2 + 2 / (1 - psi))
          + Real.sqrt (2 * (c ^ 2 * MR ^ 2 * (2 + 2 / (1 - 2 * psi))))) :=
  (rieszKernel_sectionBounds_package hpow homega hbdd hg hconst hpsi2 hpsi0).2.2.2.2.2 y

/-! ### Task 2: the cycle-encoding bridge (spec §7) -/

/-- The two cyclic successors of the landed layers agree. -/
private theorem finCyclicSucc_eq_cycleSucc' {k : ℕ} (i : Fin k) :
    Hurst.finCyclicSucc i = cycleSucc i := by
  by_cases h : i.val + 1 < k
  · simp only [Hurst.finCyclicSucc, cycleSucc, dif_pos h]
  · simp only [Hurst.finCyclicSucc, cycleSucc, dif_neg h]

/-- The `Measure.pi vol^k`-integral equals the `volume^k`-integral for integrands
supported on the `I^k`-cylinder (the general-`k` form of the landed `k = 2` transport
`integral_pi_vol_eq_pi_volume`, via `restrict_pi_pi`). -/
private theorem integral_pi_vol_eq_volume_cube (k : ℕ) (F : (Fin k → ℝ) → ℝ)
    (hF : ∀ z : Fin k → ℝ,
      F z = (Set.pi univ fun _ : Fin k => (I : Set ℝ)).indicator F z) :
    (∫ z : Fin k → ℝ, F z ∂(Measure.pi fun _ : Fin k => vol))
      = (∫ z : Fin k → ℝ, F z ∂(volume : Measure (Fin k → ℝ))) := by
  have hmeasSet : MeasurableSet (Set.pi univ fun _ : Fin k => (I : Set ℝ)) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hmeq : (Measure.pi fun _ : Fin k => (volume : Measure ℝ)).restrict
      (Set.pi univ fun _ : Fin k => (I : Set ℝ))
      = (Measure.pi fun _ : Fin k => vol).restrict
        (Set.pi univ fun _ : Fin k => (I : Set ℝ)) := by
    simp only [restrict_pi_pi, vol]
    rw [Measure.restrict_restrict_of_subset (Set.Subset.refl (I : Set ℝ))]
  have hint1 : (∫ z : Fin k → ℝ, F z ∂(Measure.pi fun _ : Fin k => vol))
      = ∫ z : Fin k → ℝ, F z
          ∂((Measure.pi fun _ : Fin k => vol).restrict
            (Set.pi univ fun _ : Fin k => (I : Set ℝ))) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hF), integral_indicator hmeasSet]
  have hint2 : (∫ z : Fin k → ℝ, F z ∂(volume : Measure (Fin k → ℝ)))
      = ∫ z : Fin k → ℝ, F z
          ∂((volume : Measure (Fin k → ℝ)).restrict
            (Set.pi univ fun _ : Fin k => (I : Set ℝ))) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hF), integral_indicator hmeasSet]
  rw [hint1, hint2]
  exact congrArg (fun M : Measure (Fin k → ℝ) => ∫ z : Fin k → ℝ, F z ∂M) hmeq.symm

/-- **The cycle-encoding bridge (spec §7)**: the HS `k`-cycle integral of the Riesz
kernel IS the continuum weighted cycle integral, unconditionally for every `k`
(the `vol^k`-integral of the cyclic kernel product transported along the
`I^k`-cylinder restriction to `volume^k`; the integrands match by
`finCyclicSucc_eq_cycleSucc'` and `rieszKernel_apply`).  This replaces the packaged
`hW` hypothesis of `hasSum_weighted_of_gate`. -/
theorem hW_bridge (psi c : ℝ) (omega : ℝ → ℝ) (k : ℕ) :
    cycleIntegral k (rieszKernel psi c omega)
      = Hurst.weightedRieszCycleIntegral k psi c omega := by
  have hzero : ∀ z : Fin k → ℝ,
      z ∉ (Set.pi univ fun _ : Fin k => (I : Set ℝ)) →
      (∏ i : Fin k, rieszKernel psi c omega (z i, z (cycleSucc i))) = 0 := by
    intro z hz
    have hex : ∃ i : Fin k, z i ∉ (I : Set ℝ) := by
      by_contra hall
      refine hz fun i _ => not_not.mp fun hcon => hall ⟨i, hcon⟩
    obtain ⟨i, hi⟩ := hex
    refine Finset.prod_eq_zero (i := i) (Finset.mem_univ i) ?_
    rw [rieszKernel_apply, Set.indicator_of_notMem hi]
    ring
  have hind : ∀ z : Fin k → ℝ,
      (∏ i : Fin k, rieszKernel psi c omega (z i, z (cycleSucc i)))
        = (Set.pi univ fun _ : Fin k => (I : Set ℝ)).indicator
            (fun w : Fin k → ℝ =>
              ∏ i : Fin k, rieszKernel psi c omega (w i, w (cycleSucc i))) z := by
    intro z
    by_cases hz : z ∈ (Set.pi univ fun _ : Fin k => (I : Set ℝ))
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz]
      exact hzero z hz
  show (∫ z : Fin k → ℝ,
      ∏ i : Fin k, rieszKernel psi c omega (z i, z (cycleSucc i))
      ∂(Measure.pi fun _ : Fin k => vol)) = _
  rw [integral_pi_vol_eq_volume_cube k _ hind, weightedRieszCycleIntegral_eq_kernelProd]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  exact Finset.prod_congr rfl fun i _ => by rw [finCyclicSucc_eq_cycleSucc' i]

/-! ### The capstone: the general-`k` HasSum at the constructed enumeration -/

/-- **The capstone `HasSum` at the constructed enumeration (all `k ≥ 2`)**: the
hypotheses are exactly the capstone Riesz data (`hpow homega hbdd hg hconst`), the
feasibility window (`hpsi2 : 2 * psi < 1`, `hpsi0 : 0 ≤ psi`), a Hilbert basis `e`
(any one works — `hBridge` is basis-uniform), and the two bridge clauses
`hBridge`/`hPair`.  The packaged `hW` hypothesis and all six section-bound shapes are
discharged internally (`hW_bridge`, `rieszKernel_sectionBounds_package`). -/
theorem rieszSpectrumVal_hasSum_of_bridge
    (psi c : ℝ) (omega : ℝ → ℝ) (MR : ℝ)
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ MR)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y)
    (hpsi2 : 2 * psi < 1) (hpsi0 : 0 ≤ psi)
    (e : HilbertBasis ℕ ℝ L2)
    (hBridge : ∀ j : ℕ, 2 ≤ j → ∀ (e' : HilbertBasis ℕ ℝ L2),
      (∑' i : ℕ, inner ℝ
        ((TOpEnd' (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg) ^ j)
          (e' i)) (e' i))
        = ∑' m : ℕ,
          rieszSpectrumVal psi c omega MR hpow homega hbdd hg hconst m ^ j)
    (hPair : ∀ (k : ℕ) (x : L2),
      (TOp (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg))
        ((TOp (compPowR (k - 2) (rieszKernel psi c omega))
          (hsKernel_compPowR (k - 2) (measurable_rieszKernel homega)
            (hsKernel_rieszKernel hpow homega hbdd hg))) x)
        = (TOpEnd' (rieszKernel psi c omega)
            (hsKernel_rieszKernel hpow homega hbdd hg) ^ k) x)
    (k : ℕ) (hk : 2 ≤ k) :
    HasSum (fun j : ℕ => rieszSpectrumVal psi c omega MR hpow homega hbdd hg hconst j ^ k)
      (Hurst.weightedRieszCycleIntegral k psi c omega) := by
  obtain ⟨hE1, hE2, hD1, hEK1, hEK2, hDK1⟩ :=
    rieszKernel_sectionBounds_package hpow homega hbdd hg hconst hpsi2 hpsi0
  exact hasSum_weighted_of_gate (rieszKernel psi c omega) psi c omega
    (measurable_rieszKernel homega) (hsKernel_rieszKernel hpow homega hbdd hg)
    (isCompactOperator_TOp_riesz hpow homega hbdd hg hconst)
    (isSymmetric_TOp_rieszKernel hpow homega hbdd hg hconst)
    (fun k (_ : 2 ≤ k) => hW_bridge psi c omega k)
    (fun k => hsKernel_compPowR (k - 2) (measurable_rieszKernel homega)
      (hsKernel_rieszKernel hpow homega hbdd hg))
    e hBridge hPair hE1 hE2 hD1 hEK1 hEK2 hDK1
    (isDiagEnum_of_entry
      (rieszSpectrum_pack psi c omega MR hpow homega hbdd hg hconst).1)
    (rieszSpectrum_pack psi c omega MR hpow homega hbdd hg hconst).2.1 k hk

/-- **`hGen` at the constructed enumeration** — the CapstoneV3 `hGen` clause discharged
by the two bridge hypotheses: the remaining hypotheses are exactly the capstone Riesz
data, the feasibility window, `hpsi0 : 0 ≤ psi`, `hBridge`, `hPair`, and a Hilbert
basis. -/
theorem rieszSpectrumVal_hGen_of_bridge
    (psi c : ℝ) (omega : ℝ → ℝ) (MR : ℝ)
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ MR)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hconst : ∀ x y : ℝ, (I : Set ℝ).indicator omega x = (I : Set ℝ).indicator omega y)
    (hpsi2 : 2 * psi < 1) (hpsi0 : 0 ≤ psi)
    (e : HilbertBasis ℕ ℝ L2)
    (hBridge : ∀ j : ℕ, 2 ≤ j → ∀ (e' : HilbertBasis ℕ ℝ L2),
      (∑' i : ℕ, inner ℝ
        ((TOpEnd' (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg) ^ j)
          (e' i)) (e' i))
        = ∑' m : ℕ,
          rieszSpectrumVal psi c omega MR hpow homega hbdd hg hconst m ^ j)
    (hPair : ∀ (k : ℕ) (x : L2),
      (TOp (rieszKernel psi c omega) (hsKernel_rieszKernel hpow homega hbdd hg))
        ((TOp (compPowR (k - 2) (rieszKernel psi c omega))
          (hsKernel_compPowR (k - 2) (measurable_rieszKernel homega)
            (hsKernel_rieszKernel hpow homega hbdd hg))) x)
        = (TOpEnd' (rieszKernel psi c omega)
            (hsKernel_rieszKernel hpow homega hbdd hg) ^ k) x)
    (k : ℕ) (hk : 3 ≤ k) :
    HasSum (fun j : ℕ => rieszSpectrumVal psi c omega MR hpow homega hbdd hg hconst j ^ k)
      (Hurst.weightedRieszCycleIntegral k psi c omega) :=
  rieszSpectrumVal_hasSum_of_bridge psi c omega MR hpow homega hbdd hg hconst hpsi2 hpsi0
    e hBridge hPair k (le_trans (by norm_num : (2 : ℕ) ≤ 3) hk)

end HS

end
