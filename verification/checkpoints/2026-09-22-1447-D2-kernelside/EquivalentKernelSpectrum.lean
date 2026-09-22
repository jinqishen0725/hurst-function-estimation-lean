import Mathlib
import Hurst.GeneralKHasSumFinal
import Hurst.PositiveSquareRoot
import Hurst.TracePerturbationEstimate
import Hurst.CountableEigenfamily
import Hurst.EndLevelTraceBridge
import Hurst.UnweightedRieszOperator

/-!
# M1-D2: the equivalent-kernel spectrum route (`B = K^{1/2} W K^{1/2}`)

Assembly module of the hconst-elimination milestone (spec §5 of
`milestone1_hconst_elimination_math_spec.md`, A8–A9 compressed-spectrum route).
The spectral object is `B = S ∘ M_omega ∘ S` with `S = sqrtOp` the positive
square root of the *unweighted* Riesz operator (`Hurst.UnweightedRieszOperator`,
`Hurst.PositiveSquareRoot`); the bridge target is the **existing**
`Hurst.weightedRieszCycleIntegral`, whose operator avatar is the *weighted*
kernel operator `TOp (rieszKernel psi c omega)` (left multiplication by the
weight IS the kernel operation).

## Honest session status (declared, not hidden)

Landed in this file, **unconditionally and without any `hconst`-type premise**:

* `rieszKernel_section_sq_col`, `rieszKernel_sectionBounds_nohconst`,
  `hP_rieszKernel_nohconst` — the Riesz section-bounds package with the
  unsatisfiable `hconst` premise REMOVED (the landed
  `rieszKernel_sectionBounds_package` consumed `hconst` only to rewrite the
  weight indicator as a constant; the pointwise bound `|ind ω a| ≤ MR` suffices).
* `diagSum_TOpRiesz_pow_eq_weightedCycle` — **the kernel side of the D2 bridge
  (steps 3-RHS, 4 and 5 of the compressed route)**: for every `k ≥ 2` and every
  Hilbert basis `e`, the power-diagonal series of the weighted kernel operator
  is summable and

    ∑' i, ⟪((TOp (rieszKernel psi c omega)) ^ k) (e i), e i⟫
      = Hurst.weightedRieszCycleIntegral k psi c omega.

  Route: `hPair_riesz` (operator power = kernel tower) + `tracePair_comp_tsum`
  (diagonal pairing = `cycle2` of the tower) + `cycleIntegral_eq_cycle2_pow`
  (peel induction, integrability from the no-hconst section package) +
  `hW_bridge` (cycle-integral encoding).  **None of these steps needs symmetry
  of the weighted kernel operator** — this is where the old
  `rieszSpectrumVal_hGen` line consumed the unsatisfiable `hconst`, and the
  present theorem replaces that dependence on the trace-power side.

Registered remaining gap (NOT landed here, honestly declared): the
**compression identity** `Diag_k(B) = Diag_k((WK)^k)` (spec §5 steps 0–3 of the
A8–A9 route: countable truncations `K_N`, finite-rank `B_N'`, the three
convergences of step 2 — of which step 2(c), the A4-type perturbation estimate,
IS landed in `Hurst.TracePerturbationEstimate.diag_pow_sub_diag_pow_le` — and
the finite-matrix A8 identity, landed in `Hurst.FiniteMatrixTraceCycle`).
Until it lands, `diagSum_B_eq_weightedCycle` and
`exists_weightedRieszSpectrum_min` are NOT produced by this file; packaging the
bridge equality itself as a hypothesis is forbidden by the session discipline
(no vacuous packaging of the pending goal).
-/

open MeasureTheory
open scoped Real

noncomputable section

namespace HS

/-! ### Steps 4–5 (kernel side): the no-`hconst` section package -/

/-- `x ≤ y` between nonnegatives squares (local copy of the private helper of
`Hurst.RieszSectionBounds`, unchanged mathematics). -/
private theorem sq_le_sq_of_nonneg' {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    x ^ 2 ≤ y ^ 2 := by
  have hy : 0 ≤ y := le_trans hx hxy
  nlinarith [sq_nonneg (y - x)]

/-- Off `I` the carrier measure gives no mass (local copy of the private helper
of `Hurst.RieszSectionBounds`). -/
private theorem indicator_ae_abs_sub' {p : ℝ} (y : ℝ) :
    ((I : Set ℝ).indicator (fun b : ℝ => |b - y| ^ (-p)))
      =ᵐ[vol] (fun a : ℝ => |a - y| ^ (-p)) := by
  filter_upwards [MeasureTheory.ae_restrict_mem
    (measurableSet_Icc : MeasurableSet (I : Set ℝ))] with a ha
  rw [Set.indicator_of_mem ha]

/-- Integrability of the distance power on `I` (local copy of the private
helper of `Hurst.RieszSectionBounds`). -/
private theorem integrable_indicator_abs_sub' {p : ℝ} (hp : p < 1) (y : ℝ) :
    MeasureTheory.Integrable ((I : Set ℝ).indicator (fun a : ℝ => |a - y| ^ (-p))) vol := by
  have hint := Hurst.intervalIntegrable_abs_sub_rpow hp y (-2 : ℝ) 2
  have h3 : MeasureTheory.IntegrableOn (fun a : ℝ => |a - y| ^ (-p))
      (Set.Ioc (-2 : ℝ) 2) MeasureTheory.volume := by
    have h4 := intervalIntegrable_iff.mp hint
    rwa [Set.uIoc_of_le (by norm_num)] at h4
  have h5 : MeasureTheory.IntegrableOn (fun a : ℝ => |a - y| ^ (-p)) (I : Set ℝ)
      MeasureTheory.volume := by
    refine h3.mono_set ?_
    intro x hx
    have h1x : (-1 : ℝ) ≤ x := hx.1
    have h2x : x ≤ 1 := hx.2
    exact ⟨by linarith, by linarith⟩
  have hmeas : ((vol : MeasureTheory.Measure ℝ).restrict (I : Set ℝ))
      = MeasureTheory.volume.restrict (I : Set ℝ) :=
    MeasureTheory.Measure.restrict_restrict_of_subset
      (Set.Subset.rfl : (I : Set ℝ) ⊆ (I : Set ℝ))
  refine (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr ?_
  show MeasureTheory.Integrable (fun a : ℝ => |a - y| ^ (-p)) ((vol).restrict (I : Set ℝ))
  rw [hmeas]
  exact h5

/-- Integrability of the plain distance power against the carrier measure
(local copy of the private helper of `Hurst.RieszSectionBounds`). -/
private theorem integrable_abs_sub_vol' {p : ℝ} (hp : p < 1) (y : ℝ) :
    MeasureTheory.Integrable (fun a : ℝ => |a - y| ^ (-p)) vol :=
  MeasureTheory.Integrable.congr (integrable_indicator_abs_sub' hp y)
    (indicator_ae_abs_sub' y)

/-- The plain distance-power integral equals the indicator-form integral
(local copy of the private helper of `Hurst.RieszSectionBounds`). -/
private theorem integral_abs_sub_vol_eq' {p : ℝ} (_hp : p < 1) (y : ℝ) :
    (∫ a : ℝ, |a - y| ^ (-p) ∂vol)
      = (∫ a : ℝ, (I : Set ℝ).indicator (fun b : ℝ => |b - y| ^ (-p)) a ∂vol) :=
  MeasureTheory.integral_congr_ae (indicator_ae_abs_sub' y).symm

/-- `ofReal |x| ^ 2 = ofReal (|x| ^ 2)` (transport step; local copy of the
private helper of `Hurst.GeneralKHasSumFinal`, unchanged mathematics). -/
private theorem ofReal_abs_pow_two (x : ℝ) :
    ENNReal.ofReal |x| ^ 2 = ENNReal.ofReal (|x| ^ 2) := by
  rw [pow_two, ← ENNReal.ofReal_mul (abs_nonneg x), ← pow_two]

/-- `|x| ≤ x ^ 2 + 1` (section-`L¹` domination; local copy of the private
helper of `Hurst.GeneralKHasSumFinal`, unchanged mathematics). -/
private theorem abs_le_sq_add_one (x : ℝ) : |x| ≤ x ^ 2 + 1 := by
  rw [← sq_abs x]
  have h : (0 : ℝ) ≤ |x| ^ 2 - 2 * |x| + 1 := by nlinarith [sq_nonneg (|x| - 1)]
  linarith [abs_nonneg x]

/-- Pointwise domination of the squared Riesz kernel by the distance power —
**no `hconst`** (local copy of the private `rieszKernel_sq_le'` of
`Hurst.GeneralKHasSumFinal`; the landed version's mathematics never used
constancy of the weight). -/
private theorem rieszKernel_sq_le_nohconst {psi c : ℝ} {omega : ℝ → ℝ} {MR : ℝ}
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

/-- **Uniform column section-`L²` bound of the Riesz kernel, without `hconst`**:
the landed `rieszKernel_section_sq` (RieszSectionBounds) consumed `hconst` only
to rewrite the weight indicator as a constant; the pointwise bound
`|(I).indicator omega a| ≤ MR` on the *integrated* variable suffices for the
domination argument.  (The transposed twin `rieszKernel_section_sq_symm` was
already hconst-free for the same reason.) -/
theorem rieszKernel_section_sq_col {psi c : ℝ} {omega : ℝ → ℝ} {MR : ℝ}
    (hbdd : ∀ x : ℝ, |omega x| ≤ MR)
    (hpsi : 2 * psi < 1) (hpsi0 : 0 ≤ psi)
    (y : ℝ) :
    ∫ a : ℝ, |rieszKernel psi c omega (a, y)| ^ 2 ∂vol
      ≤ c ^ 2 * MR ^ 2 * (2 + 2 / (1 - 2 * psi)) := by
  have hMR : (0 : ℝ) ≤ MR := le_trans (abs_nonneg (omega 0)) (hbdd 0)
  have hbind : ∀ a : ℝ, |(I : Set ℝ).indicator omega a| ≤ MR := by
    intro a
    by_cases ha : a ∈ (I : Set ℝ)
    · rw [Set.indicator_of_mem ha]; exact hbdd a
    · rw [Set.indicator_of_notMem ha, abs_zero]; exact hMR
  have h1 : ∀ a : ℝ, |rieszKernel psi c omega (a, y)|
      = |(I : Set ℝ).indicator omega a| * |c| * (|a - y| ^ (-psi)) := by
    intro a
    rw [rieszKernel_apply, abs_mul, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg (a - y)) _)]
  have hrpow : ∀ t : ℝ, (|t| ^ (-psi)) ^ 2 = |t| ^ (-(2 * psi)) := by
    intro t
    rw [← Real.rpow_natCast (|t| ^ (-psi)) 2, ← Real.rpow_mul (abs_nonneg t),
      show (2 : ℝ) * psi = psi * 2 from by ring, ← neg_mul]
    norm_num
  have ptw : ∀ a : ℝ, |rieszKernel psi c omega (a, y)| ^ 2
      ≤ c ^ 2 * MR ^ 2 * |a - y| ^ (-(2 * psi)) := by
    intro a
    rw [h1 a, ← hrpow (a - y)]
    have hz : (0 : ℝ) ≤ |a - y| ^ (-psi) := Real.rpow_nonneg (abs_nonneg (a - y)) _
    have hx0 : (0:ℝ) ≤ |(I : Set ℝ).indicator omega a| * |c| * (|a - y| ^ (-psi)) :=
      mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg c)) hz
    have h2 : (|(I : Set ℝ).indicator omega a| * |c| * (|a - y| ^ (-psi))) ^ 2
        ≤ (MR * |c| * (|a - y| ^ (-psi))) ^ 2 :=
      sq_le_sq_of_nonneg' hx0 (by
        refine mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hbind a) (abs_nonneg c)) hz)
    calc (|(I : Set ℝ).indicator omega a| * |c| * (|a - y| ^ (-psi))) ^ 2
        ≤ (MR * |c| * (|a - y| ^ (-psi))) ^ 2 := h2
      _ = MR ^ 2 * |c| ^ 2 * (|a - y| ^ (-psi)) ^ 2 := by rw [mul_pow, mul_pow]
      _ = c ^ 2 * MR ^ 2 * (|a - y| ^ (-psi)) ^ 2 := by rw [sq_abs c]; ring
  have hintBig : MeasureTheory.Integrable
      (fun a : ℝ => c ^ 2 * MR ^ 2 * |a - y| ^ (-(2 * psi))) vol :=
    MeasureTheory.Integrable.const_mul (integrable_abs_sub_vol' (by linarith) y)
      (c ^ 2 * MR ^ 2)
  calc ∫ a : ℝ, |rieszKernel psi c omega (a, y)| ^ 2 ∂vol
      ≤ ∫ a : ℝ, c ^ 2 * MR ^ 2 * |a - y| ^ (-(2 * psi)) ∂vol :=
        MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun a => sq_nonneg _) hintBig
          (Filter.Eventually.of_forall fun a => ptw a)
    _ = c ^ 2 * MR ^ 2 * ∫ a : ℝ, |a - y| ^ (-(2 * psi)) ∂vol := by
        rw [MeasureTheory.integral_const_mul]
    _ = c ^ 2 * MR ^ 2 * ∫ a : ℝ, (I : Set ℝ).indicator
          (fun b : ℝ => |b - y| ^ (-(2 * psi))) a ∂vol := by
        rw [integral_abs_sub_vol_eq' (by linarith) y]
    _ ≤ c ^ 2 * MR ^ 2 * (2 + 2 / (1 - 2 * psi)) :=
        mul_le_mul_of_nonneg_left (fract_section_bound (s := 2 * psi) (by linarith) hpsi y)
          (by positivity)

/-- The carrier measure has total mass `2` (local copy of the private helper of
`Hurst.GeneralKHasSumFinal`; `I = Icc (-1:ℝ) 1` has length `2`). -/
private theorem vol_univ_eq_two' : ((vol : Measure ℝ) Set.univ) = 2 := by
  show (MeasureTheory.volume.restrict (I : Set ℝ)) Set.univ = 2
  rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Icc]
  norm_num

/-- **The six-form Riesz section-bounds package WITHOUT `hconst`** — verbatim the
conclusion shape of the landed `rieszKernel_sectionBounds_package` (and therefore
directly consumable by `hP_of_sectionBounds`), with the unsatisfiable constancy
premise removed: the column `L²` bound is supplied by the no-`hconst`
`rieszKernel_section_sq_col`, the row bound by the (already hconst-free) landed
`rieszKernel_section_sq_symm`, and the tower/`L¹` bounds follow by the landed
`compPowR_section_aux` and section Cauchy–Schwarz. -/
theorem rieszKernel_sectionBounds_nohconst {psi c : ℝ} {omega : ℝ → ℝ} {MR : ℝ}
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ MR)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
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
  have hintcol : ∀ z : ℝ, Integrable (fun a : ℝ => K (a, z) ^ 2) vol := by
    intro z
    have hdom : Integrable (fun a : ℝ => c ^ 2 * MR ^ 2 * |a - z| ^ (-(2 * psi))) vol :=
      integrable_abs_sub_vol' (by linarith) z |>.const_mul (c ^ 2 * MR ^ 2)
    refine hdom.mono ?_ ?_
    · exact (((measurable_rieszKernel homega).comp
        (measurable_id.prodMk measurable_const)).pow measurable_const).aestronglyMeasurable
    · filter_upwards with a
      have h := rieszKernel_sq_le_nohconst (psi := psi) (c := c) hbdd a z
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
        abs_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg c) (sq_nonneg MR))
          (Real.rpow_nonneg (abs_nonneg (a - z)) _))]
      exact h
  have hintrow : ∀ z : ℝ, Integrable (fun a : ℝ => K (z, a) ^ 2) vol := by
    intro z
    have hdom : Integrable (fun a : ℝ => c ^ 2 * MR ^ 2 * |a - z| ^ (-(2 * psi))) vol :=
      integrable_abs_sub_vol' (by linarith) z |>.const_mul (c ^ 2 * MR ^ 2)
    refine hdom.mono ?_ ?_
    · exact (((measurable_rieszKernel homega).comp
        (measurable_const.prodMk measurable_id)).pow measurable_const).aestronglyMeasurable
    · filter_upwards with a
      have h := rieszKernel_sq_le_nohconst (psi := psi) (c := c) hbdd z a
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
        abs_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg c) (sq_nonneg MR))
          (Real.rpow_nonneg (abs_nonneg (a - z)) _))]
      rw [abs_sub_comm z a] at h
      exact h
  have hEcol : ∀ y : ℝ, ∫ a : ℝ, K (a, y) ^ 2 ∂vol ≤ E := by
    intro y
    have hcongr : (∫ a : ℝ, K (a, y) ^ 2 ∂vol) = ∫ a : ℝ, |K (a, y)| ^ 2 ∂vol :=
      integral_congr_ae (Filter.Eventually.of_forall fun a => (sq_abs _).symm)
    rw [hcongr]
    exact rieszKernel_section_sq_col hbdd hpsi2 hpsi0 y
  have hErow : ∀ x : ℝ, ∫ a : ℝ, K (x, a) ^ 2 ∂vol ≤ E := by
    intro x
    have hcongr : (∫ a : ℝ, K (x, a) ^ 2 ∂vol) = ∫ a : ℝ, |K (x, a)| ^ 2 ∂vol :=
      integral_congr_ae (Filter.Eventually.of_forall fun a => (sq_abs _).symm)
    rw [hcongr]
    exact rieszKernel_section_sq_symm hbdd hpsi2 hpsi0 x
  have haux := compPowR_section_aux (K := K) (measurable_rieszKernel homega)
    (hsKernel_rieszKernel hpow homega hbdd hg) hEcol hErow hintcol hintrow
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
      rw [vol_univ_eq_two']
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

/-- **The peel-chain integrability at the Riesz kernel data, WITHOUT `hconst`** —
the `hP` hypothesis of `cycleIntegral_eq_cycle2_pow` discharged by the no-hconst
section package. -/
theorem hP_rieszKernel_nohconst {psi c : ℝ} {omega : ℝ → ℝ} {MR : ℝ}
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ MR)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hpsi2 : 2 * psi < 1) (hpsi0 : 0 ≤ psi) :
    ∀ (n r : ℕ), Integrable (peelChainProd (n + 2) (kchain n r (rieszKernel psi c omega)))
      (Measure.pi fun _ : Fin (n + 2) => vol) := by
  obtain ⟨hE1, hE2, hD1, hEK1, hEK2, hDK1⟩ :=
    rieszKernel_sectionBounds_nohconst hpow homega hbdd hg hpsi2 hpsi0
  exact hP_of_sectionBounds (measurable_rieszKernel homega) hE1 hE2 hD1 hEK1 hEK2 hDK1

/-! ### Steps 4–5 (kernel side): the power-diagonal identity -/

/-- **The kernel side of the D2 bridge (steps 3-RHS, 4, 5 of the compressed route),
with NO `hconst`**: for every `k ≥ 2` and every Hilbert basis `e`, the `k`-th
power-diagonal series of the **weighted kernel operator**
`TOp (rieszKernel psi c omega)` is (absolutely) summable, and its total is exactly
the weighted Riesz cycle integral:

    ∑' i, ⟪((TOp K_R) ^ k) (e i), e i⟫ = Hurst.weightedRieszCycleIntegral k psi c omega.

Route (all landed pieces, none needing symmetry of the weighted operator — this
is where the old `rieszSpectrumVal_hGen` line consumed the unsatisfiable
`hconst`): `hPair_riesz` (operator power = kernel tower) → `tracePair_comp_tsum`
(diagonal pairing = `cycle2` of the tower) → `cycleIntegral_eq_cycle2_pow` (peel
induction, integrability from `hP_rieszKernel_nohconst`) → `hW_bridge` (cycle
encoding). -/
theorem diagSum_TOpRiesz_pow_eq_weightedCycle {psi c : ℝ} {omega : ℝ → ℝ} {MR : ℝ}
    (hpow : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-psi)) vol2)
    (homega : Measurable omega) (hbdd : ∀ x : ℝ, |omega x| ≤ MR)
    (hg : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ (-2 * psi)) vol2)
    (hpsi2 : 2 * psi < 1) (hpsi0 : 0 ≤ psi)
    (k : ℕ) (hk : 2 ≤ k) (e : HilbertBasis ℕ ℝ L2) :
    Summable (fun i : ℕ =>
        inner ℝ ((TOp (rieszKernel psi c omega)
          (hsKernel_rieszKernel hpow homega hbdd hg) ^ k) (e i)) (e i))
      ∧ (∑' i : ℕ, inner ℝ ((TOp (rieszKernel psi c omega)
          (hsKernel_rieszKernel hpow homega hbdd hg) ^ k) (e i)) (e i))
        = Hurst.weightedRieszCycleIntegral k psi c omega := by
  classical
  obtain ⟨m, hm⟩ : ∃ m : ℕ, k = m + 2 := ⟨k - 2, by omega⟩
  subst hm
  have hKR : HSKernel (rieszKernel psi c omega) :=
    hsKernel_rieszKernel hpow homega hbdd hg
  have hKm : Measurable (rieszKernel psi c omega) := measurable_rieszKernel homega
  have hKL : HSKernel (compPowR m (rieszKernel psi c omega)) :=
    hsKernel_compPowR m hKm hKR
  -- per-index transport of the operator power to the kernel-tower action
  have hfam : ∀ i : ℕ,
      inner ℝ ((TOp (rieszKernel psi c omega) hKR ^ (m + 2)) (e i)) (e i)
        = inner ℝ (TOp (rieszKernel psi c omega) hKR
            (TOp (compPowR m (rieszKernel psi c omega)) hKL (e i))) (e i) := by
    intro i
    rw [← TOpEnd'_pow_apply hKR (m + 2) (e i),
      ← hPair_riesz hKm hKR (m + 2) (by omega) (e i)]
    rfl
  have hS := tracePair_comp_summable hKR hKL e
  refine ⟨hS.congr fun i => (hfam i).symm, ?_⟩
  calc (∑' i : ℕ,
        inner ℝ ((TOp (rieszKernel psi c omega) hKR ^ (m + 2)) (e i)) (e i))
      = ∑' i : ℕ, inner ℝ (TOp (rieszKernel psi c omega) hKR
            (TOp (compPowR m (rieszKernel psi c omega)) hKL (e i))) (e i) :=
        tsum_congr fun i => hfam i
    _ = HS.cycle2 (compPowR m (rieszKernel psi c omega)) (rieszKernel psi c omega) :=
        tracePair_comp_tsum hKR hKL e
    _ = cycleIntegral (m + 2) (rieszKernel psi c omega) :=
        (cycleIntegral_eq_cycle2_pow
          (hP_rieszKernel_nohconst hpow homega hbdd hg hpsi2 hpsi0) (n := m)).symm
    _ = Hurst.weightedRieszCycleIntegral (m + 2) psi c omega :=
        hW_bridge psi c omega (m + 2)

end HS
