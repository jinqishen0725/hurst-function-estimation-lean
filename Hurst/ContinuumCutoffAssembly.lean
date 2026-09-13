import Hurst.TruncatedRieszCycleBridge
import Hurst.HyperplaneNull
import Hurst.MeshFactorizationLimit

/-!
# Continuum cutoff removal for the cyclic Riesz integral, modulo an integrable dominator

This file assembles the analytic core of `HasContinuumRieszCutoffRemoval`: the passage from
the capped cyclic integral `weightedTruncatedRieszCycleIntegral k R psi c omega` to its
uncapped limit `weightedRieszCycleIntegral k psi c omega` as `R → ∞`, by Lebesgue dominated
convergence.

* The cyclic diagonal hyperplanes `{z | z i = z (finCyclicSucc i)}` form a null set
  (`cyclicHyperplaneUnion_null`), by `Hurst.HyperplaneNull`.
* Away from them each capped edge factor is eventually constant equal to its uncapped value
  (`continuumCutoffIntegrand_tendsto`), since `rieszCycleCutoff R = (R+1)⁻¹ → 0` and the cap
  is `max (rieszCycleCutoff R) |·|`.
* The truncated integrand is dominated, uniformly in `R`, by the uncapped-edge product
  `continuumCutoffDominator` (`continuumCutoffIntegrand_abs_le`): the cap can only make the
  edge *larger*, hence the negative power *smaller*.
* `continuumCutoffRemoval_of_integrable_dominator` concludes by dominated convergence under
  the single explicit hypothesis that the dominator is integrable.  Discharging that
  integrability (a T5'-style `|omega| ≤ 1` moment bound plus `k (1 − psi) > 0`) is a
  separate task.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace Hurst

/-! ### The cyclic successor is never the index itself -/

theorem finCyclicSucc_ne_self {k : ℕ} (hk : 2 ≤ k) (i : Fin k) : finCyclicSucc i ≠ i := by
  have hilt : i.val < k := i.isLt
  by_cases h : i.val + 1 < k
  · intro hcon
    have hcon' : i.val + 1 = i.val :=
      show i.val + 1 = i.val from Fin.ext_iff.mp (by simpa only [finCyclicSucc, dif_pos h] using hcon)
    omega
  · intro hcon
    have hcon' : (0 : ℕ) = i.val :=
      show (0 : ℕ) = i.val from
        Fin.ext_iff.mp (by simpa only [finCyclicSucc, dif_neg h] using hcon)
    omega

/-! ### The union of cyclic diagonal hyperplanes is Lebesgue-null -/

theorem cyclicHyperplaneUnion_null {k : ℕ} (hk : 2 ≤ k) :
    volume {z : Fin k → ℝ | ∃ i : Fin k, z i = z (finCyclicSucc i)} = 0 := by
  rw [show {z : Fin k → ℝ | ∃ i : Fin k, z i = z (finCyclicSucc i)}
      = ⋃ i : Fin k, {z : Fin k → ℝ | z i = z (finCyclicSucc i)} from by
    ext z
    simp]
  have hle : volume (⋃ i : Fin k, {z : Fin k → ℝ | z i = z (finCyclicSucc i)})
      ≤ ∑ i : Fin k, volume {z : Fin k → ℝ | z i = z (finCyclicSucc i)} := by
    rw [show (⋃ i : Fin k, {z : Fin k → ℝ | z i = z (finCyclicSucc i)})
        = ⋃ i ∈ Finset.univ, {z : Fin k → ℝ | z i = z (finCyclicSucc i)} from by
      simp]
    exact measure_biUnion_finset_le _ _
  have hzero : ∑ i : Fin k, volume {z : Fin k → ℝ | z i = z (finCyclicSucc i)} = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    exact measure_hyperplane_eq_zero
      (Ne.symm (finCyclicSucc_ne_self hk i))
  rw [hzero] at hle
  exact le_antisymm hle zero_le

/-! ### The cutoff tends to zero -/

theorem rieszCycleCutoff_tendsto_zero :
    Tendsto (fun R : ℕ => rieszCycleCutoff R) atTop (𝓝 0) := by
  unfold rieszCycleCutoff
  exact Filter.Tendsto.inv_tendsto_atTop
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat (1 : ℕ)))

theorem eventually_rieszCycleCutoff_lt (d : ℝ) (hd : 0 < d) :
    ∀ᶠ R : ℕ in atTop, rieszCycleCutoff R < d :=
  rieszCycleCutoff_tendsto_zero.eventually
    (IsOpen.mem_nhds isOpen_Iio (Set.mem_Iio.2 hd))

/-! ### The integrands -/

/-- Whole-space indicated form of the truncated cyclic integrand: exactly the integrand
appearing in `weightedTruncatedRieszCycleIntegral`. -/
def continuumCutoffIntegrand (k R : ℕ) (psi c : ℝ) (omega : ℝ → ℝ)
    (z : Fin k → ℝ) : ℝ :=
  ∏ i : Fin k, (Icc (-1 : ℝ) 1).indicator omega (z i) *
    truncatedRieszKernel R psi c (z i) (z (finCyclicSucc i))

/-- Pointwise limit integrand: exactly the integrand appearing in
`weightedRieszCycleIntegral`. -/
def continuumCutoffLimitIntegrand (k : ℕ) (psi c : ℝ) (omega : ℝ → ℝ)
    (z : Fin k → ℝ) : ℝ :=
  ∏ i : Fin k, (Icc (-1 : ℝ) 1).indicator omega (z i) * c *
    |z i - z (finCyclicSucc i)| ^ (-psi)

/-- The integrable dominator: the uncapped-edge product with the one-dimensional indicators
made explicit.  Off the null union of cyclic diagonals it dominates every truncated
integrand uniformly in `R`, because the cap `max (rieszCycleCutoff R) |·|` can only enlarge
the edge distance, hence shrink the negative power. -/
def continuumCutoffDominator (k : ℕ) (psi c : ℝ) (omega : ℝ → ℝ)
    (z : Fin k → ℝ) : ℝ :=
  ∏ i : Fin k, (Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) (z i) *
    (|omega (z i)| * |c| * |z i - z (finCyclicSucc i)| ^ (-psi))

theorem weightedTruncatedRieszCycleIntegral_eq (k R : ℕ) (psi c : ℝ) (omega : ℝ → ℝ) :
    weightedTruncatedRieszCycleIntegral k R psi c omega =
      ∫ z : Fin k → ℝ, continuumCutoffIntegrand k R psi c omega z := rfl

theorem weightedRieszCycleIntegral_eq (k : ℕ) (psi c : ℝ) (omega : ℝ → ℝ) :
    weightedRieszCycleIntegral k psi c omega =
      ∫ z : Fin k → ℝ, continuumCutoffLimitIntegrand k psi c omega z := rfl

theorem continuumCutoffIntegrand_eq_cube_indicator (k R : ℕ) (psi c : ℝ) (omega : ℝ → ℝ)
    (z : Fin k → ℝ) :
    continuumCutoffIntegrand k R psi c omega z =
      (Set.Icc (fun _ : Fin k => (-1 : ℝ)) (fun _ => 1)).indicator
        (weightedTruncatedRieszCycleIntegrand k R psi c omega) z := by
  rw [symmetricCube_indicator_weightedTruncatedRieszCycleIntegrand]
  rfl

theorem aestronglyMeasurable_continuumCutoffIntegrand (k R : ℕ) (psi c : ℝ)
    (omega : ℝ → ℝ) (homega : Continuous omega) :
    AEStronglyMeasurable (continuumCutoffIntegrand k R psi c omega)
      (volume : Measure (Fin k → ℝ)) := by
  have hfun : continuumCutoffIntegrand k R psi c omega =
      (Set.Icc (fun _ : Fin k => (-1 : ℝ)) (fun _ => 1)).indicator
        (weightedTruncatedRieszCycleIntegrand k R psi c omega) := by
    funext z
    exact continuumCutoffIntegrand_eq_cube_indicator k R psi c omega z
  rw [hfun]
  exact ((continuous_weightedTruncatedRieszCycleIntegrand k R psi c omega homega).measurable.indicator
    measurableSet_Icc).aestronglyMeasurable

/-! ### Domination, uniformly in the truncation level -/

theorem continuumCutoffIntegrand_abs_le (k R : ℕ) (psi c : ℝ) (omega : ℝ → ℝ)
    (hpsi : 0 < psi) {z : Fin k → ℝ} (hz : ∀ i : Fin k, z i ≠ z (finCyclicSucc i)) :
    |continuumCutoffIntegrand k R psi c omega z| ≤ continuumCutoffDominator k psi c omega z := by
  have hfac : ∀ i : Fin k,
      |(Icc (-1 : ℝ) 1).indicator omega (z i) *
          truncatedRieszKernel R psi c (z i) (z (finCyclicSucc i))| ≤
        (Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) (z i) *
          (|omega (z i)| * |c| * |z i - z (finCyclicSucc i)| ^ (-psi)) := by
    intro i
    have hdpos : 0 < |z i - z (finCyclicSucc i)| := abs_sub_pos.2 (hz i)
    have hmaxpos : 0 < max (rieszCycleCutoff R) |z i - z (finCyclicSucc i)| :=
      lt_of_lt_of_le (rieszCycleCutoff_pos R) (le_max_left _ _)
    have hker : |truncatedRieszKernel R psi c (z i) (z (finCyclicSucc i))|
        ≤ |c| * |z i - z (finCyclicSucc i)| ^ (-psi) := by
      unfold truncatedRieszKernel
      rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hmaxpos _)]
      refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hdpos
        (le_max_right _ _) (by linarith)) (abs_nonneg c)
    have hind : |(Icc (-1 : ℝ) 1).indicator omega (z i)| ≤
        (Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) (z i) * |omega (z i)| := by
      by_cases hm : z i ∈ Icc (-1 : ℝ) 1
      · simp only [Set.indicator_of_mem hm]
        exact (one_mul _).ge
      · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm]
        simp
    rw [abs_mul]
    refine le_trans (mul_le_mul_of_nonneg_right hind (abs_nonneg _)) ?_
    refine le_trans (mul_le_mul_of_nonneg_left hker
      (mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (abs_nonneg _))) ?_
    exact le_of_eq (by ring)
  calc
    |continuumCutoffIntegrand k R psi c omega z|
        = ∏ i : Fin k, |(Icc (-1 : ℝ) 1).indicator omega (z i) *
            truncatedRieszKernel R psi c (z i) (z (finCyclicSucc i))| := by
      simp only [continuumCutoffIntegrand, Finset.abs_prod, abs_mul]
    _ ≤ ∏ i : Fin k, (Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) (z i) *
          (|omega (z i)| * |c| * |z i - z (finCyclicSucc i)| ^ (-psi)) := by
      refine Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hfac i)
    _ = continuumCutoffDominator k psi c omega z := rfl

/-! ### Pointwise convergence off the diagonal hyperplanes -/

theorem continuumCutoffIntegrand_tendsto (k : ℕ) (psi c : ℝ) (omega : ℝ → ℝ)
    (z : Fin k → ℝ) (hz : ∀ i : Fin k, z i ≠ z (finCyclicSucc i)) :
    Tendsto (fun R : ℕ => continuumCutoffIntegrand k R psi c omega z) atTop
      (𝓝 (continuumCutoffLimitIntegrand k psi c omega z)) := by
  have hev : ∀ i : Fin k, ∀ᶠ R : ℕ in atTop,
      (Icc (-1 : ℝ) 1).indicator omega (z i) *
          truncatedRieszKernel R psi c (z i) (z (finCyclicSucc i)) =
        (Icc (-1 : ℝ) 1).indicator omega (z i) * c *
          |z i - z (finCyclicSucc i)| ^ (-psi) := by
    intro i
    have hdpos : 0 < |z i - z (finCyclicSucc i)| := abs_sub_pos.2 (hz i)
    filter_upwards [eventually_rieszCycleCutoff_lt _ hdpos] with R hR
    unfold truncatedRieszKernel
    rw [max_eq_right hR.le]
    ring
  simp only [continuumCutoffIntegrand, continuumCutoffLimitIntegrand]
  refine tendsto_finsetProd Finset.univ fun i _ => ?_
  exact (tendsto_congr' (hev i)).2 tendsto_const_nhds

/-! ### Main theorem: continuum cutoff removal modulo the dominator -/

/-- **Continuum cutoff removal for the cyclic Riesz integral, modulo a dominator.**

For every `k ≥ 2` and `0 < psi`, if the uncapped-edge dominator
`continuumCutoffDominator k psi c omega` is integrable on `(Fin k → ℝ)` with product Lebesgue
measure, then the truncated cyclic integrals converge to the untruncated cyclic integral:

`weightedTruncatedRieszCycleIntegral k R psi c omega → weightedRieszCycleIntegral k psi c omega`
as `R → ∞`.

This is precisely `HasContinuumRieszCutoffRemoval psi c omega` at each `k ≥ 2`, modulo the
single explicit integrability hypothesis; discharging it (the T5'-style analytic moment
bound) is a separate task.  The proof is Lebesgue dominated convergence: pointwise
convergence holds off the null union of cyclic diagonal hyperplanes (removal of the cutoff),
and the cap can only shrink the negative power, so the uncapped-edge product dominates every
truncation level uniformly. -/
theorem continuumCutoffRemoval_of_integrable_dominator
    (k : ℕ) (psi c : ℝ) (omega : ℝ → ℝ) (hk : 2 ≤ k) (hpsi : 0 < psi)
    (homega : Continuous omega)
    (hdom : Integrable (continuumCutoffDominator k psi c omega)
      (volume : Measure (Fin k → ℝ))) :
    Tendsto (fun R => weightedTruncatedRieszCycleIntegral k R psi c omega) atTop
      (𝓝 (weightedRieszCycleIntegral k psi c omega)) := by
  classical
  have hae_good : ∀ᵐ z ∂(volume : Measure (Fin k → ℝ)),
      ∀ i : Fin k, z i ≠ z (finCyclicSucc i) := by
    filter_upwards [(MeasureTheory.compl_mem_ae_iff
      (μ := (volume : Measure (Fin k → ℝ)))).2 (cyclicHyperplaneUnion_null hk)] with z hz i hcon
    exact hz ⟨i, hcon⟩
  have key := tendsto_integral_of_dominated_convergence
    (continuumCutoffDominator k psi c omega)
    (fun R => aestronglyMeasurable_continuumCutoffIntegrand k R psi c omega homega)
    hdom
    (fun R => by
      filter_upwards [hae_good] with z hz
      simpa [Real.norm_eq_abs] using
        continuumCutoffIntegrand_abs_le k R psi c omega hpsi hz)
    (by
      filter_upwards [hae_good] with z hz
      exact continuumCutoffIntegrand_tendsto k psi c omega z hz)
  show Tendsto (fun R : ℕ => ∫ z : Fin k → ℝ, continuumCutoffIntegrand k R psi c omega z) atTop
      (𝓝 (∫ z : Fin k → ℝ, continuumCutoffLimitIntegrand k psi c omega z))
  exact (tendsto_congr
    (fun R => weightedTruncatedRieszCycleIntegral_eq k R psi c omega)).2 key

/-- `HasContinuumRieszCutoffRemoval` holds at every `k ≥ 2` as soon as, for each such `k`,
the continuum dominator is integrable.  This is the analytic core of the cutoff-removal
predicate, modulo the explicit integrability hypothesis `hdom` (one per `k`); discharging
`hdom` by a T5'-style moment bound is a separate task. -/
theorem hasContinuumRieszCutoffRemoval_of_integrable_dominator
    (psi c : ℝ) (omega : ℝ → ℝ) (hpsi : 0 < psi) (homega : Continuous omega)
    (hdom : ∀ k : ℕ, 2 ≤ k →
      Integrable (continuumCutoffDominator k psi c omega)
        (volume : Measure (Fin k → ℝ))) :
    HasContinuumRieszCutoffRemoval psi c omega := by
  intro k hk
  exact continuumCutoffRemoval_of_integrable_dominator k psi c omega hk hpsi homega (hdom k hk)

end Hurst
