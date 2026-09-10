import Hurst.FrozenCrossLagCorrelation
import Hurst.SecondFrozen

noncomputable section
set_option maxHeartbeats 800000
open Set MeasureTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

/-- A normalized frozen second increment is the difference of two consecutive
normalized frozen first increments. -/
theorem normalizedFrozenSecondIncrement_eq_first_difference
    (h : Ioo (0 : ℝ) 1) (s ℓ : ℝ) :
    normalizedFrozenSecondIncrement h s ℓ =
      normalizedFrozenIncrement h (s + ℓ) ℓ -
        normalizedFrozenIncrement h s ℓ := by
  unfold normalizedFrozenSecondIncrement normalizedFrozenIncrement frozenSecondIncrement
  rw [show s + ℓ + ℓ = s + 2 * ℓ by ring]
  simp only [smul_sub, smul_add, smul_smul]
  module

/-- The scale-free covariance of two normalized frozen second increments with
possibly different Hurst parameters. -/
def secondIncrementCrossLagCovariance (h k x : ℝ) : ℝ :=
  2 * firstIncrementCrossLagCorrelation h k x -
    firstIncrementCrossLagCorrelation h k (x - 1) -
    firstIncrementCrossLagCorrelation h k (x + 1)

/-- Exact fixed-lag covariance formula for normalized frozen second
increments. -/
theorem normalizedFrozenSecondIncrement_cross_parameter_lag
    (h k : Ioo (0 : ℝ) 1) (s ℓ x : ℝ) (hℓ : 0 < ℓ) :
    ⟪normalizedFrozenSecondIncrement h s ℓ,
      normalizedFrozenSecondIncrement k (s + x * ℓ) ℓ⟫ =
      secondIncrementCrossLagCovariance h k x := by
  rw [normalizedFrozenSecondIncrement_eq_first_difference,
    normalizedFrozenSecondIncrement_eq_first_difference,
    inner_sub_left, inner_sub_right]
  have h00 := normalizedFrozenIncrement_cross_parameter_lag
    h k (s + ℓ) ℓ x hℓ
  have h01 := normalizedFrozenIncrement_cross_parameter_lag
    h k (s + ℓ) ℓ (x - 1) hℓ
  have h10 := normalizedFrozenIncrement_cross_parameter_lag
    h k s ℓ (x + 1) hℓ
  have h11 := normalizedFrozenIncrement_cross_parameter_lag
    h k s ℓ x hℓ
  have h00' :
      ⟪normalizedFrozenIncrement h (s + ℓ) ℓ,
        normalizedFrozenIncrement k (s + x * ℓ + ℓ) ℓ⟫ =
        firstIncrementCrossLagCorrelation h k x := by
    convert h00 using 1 <;> ring
  have h01' :
      ⟪normalizedFrozenIncrement h (s + ℓ) ℓ,
        normalizedFrozenIncrement k (s + x * ℓ) ℓ⟫ =
        firstIncrementCrossLagCorrelation h k (x - 1) := by
    convert h01 using 1 <;> ring
  have h10' :
      ⟪normalizedFrozenIncrement h s ℓ,
        normalizedFrozenIncrement k (s + x * ℓ + ℓ) ℓ⟫ =
        firstIncrementCrossLagCorrelation h k (x + 1) := by
    convert h10 using 1 <;> ring
  rw [h00', h01', inner_sub_right, h10', h11]
  unfold secondIncrementCrossLagCovariance
  ring

theorem secondIncrementCrossLagCovariance_continuousAt
    (h k x : ℝ) (hh : 0 < h) (hh1 : h < 1)
    (hk : 0 < k) (hk1 : k < 1) :
    ContinuousAt
      (fun z : ℝ × ℝ => secondIncrementCrossLagCovariance z.1 z.2 x) (h, k) := by
  unfold secondIncrementCrossLagCovariance
  exact (((continuousAt_const.mul
    (firstIncrementCrossLagCorrelation_continuousAt h k x hh hh1 hk hk1)).sub
      (firstIncrementCrossLagCorrelation_continuousAt h k (x - 1) hh hh1 hk hk1)).sub
        (firstIncrementCrossLagCorrelation_continuousAt h k (x + 1) hh hh1 hk hk1))

theorem secondIncrementCrossLagCovariance_tendsto
    (h k x : ℝ) (hh : 0 < h) (hh1 : h < 1)
    (hk : 0 < k) (hk1 : k < 1)
    (H K : ℕ → ℝ) (hH : Tendsto H atTop (𝓝 h))
    (hK : Tendsto K atTop (𝓝 k)) :
    Tendsto (fun n => secondIncrementCrossLagCovariance (H n) (K n) x)
      atTop (𝓝 (secondIncrementCrossLagCovariance h k x)) := by
  have hc :=
    (secondIncrementCrossLagCovariance_continuousAt h k x hh hh1 hk hk1).tendsto
  change Tendsto
    ((fun z : ℝ × ℝ => secondIncrementCrossLagCovariance z.1 z.2 x) ∘
      fun n => (H n, K n)) atTop
    (𝓝 (secondIncrementCrossLagCovariance h k x))
  exact hc.comp (hH.prodMk_nhds hK)

/-- The fixed-lag correlation of normalized frozen second increments at a
common Hurst parameter. -/
def secondIncrementLagCorrelation (h x : ℝ) : ℝ :=
  (2 * firstIncrementLagCorrelation h x -
    firstIncrementLagCorrelation h (x - 1) -
    firstIncrementLagCorrelation h (x + 1)) /
    (4 - (2 : ℝ) ^ (2 * h))

theorem secondIncrementCrossLagCovariance_self (h x : ℝ)
    (hh : 0 < h) (hh1 : h < 1) :
    secondIncrementCrossLagCovariance h h x =
      2 * firstIncrementLagCorrelation h x -
        firstIncrementLagCorrelation h (x - 1) -
        firstIncrementLagCorrelation h (x + 1) := by
  unfold secondIncrementCrossLagCovariance
  rw [firstIncrementCrossLagCorrelation_self h x hh hh1,
    firstIncrementCrossLagCorrelation_self h (x - 1) hh hh1,
    firstIncrementCrossLagCorrelation_self h (x + 1) hh hh1]

theorem secondIncrementLagCorrelation_continuousAt
    (h x : ℝ) (hh : 0 < h) (hh1 : h < 1) :
    ContinuousAt (fun z => secondIncrementLagCorrelation z x) h := by
  have hc (y : ℝ) : ContinuousAt (fun z => firstIncrementLagCorrelation z y) h :=
    (firstIncrementLagCorrelation_continuousOn y).continuousAt (Ioi_mem_nhds hh)
  have hnum : ContinuousAt (fun z =>
      2 * firstIncrementLagCorrelation z x -
        firstIncrementLagCorrelation z (x - 1) -
        firstIncrementLagCorrelation z (x + 1)) h :=
    ((continuousAt_const.mul (hc x)).sub (hc (x - 1))).sub (hc (x + 1))
  have hden : ContinuousAt (fun z : ℝ => 4 - (2 : ℝ) ^ (2 * z)) h := by
    have hpow : ContinuousAt (fun z : ℝ => (2 : ℝ) ^ (2 * z)) h :=
      continuousAt_const.rpow (continuousAt_const.mul continuousAt_id)
        (Or.inl (by norm_num))
    exact continuousAt_const.sub hpow
  have hden0 : 4 - (2 : ℝ) ^ (2 * h) ≠ 0 := by
    have hp : (2 : ℝ) ^ (2 * h) < 4 := by
      calc
        (2 : ℝ) ^ (2 * h) < (2 : ℝ) ^ (2 : ℝ) :=
          Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
        _ = 4 := by norm_num
    linarith
  unfold secondIncrementLagCorrelation
  exact hnum.div hden hden0

theorem secondIncrementLagCorrelation_tendsto
    (x h : ℝ) (hh : 0 < h) (hh1 : h < 1)
    (H : ℕ → ℝ) (hH : Tendsto H atTop (𝓝 h)) :
    Tendsto (fun n => secondIncrementLagCorrelation (H n) x)
      atTop (𝓝 (secondIncrementLagCorrelation h x)) :=
  (secondIncrementLagCorrelation_continuousAt h x hh hh1).tendsto.comp hH

end Hurst
