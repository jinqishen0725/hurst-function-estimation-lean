import Hurst.FrozenLagCorrelation
import Hurst.FrozenEstimates

noncomputable section
set_option maxHeartbeats 800000
open Set MeasureTheory Filter
open scoped RealInnerProductSpace Topology
namespace Hurst

/-- The scale-free covariance of two first increments with possibly different
Hurst parameters and a common mesh step. -/
def firstIncrementCrossLagCorrelation (h k x : ℝ) : ℝ :=
  harmonizableD ((h + k) / 2) ^ 2 / (2 * harmonizableD h * harmonizableD k) *
    (|x + 1| ^ (h + k) + |x - 1| ^ (h + k) - 2 * |x| ^ (h + k))

theorem firstIncrementCrossLagCorrelation_self (h x : ℝ)
    (hh : 0 < h) (hh1 : h < 1) :
    firstIncrementCrossLagCorrelation h h x = firstIncrementLagCorrelation h x := by
  have hD : harmonizableD h ≠ 0 := (harmonizableD_pos h hh hh1).ne'
  unfold firstIncrementCrossLagCorrelation firstIncrementLagCorrelation
  rw [show (h + h) / 2 = h by ring]
  rw [show h + h = 2 * h by ring]
  field_simp [hD]

/-- Exact cross-parameter fixed-lag formula.  The powers of the common mesh
step cancel, so the right side depends only on the two parameters and the lag. -/
theorem normalizedFrozenIncrement_cross_parameter_lag
    (h k : Ioo (0 : ℝ) 1) (s ℓ x : ℝ) (hℓ : 0 < ℓ) :
    ⟪normalizedFrozenIncrement h s ℓ,
      normalizedFrozenIncrement k (s + x * ℓ) ℓ⟫ =
      firstIncrementCrossLagCorrelation h k x := by
  unfold normalizedFrozenIncrement
  rw [real_inner_smul_left, real_inner_smul_right]
  have habs1 : |s + ℓ| ^ ((h : ℝ) + k) +
        |s + x * ℓ + ℓ| ^ ((h : ℝ) + k) -
        |s + ℓ - (s + x * ℓ + ℓ)| ^ ((h : ℝ) + k) -
        (|s + ℓ| ^ ((h : ℝ) + k) +
          |s + x * ℓ| ^ ((h : ℝ) + k) -
          |s + ℓ - (s + x * ℓ)| ^ ((h : ℝ) + k)) -
        (|s| ^ ((h : ℝ) + k) +
          |s + x * ℓ + ℓ| ^ ((h : ℝ) + k) -
          |s - (s + x * ℓ + ℓ)| ^ ((h : ℝ) + k)) +
        (|s| ^ ((h : ℝ) + k) +
          |s + x * ℓ| ^ ((h : ℝ) + k) -
          |s - (s + x * ℓ)| ^ ((h : ℝ) + k)) =
      ℓ ^ ((h : ℝ) + k) *
        (|x + 1| ^ ((h : ℝ) + k) + |x - 1| ^ ((h : ℝ) + k) -
          2 * |x| ^ ((h : ℝ) + k)) := by
    have e1 : |s + ℓ - (s + x * ℓ + ℓ)| = ℓ * |x| := by
      rw [show s + ℓ - (s + x * ℓ + ℓ) = -x * ℓ by ring,
        abs_mul, abs_neg, abs_of_pos hℓ]
      ring
    have e2 : |s + ℓ - (s + x * ℓ)| = ℓ * |x - 1| := by
      rw [show s + ℓ - (s + x * ℓ) = -(x - 1) * ℓ by ring,
        abs_mul, abs_neg, abs_of_pos hℓ]
      ring
    have e3 : |s - (s + x * ℓ + ℓ)| = ℓ * |x + 1| := by
      rw [show s - (s + x * ℓ + ℓ) = -(x + 1) * ℓ by ring,
        abs_mul, abs_neg, abs_of_pos hℓ]
      ring
    have e4 : |s - (s + x * ℓ)| = ℓ * |x| := by
      rw [show s - (s + x * ℓ) = -x * ℓ by ring,
        abs_mul, abs_neg, abs_of_pos hℓ]
      ring
    rw [e1, e2, e3, e4]
    simp_rw [Real.mul_rpow hℓ.le (abs_nonneg _)]
    ring
  simp only [inner_sub_left, inner_sub_right, harmonizableFeature_inner_formula]
  let c := harmonizableD (((h : ℝ) + k) / 2) ^ 2 /
    (2 * harmonizableD h * harmonizableD k)
  change ℓ ^ (-(h : ℝ)) * (ℓ ^ (-(k : ℝ)) *
    (c * (|s + ℓ| ^ ((h : ℝ) + k) + |s + x * ℓ + ℓ| ^ ((h : ℝ) + k) -
          |s + ℓ - (s + x * ℓ + ℓ)| ^ ((h : ℝ) + k)) -
      c * (|s| ^ ((h : ℝ) + k) + |s + x * ℓ + ℓ| ^ ((h : ℝ) + k) -
          |s - (s + x * ℓ + ℓ)| ^ ((h : ℝ) + k)) -
      (c * (|s + ℓ| ^ ((h : ℝ) + k) + |s + x * ℓ| ^ ((h : ℝ) + k) -
          |s + ℓ - (s + x * ℓ)| ^ ((h : ℝ) + k)) -
       c * (|s| ^ ((h : ℝ) + k) + |s + x * ℓ| ^ ((h : ℝ) + k) -
          |s - (s + x * ℓ)| ^ ((h : ℝ) + k))))) = _
  rw [show
    c * (|s + ℓ| ^ ((h : ℝ) + k) + |s + x * ℓ + ℓ| ^ ((h : ℝ) + k) -
          |s + ℓ - (s + x * ℓ + ℓ)| ^ ((h : ℝ) + k)) -
      c * (|s| ^ ((h : ℝ) + k) + |s + x * ℓ + ℓ| ^ ((h : ℝ) + k) -
          |s - (s + x * ℓ + ℓ)| ^ ((h : ℝ) + k)) -
      (c * (|s + ℓ| ^ ((h : ℝ) + k) + |s + x * ℓ| ^ ((h : ℝ) + k) -
          |s + ℓ - (s + x * ℓ)| ^ ((h : ℝ) + k)) -
       c * (|s| ^ ((h : ℝ) + k) + |s + x * ℓ| ^ ((h : ℝ) + k) -
          |s - (s + x * ℓ)| ^ ((h : ℝ) + k))) =
      c * (|s + ℓ| ^ ((h : ℝ) + k) + |s + x * ℓ + ℓ| ^ ((h : ℝ) + k) -
          |s + ℓ - (s + x * ℓ + ℓ)| ^ ((h : ℝ) + k) -
        (|s + ℓ| ^ ((h : ℝ) + k) + |s + x * ℓ| ^ ((h : ℝ) + k) -
          |s + ℓ - (s + x * ℓ)| ^ ((h : ℝ) + k)) -
        (|s| ^ ((h : ℝ) + k) + |s + x * ℓ + ℓ| ^ ((h : ℝ) + k) -
          |s - (s + x * ℓ + ℓ)| ^ ((h : ℝ) + k)) +
        (|s| ^ ((h : ℝ) + k) + |s + x * ℓ| ^ ((h : ℝ) + k) -
          |s - (s + x * ℓ)| ^ ((h : ℝ) + k))) by ring,
    habs1]
  have hcancel : ℓ ^ (-(h : ℝ)) *
      (ℓ ^ (-(k : ℝ)) * ℓ ^ ((h : ℝ) + k)) = 1 := by
    rw [← Real.rpow_add hℓ, ← Real.rpow_add hℓ]
    convert Real.rpow_zero ℓ using 1
    congr 1
    ring
  unfold firstIncrementCrossLagCorrelation
  change ℓ ^ (-(h : ℝ)) *
    (ℓ ^ (-(k : ℝ)) * (c * (ℓ ^ ((h : ℝ) + k) *
      (|x + 1| ^ ((h : ℝ) + k) + |x - 1| ^ ((h : ℝ) + k) -
        2 * |x| ^ ((h : ℝ) + k))))) = _
  dsimp only [c]
  calc
    _ = (ℓ ^ (-(h : ℝ)) * (ℓ ^ (-(k : ℝ)) * ℓ ^ ((h : ℝ) + k))) *
        (harmonizableD (((h : ℝ) + k) / 2) ^ 2 /
          (2 * harmonizableD h * harmonizableD k) *
            (|x + 1| ^ ((h : ℝ) + k) + |x - 1| ^ ((h : ℝ) + k) -
              2 * |x| ^ ((h : ℝ) + k))) := by ring
    _ = _ := by rw [hcancel, one_mul]

theorem firstIncrementCrossLagCorrelation_continuousAt
    (h k x : ℝ) (hh : 0 < h) (hh1 : h < 1)
    (hk : 0 < k) (hk1 : k < 1) :
    ContinuousAt
      (fun z : ℝ × ℝ => firstIncrementCrossLagCorrelation z.1 z.2 x) (h, k) := by
  have hDh : ContinuousAt harmonizableD h :=
    harmonizableD_continuousOn.continuousAt (Ioo_mem_nhds hh hh1)
  have hDk : ContinuousAt harmonizableD k :=
    harmonizableD_continuousOn.continuousAt (Ioo_mem_nhds hk hk1)
  have hmid : ContinuousAt (fun z : ℝ × ℝ => (z.1 + z.2) / 2) (h, k) :=
    (continuousAt_fst.add continuousAt_snd).div_const 2
  have hmpos : 0 < (h + k) / 2 := by linarith
  have hmone : (h + k) / 2 < 1 := by linarith
  have hDm0 : ContinuousAt harmonizableD ((h + k) / 2) :=
    harmonizableD_continuousOn.continuousAt (Ioo_mem_nhds hmpos hmone)
  have hDm : ContinuousAt
      (fun z : ℝ × ℝ => harmonizableD ((z.1 + z.2) / 2)) (h, k) := by
    convert (ContinuousAt.comp (f := fun z : ℝ × ℝ => (z.1 + z.2) / 2)
      hDm0 hmid) using 1
    ext z
    rfl
  have hexp : ContinuousAt (fun z : ℝ × ℝ => z.1 + z.2) (h, k) :=
    continuousAt_fst.add continuousAt_snd
  have hpow (y : ℝ) : ContinuousAt
      (fun z : ℝ × ℝ => |y| ^ (z.1 + z.2)) (h, k) :=
    continuousAt_const.rpow hexp (Or.inr (by dsimp; linarith))
  unfold firstIncrementCrossLagCorrelation
  apply ((hDm.pow 2).div
    ((continuousAt_const.mul (hDh.comp continuousAt_fst)).mul
      (hDk.comp continuousAt_snd)) ?_).mul
    (((hpow (x + 1)).add (hpow (x - 1))).sub
      (continuousAt_const.mul (hpow x)))
  have h1 := (harmonizableD_pos h hh hh1).ne'
  have h2 := (harmonizableD_pos k hk hk1).ne'
  dsimp
  exact mul_ne_zero (mul_ne_zero (by norm_num) h1) h2

theorem firstIncrementCrossLagCorrelation_tendsto
    (h k x : ℝ) (hh : 0 < h) (hh1 : h < 1)
    (hk : 0 < k) (hk1 : k < 1)
    (H K : ℕ → ℝ) (hH : Tendsto H atTop (𝓝 h))
    (hK : Tendsto K atTop (𝓝 k)) :
    Tendsto (fun n => firstIncrementCrossLagCorrelation (H n) (K n) x)
      atTop (𝓝 (firstIncrementCrossLagCorrelation h k x)) := by
  have hc :=
    (firstIncrementCrossLagCorrelation_continuousAt h k x hh hh1 hk hk1).tendsto
  have hp := hH.prodMk_nhds hK
  change Tendsto
    ((fun z : ℝ × ℝ => firstIncrementCrossLagCorrelation z.1 z.2 x) ∘
      fun n => (H n, K n)) atTop
    (𝓝 (firstIncrementCrossLagCorrelation h k x))
  exact hc.comp hp

theorem firstIncrementCrossLagCorrelation_tendsto_self
    (h x : ℝ) (hh : 0 < h) (hh1 : h < 1)
    (H K : ℕ → ℝ) (hH : Tendsto H atTop (𝓝 h))
    (hK : Tendsto K atTop (𝓝 h)) :
    Tendsto (fun n => firstIncrementCrossLagCorrelation (H n) (K n) x)
      atTop (𝓝 (firstIncrementLagCorrelation h x)) := by
  rw [← firstIncrementCrossLagCorrelation_self h x hh hh1]
  exact firstIncrementCrossLagCorrelation_tendsto h h x hh hh1 hh hh1 H K hH hK

end Hurst
